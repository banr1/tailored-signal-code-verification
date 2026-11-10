/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbEk
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4-KiB Hook Companion for `<EkSentCt1Received>::from_pb`

Proves `ek_sent_ct1_received_from_pb_ok_ext` and `ek_sent_ct1_received_from_pb_ok_x`
under `SpqrV1.Alloc.AllocContracts4K`.
-/

namespace CryptoVerification.SpqrV1.Unchunked.Ext4K

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L25

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

@[simp]
private theorem spqrAuthApi_from_pb (F : ShaCompress) :
    (spqrAuthApi F).from_pb = Authenticator.fromPb := rfl

@[local arm64_norm]
private theorem sub_beq_zero_eq_beq (x y : BitVec 64) :
  (x - y == 0#64) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : x - y ≠ 0#64 := by intro h0; apply h; bv_omega
    simp [h, hne]

@[local arm64_norm]
private theorem bne_eq_not_beq (x y : BitVec 64) :
    (x != y) = !(x == y) := rfl

private theorem authenticatorPBPinnedAt_48_entails_dealloc (A : RustAlloc)
    (ga : AuthenticatorPBGhost) (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 48#64) auth ⊢
      auth48HeadersAt a ⟨ga.rootKey, ga.macKey⟩ ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
        vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr := by
  rw [← twoVecHeadersAt_48_eq]
  exact authenticatorPBPinnedAt_entails_dealloc A ga (a + 48#64) auth

private theorem protoUnchunked2VecHeadersAt_entails_memRegion_104 (a : BitVec 64) (g : TwoVecGhost) :
    protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ⊢
      memRegion a 104 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56)
        (b' := a + 48#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 48) (k := 8)
        (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (twoVecHeadersAt_entails_memRegion_48 a g)

set_option maxHeartbeats 800000 in
private theorem ek_sent_ct1_received_from_pb_err_drop {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {out pbA : BitVec 64} {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    {v_out0 : BitVec 64} {v_out8 : BitVec 8}
    {g : TwoVecGhost}
    (hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName +
        bv% (ls_rel% "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr ekSentCt1ReceivedFromPbName + 176#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out)
    (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗
          optProtoAuthenticatorAt A (pbA + 48#64) pb.auth ∗
          memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
        A.pool ∗
        memRegion (s0.sp - 4304#64) 64 ∗
        stackAt (s0.sp - 144#64) allocHookStack ∗
        memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPostEk, ekSentCt1ReceivedFromPbSpec, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hcond, Bool.false_eq_true, ↓reduceIte,
    ekSentCt1ReceivedResultAt, stackAt_ekSentCt1ReceivedFromPb_split_allocHook, rustDeallocSpec]
    at hdealloc_raw ⊢
  ekSentCt1ReceivedFromPb_fetches b (Rust.withPanics ext) 176 120
  ekSentCt1ReceivedFromPb_fetches b (Rust.withPanics ext) 336 20
  dsimp only [tripleRatchetProgAtExt, ekSentCt1ReceivedFromPbName, BitVec.ofNat_eq_ofNat]
    at hdealloc_raw hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" = entry
  examples_hide_fetches
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine seq_clean (mid := entry + 236#64)
    (P_mid := (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
      (protoUnchunked2VecHeadersAt pbA g ∗
        memRegion (pbA + 48#64) 48 ∗
        memRegion (pbA + 96#64) 8 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
      A.pool ∗
      memRegion (s0.sp - 4304#64) 64 ∗
      stackAt (s0.sp - 144#64) allocHookStack ∗
      memRegion (s0.sp - 144#64) 96 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA)
    ?_ ?_
  · cases pb.auth with
    | none =>
      rw [optProtoAuthenticatorAt_48_none]
      have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 236#64) s1
          (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
            (protoUnchunked2VecHeadersAt pbA g ∗
              (((pbA + 48#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 56#64) 40) ∗
              memRegion (pbA + 96#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
            A.pool ∗
            memRegion (s0.sp - 4304#64) 64 ∗
            stackAt (s0.sp - 144#64) allocHookStack ∗
            memRegion (s0.sp - 144#64) 96 ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (fun sm Pm =>
            (Pm ⊢ (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
              (protoUnchunked2VecHeadersAt pbA g ∗
                (((pbA + 48#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 56#64) 40) ∗
                memRegion (pbA + 96#64) 8 ∗
                vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
              A.pool ∗
              memRegion (s0.sp - 4304#64) 64 ∗
              stackAt (s0.sp - 144#64) allocHookStack ∗
              memRegion (s0.sp - 144#64) 96 ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
            Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) := by
        wp_steps; refine align_pre (by dsimp only [noneCap]) ?_; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
          (optProtoAuthenticatorAt_48_none_entails_memRegion_48 A pbA)))))
        hstep
    | some a =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
          (protoAuthenticatorAt_entails_dealloc A (pbA + 48#64) a))))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro ga
      rw [twoVecHeadersAt_48_eq]
      have hpull_ga :
          (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
            (protoUnchunked2VecHeadersAt pbA g ∗
              (⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗
                auth48HeadersAt pbA ga ∗
                vecCapPtrDealloc A ga.v1.cap ga.v1.ptr ∗
                vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (pbA + 96#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
            A.pool ∗
            memRegion (s0.sp - 4304#64) 64 ∗
            stackAt (s0.sp - 144#64) allocHookStack ∗
            memRegion (s0.sp - 144#64) 96 ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) =
          (⌜ga.v1.cap.toNat < 2 ^ 63⌝ ∗
            (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
              (protoUnchunked2VecHeadersAt pbA g ∗
                (auth48HeadersAt pbA ga ∗
                  vecCapPtrDealloc A ga.v1.cap ga.v1.ptr ∗
                  vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
                memRegion (pbA + 96#64) 8 ∗
                vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
              A.pool ∗
              memRegion (s0.sp - 4304#64) 64 ∗
              stackAt (s0.sp - 144#64) allocHookStack ∗
              memRegion (s0.sp - 144#64) 96 ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) := by ac_rfl
      rw [hpull_ga]
      apply SepWP.pure_elim; intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      refine seq_clean (mid := entry + 216#64)
        (P_mid := (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
          (protoUnchunked2VecHeadersAt pbA g ∗
            (auth48HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
            memRegion (pbA + 96#64) 8 ∗
            vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
            vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
          A.pool ∗
          memRegion (s0.sp - 4304#64) 64 ∗
          stackAt (s0.sp - 144#64) allocHookStack ∗
          memRegion (s0.sp - 144#64) 96 ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA)
        ?_ ?_
      · dsimp only [auth48HeadersAt, vecCapPtrDealloc]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine align_pre (by dsimp only [noneCap]) ?_; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [noneCap]; ac_rfl) ?_; wp_done
      · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1⟩, hx19_a1⟩
        have hstepa2 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 236#64) sa1
            (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
              (protoUnchunked2VecHeadersAt pbA g ∗
                (auth48HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
                memRegion (pbA + 96#64) 8 ∗
                vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
              A.pool ∗
              memRegion (s0.sp - 4304#64) 64 ∗
              stackAt (s0.sp - 144#64) allocHookStack ∗
              memRegion (s0.sp - 144#64) 96 ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (fun sm Pm =>
              (Pm ⊢ (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
                (protoUnchunked2VecHeadersAt pbA g ∗
                  auth48HeadersAt pbA ga ∗
                  memRegion (pbA + 96#64) 8 ∗
                  vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
                  vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
                A.pool ∗
                memRegion (s0.sp - 4304#64) 64 ∗
                stackAt (s0.sp - 144#64) allocHookStack ∗
                memRegion (s0.sp - 144#64) 96 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
              Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) := by
          dsimp only [auth48HeadersAt, vecCapPtrDealloc]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_a1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
            (auth48HeadersAt_entails_memRegion_48 pbA ga)))))
          hstepa2
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2⟩
    refine seq_clean (mid := entry + 256#64)
      (P_mid := (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗
          memRegion (pbA + 48#64) 48 ∗
          memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
        A.pool ∗
        memRegion (s0.sp - 4304#64) 64 ∗
        stackAt (s0.sp - 144#64) allocHookStack ∗
        memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA)
      ?_ ?_
    · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]
        wp_done
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans
            (Entails.of_eq (show _ =
              (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8) ∗
              (A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) by
                unfold protoUnchunked2VecHeadersAt twoVecHeadersAt; ac_rfl))
            (sepConj_mono_left (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)))
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_apply
        wp_done

private theorem authenticatorAt_sub144_unpack (A : RustAlloc) (sp : BitVec 64)
    (auth : Authenticator) :
    authenticatorAt A (sp - 144#64) auth ⊢
      ∃∗ ca1 : BitVec 64, ∃∗ pa1 : BitVec 64,
      ∃∗ ca2 : BitVec 64, ∃∗ pa2 : BitVec 64,
        (((sp - 144#64) ↦₆₄ ca1) ∗ ((sp - 136#64) ↦₆₄ pa1) ∗
         ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp - 120#64) ↦₆₄ ca2) ∗ ((sp - 112#64) ↦₆₄ pa2) ∗
         ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)) ∗
        vecU8Payload A ca1 pa1 auth.rootKey ∗
        vecU8Payload A ca2 pa2 auth.macKey := by
  have h := authenticatorAt_unpack A (sp - 144#64) auth
  have h1 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have h2 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  have h3 : (sp - 144#64) + 24#64 = sp - 120#64 := by bv_omega
  have h4 : (sp - 144#64) + 32#64 = sp - 112#64 := by bv_omega
  have h5 : (sp - 144#64) + 40#64 = sp - 104#64 := by bv_omega
  rw [h1, h2, h3, h4, h5] at h
  exact h

set_option maxHeartbeats 1200000 in
private theorem ek_sent_ct1_received_from_pb_ok_after_auth {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {auth : ProtoAuthenticator}
    {ga : AuthenticatorPBGhost} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName +
        bv% (ls_rel% "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth)
    (hpc1 : s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr ekSentCt1ReceivedFromPbName + 80#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx19_1 : s1.readReg64 .x19 = pbA)
    (hx20_1 : s1.readReg64 .x20 = ga.rootKey.cap)
    (hx21_1 : s1.readReg64 .x21 = pb.epoch)
    (hx22_1 : s1.readReg64 .x22 = out)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         authenticatorPBPinnedAt A ga (pbA + 48#64) auth ∗
         ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A c1 p1 pb.dk ∗
         vecU8Payload A c2 p2 pb.ct1) ∗
        A.pool ∗
        stackAt (s0.sp - 144#64) authFromPbStack ∗
        authenticatorAt A (s0.sp - 144#64) (Authenticator.fromPb auth) ∗
        memRegion (s0.sp - 96#64) 48 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPostEk, ekSentCt1ReceivedFromPbSpec, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hcond, hauth, ↓reduceIte, spqrAuthApi, ekSentCt1ReceivedResultAt,
    stackAt_ekSentCt1ReceivedFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  ekSentCt1ReceivedFromPb_fetches b (Rust.withPanics ext) 80 96
  ekSentCt1ReceivedFromPb_fetches b (Rust.withPanics ext) 268 28
  ekSentCt1ReceivedFromPb_fetches b (Rust.withPanics ext) 336 20
  dsimp only [tripleRatchetProgAtExt, ekSentCt1ReceivedFromPbName, BitVec.ofNat_eq_ofNat]
    at hdealloc_raw hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" = entry
  examples_hide_fetches
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine seq_clean (mid := entry + 140#64)
    (P_mid := (ekSentCt1ReceivedAt A (F := F) out
        { epoch := pb.epoch, auth := Authenticator.fromPb auth,
          dk := pb.dk, ct1 := pb.ct1 } ∗
      (memRegion pbA 48 ∗
        auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗
        memRegion (pbA + 96#64) 8 ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
        vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗
      A.pool ∗
      memRegion (s0.sp - 4304#64) 64 ∗
      stackAt (s0.sp - 144#64) allocHookStack ∗
      memRegion (s0.sp - 144#64) 96 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧
      sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (authenticatorPBPinnedAt_48_entails_dealloc A ga pbA auth))))))))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (authenticatorAt_sub144_unpack A s0.sp (Authenticator.fromPb auth))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.SepWP.exists_left; intro ca1
    apply ProofLib.SepWP.exists_left; intro pa1
    apply ProofLib.SepWP.exists_left; intro ca2
    apply ProofLib.SepWP.exists_left; intro pa2
    rw [ProofLib.memRegion_cells (s0.sp - 96#64) 6 (by decide), memRegion_104_eq_cells13 out]
    cells_unfold
    simp only [ProofLib.cells_succ, ProofLib.cells_zero,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_right]
    wp_pull_exists
    wp_steps
    rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
    have hpack_out := ekSentCt1ReceivedAt_pack A (F := F) out
      ca1 pa1 ca2 pa2 c1 p1 c2 p2 pb.epoch
      (Authenticator.fromPb auth) pb.dk pb.ct1
    have hpack_sp := memRegion_ekSentCt1Received_scratch_restore s0.sp
      ca1 pa1 (BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length)
      ca2 pa2 (BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)
      c1 p1 (BitVec.ofNat 64 pb.dk.length)
      c2 p2 (BitVec.ofNat 64 pb.ct1.length)
    have hpack_pb := unpacked_ekSentCt1Received_headers_entails_memRegion_48_8 pbA
      c1 p1 (BitVec.ofNat 64 pb.dk.length)
      c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗
        ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗
        ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) ∗
        ((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗
        ((out + 64#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗
        ((out + 88#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        ((out + 96#64) ↦₆₄ pb.epoch)) ∗
       vecU8Payload A ca1 pa1 (Authenticator.fromPb auth).rootKey ∗
       vecU8Payload A ca2 pa2 (Authenticator.fromPb auth).macKey ∗
       vecU8Payload A c1 p1 pb.dk ∗
       vecU8Payload A c2 p2 pb.ct1) ∗
      (((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        ((pbA + 96#64) ↦₆₄ pb.epoch)) ∗
       auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗
       vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗
       vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗
      ((((s0.sp - 144#64) ↦₆₄ ca1) ∗ ((s0.sp - 136#64) ↦₆₄ pa1) ∗
        ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((s0.sp - 120#64) ↦₆₄ ca2) ∗ ((s0.sp - 112#64) ↦₆₄ pa2) ∗
        ((s0.sp - 104#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)) ∗
       (((s0.sp - 96#64) ↦₆₄ c1) ∗ ((s0.sp - 88#64) ↦₆₄ p1) ∗
        ((s0.sp - 80#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((s0.sp - 72#64) ↦₆₄ c2) ∗ ((s0.sp - 64#64) ↦₆₄ p2) ∗
        ((s0.sp - 56#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length))) ∗
      A.pool ∗
      memRegion (s0.sp - 4304#64) 64 ∗
      stackAt (s0.sp - 144#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) by ac_rfl))
      (sepConj_mono hpack_out (sepConj_mono (sepConj_mono_left hpack_pb) (sepConj_mono_left hpack_sp)))) ?_
    refine align_pre (by ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2, hx20_2⟩
    refine seq_clean (mid := entry + 160#64)
      (P_mid := (ekSentCt1ReceivedAt A (F := F) out
          { epoch := pb.epoch, auth := Authenticator.fromPb auth,
            dk := pb.dk, ct1 := pb.ct1 } ∗
        (memRegion pbA 48 ∗
          auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗
          memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗
        A.pool ∗
        memRegion (s0.sp - 4304#64) 64 ∗
        stackAt (s0.sp - 144#64) allocHookStack ∗
        memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA)
      ?_ ?_
    · dsimp only [auth48HeadersAt, vecCapPtrDealloc]
      by_cases hca1 : (ga.rootKey.cap == 0#64) = true <;>
        simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      dsimp only [auth48HeadersAt, vecCapPtrDealloc]
      by_cases hca2 : (ga.macKey.cap == 0#64) = true <;>
        simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (memRegion_48_auth48_8_entails_104 pbA ⟨ga.rootKey, ga.macKey⟩)
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]
        wp_done
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans
            (Entails.of_eq (show _ =
              (memRegion pbA 48 ∗ auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8) ∗
              (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ memRegion ga.macKey.ptr ga.macKey.cap.toNat) by
                unfold auth48HeadersAt; ac_rfl))
            (sepConj_mono_left (memRegion_48_auth48_8_entails_104 pbA ⟨ga.rootKey, ga.macKey⟩)))
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_apply
        wp_done

attribute [local irreducible] spqrAuthApi

set_option maxHeartbeats 800000 in
private theorem ek_sent_ct1_received_from_pb_auth_none {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {out pbA : BitVec 64} {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    {v_out0 : BitVec 64} {v_out8 : BitVec 8}
    {g : TwoVecGhost}
    (hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName +
        bv% (ls_rel% "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = none)
    (hpc1 : s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr ekSentCt1ReceivedFromPbName + 296#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out)
    (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗
          memRegion (pbA + 48#64) 48 ∗
          memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
        A.pool ∗
        memRegion (s0.sp - 4304#64) 64 ∗
        stackAt (s0.sp - 144#64) allocHookStack ∗
        memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPostEk, ekSentCt1ReceivedFromPbSpec, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hcond, hauth, ↓reduceIte,
    ekSentCt1ReceivedResultAt, stackAt_ekSentCt1ReceivedFromPb_split_allocHook, rustDeallocSpec]
    at hdealloc_raw ⊢
  ekSentCt1ReceivedFromPb_fetches b (Rust.withPanics ext) 264 92
  dsimp only [tripleRatchetProgAtExt, ekSentCt1ReceivedFromPbName, BitVec.ofNat_eq_ofNat]
    at hdealloc_raw hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" = entry
  examples_hide_fetches
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine seq_clean (mid := entry + 328#64)
    (P_mid := (((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 95) ∗
      (protoUnchunked2VecHeadersAt pbA g ∗
        memRegion (pbA + 48#64) 48 ∗
        memRegion (pbA + 96#64) 8 ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
      A.pool ∗
      memRegion (s0.sp - 4304#64) 64 ∗
      stackAt (s0.sp - 144#64) allocHookStack ∗
      memRegion (s0.sp - 144#64) 96 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA)
    ?_ ?_
  · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine align_pre (by dsimp only [noneCap]) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [noneCap]; ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2⟩
    dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
    by_cases hc2 : (g.v2.cap == 0#64) = true <;>
      simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
        (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)
        (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
      rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]
      wp_done
    · wp_steps
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
        (Entails.trans
          (Entails.of_eq (show _ =
            (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8) ∗
            (A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) by
              unfold protoUnchunked2VecHeadersAt twoVecHeadersAt; ac_rfl))
          (sepConj_mono_left (protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)))
        (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
      wp_apply
      wp_done

private theorem ek_sent_ct1_received_from_pb_err_drop_unpacked {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName +
        bv% (ls_rel% "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr ekSentCt1ReceivedFromPbName + 176#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out)
    (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A (pbA + 48#64) pb.auth ∗
         ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A c1 p1 pb.dk ∗
         vecU8Payload A c2 p2 pb.ct1) ∗
        A.pool ∗
        stackAt (s0.sp - 144#64) authFromPbStack ∗
        memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
  refine SepWP.weaken_pre
    (sepConj_mono (memRegion_104_err_split out)
      (sepConj_mono_left (unpacked_ekSentCt1Received_entails_dealloc A pbA c1 p1
        (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length)
        pb.epoch pb.auth pb.dk pb.ct1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0
  apply ProofLib.SepWP.exists_left; intro v_out8
  refine SepWP.weaken_pre ?_
    (ek_sent_ct1_received_from_pb_err_drop (v_out0 := v_out0) (v_out8 := v_out8) (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩)
      hdealloc_raw hcond hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align)
  exact Entails.of_eq (by ac_rfl)

private theorem ek_sent_ct1_received_from_pb_auth_none_unpacked {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName +
        bv% (ls_rel% "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = none)
    (hpc1 : s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr ekSentCt1ReceivedFromPbName + 296#64)
    (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out)
    (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A (pbA + 48#64) none ∗
         ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A c1 p1 pb.dk ∗
         vecU8Payload A c2 p2 pb.ct1) ∗
        A.pool ∗
        stackAt (s0.sp - 144#64) authFromPbStack ∗
        memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
  refine SepWP.weaken_pre
    (sepConj_mono (memRegion_104_err_split out)
      (sepConj_mono_left (Entails.trans
        (unpacked_ekSentCt1Received_entails_dealloc A pbA c1 p1
          (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length)
          pb.epoch none pb.dk pb.ct1)
        (sepConj_mono_right (sepConj_mono_left (by
          rw [optProtoAuthenticatorAt_48_none]
          exact optProtoAuthenticatorAt_48_none_entails_memRegion_48 A pbA)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0
  apply ProofLib.SepWP.exists_left; intro v_out8
  refine SepWP.weaken_pre ?_
    (ek_sent_ct1_received_from_pb_auth_none (v_out0 := v_out0) (v_out8 := v_out8) (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩)
      hdealloc_raw hcond hauth hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align)
  exact Entails.of_eq (by ac_rfl)

private theorem fnAddr_eq_sub_of_rel {P : Program} {n1 n2 : String} {k : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (hrel : (P.rebase b X).fnAddr n2 = (P.rebase b X).fnAddr n1 + BitVec.ofNat 64 k) :
    (P.rebase b X).fnAddr n1 = (P.rebase b X).fnAddr n2 - BitVec.ofNat 64 k := by
  rw [hrel, BitVec.add_sub_cancel]

private theorem sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

private theorem onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : sm.trace = s0.trace) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

private theorem sepWPp_pure_elim_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (h : φ → SepWPp prog ret s P' Q Qp oom)
    (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp oom := by
  rw [hf]
  exact SepWPp.pure_left h

private theorem sepWPp_call_ret {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))
    (fun sf _ _ hm => False.elim (by rw [hoom_eq] at hm; exact not_satisfies_false_sepConj hm))

private theorem add_neg_38492_eq (a : BitVec 64) :
    a - bv% (ls_rel% "<spqr::authenticator::Authenticator>::from_pb" "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb") =
      a + bv% (2 ^ 64 - ls_rel% "<spqr::authenticator::Authenticator>::from_pb" "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb") := by
  bv_omega

private theorem memRegion_144_96_split_48_48 (sp : BitVec 64) :
    memRegion (sp - 144#64) 96 =
      memRegion (sp - 144#64) 48 ∗
      memRegion (sp - 96#64) 48 :=
  ProofLib.memRegion_split' (b := sp - 144#64) (n := 48) (k := 48)
    (b' := sp - 96#64) rfl (by bv_omega) (by decide)

set_option maxHeartbeats 1200000 in
theorem ek_sent_ct1_received_from_pb_ok_ext {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName)
      (ekSentCt1ReceivedFromPbSpec A F) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName +
        bv% (ls_rel% "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := num% (ls_rel% "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" "__rustc::__rust_dealloc"))
      (b := b) (X := Rust.withPanics ext)
      ekSentCt1ReceivedFromPb_fnOff
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hA.dealloc
  have hauth_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekSentCt1ReceivedFromPbName +
        bv% (2 ^ 64 - ls_rel% "<spqr::authenticator::Authenticator>::from_pb" "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb"))
      (authFromPbPinnedSpec A) := sub_ok_of_addr_eq
    (by
      rw [← add_neg_38492_eq]
      exact fnAddr_eq_sub_of_rel (Program.fnAddr_rel
        (k := num% (ls_rel% "<spqr::authenticator::Authenticator>::from_pb" "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb"))
        (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::from_pb")
        ekSentCt1ReceivedFromPb_fnOff (by decide)))
    (CryptoVerification.SpqrV1.Auth.Ext4K.auth_from_pb_pinned_ok_ext hA)
  have h_after_auth := @ek_sent_ct1_received_from_pb_ok_after_auth A F b ext
  have h_auth_none := @ek_sent_ct1_received_from_pb_auth_none_unpacked A F b ext
  have h_err_drop := @ek_sent_ct1_received_from_pb_err_drop_unpacked A F b ext
  ekSentCt1ReceivedFromPb_fetches b (Rust.withPanics ext) 0 80
  dsimp only [tripleRatchetProgAtExt, ekSentCt1ReceivedFromPbName, BitVec.ofNat_eq_ofNat]
    at hdealloc_raw hauth_raw h_after_auth h_auth_none h_err_drop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb" = entry
  examples_hide_fetches
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align_bv : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hpre' : s0.mem ⊨
      (memRegion out 104 ∗ protoUnchunkedEkSentCt1ReceivedAt A pbA pb ∗
        A.pool ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack) ∗ R ∧
      s0.readReg64 .x0 = out ∧ s0.readReg64 .x1 = pbA := by
    simp only [ekSentCt1ReceivedFromPbSpec] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact ⟨hpre.2, hpre.1⟩
  rcases hpre' with ⟨hm0, hx0, hx1⟩
  refine ⟨memRegion out 104 ∗ protoUnchunkedEkSentCt1ReceivedAt A pbA pb ∗
    A.pool ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack, R, hm0, ?_⟩
  rw [stackAt_ekSentCt1ReceivedFromPb_split s0.sp]
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_unpack A pbA pb))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro c1
  apply SepWPp.exists_elim; intro p1
  apply SepWPp.exists_elim; intro c2
  apply SepWPp.exists_elim; intro p2
  apply sepWPp_pure_elim_focus (pb.dk.length < 2 ^ 63 ∧ pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63)
  intro ⟨hl1, hl2, _⟩
  cells_unfold
  apply SepWPp.exists_elim; intro fp_old
  apply SepWPp.exists_elim; intro lr_old
  apply SepWPp.exists_elim; intro x22_old
  apply SepWPp.exists_elim; intro x21_old
  apply SepWPp.exists_elim; intro x20_old
  apply SepWPp.exists_elim; intro x19_old
  by_cases hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
      pb.ct1.length == CIPHERTEXT1_SIZE) = true
  · have hdk_t : (BitVec.ofNat 64 pb.dk.length == 2400#64) = true := by
      rw [ofNat_beq_lit_iff hl1 (by decide)]
      simp only [Bool.and_eq_true] at hcond; exact hcond.1
    have hct1_t : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true := by
      rw [ofNat_beq_lit_iff hl2 (by decide)]
      simp only [Bool.and_eq_true] at hcond; exact hcond.2
    cases hauth : pb.auth with
    | none =>
      apply SepWPp.of_sepWP_ret
      rw [optProtoAuthenticatorAt_48_none]
      refine seq_clean (mid := entry + 296#64)
        (P_mid := (memRegion out 104 ∗
          ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
           ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
           optProtoAuthenticatorAt A (pbA + 48#64) none ∗
           ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
           vecU8Payload A c1 p1 pb.dk ∗
           vecU8Payload A c2 p2 pb.ct1) ∗
          A.pool ∗
          stackAt (s0.sp - 144#64) authFromPbStack ∗
          memRegion (s0.sp - 144#64) 96 ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧
          sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA)
        ?_ ?_
      · wp_steps
        rw [optProtoAuthenticatorAt_48_none]
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19, noneCap]; ac_rfl) ?_
        wp_done
      · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1, hx19_1⟩
        exact h_auth_none hdealloc_raw hcond hauth
          hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv
    | some auth =>
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        optProtoAuthenticatorAt A (pbA + 48#64) (some auth) ∗
        (memRegion out 104 ∗
         (pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A c1 p1 pb.dk ∗
         vecU8Payload A c2 p2 pb.ct1 ∗
         A.pool ∗
         stackAt (s0.sp - 144#64) authFromPbStack ∗
         memRegion (s0.sp - 144#64) 96 ∗
         ((s0.sp - 48#64) ↦₆₄ fp_old) ∗ ((s0.sp - 40#64) ↦₆₄ lr_old) ∗
         ((s0.sp - 32#64) ↦₆₄ x22_old) ∗ ((s0.sp - 24#64) ↦₆₄ x21_old) ∗
         ((s0.sp - 16#64) ↦₆₄ x20_old) ∗ ((s0.sp - 8#64) ↦₆₄ x19_old)) by ac_rfl))
        (sepConj_mono_left (optProtoAuthenticatorAt_some_unpack A (pbA + 48#64) auth))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro ga
      apply sepWPp_pure_elim_focus (ga.rootKey.cap.toNat < 2 ^ 63); intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      rw [memRegion_144_96_split_48_48 s0.sp]
      refine sepWPp_seq_clean
        (mid := entry + bv% (2 ^ 64 - ls_rel% "<spqr::authenticator::Authenticator>::from_pb" "<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb"))
        (P_mid := (memRegion (s0.sp - 144#64) 48 ∗
          authenticatorPBPinnedAt A ga (pbA + 48#64) auth ∗
          A.pool ∗
          stackAt (s0.sp - 144#64) authFromPbStack) ∗
          (memRegion out 104 ∗
           ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
            ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
            ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
            vecU8Payload A c1 p1 pb.dk ∗
            vecU8Payload A c2 p2 pb.ct1) ∗
           memRegion (s0.sp - 96#64) 48 ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q_regs := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧
          sm.readReg64 .x0 = s0.sp - 144#64 ∧ sm.readReg64 .x1 = pbA + 48#64 ∧
          sm.readReg64 .lr = entry + 80#64 ∧
          sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap ∧
          sm.readReg64 .x21 = pb.epoch ∧ sm.readReg64 .x22 = out)
        ?_ ?_
      · wp_steps
        rw [← sepConj_assoc ((pbA + 48#64) ↦₆₄ ga.rootKey.cap),
            ← authenticatorPBPinnedAt_eq_cap_tail A ga (pbA + 48#64) auth]
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_
        wp_done
      · intro sm hpcm hrunm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx0_m, hx1_m, hlr_m, hx19_m, hx20_m, hx21_m, hx22_m⟩
        have hsp_align_m : sm.spAligned = true := by
          simp only [State.spAligned, hsp_m, sp_and_15_sub_aligned s0.sp 144#64 (by decide)]
          exact hsp_align_bv
        refine sepWPp_call_ret hauth_raw
          (x := ⟨s0.sp - 144#64, pbA + 48#64, ga, auth⟩)
          hpcm hrunm hsp_align_m hlr_m ?_ ?_ (fun _ _ => rfl) ?_
        · intro R' hm'
          dsimp only [authFromPbPinnedSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0_m, hx1_m⟩, ?_⟩
          exact Satisfies.mono (Entails.of_eq (by rw [hsp_m])) hm'
        · intro sf
          dsimp only [authFromPbPinnedSpec, ekSentCt1ReceivedFromPbSpec]
          exact onPanic_frame_entails htrace_m
        · intro s1 hpc1 hrun1 hsp1 hcs1
          rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1,
            hx27_1, hx28_1, _, hvregs_1⟩
          rw [hx19_m] at hx19_1
          rw [hx20_m] at hx20_1
          rw [hx21_m] at hx21_1
          rw [hx22_m] at hx22_1
          rw [hx23_m] at hx23_1
          rw [hx24_m] at hx24_1
          rw [hx25_m] at hx25_1
          rw [hx26_m] at hx26_1
          rw [hx27_m] at hx27_1
          rw [hx28_m] at hx28_1
          rw [hsp_m] at hsp1
          dsimp only [authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply ProofLib.SepWP.pure_elim; intro htrace_s1
          rw [htrace_m] at htrace_s1
          have hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64) :=
            ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp1, htrace_s1, hvregs_1.trans hvregs_m⟩
          exact SepWP.weaken_pre (Entails.of_eq (by rw [hsp_m]; ac_rfl))
            (h_after_auth hdealloc_raw hcond hauth
              hpc1 hrun1 hpres1 hx19_1 hx20_1 hx21_1 hx22_1 hsp_align_bv)
  · apply SepWPp.of_sepWP_ret
    have hcond_f : (pb.dk.length == DECAPSULATION_KEY_SIZE &&
        pb.ct1.length == CIPHERTEXT1_SIZE) = false := Bool.eq_false_iff.mpr hcond
    refine seq_clean (mid := entry + 176#64)
      (P_mid := (memRegion out 104 ∗
        ((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
         ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
         optProtoAuthenticatorAt A (pbA + 48#64) pb.auth ∗
         ((pbA + 96#64) ↦₆₄ pb.epoch) ∗
         vecU8Payload A c1 p1 pb.dk ∗
         vecU8Payload A c2 p2 pb.ct1) ∗
        A.pool ∗
        stackAt (s0.sp - 144#64) authFromPbStack ∗
        memRegion (s0.sp - 144#64) 96 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧
        sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA)
      ?_ ?_
    · by_cases h1 : (BitVec.ofNat 64 pb.dk.length == 2400#64) = true
      · by_cases h2 : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true
        · exfalso; apply hcond
          rw [ofNat_beq_lit_iff hl1 (by decide)] at h1
          rw [ofNat_beq_lit_iff hl2 (by decide)] at h2
          simp [h1, h2, DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE]
        · have h2_f : (BitVec.ofNat 64 pb.ct1.length == 960#64) = false := Bool.eq_false_iff.mpr h2
          wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
      · have h1_f : (BitVec.ofNat 64 pb.dk.length == 2400#64) = false := Bool.eq_false_iff.mpr h1
        wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1, hx19_1⟩
      exact h_err_drop hdealloc_raw hcond_f
        hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv

theorem ek_sent_ct1_received_from_pb_ok_x {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : AllocContracts4K img.base A ext) :
    EkSentCt1ReceivedFromPbOkX img A F ext := by
  dsimp only [EkSentCt1ReceivedFromPbOkX]
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (ek_sent_ct1_received_from_pb_ok_ext hA).mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout


end CryptoVerification.SpqrV1.Unchunked.Ext4K
