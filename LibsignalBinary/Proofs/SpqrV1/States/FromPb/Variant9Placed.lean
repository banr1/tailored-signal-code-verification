/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.UnchunkedFromPbClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9d
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlaced
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPb
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 9 (`Ct1Acknowledged`, `+444`, Block `333`) — Top-Level Proof

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant9.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9Placed

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9cPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 blkPC_339 lsProg_339 blkPl_339 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 0. `withLsCodeLoaded` `SepWP` / `SepWPp` Helpers & Block `339` Callee Contract -/

section Ct1SentFromPbPlaced
set_option hygiene false

private abbrev drop_seq_clean := @_root_.CryptoVerification.SpqrV1.Drop.seq_clean
private abbrev drop_align_pre := @_root_.CryptoVerification.SpqrV1.Drop.align_pre

@[local arm64_norm] private theorem sub_beq_zero_eq_beq (x y : BitVec 64) : (x - y == 0#64) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : x - y ≠ 0#64 := by intro h0; apply h; bv_omega
    simp [h, hne]

@[local arm64_norm] private theorem bne_eq_not_beq (x y : BitVec 64) : (x != y) = !(x == y) := rfl

private theorem onPanic_frame_entails {s0 sm sf : State} {F : SepProp} (htrace : sm.trace = s0.trace) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]; apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢; rw [htrace] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

private theorem sepWPp_pure_elim_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (h : φ → SepWPp prog ret s P' Q Qp oom) (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp oom := by rw [hf]; exact SepWPp.pure_left h

private theorem sepWPp_call_ret {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf) (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))
    (fun sf _ _ hm => False.elim (by rw [hoom_eq] at hm; exact not_satisfies_false_sepConj hm))

private theorem authenticatorAt_sub168_unpack (A : RustAlloc) (sp : BitVec 64) (auth : Authenticator) :
    authenticatorAt A (sp - 168#64) auth ⊢
      ∃∗ ca1 : BitVec 64, ∃∗ pa1 : BitVec 64, ∃∗ ca2 : BitVec 64, ∃∗ pa2 : BitVec 64,
        (((sp - 168#64) ↦₆₄ ca1) ∗ ((sp - 160#64) ↦₆₄ pa1) ∗ ((sp - 152#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp - 144#64) ↦₆₄ ca2) ∗ ((sp - 136#64) ↦₆₄ pa2) ∗ ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)) ∗
        vecU8Payload A ca1 pa1 auth.rootKey ∗ vecU8Payload A ca2 pa2 auth.macKey := by
  have h := authenticatorAt_unpack A (sp - 168#64) auth
  have h1 : (sp - 168#64) + 8#64 = sp - 160#64 := by bv_omega
  have h2 : (sp - 168#64) + 16#64 = sp - 152#64 := by bv_omega
  have h3 : (sp - 168#64) + 24#64 = sp - 144#64 := by bv_omega
  have h4 : (sp - 168#64) + 32#64 = sp - 136#64 := by bv_omega
  have h5 : (sp - 168#64) + 40#64 = sp - 128#64 := by bv_omega
  rwa [h1, h2, h3, h4, h5] at h

private theorem authenticatorPBPinnedAt_72_entails_dealloc (A : RustAlloc)
    (ga : AuthenticatorPBGhost) (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 72#64) auth ⊢ auth72HeadersAt a ⟨ga.rootKey, ga.macKey⟩ ∗
      vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr := by
  rw [← twoVecHeadersAt_72_eq]; exact authenticatorPBPinnedAt_entails_dealloc A ga (a + 72#64) auth

private theorem memRegion_176_128_split_8_48_72 (sp : BitVec 64) :
    memRegion (sp - 176#64) 128 = memRegion (sp - 176#64) 8 ∗ memRegion (sp - 168#64) 48 ∗ memRegion (sp - 120#64) 72 := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 120) (b' := sp - 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 168#64) (n := 48) (k := 72) (b' := sp - 120#64) rfl (by bv_omega) (by decide)]

private theorem sepWP_pure_elim_focus {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P Rest : SepProp} {Q : State → SepProp → Prop}
    (h : φ → SepWP prog ret s Rest Q) (heq : P = ⌜φ⌝ ∗ Rest := by sep_focus) :
    SepWP prog ret s P Q := by rw [heq]; exact SepWP.pure_elim h

local macro "saved48S0" sp:term "," s0:term : term =>
  `((($sp - 48#64) ↦₆₄ ($s0).readReg64 .fp) ∗ (($sp - 40#64) ↦₆₄ ($s0).readReg64 .lr) ∗
    (($sp - 32#64) ↦₆₄ ($s0).readReg64 .x22) ∗ (($sp - 24#64) ↦₆₄ ($s0).readReg64 .x21) ∗
    (($sp - 16#64) ↦₆₄ ($s0).readReg64 .x20) ∗ (($sp - 8#64) ↦₆₄ ($s0).readReg64 .x19))
local macro "saved48Vars" sp:term "," fp:term "," lr:term "," x22:term "," x21:term "," x20:term "," x19:term : term =>
  `((($sp - 48#64) ↦₆₄ $fp) ∗ (($sp - 40#64) ↦₆₄ $lr) ∗ (($sp - 32#64) ↦₆₄ $x22) ∗
    (($sp - 24#64) ↦₆₄ $x21) ∗ (($sp - 16#64) ↦₆₄ $x20) ∗ (($sp - 8#64) ↦₆₄ $x19))
local macro "ct1Tail" A:term "," s0:term : term =>
  `(($A).pool ∗ memRegion (($s0).sp - 4336#64) 64 ∗ stackAt (($s0).sp - 176#64) allocHookStack ∗
    memRegion (($s0).sp - 176#64) 128 ∗ (saved48S0 ($s0).sp, $s0))
local macro "ct1OutNone" out:term : term => `(($out ↦₆₄ noneCap) ∗ (($out + 8#64) ↦₈ 0#8) ∗ memRegion ($out + 9#64) 119)
local macro "ct1Vecs" A:term "," pbA:term "," pb:term "," c1:term "," p1:term "," c2:term "," p2:term "," c3:term "," p3:term : term =>
  `(($pbA ↦₆₄ $c1) ∗ (($pbA + 8#64) ↦₆₄ $p1) ∗ (($pbA + 16#64) ↦₆₄ BitVec.ofNat 64 ($pb).hdr.length) ∗
    (($pbA + 24#64) ↦₆₄ $c2) ∗ (($pbA + 32#64) ↦₆₄ $p2) ∗ (($pbA + 40#64) ↦₆₄ BitVec.ofNat 64 ($pb).es.length) ∗
    (($pbA + 48#64) ↦₆₄ $c3) ∗ (($pbA + 56#64) ↦₆₄ $p3) ∗ (($pbA + 64#64) ↦₆₄ BitVec.ofNat 64 ($pb).ct1.length) ∗
    (($pbA + 120#64) ↦₆₄ ($pb).epoch) ∗ vecU8Payload $A $c1 $p1 ($pb).hdr ∗ vecU8Payload $A $c2 $p2 ($pb).es ∗ vecU8Payload $A $c3 $p3 ($pb).ct1)
local macro "ct1Unpacked" A:term "," pbA:term "," pb:term "," authOpt:term "," c1:term "," p1:term "," c2:term "," p2:term "," c3:term "," p3:term : term =>
  `(($pbA ↦₆₄ $c1) ∗ (($pbA + 8#64) ↦₆₄ $p1) ∗ (($pbA + 16#64) ↦₆₄ BitVec.ofNat 64 ($pb).hdr.length) ∗
    (($pbA + 24#64) ↦₆₄ $c2) ∗ (($pbA + 32#64) ↦₆₄ $p2) ∗ (($pbA + 40#64) ↦₆₄ BitVec.ofNat 64 ($pb).es.length) ∗
    (($pbA + 48#64) ↦₆₄ $c3) ∗ (($pbA + 56#64) ↦₆₄ $p3) ∗ (($pbA + 64#64) ↦₆₄ BitVec.ofNat 64 ($pb).ct1.length) ∗
    $authOpt ∗ (($pbA + 120#64) ↦₆₄ ($pb).epoch) ∗ vecU8Payload $A $c1 $p1 ($pb).hdr ∗ vecU8Payload $A $c2 $p2 ($pb).es ∗ vecU8Payload $A $c3 $p3 ($pb).ct1)

set_option maxHeartbeats 800000 in
private theorem ct1_sent_from_pb_err_drop_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA : BitVec 64} {pb : V1State.Unchunked.Ct1Sent}
    {R : SepProp} {s0 s1 : State} {v_out0 : BitVec 64} {v_out8 : BitVec 8} {g : ThreeVecGhost}
    (hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_339).base + 236#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 176#64)) (hx0_1 : s1.readReg64 .x0 = out)
    (hx19_1 : s1.readReg64 .x19 = pbA) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_339).rebase (blkPl_339).base H) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 119) ∗
        (protoUnchunked3VecHeadersAt pbA g ∗ optProtoAuthenticatorAt A (pbA + 72#64) pb.auth ∗
          memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)
      (WppPost (ct1SentFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPost, ct1SentFromPbSpec, Unchunked.SendCt.Ct1Sent.from_pb, hcond, Bool.false_eq_true, ↓reduceIte,
    ct1SentResultAt, stackAt_ct1SentFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine drop_seq_clean (mid := (blkPl_339).base + 296#64)
    (P_mid := ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗
      memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
      vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
  · cases pb.auth with
    | none =>
      rw [optProtoAuthenticatorAt_72_none]
      have hstep : SepWP ((blkPC_339).rebase (blkPl_339).base H) ((blkPl_339).base + 296#64) s1
          (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 119) ∗
            (protoUnchunked3VecHeadersAt pbA g ∗ (((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40) ∗
              memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)
          (fun sm Pm => (Pm ⊢ ((ct1OutNone out) ∗
            (protoUnchunked3VecHeadersAt pbA g ∗ (((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40) ∗
              memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)) ∧
            Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) := by
        wp_steps; refine drop_align_pre (by dsimp only [noneCap]) ?_; wp_done
      exact SepWP.strengthen_entails_const (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (optProtoAuthenticatorAt_72_none_entails_memRegion_48 A pbA))))) hstep
    | some a =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (protoAuthenticatorAt_entails_dealloc A (pbA + 72#64) a))))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro ga; rw [twoVecHeadersAt_72_eq]
      apply sepWP_pure_elim_focus (ga.v1.cap.toNat < 2 ^ 63); intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      refine drop_seq_clean (mid := (blkPl_339).base + 276#64)
        (P_mid := ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗
          (auth72HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (pbA + 120#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · dsimp only [auth72HeadersAt, vecCapPtrDealloc]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine drop_align_pre (by dsimp only [noneCap]; ac_rfl) ?_; wp_done
        · wp_steps; wp_apply; refine drop_align_pre (by rw [hsp_1]; dsimp only [noneCap]; ac_rfl) ?_; wp_done
      · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1⟩, hx19_a1⟩
        have hstepa2 : SepWP ((blkPC_339).rebase (blkPl_339).base H) ((blkPl_339).base + 296#64) sa1
            ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗
              (auth72HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (pbA + 120#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
              vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)
            (fun sm Pm => (Pm ⊢ ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗ auth72HeadersAt pbA ga ∗
              memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0)) ∧
              Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) := by
          dsimp only [auth72HeadersAt, vecCapPtrDealloc]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine drop_align_pre (by rw [hsp_a1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
          (sepConj_mono_left (auth72HeadersAt_entails_memRegion_48 pbA ga))))) hstepa2
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2⟩
    refine drop_seq_clean (mid := (blkPl_339).base + 316#64)
      (P_mid := ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗
        memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine drop_align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      refine drop_seq_clean (mid := (blkPl_339).base + 336#64)
        (P_mid := ((ct1OutNone out) ∗ (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗
          memRegion (pbA + 120#64) 8 ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗ ct1Tail A, s0))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine drop_align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
      · intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩, hx19_4⟩
        dsimp only [protoUnchunked3VecHeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;> simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (protoUnchunked3VecHeadersAt_entails_memRegion_128 pbA g)
            (sepConj_mono_right (stackAt_ct1SentFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
          rw [stackAt_ct1SentFromPb_split_allocHook s0.sp]; wp_done
        · wp_steps
          refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
            (Entails.trans (Entails.of_eq (show _ =
              (protoUnchunked3VecHeadersAt pbA g ∗ memRegion (pbA + 72#64) 48 ∗ memRegion (pbA + 120#64) 8) ∗
              (A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) by unfold protoUnchunked3VecHeadersAt; ac_rfl))
              (sepConj_mono_left (protoUnchunked3VecHeadersAt_entails_memRegion_128 pbA g)))
            (sepConj_mono_right (stackAt_ct1SentFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
          wp_apply; wp_done

private theorem ct1_sent_from_pb_err_drop_unpacked_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 c3 p3 : BitVec 64}
    {pb : V1State.Unchunked.Ct1Sent} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_339).base + 236#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 176#64)) (hx0_1 : s1.readReg64 .x0 = out)
    (hx19_1 : s1.readReg64 .x19 = pbA) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_339).rebase (blkPl_339).base H) (s0.readReg64 .lr) s1
      (memRegion out 128 ∗ (ct1Unpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 72#64) pb.auth), c1, p1, c2, p2, c3, p3) ∗
        A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ (saved48S0 s0.sp, s0))
      (WppPost (ct1SentFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub176 s0.sp]
  refine SepWP.weaken_pre (sepConj_mono (memRegion_128_err_split out)
    (sepConj_mono_left (unpacked_ct1Sent_entails_dealloc A pbA c1 p1 (BitVec.ofNat 64 pb.hdr.length)
      c2 p2 (BitVec.ofNat 64 pb.es.length) c3 p3 (BitVec.ofNat 64 pb.ct1.length) pb.epoch pb.auth pb.hdr pb.es pb.ct1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0; apply ProofLib.SepWP.exists_left; intro v_out8
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (ct1_sent_from_pb_err_drop_placed (v_out0 := v_out0) (v_out8 := v_out8)
      (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩, ⟨c3, p3⟩⟩) hdealloc_raw hcond hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align)

set_option maxHeartbeats 1200000 in
private theorem ct1_sent_from_pb_ok_after_auth_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 c3 p3 : BitVec 64}
    {pb : V1State.Unchunked.Ct1Sent} {auth : ProtoAuthenticator} {ga : AuthenticatorPBGhost} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth) (hpc1 : s1.pc = (blkPl_339).base + 92#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 176#64)) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hx20_1 : s1.readReg64 .x20 = ga.rootKey.cap) (hx21_1 : s1.readReg64 .x21 = pb.epoch)
    (hx22_1 : s1.readReg64 .x22 = out) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_339).rebase (blkPl_339).base H) (s0.readReg64 .lr) s1
      (memRegion out 128 ∗ (ct1Unpacked A, pbA, pb, (authenticatorPBPinnedAt A ga (pbA + 72#64) auth), c1, p1, c2, p2, c3, p3) ∗
        A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 8 ∗
        authenticatorAt A (s0.sp - 168#64) (Authenticator.fromPb auth) ∗ memRegion (s0.sp - 120#64) 72 ∗ (saved48S0 s0.sp, s0))
      (WppPost (ct1SentFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPost, ct1SentFromPbSpec, Unchunked.SendCt.Ct1Sent.from_pb, hcond, hauth, ↓reduceIte,
    spqrAuthApi, ct1SentResultAt, stackAt_ct1SentFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine drop_seq_clean (mid := (blkPl_339).base + 180#64)
    (P_mid := (ct1SentAt A (F := F) out { epoch := pb.epoch, auth := Authenticator.fromPb auth, hdr := pb.hdr, es := pb.es, ct1 := pb.ct1 } ∗
      (memRegion pbA 72 ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 120#64) 8 ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗ ct1Tail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap) ?_ ?_
  · refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (authenticatorPBPinnedAt_72_entails_dealloc A ga pbA auth)))))))))))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (authenticatorAt_sub168_unpack A s0.sp (Authenticator.fromPb auth)))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.SepWP.exists_left; intro ca1; apply ProofLib.SepWP.exists_left; intro pa1
    apply ProofLib.SepWP.exists_left; intro ca2; apply ProofLib.SepWP.exists_left; intro pa2
    rw [ProofLib.memRegion_cells (s0.sp - 120#64) 9 (by decide), memRegion_128_eq_cells16 out]
    cells_unfold
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_right]
    wp_pull_exists; wp_steps; rw [stackAt_authFromPb_split_allocHook_sub176 s0.sp]
    have hpack_out := ct1SentAt_pack A (F := F) out ca1 pa1 ca2 pa2 c1 p1 c2 p2 c3 p3 pb.epoch (Authenticator.fromPb auth) pb.hdr pb.es pb.ct1
    have hpack_sp := memRegion_ct1Sent_scratch_restore s0.sp ca1 pa1 (BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length)
      ca2 pa2 (BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) c1 p1 (BitVec.ofNat 64 pb.hdr.length)
      c2 p2 (BitVec.ofNat 64 pb.es.length) c3 p3 (BitVec.ofNat 64 pb.ct1.length)
    have hpack_pb := unpacked_ct1Sent_headers_entails_memRegion_72_8 pbA c1 p1 (BitVec.ofNat 64 pb.hdr.length)
      c2 p2 (BitVec.ofNat 64 pb.es.length) c3 p3 (BitVec.ofNat 64 pb.ct1.length) pb.epoch
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗ ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) ∗
        ((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗ ((out + 64#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
        ((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗ ((out + 88#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
        ((out + 96#64) ↦₆₄ c3) ∗ ((out + 104#64) ↦₆₄ p3) ∗ ((out + 112#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        ((out + 120#64) ↦₆₄ pb.epoch)) ∗
       vecU8Payload A ca1 pa1 (Authenticator.fromPb auth).rootKey ∗ vecU8Payload A ca2 pa2 (Authenticator.fromPb auth).macKey ∗
       vecU8Payload A c1 p1 pb.hdr ∗ vecU8Payload A c2 p2 pb.es ∗ vecU8Payload A c3 p3 pb.ct1) ∗
      (((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
        ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
        ((pbA + 48#64) ↦₆₄ c3) ∗ ((pbA + 56#64) ↦₆₄ p3) ∗ ((pbA + 64#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗
        ((pbA + 120#64) ↦₆₄ pb.epoch)) ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗
       vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗
      (memRegion (s0.sp - 176#64) 8 ∗
        (((s0.sp - 168#64) ↦₆₄ ca1) ∗ ((s0.sp - 160#64) ↦₆₄ pa1) ∗ ((s0.sp - 152#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
         ((s0.sp - 144#64) ↦₆₄ ca2) ∗ ((s0.sp - 136#64) ↦₆₄ pa2) ∗ ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)) ∗
        (((s0.sp - 120#64) ↦₆₄ c1) ∗ ((s0.sp - 112#64) ↦₆₄ p1) ∗ ((s0.sp - 104#64) ↦₆₄ BitVec.ofNat 64 pb.hdr.length) ∗
         ((s0.sp - 96#64) ↦₆₄ c2) ∗ ((s0.sp - 88#64) ↦₆₄ p2) ∗ ((s0.sp - 80#64) ↦₆₄ BitVec.ofNat 64 pb.es.length) ∗
         ((s0.sp - 72#64) ↦₆₄ c3) ∗ ((s0.sp - 64#64) ↦₆₄ p3) ∗ ((s0.sp - 56#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length))) ∗
      A.pool ∗ memRegion (s0.sp - 4336#64) 64 ∗ stackAt (s0.sp - 176#64) allocHookStack ∗ (saved48S0 s0.sp, s0) by ac_rfl))
      (sepConj_mono hpack_out (sepConj_mono (sepConj_mono_left hpack_pb) (sepConj_mono_left hpack_sp)))) ?_
    refine drop_align_pre (by ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2, hx20_2⟩
    refine drop_seq_clean (mid := (blkPl_339).base + 200#64)
      (P_mid := (ct1SentAt A (F := F) out { epoch := pb.epoch, auth := Authenticator.fromPb auth, hdr := pb.hdr, es := pb.es, ct1 := pb.ct1 } ∗
        (memRegion pbA 72 ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 120#64) 8 ∗
          vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗ ct1Tail A, s0))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [auth72HeadersAt, vecCapPtrDealloc]
      by_cases hca1 : (ga.rootKey.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine drop_align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      dsimp only [auth72HeadersAt, vecCapPtrDealloc]
      by_cases hca2 : (ga.macKey.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (memRegion_72_auth72_8_entails_128 pbA ⟨ga.rootKey, ga.macKey⟩)
          (sepConj_mono_right (stackAt_ct1SentFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        rw [stackAt_ct1SentFromPb_split_allocHook s0.sp]; wp_done
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans (Entails.of_eq (show _ =
            (memRegion pbA 72 ∗ auth72HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 120#64) 8) ∗
            (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ memRegion ga.macKey.ptr ga.macKey.cap.toNat) by unfold auth72HeadersAt; ac_rfl))
            (sepConj_mono_left (memRegion_72_auth72_8_entails_128 pbA ⟨ga.rootKey, ga.macKey⟩)))
          (sepConj_mono_right (stackAt_ct1SentFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_apply; wp_done

set_option maxHeartbeats 1200000 in
theorem v9_ct1_sent_from_pb_cl_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_339 (Rust.withPanics ext)) (lsmpl.base 339) (withLsCodeLoaded lsmpl (ct1SentFromPbSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 339)]
  change subroutine_ok ((blkPC_339).rebase (blkPl_339).base (Rust.withPanics ext)) (blkPl_339).base _
  have hdealloc_raw : subroutine_ok ((blkPC_339).rebase (blkPl_339).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) := spqr_hook_ok_of_mem hA.dealloc
  have hauth_cl : subroutine_ok ((blkPC_339).rebase (blkPl_339).base (Rust.withPanics ext))
      (lsmpl.base 330) (withLsCodeLoaded lsmpl (authFromPbPinnedSpec A)) := v9_auth_from_pb_pinned_cl_on hA
  apply subroutine_ok_of_sepWPp; intro ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align_bv : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  have ⟨hm0, hx0, hx1⟩ : s0.mem ⊨ (memRegion out 128 ∗ protoUnchunkedCt1SentAt A pbA pb ∗
      A.pool ∗ stackAt s0.sp ct1SentFromPbStack) ∗ R ∧ s0.readReg64 .x0 = out ∧ s0.readReg64 .x1 = pbA := by
    simp only [ct1SentFromPbSpec] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; exact ⟨hpre.2, hpre.1⟩
  refine ⟨memRegion out 128 ∗ protoUnchunkedCt1SentAt A pbA pb ∗ A.pool ∗ stackAt s0.sp ct1SentFromPbStack, R, hm0, ?_⟩
  rw [stackAt_ct1SentFromPb_split s0.sp]
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left (protoUnchunkedCt1SentAt_unpack A pbA pb))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro c1; apply SepWPp.exists_elim; intro p1
  apply SepWPp.exists_elim; intro c2; apply SepWPp.exists_elim; intro p2
  apply SepWPp.exists_elim; intro c3; apply SepWPp.exists_elim; intro p3
  apply sepWPp_pure_elim_focus (pb.hdr.length < 2 ^ 63 ∧ pb.es.length < 2 ^ 63 ∧
    pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63); intro ⟨hl1, hl2, hl3, _⟩
  cells_unfold
  apply SepWPp.exists_elim; intro fp_old; apply SepWPp.exists_elim; intro lr_old
  apply SepWPp.exists_elim; intro x22_old; apply SepWPp.exists_elim; intro x21_old
  apply SepWPp.exists_elim; intro x20_old; apply SepWPp.exists_elim; intro x19_old
  by_cases hcond : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true
  · have hhdr_t : (BitVec.ofNat 64 pb.hdr.length == 64#64) = true := by
      rw [ofNat_beq_lit_iff hl1 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.1.1
    have hes_t : (BitVec.ofNat 64 pb.es.length == 2080#64) = true := by
      rw [ofNat_beq_lit_iff hl2 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.1.2
    have hct1_t : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true := by
      rw [ofNat_beq_lit_iff hl3 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.2
    cases hauth : pb.auth with
    | none =>
      apply SepWPp.of_sepWP_ret
      simp only [withMemEq, ct1SentFromPbSpec, Unchunked.SendCt.Ct1Sent.from_pb, hcond, hauth, ↓reduceIte,
        ct1SentResultAt, stackAt_ct1SentFromPb_split_dropStack32]
      rw [optProtoAuthenticatorAt_72_none]
      refine SepWP.weaken_pre (sepConj_mono_left (memRegion_128_err_split out)) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro v_out0; apply ProofLib.SepWP.exists_left; intro v_out8
      refine seq_clean_lscl hcl (mid := lsmpl.base 286)
        (P_mid := (ct1OutNone out) ∗
          protoUnchunkedCt1SentEkReceivedAt A pbA { epoch := pb.epoch, auth := none, es := pb.hdr, ek := pb.es, ct1 := pb.ct1 } ∗
          A.pool ∗ (memRegion (s0.sp - 4336#64) 208 ∗ stackAt s0.sp dropStack32))
        (Q := fun sm => sm.readReg64 .x0 = pbA ∧ sm.readReg64 .lr = s0.readReg64 .lr ∧
          sm.sp = s0.sp ∧ CalleeSavedPreserved s0 sm ∧ sm.trace = s0.trace) ?_ ?_
      · wp_steps
        have hpre_none :
            ((out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₈ 0#8) ∗ memRegion (out + 9#64) 119 ∗
             (ct1Unpacked A, pbA, pb, (((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40), c1, p1, c2, p2, c3, p3) ∗
             A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ saved48S0 s0.sp, s0) ⊢
            (ct1OutNone out) ∗ protoUnchunkedCt1SentEkReceivedAt A pbA { epoch := pb.epoch, auth := none, es := pb.hdr, ek := pb.es, ct1 := pb.ct1 } ∗
            A.pool ∗ (memRegion (s0.sp - 4336#64) 208 ∗ stackAt s0.sp dropStack32) := by
          refine Entails.trans (Entails.of_eq (show _ = (ct1OutNone out) ∗
            (ct1Unpacked A, pbA, pb, (((pbA + 72#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 80#64) 40), c1, p1, c2, p2, c3, p3) ∗
            A.pool ∗ (stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ (saved48S0 s0.sp, s0)) by ac_rfl)) ?_
          exact sepConj_mono_right (sepConj_mono
            (unpacked_ct1Sent_auth_none_pack A pbA c1 p1 c2 p2 c3 p3 pb.epoch pb.hdr pb.es pb.ct1)
            (sepConj_mono_right (stackAt_ct1SentFromPb_tail_dropStack32 s0.sp _ _ _ _ _ _)))
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by
          dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl)) hpre_none) ?_; wp_done
      · intro sm hpcm hrunm hclm ⟨hx0_m, hlr_m, hsp_m, hcs_m, htr_m⟩
        have hdrop_raw := drop_proto_unchunked_ct1_sent_ek_received_mem_on
          (callerProg := (blkPC_339).rebase (blkPl_339).base (Rust.withPanics ext)) hA.dealloc hclm
        simp only [withMemEq, dropProtoUnchunkedCt1SentEkReceivedSpec] at hdrop_raw
        dsimp only [protoUnchunkedCt1SentEkReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop_raw
        wp_apply; wp_done
    | some auth =>
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        optProtoAuthenticatorAt A (pbA + 72#64) (some auth) ∗
        (memRegion out 128 ∗ (ct1Vecs A, pbA, pb, c1, p1, c2, p2, c3, p3) ∗
         A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗
         saved48Vars s0.sp, fp_old, lr_old, x22_old, x21_old, x20_old, x19_old) by ac_rfl))
        (sepConj_mono_left (optProtoAuthenticatorAt_some_unpack A (pbA + 72#64) auth))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro ga
      apply sepWPp_pure_elim_focus (ga.rootKey.cap.toNat < 2 ^ 63); intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      rw [memRegion_176_128_split_8_48_72 s0.sp]
      refine sepWPp_seq_clean_lscl hcl (mid := lsmpl.base 330)
        (P_mid := (memRegion (s0.sp - 168#64) 48 ∗ authenticatorPBPinnedAt A ga (pbA + 72#64) auth ∗
          A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack) ∗
          (memRegion out 128 ∗ (ct1Vecs A, pbA, pb, c1, p1, c2, p2, c3, p3) ∗
           memRegion (s0.sp - 176#64) 8 ∗ memRegion (s0.sp - 120#64) 72 ∗ (saved48S0 s0.sp, s0)))
        (Q_mid := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧
          sm.readReg64 .x0 = s0.sp - 168#64 ∧ sm.readReg64 .x1 = pbA + 72#64 ∧
          sm.readReg64 .lr = (blkPl_339).base + 92#64 ∧
          sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap ∧
          sm.readReg64 .x21 = pb.epoch ∧ sm.readReg64 .x22 = out) ?_ ?_
      · wp_steps
        rw [← sepConj_assoc ((pbA + 72#64) ↦₆₄ ga.rootKey.cap), ← authenticatorPBPinnedAt_eq_cap_tail A ga (pbA + 72#64) auth]
        refine drop_align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
      · intro sm hpcm hrunm hclm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx0_m, hx1_m, hlr_m, hx19_m, hx20_m, hx21_m, hx22_m⟩
        have hsp_align_m : sm.spAligned = true := by
          simp only [State.spAligned, hsp_m, sp_and_15_sub_aligned s0.sp 176#64 (by decide)]; exact hsp_align_bv
        refine sepWPp_call_ret hauth_cl (x := ⟨s0.sp - 168#64, pbA + 72#64, ga, auth⟩)
          hpcm hrunm hsp_align_m hlr_m ?_ ?_ (fun _ _ => rfl) ?_
        · intro R' hm'; dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hclm, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0_m, hx1_m⟩, Satisfies.mono (Entails.of_eq (by rw [hsp_m])) hm'⟩
        · intro sf; dsimp only [withLsCodeLoaded, withMemEq, authFromPbPinnedSpec, ct1SentFromPbSpec]
          exact onPanic_frame_entails htrace_m
        · intro s1 hpc1 hrun1 hsp1 ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
          rw [hx19_m] at hx19_1; rw [hx20_m] at hx20_1; rw [hx21_m] at hx21_1; rw [hx22_m] at hx22_1
          rw [hx23_m] at hx23_1; rw [hx24_m] at hx24_1; rw [hx25_m] at hx25_1; rw [hx26_m] at hx26_1
          rw [hx27_m] at hx27_1; rw [hx28_m] at hx28_1; rw [hsp_m] at hsp1
          dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]; rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply ProofLib.SepWP.pure_elim; intro htrace_s1; rw [htrace_m] at htrace_s1
          exact SepWP.weaken_pre (Entails.of_eq (by rw [hsp_m]; ac_rfl))
            (ct1_sent_from_pb_ok_after_auth_placed hdealloc_raw hcond hauth hpc1 hrun1
              ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp1, htrace_s1, hvregs_1.trans hvregs_m⟩
              hx19_1 hx20_1 hx21_1 hx22_1 hsp_align_bv)
  · apply SepWPp.of_sepWP_ret
    have hcond_f : (pb.hdr.length == HEADER_SIZE && pb.es.length == ENCAPSULATION_STATE_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false := Bool.eq_false_iff.mpr hcond
    refine drop_seq_clean (mid := (blkPl_339).base + 236#64)
      (P_mid := (memRegion out 128 ∗ (ct1Unpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 72#64) pb.auth), c1, p1, c2, p2, c3, p3) ∗
        A.pool ∗ stackAt (s0.sp - 176#64) authFromPbStack ∗ memRegion (s0.sp - 176#64) 128 ∗ (saved48S0 s0.sp, s0)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 176#64) ∧ sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · by_cases h1 : (BitVec.ofNat 64 pb.hdr.length == 64#64) = true
      · by_cases h2 : (BitVec.ofNat 64 pb.es.length == 2080#64) = true
        · by_cases h3 : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true
          · exfalso; apply hcond
            rw [ofNat_beq_lit_iff hl1 (by decide)] at h1; rw [ofNat_beq_lit_iff hl2 (by decide)] at h2
            rw [ofNat_beq_lit_iff hl3 (by decide)] at h3; simp [h1, h2, h3, HEADER_SIZE, ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE]
          · have h3_f : (BitVec.ofNat 64 pb.ct1.length == 960#64) = false := Bool.eq_false_iff.mpr h3
            wp_steps; refine drop_align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
        · have h2_f : (BitVec.ofNat 64 pb.es.length == 2080#64) = false := Bool.eq_false_iff.mpr h2
          wp_steps; refine drop_align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
      · have h1_f : (BitVec.ofNat 64 pb.hdr.length == 64#64) = false := Bool.eq_false_iff.mpr h1
        wp_steps; refine drop_align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1, hx19_1⟩
      exact ct1_sent_from_pb_err_drop_unpacked_placed hdealloc_raw hcond_f hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv

theorem v9_sub_ok_ct1_sent_from_pb_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 339) (withLsCodeLoaded lsmpl (ct1SentFromPbSpec A F)) :=
  ls_subroutine_ok_of_block (v9_ct1_sent_from_pb_cl_placed_ok hA) (by decide)

end Ct1SentFromPbPlaced

theorem v9_seq_clean_lscl [LibsignalPlacement]
    {ext : String → Option (State → State)} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP (lsProg_333 (Rust.withPanics ext)) mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm →
      SepWP (lsProg_333 (Rust.withPanics ext)) ret sm P_mid Q) :
    SepWP (lsProg_333 (Rust.withPanics ext)) ret s P Q :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _ hpc hrun ⟨hP, hQ⟩ hclm =>
    SepWP.weaken_pre hP (h2 sm hpc hrun hclm hQ))

theorem v9_sepWPp_seq_clean_lscl [LibsignalPlacement]
    {ext : String → Option (State → State)} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP (lsProg_333 (Rust.withPanics ext)) mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp (lsProg_333 (Rust.withPanics ext)) ret sm P_mid Q Qp) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) ret s P Q Qp :=
  sepWPp_seq_clean_lscl hcl h1 h2

theorem v9_sepWPp_call_ret_entails_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step F : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpre : P_step ⊢ spec.pre x s)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf) (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => P_f ⊢ Qpan sf) :=
  v9_sepWPp_call_ret_entails hcall (x := x) (Qpan := Qpan) hpc hrun hsp_align hlr
    (by dsimp only [withLsCodeLoaded]; exact Entails.trans (Entails.pure_right hcl hpre) (Entails.of_eq (by ac_rfl)))
    (fun sf => by dsimp only [withLsCodeLoaded]; exact hpan sf)
    (fun code sf => by dsimp only [withLsCodeLoaded]; exact hexit_eq code sf)
    hnext
    (fun sf => by dsimp only [withLsCodeLoaded]; exact hoom_eq sf)

theorem v9_sepWPp_call_entails_lscl [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    {x : α} {s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    {P_step F : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpre : P_step ⊢ spec.pre x s)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf) (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      LibsignalCodeLoaded lsmpl sf.mem → sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post (fun sf' P_f => P_f ⊢ Qpan sf'))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => P_f ⊢ Qpan sf) := by
  have h1 : SepWPp prog ret_pc s (P_step ∗ F)
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post x s sm ∗ F)
      (fun sf P_f => P_f ⊢ Qpan sf) := by
    refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
      (fun R' hm => by
        rw [sepConj_assoc] at hm
        dsimp only [withLsCodeLoaded]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨hcl, Satisfies.mono (sepConj_mono_left hpre) hm⟩)
      (fun sf code _ _ hpost => by
        dsimp only [withLsCodeLoaded] at hpost
        rw [hexit_eq] at hpost
        exact not_satisfies_false_sepConj hpost)
      (fun sm _ => hpan sm)
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf _ _ hpost => by
        dsimp only [withLsCodeLoaded] at hpost
        rw [hoom_eq] at hpost
        exact (not_satisfies_false_sepConj hpost).elim)
  intro R' hm hL
  rcases h1 R' hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan_out | hoom_out⟩
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm (hcl.of_keepsFrozen hsteps.keepsFrozen) hspm hcsm R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan_out)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

/-! ## 1. From `+2864` (Return of `Ct1Sent::from_pb`) to `s0.x30` -/

set_option maxHeartbeats 800000 in
/-- From `+2864` (after `ct1SentFromPb` returns) to `s0.x30`. -/
theorem v9_tail_2864_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hDec : DecoderFromPbPlacedOkExt A ext)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (optDec : Option PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 2864#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = w8) (hx21 : s.readReg64 .x21 = w0)
    (hx22 : s.readReg64 .x22 = w16) (hx23 : s.readReg64 .x23 = w32) (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA)
    (htr : TraceCalleeSaved s s0) (hpts : ∀ d, optDec = some d → (d.ptsNeeded == 576#32) = true) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (ct1SentResultAt A (fsp + 1888#64) (Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u) ∗
        (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
        v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
        A.pool ∗ stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := optDec }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases hres : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u with
  | error e =>
    have he : e = .err .stateDecode := v9_ct1Sent_from_pb_err_eq u hres
    subst he
    have hmod : States.from_pb spqrPolyApi (spqrAuthApi F)
        { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := optDec }) } = .error (.err .stateDecode) := by
      cases optDec with
      | none => rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_none u, hres]
      | some d => rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_some u d (hpts d rfl), hres]
    rw [hmod]; apply SepWPp.of_sepWP_ret; dsimp only [ct1SentResultAt]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hbw := v9_byte_region119_to_words (fsp + 1896#64) 0#8
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbw
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1896#64) ↦₈ 0#8) ∗ memRegion (fsp + 1897#64) 119) ∗
        (((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
         ((fsp + 1888#64) ↦₆₄ noneCap) ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
      (sepConj_mono hbw (sepConj_mono_left (v9_pbA_128_entails_224 pbA w0 w8 w16 d24 d28 w32)))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w1896; apply ProofLib.SepWP.exists_left; intro w1904
    apply ProofLib.SepWP.exists_left; intro w1912; apply SepWP.pure_elim; intro hw1896
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 5360#64)
      (P_mid := v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (Q := fun s1 => v9_Saved5368Preserved s0 s1 fsp out w8 w0 w1896 ∧ s1.readReg64 .x22 = w16) ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (show _ =
        ((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
        ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗
        (memRegion (fsp + 1920#64) 96 ∗ memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
        (SepWP.strengthen_entails_const ?_
          (v9_step_2864_err_to_5360_placed s0 s fsp out w8 w0 w16 w1896 w1904 w1912 _
            hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 htr))
      refine Entails.trans (Entails.of_eq (show _ =
        v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        (memRegion fsp 1888 ∗ (((fsp + 1888#64) ↦₆₄ noneCap) ∗ ((fsp + 1896#64) ↦₆₄ w1896) ∗
          ((fsp + 1904#64) ↦₆₄ w1904) ∗ ((fsp + 1912#64) ↦₆₄ w1912) ∗ memRegion (fsp + 1920#64) 96) ∗
         memRegion (fsp + 2016#64) 288) ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize by ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (v9_fsp_1888_err_entails_2304 fsp noneCap w1896 w1904 w1912)))))
    · rintro s1 hpc1 hrun1 ⟨hpres1, hx22_1⟩
      exact v9_tail_5360_to_ret_placed hA s0 s1 fsp out pbA w0 w8 w16 d24 d28 w32 w1896
        (optDec.map pbToProtoPolyDecoder) .stateDecode hsp0_align hfsp_eq hpc1 hrun1 hpres1 hx22_1 hw1896
  | ok uc =>
    dsimp only [ct1SentResultAt]
    refine SepWPp.weaken_pre (sepConj_mono_left (v9_ct1SentAt_unpack A (fsp + 1888#64) uc)) ?_
    simp only [sepExists_sepConj_left]
    apply v9_sepWPp_exists_left; intro rkCap; apply v9_sepWPp_exists_left; intro rkPtr
    apply v9_sepWPp_exists_left; intro rkLen; apply v9_sepWPp_exists_left; intro mkCap
    apply v9_sepWPp_exists_left; intro mkPtr; apply v9_sepWPp_exists_left; intro mkLen
    apply v9_sepWPp_exists_left; intro hdrCap; apply v9_sepWPp_exists_left; intro hdrPtr
    apply v9_sepWPp_exists_left; intro hdrLen; apply v9_sepWPp_exists_left; intro esCap
    apply v9_sepWPp_exists_left; intro esPtr; apply v9_sepWPp_exists_left; intro esLen
    apply v9_sepWPp_exists_left; intro ct1Cap; apply v9_sepWPp_exists_left; intro ct1Ptr
    apply v9_sepWPp_exists_left; intro ct1Len
    refine SepWPp.weaken_pre (Entails.trans (sepConj_mono_left (sepConj_mono_right
        (v9_ct1SentHeap_rkCap_lt A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc)))
      (Entails.of_eq (show _ = ⌜rkCap.toNat < 2 ^ 63⌝ ∗
        (v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1888 ∗ memRegion (fsp + 2016#64) 288 ∗
         A.pool ∗ stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
    apply v9_sepWPp_pure_left; intro hrk_lt
    cases optDec with
    | none =>
      rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_none u, hres]; apply SepWPp.of_sepWP_ret
      dsimp only [Option.map, v9_optProtoPolyDecoderHeap]
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = ⌜w0 = noneCap⌝ ∗
          (((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
            v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
           memRegion fsp 1888 ∗
           (v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
              esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
            v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
              esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
            memRegion (fsp + 2016#64) 288 ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
            statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
        (sepConj_mono_right (sepConj_mono (v9_pbA_128_entails_224 pbA w0 w8 w16 d24 d28 w32)
          (sepConj_mono_left (v9_memRegion_1888_split_none fsp))))) ?_
      apply SepWP.pure_elim; rintro rfl
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro w248; apply ProofLib.SepWP.exists_left; intro w240
      apply ProofLib.SepWP.exists_left; intro w152; apply ProofLib.SepWP.exists_left; intro w144
      apply ProofLib.SepWP.exists_left; intro w128; apply ProofLib.SepWP.exists_left; intro d96
      apply ProofLib.SepWP.exists_left; intro w72
      refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 6904#64)
        (P_mid := memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ memRegion (fsp + 160#64) 2144 ∗
          v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        (Q := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = mkPtr ∧ s1.readReg64 .x1 = mkCap ∧
          s1.readReg64 .x10 = rkCap ∧ s1.readReg64 .x13 = ct1Cap ∧ s1.readReg64 .x14 = ct1Ptr ∧
          s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0) ?_ ?_
      · refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗ ((fsp + 128#64) ↦₆₄ w128) ∗
          ((fsp + 144#64) ↦₆₄ w144) ∗ ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
          ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248) ∗
          v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
          (memRegion fsp 72 ∗ memRegion (fsp + 80#64) 16 ∗ memRegion (fsp + 100#64) 28 ∗
           memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 80 ∗ memRegion (fsp + 255#64) 1633 ∗
           memRegion (fsp + 2016#64) 288 ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
          (SepWP.strengthen_entails_const ?_
            (v9_step_2864_ok_none_to_6904_placed s0 s fsp out rkCap rkPtr rkLen mkCap mkPtr mkLen
              hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
              w72 w128 w144 w152 w240 w248 d96 _ hfsp_align hrk_lt hpc hrun hsp hx19 hx21 hx25 htr))
        have hcol := v9_fsp_2864_none_collapse fsp
          (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) uc.epoch
          ((EncoderFromPb.loByte ct1Len).zeroExtend 32)
        refine Entails.trans (Entails.of_eq (show _ =
          ((memRegion (fsp + 80#64) 16 ∗ ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
            memRegion (fsp + 100#64) 28) ∗
           (memRegion (fsp + 160#64) 80 ∗
            ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
            ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 1633 ∗
            memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288)) ∗
          (memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗
           memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hcol) (Entails.of_eq (by ac_rfl))
      · rintro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx10_1, hx13_1, hx14_1, hx19_1, hx28_1, htr1⟩
        exact v9_tail_6904_to_ret_placed hA s0 s1 fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen
          hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
          hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx0_1 hx1_1 hx10_1 hx13_1 hx14_1 hx19_1 hx28_1 htr1
    | some d =>
      rw [v9_states_from_pb_ct1Acknowledged_uc_some_dec_some u d (hpts d rfl), hres]; dsimp only [Option.map]
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
          v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d24 d28 w32 ∗
          memRegion fsp 1888 ∗
          (v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
           v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
           memRegion (pbA + 176#64) 48 ∗ memRegion (fsp + 2016#64) 288 ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
        (sepConj_mono (v9_optProtoPolyDecoderHeap_some_cap_lt A (pbToProtoPolyDecoder d) w0 w8 w16 d24 d28 w32)
          (sepConj_mono_left (v9_memRegion_1888_split_some fsp)))) ?_
      rw [sepConj_assoc]; apply v9_sepWPp_pure_left; rintro ⟨hw0_lt, _⟩
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply v9_sepWPp_exists_left; intro w248; apply v9_sepWPp_exists_left; intro w240
      apply v9_sepWPp_exists_left; intro w216; apply v9_sepWPp_exists_left; intro w200
      apply v9_sepWPp_exists_left; intro w152; apply v9_sepWPp_exists_left; intro w144
      apply v9_sepWPp_exists_left; intro w136; apply v9_sepWPp_exists_left; intro w128
      apply v9_sepWPp_exists_left; intro d96; apply v9_sepWPp_exists_left; intro w80
      apply v9_sepWPp_exists_left; intro w72; apply v9_sepWPp_exists_left; intro w56
      apply v9_sepWPp_exists_left; intro w48; apply v9_sepWPp_exists_left; intro w40
      refine v9_sepWPp_seq_clean_lscl hcl (mid := lsmpl.base 376)
        (P_mid := (protoPolynomialDecoderAt A (fsp + 896#64) (pbToProtoPolyDecoder d) ∗
            memRegion (fsp + 1888#64) 400 ∗ A.pool ∗ stackAt fsp decoderFromPbStack) ∗
          (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
           ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
           ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
           ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
           ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
           ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
           ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
           memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
           memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 936#64) 952 ∗
           memRegion (fsp + 2288#64) 16 ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize))
        (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧
          s1.readReg64 .x1 = fsp + 896#64 ∧ s1.readReg64 .x19 = out ∧
          s1.readReg64 .x21 = fsp + 848#64 ∧ s1.readReg64 .x24 = fsp + 1888#64 ∧
          s1.readReg64 .x25 = esLen ∧ s1.readReg64 .x26 = rkLen ∧ s1.readReg64 .x28 = rkPtr ∧
          s1.readReg64 .x30 = lsmpl.base 333 + 3044#64 ∧ TraceCalleeSaved s1 s0) ?_ ?_
      · refine SepWP.weaken_pre (Entails.of_eq (show _ =
          ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
          ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗
          ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗ ((fsp + 144#64) ↦₆₄ w144) ∗
          ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
          ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248) ∗
          memRegion (fsp + 896#64) 40 ∗
          v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
          v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d24 d28 w32 ∗
          ((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
           memRegion (pbA + 176#64) 48 ∗ memRegion (fsp + 2016#64) 288 ∗
           memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
           memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
           memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 936#64) 952 ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           A.pool ∗ stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
        refine SepWP.mono
          (v9_step_2864_ok_some_to_3040_placed s0 s fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen
            hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
            w0 w8 w16 d24 d28 w32 d w40 w48 w56 w72 w80 w128 w136 w144 w152 w200 w216 w240 w248 d96 _
            hfsp_align hrk_lt hw0_lt hpc hrun hsp hx19 hx20 hx21 hx23 hx25 hx27 htr) ?_
        rintro s1 P1 _ _ ⟨hP1, hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1, hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩
        rw [hx24] at hx24_1
        refine ⟨Entails.trans hP1 ?_, hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1, hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩
        refine Entails.trans (Entails.of_eq (show _ =
          ((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
           v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
          (memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288) ∗ stackAt fsp decoderFromPbStack ∗
          (protoPolynomialDecoderAt A (fsp + 896#64) (pbToProtoPolyDecoder d) ∗ A.pool ∗
           ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
           ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
           ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
           ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
           ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
           ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
           ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
           memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
           memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 936#64) 952 ∗
           v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
             esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
        rw [v9_memRegion_1888_2016_eq_400_16 fsp]
        exact Entails.trans (sepConj_mono_left (v9_pbA_128_entails_224 pbA w0 w8 w16 d24 d28 w32)) (Entails.of_eq (by ac_rfl))
      · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx21_1, hx24_1, hx25_1, hx26_1, hx28_1, hx30_1, htr1⟩
        have hsp1_align : s1.spAligned = true := by unfold State.spAligned; rw [hsp1]; exact hfsp_align
        refine v9_sepWPp_call_ret_entails_lscl (v9_sub_ok_decoder_from_pb_placed hDec)
          (x := ⟨fsp + 1888#64, fsp + 896#64, pbToProtoPolyDecoder d⟩) hcl1 (Qpan := statesFromPbOnPanic s0)
          hpc1 hrun1 hsp1_align hx30_1
          (by dsimp only [decoderFromPbSpec, polyDecoderSize]; rw [hsp1]; exact Entails.pure_right ⟨hx0_1, hx1_1⟩ (Entails.of_eq (by ac_rfl)))
          (fun sf => by dsimp only [decoderFromPbSpec]; exact v9_onPanic_frame_entails htr1) (fun _ _ => rfl) ?_
        intro s2 hpc2 hrun2 hsp2 hcs2
        obtain ⟨hx19_2, _, hx21_2, _, _, hx24_2, hx25_2, hx26_2, _, hx28_2, _, hvregs_2⟩ := hcs2
        rw [hsp1] at hsp2; rw [hx19_1] at hx19_2; rw [hx21_1] at hx21_2
        rw [hx24_1] at hx24_2; rw [hx25_1] at hx25_2; rw [hx26_1] at hx26_2; rw [hx28_1] at hx28_2
        dsimp only [decoderFromPbSpec, protoPolynomialDecoderSize]; rw [hsp1, sepConj_assoc]
        apply SepWP.pure_elim; intro htr2
        have htr2 : TraceCalleeSaved s2 s0 := ⟨htr2.trans htr1.1, hvregs_2.trans htr1.2⟩
        refine SepWP.weaken_pre (Entails.of_eq (show _ =
          resultPolyDecoderFromPbAt A (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
          ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
          ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
          ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
          memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
          memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
          memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
          v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
            esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize by ac_rfl))
          (v9_tail_3044_to_ret_placed hA s0 s2 fsp out pbA rkCap rkPtr rkLen mkCap mkPtr mkLen
            hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc d
            hsp0_align hfsp_eq hpc2 hrun2 hsp2 hx19_2 hx21_2 hx24_2 hx25_2 hx26_2 hx28_2 htr2)

/-! ## 2. From `+2768` (Check & Copy `uc`, Call `Ct1Sent::from_pb`) to `s0.x30` -/

set_option maxHeartbeats 800000 in
/-- From `+2768` (after checking `receivingEk`) to `s0.x30`. -/
theorem v9_tail_2768_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hDec : DecoderFromPbPlacedOkExt A ext)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem) (fsp out pbA : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64)
    (optUc : Option V1State.Unchunked.Ct1Sent) (optDec : Option PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 2768#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = u0) (hx9 : s.readReg64 .x9 = ((EncoderFromPb.loByte u8).zeroExtend 32).zeroExtend 64)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64) (hx19 : s.readReg64 .x19 = out) (hx20 : s.readReg64 .x20 = w8)
    (hx21 : s.readReg64 .x21 = w0) (hx22 : s.readReg64 .x22 = w16) (hx23 : s.readReg64 .x23 = w32)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s s0)
    (hpts : ∀ d, optDec = some d → (d.ptsNeeded == 576#32) = true) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      ((pbA ↦₆₄ 0x8000000000000009#64) ∗
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
        v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F)
              { innerState := some (.ct1Acknowledged { uc := optUc, receivingEk := optDec }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases optUc with
  | none =>
    have hmod : States.from_pb spqrPolyApi (spqrAuthApi F)
        { innerState := some (.ct1Acknowledged { uc := none, receivingEk := optDec }) } = .error (.err .stateDecode) := by
      cases optDec with
      | none => exact v9_states_from_pb_ct1Acknowledged_uc_none_dec_none
      | some d => exact v9_states_from_pb_ct1Acknowledged_uc_none_dec_some d (hpts d rfl)
    rw [hmod]; apply SepWPp.of_sepWP_ret; dsimp only [v9_optProtoUcHeap]
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = ⌜u0 = noneCap⌝ ∗
        (((pbA ↦₆₄ 0x8000000000000009#64) ∗
          v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
         (v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
          A.pool ∗ stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
          statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
      (sepConj_mono_right (sepConj_mono_left
        (v9_pbA_entails_224 pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 w0 w8 w16 d24 d28 w32)))) ?_
    apply SepWP.pure_elim; rintro rfl
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 5360#64)
      (P_mid := v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (Q := fun s1 => v9_Saved5368Preserved s0 s1 fsp out w8 w0 0#64 ∧ s1.readReg64 .x22 = w16) ?_ ?_
    · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (v9_states_from_pb_uc_none_2768_placed s0 s fsp out w8 w0 w16 _ hpc hrun hsp hx8 hx19 hx20 hx21 hx22 htr)
    · rintro s1 hpc1 hrun1 ⟨hpres1, hx22_1⟩
      exact v9_tail_5360_to_ret_placed hA s0 s1 fsp out pbA w0 w8 w16 d24 d28 w32 0#64
        (optDec.map pbToProtoPolyDecoder) .stateDecode hsp0_align hfsp_eq hpc1 hrun1 hpres1 hx22_1 rfl
  | some u =>
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        memRegion fsp 2304 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
      (sepConj_mono
        (v9_optProtoUcHeap_some_cap_lt A u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)
        (sepConj_mono_left (v9_memRegion_2304_split_2768 fsp)))) ?_
    rw [sepConj_assoc]; apply v9_sepWPp_pure_left; intro hu0_lt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply v9_sepWPp_exists_left; intro z1512; apply v9_sepWPp_exists_left; intro z1504
    apply v9_sepWPp_exists_left; intro z1496; apply v9_sepWPp_exists_left; intro z1488
    apply v9_sepWPp_exists_left; intro z1480; apply v9_sepWPp_exists_left; intro z1472
    apply v9_sepWPp_exists_left; intro z1464; apply v9_sepWPp_exists_left; intro z1456
    apply v9_sepWPp_exists_left; intro z1448; apply v9_sepWPp_exists_left; intro z1440
    apply v9_sepWPp_exists_left; intro z1432; apply v9_sepWPp_exists_left; intro z1424
    apply v9_sepWPp_exists_left; intro z1417; apply v9_sepWPp_exists_left; intro z1409
    apply v9_sepWPp_exists_left; intro z1401; apply v9_sepWPp_exists_left; intro b1400
    apply v9_sepWPp_exists_left; intro z1392
    refine v9_sepWPp_seq_clean_lscl hcl (mid := lsmpl.base 339)
      (P_mid := (protoUnchunkedCt1SentAt A (fsp + 1392#64) u ∗
          memRegion (fsp + 1888#64) 128 ∗ A.pool ∗ stackAt fsp ct1SentFromPbStack) ∗
        (memRegion (fsp - 5152#64) 816 ∗ (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1392 ∗ memRegion (fsp + 1520#64) 368 ∗
         memRegion (fsp + 2016#64) 288 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize))
      (Q_regs := fun s1 => s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧
        s1.readReg64 .x1 = fsp + 1392#64 ∧ s1.readReg64 .x19 = out ∧
        s1.readReg64 .x20 = w8 ∧ s1.readReg64 .x21 = w0 ∧ s1.readReg64 .x22 = w16 ∧
        s1.readReg64 .x23 = w32 ∧ s1.readReg64 .x24 = fsp + 1888#64 ∧
        s1.readReg64 .x25 = fsp + 1792#64 ∧ s1.readReg64 .x27 = pbA ∧
        s1.readReg64 .x30 = lsmpl.base 333 + 2864#64 ∧ TraceCalleeSaved s1 s0) ?_ ?_
    · refine SepWP.weaken_pre (Entails.of_eq (show _ =
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        ((fsp + 1392#64) ↦₆₄ z1392) ∗ ((fsp + 1400#64) ↦₈ b1400) ∗ ((fsp + 1401#64) ↦₆₄ z1401) ∗
        ((fsp + 1409#64) ↦₆₄ z1409) ∗ ((fsp + 1417#64) ↦ₛ EncoderFromPb.loBytes7 z1417) ∗
        ((fsp + 1424#64) ↦₆₄ z1424) ∗ ((fsp + 1432#64) ↦₆₄ z1432) ∗ ((fsp + 1440#64) ↦₆₄ z1440) ∗
        ((fsp + 1448#64) ↦₆₄ z1448) ∗ ((fsp + 1456#64) ↦₆₄ z1456) ∗ ((fsp + 1464#64) ↦₆₄ z1464) ∗
        ((fsp + 1472#64) ↦₆₄ z1472) ∗ ((fsp + 1480#64) ↦₆₄ z1480) ∗ ((fsp + 1488#64) ↦₆₄ z1488) ∗
        ((fsp + 1496#64) ↦₆₄ z1496) ∗ ((fsp + 1504#64) ↦₆₄ z1504) ∗ ((fsp + 1512#64) ↦₆₄ z1512) ∗
        (v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         (pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1392 ∗ memRegion (fsp + 1520#64) 368 ∗
         memRegion (fsp + 1888#64) 128 ∗ memRegion (fsp + 2016#64) 288 ∗
         A.pool ∗ stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
      refine SepWP.mono
        (v9_states_from_pb_copy_uc_to_call_2768_placed s0 s fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 w0 w8 w16 w32
          z1392 z1401 z1409 z1417 z1424 z1432 z1440 z1448 z1456 z1464 z1472 z1480 z1488 z1496 z1504 z1512 b1400 _
          hfsp_align hu0_lt hpc hrun hsp hx8 hx9 hx13 hx19 hx20 hx21 hx22 hx23 hx25 hx27 htr) ?_
      rintro s1 P1 _ _ ⟨hP1, hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, _, hx30_1, htr1⟩
      refine ⟨Entails.trans hP1 ?_, hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx30_1, htr1⟩
      rw [v9_stackAt_encoderFromPbStack_eq_ct1SentFromPb fsp]
      refine Entails.trans (Entails.of_eq (show _ =
        (v9_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120) ∗
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        (memRegion (fsp + 1888#64) 128 ∗ A.pool ∗ stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816 ∗
         (pbA ↦₆₄ 0x8000000000000009#64) ∗ v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 1392 ∗ memRegion (fsp + 1520#64) 368 ∗
         memRegion (fsp + 2016#64) 288 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono
        (v9_protoUcAt_pack A (fsp + 1392#64) u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)
        (sepConj_mono_left (v9_optProtoUcWordsAt_entails_128 (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)))
        (Entails.of_eq (by ac_rfl))
    · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx30_1, htr1⟩
      have hsp1_align : s1.spAligned = true := by unfold State.spAligned; rw [hsp1]; exact hfsp_align
      refine v9_sepWPp_call_entails_lscl (v9_sub_ok_ct1_sent_from_pb_placed (F := F) hA)
        (x := ⟨fsp + 1888#64, fsp + 1392#64, u⟩) hcl1 (Qpan := statesFromPbOnPanic s0)
        hpc1 hrun1 hsp1_align hx30_1
        (by dsimp only [ct1SentFromPbSpec, protoUnchunkedCt1SentSize]; rw [hsp1]; exact Entails.pure_right ⟨hx0_1, hx1_1⟩ (Entails.of_eq (by ac_rfl)))
        (fun sf => by dsimp only [ct1SentFromPbSpec]; exact v9_onPanic_frame_entails htr1) (fun _ _ => rfl) ?_
      intro s2 hpc2 hrun2 hcl2 hsp2 hcs2
      obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, _, hx27_2, _, _, hvregs_2⟩ := hcs2
      rw [hsp1] at hsp2; rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2
      rw [hx21_1] at hx21_2; rw [hx22_1] at hx22_2; rw [hx23_1] at hx23_2
      rw [hx24_1] at hx24_2; rw [hx25_1] at hx25_2; rw [hx27_1] at hx27_2
      dsimp only [ct1SentFromPbSpec, protoUnchunkedCt1SentSize]; rw [hsp1, sepConj_assoc]
      apply v9_sepWPp_pure_left; intro htr2
      have htr2 : TraceCalleeSaved s2 s0 := ⟨htr2.trans htr1.1, hvregs_2.trans htr1.2⟩
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        (memRegion fsp 1392 ∗ memRegion (fsp + 1392#64) 128 ∗ memRegion (fsp + 1520#64) 368) ∗
        (stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816) ∗
        (ct1SentResultAt A (fsp + 1888#64) (Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u) ∗
         (pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         v9_optProtoPolyDecoderHeap A (optDec.map pbToProtoPolyDecoder) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion (fsp + 2016#64) 288 ∗
         A.pool ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_)
        (v9_tail_2864_to_ret_placed hA hDec s0 s2 hcl2 fsp out pbA w0 w8 w16 d24 d28 w32 u optDec
          hsp0_align hfsp_eq hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 htr2 hpts)
      rw [← v9_stackAt_encoderFromPbStack_eq_ct1SentFromPb fsp]
      exact Entails.trans (sepConj_mono_left (v9_memRegion_1392_1520_entails_1888 fsp)) (Entails.of_eq (by ac_rfl))

/-! ## 3. Variant 9 (`Ct1Acknowledged`, `+444`) & Top-Level Theorem -/

set_option maxHeartbeats 800000 in
/-- Variant 9 (`Ct1Acknowledged`) from the switch target `+444` to `s0.x30`. -/
theorem states_from_pb_ct1Acknowledged_444_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hDec : DecoderFromPbPlacedOkExt A ext)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem) (fsp out pbA : BitVec 64)
    (st : V1State.Chunked.Ct1Acknowledged)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = lsmpl.base 333 + 444#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx13 : s.readReg64 .x13 = fsp + 1264#64) (hx19 : s.readReg64 .x19 = out)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (optProtoInnerStateAt A pbA (some (.ct1Acknowledged st)) ∗
        A.pool ∗ stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ct1Acknowledged st) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  rcases st with ⟨optUc, optDec⟩
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1AcknowledgedAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono (v9_optProtoUcAt_unpack A (pbA + 8#64) optUc)
    (sepConj_mono_left (v9_optProtoPolyDecoderAt_unpack A (pbA + 136#64) (optDec.map pbToProtoPolyDecoder))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply v9_sepWPp_exists_left; intro w0; apply v9_sepWPp_exists_left; intro w8
  apply v9_sepWPp_exists_left; intro w16; apply v9_sepWPp_exists_left; intro d24
  apply v9_sepWPp_exists_left; intro d28; apply v9_sepWPp_exists_left; intro w32
  apply v9_sepWPp_exists_left; intro u0; apply v9_sepWPp_exists_left; intro u8
  apply v9_sepWPp_exists_left; intro u16; apply v9_sepWPp_exists_left; intro u24
  apply v9_sepWPp_exists_left; intro u32; apply v9_sepWPp_exists_left; intro u40
  apply v9_sepWPp_exists_left; intro u48; apply v9_sepWPp_exists_left; intro u56
  apply v9_sepWPp_exists_left; intro u64; apply v9_sepWPp_exists_left; intro u72
  apply v9_sepWPp_exists_left; intro u80; apply v9_sepWPp_exists_left; intro u88
  apply v9_sepWPp_exists_left; intro u96; apply v9_sepWPp_exists_left; intro u104
  apply v9_sepWPp_exists_left; intro u112; apply v9_sepWPp_exists_left; intro u120
  cases optDec with
  | none =>
    dsimp only [Option.map, v9_optProtoPolyDecoderHeap]
    refine SepWPp.weaken_pre (Entails.of_eq (show _ = ⌜w0 = noneCap⌝ ∗
      (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
       v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
       ((pbA ↦₆₄ 0x8000000000000009#64) ∗
        v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl)) ?_
    apply v9_sepWPp_pure_left; rintro rfl
    refine v9_sepWPp_seq_clean_lscl hcl
      (v9_states_from_pb_step_444_to_2768_none_placed s0 s fsp out pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
        w8 w16 d24 d28 w32 _ hpc hrun hsp hx19 hx27 htr) ?_
    rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx9_1, hx13_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, _, htr1⟩
    rw [hx13] at hx13_1; rw [hx25] at hx25_1
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (by ac_rfl))
        (Entails.trans (Entails.pure_right (rfl : noneCap = noneCap) (Entails.refl _))
          (Entails.of_eq (by dsimp only [Option.map, v9_optProtoPolyDecoderHeap]; ac_rfl))))
      (v9_tail_2768_to_ret_placed hA hDec s0 s1 hcl1 fsp out pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
        noneCap w8 w16 d24 d28 w32 optUc none
        hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx8_1 hx9_1 hx13_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1
        (by intro d hd; cases hd))
  | some d =>
    dsimp only [Option.map]
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d24 d28 w32 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
      (sepConj_mono_left (v9_optProtoPolyDecoderHeap_some_cap_lt A (pbToProtoPolyDecoder d) w0 w8 w16 d24 d28 w32))) ?_
    rw [sepConj_assoc]; apply v9_sepWPp_pure_left; rintro ⟨hw0_lt, hd24⟩
    change d24 = d.ptsNeeded at hd24; subst hd24
    cases hpts : d.ptsNeeded == 576#32
    · have hd24_ne : d.ptsNeeded ≠ 576#32 := by intro heq; rw [heq] at hpts; revert hpts; decide
      rw [v9_states_from_pb_ct1Acknowledged_ptsNeeded_ne optUc d hpts]; apply SepWPp.of_sepWP_ret
      refine SepWP.weaken_pre (Entails.of_eq (show _ =
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
      refine v9_seq_clean_lscl hcl
        (v9_states_from_pb_step_444_to_488_err_placed s0 s fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d.ptsNeeded d28 w32 _ hw0_lt hd24_ne hpc hrun hsp hx19 hx27 htr) ?_
      rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx8_1, hx19_1, hx20_1, hx21_1, hx22_1, _, _, htr1⟩
      cases optUc with
      | none =>
        dsimp only [v9_optProtoUcHeap]
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = ⌜u0 = noneCap⌝ ∗
            (((pbA ↦₆₄ 0x8000000000000009#64) ∗
              v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
              v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
             (v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              A.pool ∗ stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
              statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
          (sepConj_mono_right (sepConj_mono_left
            (v9_pbA_entails_224 pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
              w0 w8 w16 d.ptsNeeded d28 w32)))) ?_
        apply SepWP.pure_elim; rintro rfl
        refine EncoderFromPb.seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
          (v9_states_from_pb_drop_proto_uc_none_488_placed s0 s1 fsp out w8 w0 w16
            (v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
             memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
            hpc1 hrun1 hsp1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 htr1)) ?_
        rintro s2 hpc2 hrun2 ⟨hpres2, hx22_2⟩
        exact v9_tail_5368_to_ret_placed hA s0 s2 fsp out pbA w0 w8 w16 d.ptsNeeded d28 w32 2#64
          (pbToProtoPolyDecoder d) .msgDecode hsp0_align hfsp_eq hpc2 hrun2 hpres2 hx22_2 rfl
      | some u =>
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
            v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
            (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
             stackAt fsp encoderFromPbStack ∗
             ((pbA ↦₆₄ 0x8000000000000009#64) ∗
              v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
              memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
              A.pool ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
          (sepConj_mono_left
            (v9_optProtoUcHeap_some_cap_lt A u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120))) ?_
        rw [sepConj_assoc]; apply SepWP.pure_elim; intro hu0_lt
        refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
            (v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
             v9_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120) ∗
            stackAt fsp encoderFromPbStack ∗
            (A.pool ∗ (pbA ↦₆₄ 0x8000000000000009#64) ∗
             v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
          (sepConj_mono
            (v9_protoUcAt_pack A (pbA + 8#64) u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120)
            (sepConj_mono_left (Entails.trans (v9_stackAt_encoderFromPbStack_to_allocHook fsp)
              (v9_stackAt_allocHook_to_drop32 fsp))))) ?_
        refine EncoderFromPb.seq_clean
          (P_mid := v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
            memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
            memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          (SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
            (SepWP.strengthen_entails_const ?_
              (v9_states_from_pb_drop_proto_uc_some_488_placed hA s0 s1 fsp out (pbA + 8#64) u0 w8 w0 w16 u
                (memRegion (fsp - 5152#64) 1024 ∗ (pbA ↦₆₄ 0x8000000000000009#64) ∗
                 v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗
                 v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
                 memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗
                 statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
                hcl1 hfsp_align hu0_lt hpc1 hrun1 hsp1 hx0_1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 htr1))) ?_
        · refine Entails.trans (Entails.of_eq (show _ =
            ((pbA ↦₆₄ 0x8000000000000009#64) ∗ memRegion (pbA + 8#64) 128 ∗
             v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d.ptsNeeded d28 w32 ∗ memRegion (pbA + 176#64) 48) ∗
            (stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024) ∗
            (v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
             A.pool ∗ memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
          exact Entails.trans (sepConj_mono (v9_pbA_128_entails_224 pbA w0 w8 w16 d.ptsNeeded d28 w32)
            (sepConj_mono_left (Entails.trans (v9_stackAt_drop32_to_allocHook fsp)
              (v9_stackAt_allocHook_to_encoderFromPbStack fsp)))) (Entails.of_eq (by ac_rfl))
        · rintro s2 hpc2 hrun2 ⟨hpres2, hx22_2⟩
          exact v9_tail_5368_to_ret_placed hA s0 s2 fsp out pbA w0 w8 w16 d.ptsNeeded d28 w32 2#64
            (pbToProtoPolyDecoder d) .msgDecode hsp0_align hfsp_eq hpc2 hrun2 hpres2 hx22_2 rfl
    · have hd24_eq : d.ptsNeeded = 576#32 := beq_iff_eq.mp hpts
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 576#32 d28 w32 ∗
        ((pbA ↦₆₄ 0x8000000000000009#64) ∗
         v9_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
         v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) w0 w8 w16 d.ptsNeeded d28 w32 ∗
         memRegion (pbA + 176#64) 48 ∗ memRegion fsp 2304 ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by rw [hd24_eq]; ac_rfl)) ?_
      refine v9_sepWPp_seq_clean_lscl hcl
        (v9_states_from_pb_step_444_to_2768_some_placed s0 s fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d28 w32 _ hw0_lt hpc hrun hsp hx19 hx27 htr) ?_
      rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx9_1, _, hx13_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx27_1, _, htr1⟩
      rw [hx13] at hx13_1; rw [hx25] at hx25_1
      refine SepWPp.weaken_pre (Entails.of_eq (by rw [hd24_eq]; ac_rfl))
        (v9_tail_2768_to_ret_placed hA hDec s0 s1 hcl1 fsp out pbA
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120
          w0 w8 w16 d.ptsNeeded d28 w32 optUc (some d)
          hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx8_1 hx9_1 hx13_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx27_1 htr1
          (by intro d' hd'; cases hd'; exact hpts))

theorem v9_sepWPp_to_variantPlacedSpec [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (s0 s : State) (out pbA : BitVec 64) (pb : V1State) (P R : SepProp)
    (h : SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢ (resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) pb) ∗
           memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∗
          statesFromPbJumpTablePlacedAt) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf)) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)).post (out, pbA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F pb)).onPanic (out, pbA) s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  rcases hout with ⟨hpc, hrun, Pf, hmf, ⟨hPf, hsp, hcs, htr⟩⟩ | ⟨hst, Pf, hmf, hPf⟩ | hoom
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, ⟨fun hmem_f => ?_, hsp, hcs⟩⟩⟩
    dsimp only [withLsCodeLoaded, statesFromPbVariantPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, Satisfies.mono (Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (by ac_rfl))) hmem_f⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hst, Pf, hmf, fun hmem_f => Satisfies.mono (sepConj_mono_left hPf) hmem_f⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- Top-level `subroutine_ok` for Variant 9 (`some (.ct1Acknowledged st)`). -/
theorem states_from_pb_ct1Acknowledged_ok_ext_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (hDec : DecoderFromPbPlacedOkExt A ext)
    (st : V1State.Chunked.Ct1Acknowledged) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 333)
      (withLsCodeLoaded lsmpl (statesFromPbVariantPlacedSpec A F { innerState := some (.ct1Acknowledged st) })) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [statesFromPbVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, _⟩, hmem⟩
  refine ⟨stackAt s0.sp statesFromPbStack ∗
      (memRegion out chunkedStatesSize ∗ optProtoInnerStateAt A pbA (some (.ct1Acknowledged st)) ∗
       statesFromPbJumpTablePlacedAt ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  refine v9_sepWPp_to_variantPlacedSpec s0 s0 out pbA { innerState := some (.ct1Acknowledged st) } _ R ?_
  have hpro := states_from_pb_prologue_placed (ext := ext) s0 out pbA
    (memRegion out chunkedStatesSize ∗ optProtoInnerStateAt A pbA (some (.ct1Acknowledged st)) ∗
     statesFromPbJumpTablePlacedAt ∗ A.pool) hsp0_align hpc0 hrun0 hx8 hx0
  refine v9_sepWPp_seq_clean_lscl hcl0 hpro ?_
  rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, _, hx8_1, hx0_1, htr1⟩
  dsimp only [optProtoInnerStateAt, protoInnerStateAt]
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (((s0.sp - 2400#64) ↦₆₄ 0#64) ∗ memRegion ((s0.sp - 2400#64) + 8#64) 2296) ∗
      ((pbA ↦₆₄ 0x8000000000000009#64) ∗ statesFromPbJumpTablePlacedAt ∗
       (protoChunkedCt1AcknowledgedAt A (pbA + 8#64) st ∗ memRegion (pbA + 176#64) 48 ∗
        A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)) by ac_rfl))
      (sepConj_mono_left (cell0_2296_entails_memRegion_2304 (s0.sp - 2400#64) 0#64))) ?_
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (pbA ↦₆₄ 0x8000000000000009#64) ∗ statesFromPbJumpTablePlacedAt ∗
    (protoChunkedCt1AcknowledgedAt A (pbA + 8#64) st ∗ memRegion (pbA + 176#64) 48 ∗
     A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
  refine v9_sepWPp_seq_clean_lscl hcl1
    (states_from_pb_dispatch_tagged_placed (ext := ext) s0 s1 out pbA 0x8000000000000009#64 444#64 _
      TaggedVariantDispatch.ct1Acknowledged hpc1 hrun1 hsp1 hx8_1 hx0_1 htr1) ?_
  rintro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx27_2, _, hx25_2, _, hx13_2, _, htr2⟩
  have hx13_2' : s2.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64 := by rw [hx13_2]; bv_omega
  have hx25_2' : s2.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64 := by rw [hx25_2]; bv_omega
  refine SepWPp.weaken_pre (by dsimp only [optProtoInnerStateAt, protoInnerStateAt]; exact Entails.of_eq (by ac_rfl))
    (v9_sepWPp_frame_right (J := statesFromPbJumpTablePlacedAt)
      (states_from_pb_ct1Acknowledged_444_placed hA hDec s0 s2 hcl2 (s0.sp - 2400#64) out pbA st
        hsp0_align rfl hpc2 hrun2 hsp2 hx13_2' hx19_2 hx25_2' hx27_2 htr2))

abbrev states_from_pb_variant8_placed := @states_from_pb_ct1Acknowledged_ok_ext_placed

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9Placed

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9Placed (
  v9_sub_ok_ct1_sent_from_pb_placed
  v9_tail_2864_to_ret_placed
  v9_tail_2768_to_ret_placed
  states_from_pb_ct1Acknowledged_444_placed
  states_from_pb_ct1Acknowledged_ok_ext_placed
  states_from_pb_variant8_placed
)
end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9Placed (
  v9_sub_ok_ct1_sent_from_pb_placed
  v9_tail_2864_to_ret_placed
  v9_tail_2768_to_ret_placed
  states_from_pb_ct1Acknowledged_444_placed
  states_from_pb_ct1Acknowledged_ok_ext_placed
  states_from_pb_variant8_placed
)
end CryptoVerification.SpqrV1.States.FromPb
