/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for Protobuf Chunked States (`HeaderReceived`, `EkSentCt1Received`, `HeaderSent`)

**Checked by Lean.**

Proves subroutine contracts for:
- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>` (`0x4cc0c`, Block `283`)
- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>` (`0x4cda4`, Block `285`)
- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>` (`0x4ca84`, Block `281`)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L14

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Stack Frame Helpers for `dropStack96` (`0x4ca84`) -/

theorem stackAt_dropStack96_split_cells (sp : BitVec 64) :
    stackAt sp dropStack96 =
      stackAt (sp - 48#64) dropStack48 ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp dropStack48 6 (by decide)

theorem stackAt_dropStack48_sub48_split_bottom (sp : BitVec 64) :
    stackAt (sp - 48#64) dropStack48 =
      memRegion (sp - 4192#64) 48 ∗ stackAt (sp - 48#64) allocHookStack := by
  have hsub : (sp - 48#64) - 4144#64 = sp - 4192#64 := by bv_omega
  rw [stackAt_dropStack48_split_bottom (sp - 48#64), hsub]

theorem stackAt_dropStack96_split (sp : BitVec 64) :
    stackAt sp dropStack96 =
      (memRegion (sp - 4192#64) 48 ∗ stackAt (sp - 48#64) allocHookStack) ∗
        cells (sp - 48#64) 6 := by
  rw [stackAt_dropStack96_split_cells sp, stackAt_dropStack48_sub48_split_bottom sp]

theorem stack_restore_96_allocHook (sp fp lr x22 x21 x20 x19 : BitVec 64) :
    (memRegion (sp - 4192#64) 48 ∗ stackAt (sp - 48#64) allocHookStack) ∗
      (((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
       ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
       ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19)) ⊢
    stackAt sp dropStack96 := by
  rw [stackAt_dropStack96_split sp]
  exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)

theorem stackAt_dropStack96_split_bottom (sp : BitVec 64) :
    stackAt sp dropStack96 = memRegion (sp - 4192#64) 96 ∗ stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 96 (by decide)

/-! ## `drop_glue::<proto::pq_ratchet::v1_state::chunked::HeaderReceived>` (`0x4cc0c`) -/

local macro "proto_chunked2_body_steps" prog:term:max entry:term:max off_mid:term:max : tactic =>
  `(tactic| (
  intro cur cnt bs s Frame hpc hrun ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩ hx19 hx20 hx21 hx22
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP $prog ($entry + $off_mid) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗ vecCapPtrDealloc A cap vptr) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm => (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep))

local macro "proto_chunked2_loop_steps" entry:term:max off_mid:term:max off_head:term:max : tactic =>
  `(tactic| (
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := $entry + $off_mid)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩; wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := $entry + $off_head)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x22 = (cur + 24#64) + 8#64) ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _))

local macro "proto_chunked_header_received_main_steps" entry:term : tactic =>
  `(tactic| (
  wp_init x s0; rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropProtoChunkedHeaderReceivedGhost.a, DropProtoChunkedHeaderReceivedGhost.st,
    protoChunkedHeaderReceivedAt] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack48_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := $entry + 100#64)
    (P_mid := (memRegion a 80 ∗
      optProtoPolynomialDecoderAt A (a + 80#64) (st.receivingEk.map pbToProtoPolyDecoder)) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedHeaderReceivedAt_none]; wp_steps
      refine SepWP.focus_weaken (optProtoUnchunked1Vec_none_entails_memRegion_80 a) (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedHeaderReceivedAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (protoUnchunkedHeaderReceivedAt_entails_dealloc A a u)) ?_
      wp_pull_exists; rename_i v1; wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean (mid := $entry + 80#64)
        (P_mid := ((protoUnchunked1VecHeadersAt a v1 ∗ memRegion (a + 24#64) 48 ∗ memRegion (a + 72#64) 8 ∗
          vecCapPtrDealloc A v1.cap v1.ptr) ∗
          optProtoPolynomialDecoderAt A (a + 80#64) (st.receivingEk.map pbToProtoPolyDecoder)) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = v1.cap) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_24_none]; dsimp only [protoUnchunked1VecHeadersAt]; wp_steps
          refine SepWP.focus_weaken (optProtoAuthenticatorAt_24_none_entails_memRegion_48 A a) (by sep_focus) ?_
          refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (a + 24#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_24_eq]; wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean (mid := $entry + 60#64)
            (P_mid := ((protoUnchunked1VecHeadersAt a v1 ∗ (auth24HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 72#64) 8 ∗ vecCapPtrDealloc A v1.cap v1.ptr) ∗
              optProtoPolynomialDecoderAt A (a + 80#64) (st.receivingEk.map pbToProtoPolyDecoder)) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = v1.cap) ?_ ?_
          · dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
          · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1, hx20_a1⟩
            dsimp only [auth24HeadersAt, vecCapPtrDealloc]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken (auth24HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine SepWP.focus_weaken (auth24HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by rw [hsp_a1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
        dsimp only [protoUnchunked1VecHeadersAt, vecCapPtrDealloc]
        by_cases hc1 : (v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine SepWP.focus_weaken (protoUnchunked1VecHeadersAt_entails_memRegion_80' a v1) (by sep_focus) ?_; wp_done
        · wp_steps; wp_apply; refine SepWP.focus_weaken (protoUnchunked1VecHeadersAt_entails_memRegion_80' a v1) (by sep_focus) ?_
          refine align_pre (by rw [hsp_1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    have hjoin120_from_40 : memRegion a 80 ∗ memRegion (a + 80#64) 40 ⊢ memRegion a 120 := by
      rw [ProofLib.memRegion_split' (b := a) (n := 80) (k := 40) (b' := a + 80#64) rfl rfl (by decide)]
      exact Entails.refl _
    have h88 : (a + 80#64) + 8#64 = a + 88#64 := BitVec.add_assoc a 80#64 8#64
    have h96 : (a + 80#64) + 16#64 = a + 96#64 := BitVec.add_assoc a 80#64 16#64
    have h104 : (a + 80#64) + 24#64 = a + 104#64 := BitVec.add_assoc a 80#64 24#64
    cases hek : st.receivingEk with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
      rw [h88]; wp_steps
      have hnone40 : ((a + 80#64) ↦₆₄ noneCap) ∗ memRegion (a + 88#64) 32 ⊢ memRegion (a + 80#64) 40 := by
        rw [← h88]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 80#64)
      refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin120_from_40 (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      wp_done
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (a + 80#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; rw [h88, h96, h104]
      wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 (cap : BitVec 64) :
          ((a + 80#64) ↦₆₄ cap) ∗ ((a + 88#64) ↦₆₄ g.ptr) ∗
            ((a + 96#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 104#64) 16 ⊢
          memRegion (a + 80#64) 40 := by
        rw [← h88, ← h96, ← h104]
        exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 80#64) cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      refine seq_clean (mid := $entry + 164#64)
        (P_mid := memRegion a 80 ∗ ((a + 80#64) ↦₆₄ g.cap) ∗ ((a + 88#64) ↦₆₄ g.ptr) ∗
          ((a + 96#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          memRegion (a + 104#64) 16 ∗ A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢
        cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
          wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := $entry + 140#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              (memRegion a 80 ∗ ((a + 80#64) ↦₆₄ g.cap) ∗ ((a + 88#64) ↦₆₄ g.ptr) ∗
               ((a + 96#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ A.live g.ptr (g.cap.toNat * 24) 8 ∗
               memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 104#64) 16 ∗
               (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64) ?_ ?_
          · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            refine SepWP.strengthen_entails_const ?_
              (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hx19_loop hx20_loop hx21_loop hx22_loop)
            have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
            conv_rhs =>
              arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
              rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24) ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
            exact Entails.of_eq (by ac_rfl)
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
        by_cases hc : g.cap = 0
        · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_3 ⊢; wp_steps
          refine SepWP.focus_weaken (hhdr40 0) (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin120_from_40 (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          wp_done
        · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt
          simp only [hc, ↓reduceIte]; wp_steps
          refine SepWP.focus_weaken (hhdr40 g.cap) (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin120_from_40 (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          rw [stackAt_dropStack48_split_bottom s0.sp]
          wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
          rw [← stackAt_dropStack48_split_bottom s0.sp]
          wp_done))

private theorem drop_proto_chunked_header_received_body {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderReceivedName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderReceivedName + 140#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderReceivedName + 128#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; dsimp only [dropProgAtExt, dropProtoChunkedHeaderReceivedName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>" = entry
  examples_hide_fetches; proto_chunked2_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry 128#64

private theorem drop_proto_chunked_header_received_loop {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderReceivedName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderReceivedName + 140#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderReceivedName + 164#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_header_received_body (b := b) (ext := ext) hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  dsimp only [dropProgAtExt, dropProtoChunkedHeaderReceivedName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>" = entry
  examples_hide_fetches; proto_chunked2_loop_steps entry 128#64 140#64

theorem drop_proto_chunked_header_received_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderReceivedName) (dropProtoChunkedHeaderReceivedSpec A) := by
  simp only [dropProtoChunkedHeaderReceivedSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderReceivedName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>") (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hloop := drop_proto_chunked_header_received_loop (b := b) (ext := ext) hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>"
  dsimp only [dropProgAtExt, dropProtoChunkedHeaderReceivedName, protoChunkedHeaderReceivedSize, BitVec.ofNat_eq_ofNat] at hloop hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived>" = entry
  examples_hide_fetches; proto_chunked_header_received_main_steps entry

section PlacedHeaderReceived
variable [LibsignalPlacement]

private theorem drop_proto_chunked_header_received_body_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_283).rebase (blkPl_283).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_283).base + 140#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_283).rebase (blkPl_283).base H) ((blkPl_283).base + 128#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; proto_chunked2_body_steps ((blkPC_283).rebase (blkPl_283).base H) (blkPl_283).base 128#64

private theorem drop_proto_chunked_header_received_loop_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_283).rebase (blkPl_283).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_283).base + 140#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_283).rebase (blkPl_283).base H) ((blkPl_283).base + 164#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_header_received_body_placed hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  proto_chunked2_loop_steps (blkPl_283).base 128#64 140#64

theorem drop_proto_chunked_header_received_placed_ok {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_283).rebase (blkPl_283).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_283).rebase (blkPl_283).base H) (blkPl_283).base (dropProtoChunkedHeaderReceivedSpec A) := by
  simp only [dropProtoChunkedHeaderReceivedSpec]
  have hdealloc_raw := hdealloc
  have hloop := drop_proto_chunked_header_received_loop_placed hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw; dsimp only [protoChunkedHeaderReceivedSize] at *
  proto_chunked_header_received_main_steps (blkPl_283).base

end PlacedHeaderReceived

/-! ## `drop_glue::<proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>` (`0x4cda4`) -/

local macro "proto_chunked_ek_sent_ct1_received_main_steps" entry:term : tactic =>
  `(tactic| (
  wp_init x s0; rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropProtoChunkedEkSentCt1ReceivedGhost.a, DropProtoChunkedEkSentCt1ReceivedGhost.st,
    protoChunkedEkSentCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack48_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := $entry + 120#64)
    (P_mid := (memRegion a 104 ∗
      optProtoPolynomialDecoderAt A (a + 104#64) (st.receivingCt2.map pbToProtoPolyDecoder)) ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]; wp_steps
      refine SepWP.focus_weaken (optProtoUnchunked2Vec_none_entails_memRegion_104 a) (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A a u)) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean (mid := $entry + 80#64)
        (P_mid := ((protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
          optProtoPolynomialDecoderAt A (a + 104#64) (st.receivingCt2.map pbToProtoPolyDecoder)) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_48_none]; dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt]; wp_steps
          refine SepWP.focus_weaken (optProtoAuthenticatorAt_48_none_entails_memRegion_48 A a) (by sep_focus) ?_
          refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (a + 48#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_48_eq]; wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean (mid := $entry + 60#64)
            (P_mid := ((protoUnchunked2VecHeadersAt a g ∗ (auth48HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
              optProtoPolynomialDecoderAt A (a + 104#64) (st.receivingCt2.map pbToProtoPolyDecoder)) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap) ?_ ?_
          · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt, vecCapPtrDealloc]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
          · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1, hx20_a1⟩
            dsimp only [auth48HeadersAt, vecCapPtrDealloc]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by rw [hsp_a1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
        refine seq_clean (mid := $entry + 100#64)
          (P_mid := ((protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
            vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
            optProtoPolynomialDecoderAt A (a + 104#64) (st.receivingCt2.map pbToProtoPolyDecoder)) ∗
            A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
          by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
        · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine SepWP.focus_weaken (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g) (by sep_focus) ?_; wp_done
          · wp_steps; wp_apply; refine SepWP.focus_weaken (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g) (by sep_focus) ?_
            refine align_pre (by rw [hsp_2]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
  · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
    have hjoin144_from_40 : memRegion a 104 ∗ memRegion (a + 104#64) 40 ⊢ memRegion a 144 := by
      rw [ProofLib.memRegion_split' (b := a) (n := 104) (k := 40) (b' := a + 104#64) rfl rfl (by decide)]
      exact Entails.refl _
    have h112 : (a + 104#64) + 8#64 = a + 112#64 := BitVec.add_assoc a 104#64 8#64
    have h120 : (a + 104#64) + 16#64 = a + 120#64 := BitVec.add_assoc a 104#64 16#64
    have h128 : (a + 104#64) + 24#64 = a + 128#64 := BitVec.add_assoc a 104#64 24#64
    cases hct2 : st.receivingCt2 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
      rw [h112]; wp_steps
      have hnone40 : ((a + 104#64) ↦₆₄ noneCap) ∗ memRegion (a + 112#64) 32 ⊢ memRegion (a + 104#64) 40 := by
        rw [← h112]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 104#64)
      refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin144_from_40 (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      wp_done
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (a + 104#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; rw [h112, h120, h128]
      wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have hhdr40 (cap : BitVec 64) :
          ((a + 104#64) ↦₆₄ cap) ∗ ((a + 112#64) ↦₆₄ g.ptr) ∗
            ((a + 120#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 128#64) 16 ⊢
          memRegion (a + 104#64) 40 := by
        rw [← h112, ← h120, ← h128]
        exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 104#64) cap g.ptr (BitVec.ofNat 64 pb.pts.length)
      refine seq_clean (mid := $entry + 184#64)
        (P_mid := memRegion a 104 ∗ ((a + 104#64) ↦₆₄ g.cap) ∗ ((a + 112#64) ↦₆₄ g.ptr) ∗
          ((a + 120#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          memRegion (a + 128#64) 16 ∗ A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢
        cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
          wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := $entry + 160#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗
              A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              (memRegion a 104 ∗ ((a + 104#64) ↦₆₄ g.cap) ∗ ((a + 112#64) ↦₆₄ g.ptr) ∗
               ((a + 120#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ A.live g.ptr (g.cap.toNat * 24) 8 ∗
               memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 128#64) 16 ∗
               (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64) ?_ ?_
          · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            refine SepWP.strengthen_entails_const ?_
              (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hx19_loop hx20_loop hx21_loop hx22_loop)
            have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
            conv_rhs =>
              arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
              rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24) ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
            exact Entails.of_eq (by ac_rfl)
      · intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4⟩
        by_cases hc : g.cap = 0
        · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_4 ⊢; wp_steps
          refine SepWP.focus_weaken (hhdr40 0) (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin144_from_40 (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          wp_done
        · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt
          simp only [hc, ↓reduceIte]; wp_steps
          refine SepWP.focus_weaken (hhdr40 g.cap) (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin144_from_40 (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          rw [stackAt_dropStack48_split_bottom s0.sp]
          wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
          rw [← stackAt_dropStack48_split_bottom s0.sp]
          wp_done))

private theorem drop_proto_chunked_ek_sent_ct1_received_body {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedEkSentCt1ReceivedName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoChunkedEkSentCt1ReceivedName + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoChunkedEkSentCt1ReceivedName + 148#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; dsimp only [dropProgAtExt, dropProtoChunkedEkSentCt1ReceivedName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>" = entry
  examples_hide_fetches; proto_chunked2_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry 148#64

private theorem drop_proto_chunked_ek_sent_ct1_received_loop {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedEkSentCt1ReceivedName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoChunkedEkSentCt1ReceivedName + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoChunkedEkSentCt1ReceivedName + 184#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_ek_sent_ct1_received_body (b := b) (ext := ext) hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  dsimp only [dropProgAtExt, dropProtoChunkedEkSentCt1ReceivedName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>" = entry
  examples_hide_fetches; proto_chunked2_loop_steps entry 148#64 160#64

theorem drop_proto_chunked_ek_sent_ct1_received_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoChunkedEkSentCt1ReceivedName) (dropProtoChunkedEkSentCt1ReceivedSpec A) := by
  simp only [dropProtoChunkedEkSentCt1ReceivedSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedEkSentCt1ReceivedName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>") (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hloop := drop_proto_chunked_ek_sent_ct1_received_loop (b := b) (ext := ext) hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>"
  dsimp only [dropProgAtExt, dropProtoChunkedEkSentCt1ReceivedName, protoChunkedEkSentCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hloop hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::EkSentCt1Received>" = entry
  examples_hide_fetches; proto_chunked_ek_sent_ct1_received_main_steps entry

section PlacedEkSentCt1Received
variable [LibsignalPlacement]

private theorem drop_proto_chunked_ek_sent_ct1_received_body_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_285).rebase (blkPl_285).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_285).base + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_285).rebase (blkPl_285).base H) ((blkPl_285).base + 148#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; proto_chunked2_body_steps ((blkPC_285).rebase (blkPl_285).base H) (blkPl_285).base 148#64

private theorem drop_proto_chunked_ek_sent_ct1_received_loop_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_285).rebase (blkPl_285).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_285).base + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_285).rebase (blkPl_285).base H) ((blkPl_285).base + 184#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_ek_sent_ct1_received_body_placed hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  proto_chunked2_loop_steps (blkPl_285).base 148#64 160#64

theorem drop_proto_chunked_ek_sent_ct1_received_placed_ok {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_285).rebase (blkPl_285).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_285).rebase (blkPl_285).base H) (blkPl_285).base (dropProtoChunkedEkSentCt1ReceivedSpec A) := by
  simp only [dropProtoChunkedEkSentCt1ReceivedSpec]
  have hdealloc_raw := hdealloc
  have hloop := drop_proto_chunked_ek_sent_ct1_received_loop_placed hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw; dsimp only [protoChunkedEkSentCt1ReceivedSize] at *
  proto_chunked_ek_sent_ct1_received_main_steps (blkPl_285).base

end PlacedEkSentCt1Received

/-! ## `drop_glue::<proto::pq_ratchet::v1_state::chunked::HeaderSent>` (`0x4ca84`) -/

local macro "proto_chunked_header_sent_main_steps" entry:term : tactic =>
  `(tactic| (
  wp_init x s0; rcases x with ⟨a, st⟩; have hx0 : s0.readReg64 .x0 = a := h
  dsimp only [DropProtoChunkedHeaderSentGhost.a, DropProtoChunkedHeaderSentGhost.st, protoChunkedHeaderSentAt] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := $entry + 100#64)
    (P_mid := (memRegion a 80 ∗
      optProtoPolynomialEncoderAt A (a + 80#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
      optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingCt1.map pbToProtoPolyDecoder)) ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedEkSentAt_none]; wp_steps
      refine SepWP.focus_weaken (optProtoUnchunked1Vec_none_entails_memRegion_80 a) (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedEkSentAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (protoUnchunkedEkSentAt_entails_dealloc A a u)) ?_
      wp_pull_exists; rename_i v1; wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean (mid := $entry + 80#64)
        (P_mid := ((protoUnchunked1VecHeadersAt a v1 ∗ memRegion (a + 24#64) 48 ∗ memRegion (a + 72#64) 8 ∗
          vecCapPtrDealloc A v1.cap v1.ptr) ∗
          optProtoPolynomialEncoderAt A (a + 80#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
          optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingCt1.map pbToProtoPolyDecoder)) ∗
          A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = v1.cap) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_24_none]; dsimp only [protoUnchunked1VecHeadersAt]; wp_steps
          refine SepWP.focus_weaken (optProtoAuthenticatorAt_24_none_entails_memRegion_48 A a) (by sep_focus) ?_
          refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (a + 24#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_24_eq]; wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean (mid := $entry + 60#64)
            (P_mid := ((protoUnchunked1VecHeadersAt a v1 ∗ (auth24HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 72#64) 8 ∗ vecCapPtrDealloc A v1.cap v1.ptr) ∗
              optProtoPolynomialEncoderAt A (a + 80#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
              optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingCt1.map pbToProtoPolyDecoder)) ∗
              A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = v1.cap) ?_ ?_
          · dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
          · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1, hx20_a1⟩
            dsimp only [auth24HeadersAt, vecCapPtrDealloc]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken (auth24HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine SepWP.focus_weaken (auth24HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by rw [hsp_a1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
        dsimp only [protoUnchunked1VecHeadersAt, vecCapPtrDealloc]
        by_cases hc1 : (v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine SepWP.focus_weaken (protoUnchunked1VecHeadersAt_entails_memRegion_80' a v1) (by sep_focus) ?_; wp_done
        · wp_steps; wp_apply; refine SepWP.focus_weaken (protoUnchunked1VecHeadersAt_entails_memRegion_80' a v1) (by sep_focus) ?_
          refine align_pre (by rw [hsp_1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    refine seq_clean (mid := $entry + 120#64)
      (P_mid := (memRegion a 136 ∗
        optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingCt1.map pbToProtoPolyDecoder)) ∗
        A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · cases hek : st.sendingEk with
      | none =>
        simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
        have h88 : (a + 80#64) + 8#64 = a + 88#64 := BitVec.add_assoc a 80#64 8#64
        rw [h88]; wp_steps
        have hjoin136 : memRegion a 80 ∗ ((a + 80#64) ↦₆₄ noneCap) ∗ memRegion (a + 88#64) 48 ⊢ memRegion a 136 := by
          rw [← h88, ProofLib.memRegion_split' (b := a) (n := 80) (k := 56) (b' := a + 80#64) rfl rfl (by decide)]
          exact sepConj_mono_right (optProtoPolyEncoder_none_entails_memRegion_56 (a + 80#64))
        refine SepWP.focus_weaken hjoin136 (by sep_focus) ?_; wp_done
      | some enc =>
        simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
        refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A (a + 80#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
        wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
        have hne_none := cap_add_one_beq_zero_false hcap_lt
        wp_steps
        refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A (a + 80#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
        have hstack_fold : memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack ⊢ stackAt (s0.sp - 48#64) dropStack48 :=
          Entails.of_eq (stackAt_dropStack48_sub48_split_bottom s0.sp).symm
        refine SepWP.focus_weaken hstack_fold (by sep_focus) ?_
        wp_call hpoly_enc_raw ⟨a + 80#64, pbToProtoPolyEncoder enc⟩
        rw [hsp_2, stackAt_dropStack48_sub48_split_bottom s0.sp]
        have hjoin136 : memRegion a 80 ∗ memRegion (a + 80#64) protoPolynomialEncoderSize ⊢ memRegion a 136 := by
          rw [show (136 : Nat) = 80 + protoPolynomialEncoderSize from rfl,
              ProofLib.memRegion_split a 80 protoPolynomialEncoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin136 (by sep_focus) ?_
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
      have hjoin176_from_40 : memRegion a 136 ∗ memRegion (a + 136#64) 40 ⊢ memRegion a 176 := by
        rw [ProofLib.memRegion_split' (b := a) (n := 136) (k := 40) (b' := a + 136#64) rfl rfl (by decide)]
        exact Entails.refl _
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      have h152 : (a + 136#64) + 16#64 = a + 152#64 := BitVec.add_assoc a 136#64 16#64
      have h160 : (a + 136#64) + 24#64 = a + 160#64 := BitVec.add_assoc a 136#64 24#64
      cases hct1 : st.receivingCt1 with
      | none =>
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
        rw [h144]; wp_steps
        have hnone40 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 32 ⊢ memRegion (a + 136#64) 40 := by
          rw [← h144]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 136#64)
        refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin176_from_40 (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        wp_done
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
        let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (a + 136#64) pb) (by sep_focus) ?_
        wp_pull_exists; rename_i g; rw [h144, h152, h160]
        wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
        have hhdr40 (cap : BitVec 64) :
            ((a + 136#64) ↦₆₄ cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
              ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 160#64) 16 ⊢
            memRegion (a + 136#64) 40 := by
          rw [← h144, ← h152, ← h160]
          exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 136#64) cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        refine seq_clean (mid := $entry + 184#64)
          (P_mid := memRegion a 136 ∗ ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
            ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            memRegion (a + 160#64) 16 ∗ A.pool ∗
            (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
        · generalize hxs : pb.pts = xs at hpts_le ⊢
          cases xs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
            wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          | cons bs tl =>
            have hlen_pos : 0 < (bs :: tl).length := by simp
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
              have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
            have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
            have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_clean (mid := $entry + 160#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗
                A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                (memRegion a 136 ∗ ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
                 ((a + 152#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ A.live g.ptr (g.cap.toNat * 24) 8 ∗
                 memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (a + 160#64) 16 ∗ memRegion (s0.sp - 4192#64) 48 ∗
                 (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
              (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
                sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64) ?_ ?_
            · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
            · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
              refine SepWP.strengthen_entails_const ?_
                (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr s_loop _
                  (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hx19_loop hx20_loop hx21_loop hx22_loop)
              have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
                rw [← Nat.add_mul]; congr 1; omega
              have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
              conv_rhs =>
                arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
                rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24) ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
              exact Entails.of_eq (by ac_rfl)
        · intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4⟩
          by_cases hc : g.cap = 0
          · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_4 ⊢; wp_steps
            refine SepWP.focus_weaken (hhdr40 0) (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin176_from_40 (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            wp_done
          · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_mul_24 hpts_cap_lt
            simp only [hc, ↓reduceIte]; wp_steps
            refine SepWP.focus_weaken (hhdr40 g.cap) (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin176_from_40 (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            rw [stackAt_dropStack96_split_bottom s0.sp]
            wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
            rw [← stackAt_dropStack96_split_bottom s0.sp]
            wp_done))

private theorem drop_proto_chunked_header_sent_body {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName + 148#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; dsimp only [dropProgAtExt, dropProtoChunkedHeaderSentName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>" = entry
  examples_hide_fetches; proto_chunked2_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry 148#64

private theorem drop_proto_chunked_header_sent_loop {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>" "__rustc::__rust_dealloc")) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName + 184#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_header_sent_body (b := b) (ext := ext) hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  dsimp only [dropProgAtExt, dropProtoChunkedHeaderSentName, BitVec.ofNat_eq_ofNat] at *
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>"
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>" = entry
  examples_hide_fetches; proto_chunked2_loop_steps entry 148#64 160#64

theorem drop_proto_chunked_header_sent_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName) (dropProtoChunkedHeaderSentSpec A) := by
  simp only [dropProtoChunkedHeaderSentSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>" "__rustc::__rust_dealloc")) (rustDeallocSpec A) :=
    sub_ok_of_addr_eq (Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>") (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hpoly_enc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName + bv% (2 ^ 64 - ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>"))
      (dropProtoPolyEncoderSpec A) := by
    have hrel : (dropProgAtExt b ext).fnAddr dropProtoChunkedHeaderSentName =
        (dropProgAtExt b ext).fnAddr dropProtoPolyEncoderName + bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>") :=
      Program.fnAddr_rel (k := num% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>")) (b := b) (X := Rust.withPanics ext)
        (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::PolynomialEncoder>") (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>") (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_proto_poly_encoder_ok_ext hdealloc)
    rw [hrel, BitVec.add_assoc]; simp
  have hloop := drop_proto_chunked_header_sent_loop (b := b) (ext := ext) hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw
  ls_code_fetches libsignalSessionCode spqrDropChainEpochBin b (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>"
  dsimp only [dropProgAtExt, dropProtoChunkedHeaderSentName, protoChunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at hloop hdealloc_raw hpoly_enc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "core::ptr::drop_glue::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent>" = entry
  examples_hide_fetches; proto_chunked_header_sent_main_steps entry

section PlacedHeaderSent
variable [LibsignalPlacement]

private theorem drop_proto_chunked_header_sent_body_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_281).rebase (blkPl_281).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_281).base + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_281).rebase (blkPl_281).base H) ((blkPl_281).base + 148#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc; proto_chunked2_body_steps ((blkPC_281).rebase (blkPl_281).base H) (blkPl_281).base 148#64

private theorem drop_proto_chunked_header_sent_loop_placed {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_281).rebase (blkPl_281).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_281).base + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_281).rebase (blkPl_281).base H) ((blkPl_281).base + 184#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_header_sent_body_placed hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  proto_chunked2_loop_steps (blkPl_281).base 148#64 160#64

theorem drop_proto_chunked_header_sent_placed_ok {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_281).rebase (blkPl_281).base H) (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly_enc_raw : subroutine_ok ((blkPC_281).rebase (blkPl_281).base H) (lsmpl.base 271) (dropProtoPolyEncoderSpec A)) :
    subroutine_ok ((blkPC_281).rebase (blkPl_281).base H) (blkPl_281).base (dropProtoChunkedHeaderSentSpec A) := by
  simp only [dropProtoChunkedHeaderSentSpec]
  have hdealloc_raw := hdealloc
  have hloop := drop_proto_chunked_header_sent_loop_placed hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw; dsimp only [protoChunkedHeaderSentSize] at *
  proto_chunked_header_sent_main_steps (blkPl_281).base

end PlacedHeaderSent

end CryptoVerification.SpqrV1.Drop
