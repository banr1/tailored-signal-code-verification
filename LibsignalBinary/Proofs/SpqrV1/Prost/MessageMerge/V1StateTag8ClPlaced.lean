/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag9ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag8
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Tag Arm 8 (`Ct1Sampled`) for `V1State::merge` (Block `298`)

Verifies tag arm 8 (`Ct1Sampled`, entry `+516`, fresh-init `+1272`) under `[LibsignalPlacement]`
with `withLsCl`-wrapped cross-block drops (`286`, `271`, `267`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Drop hiding cap_add_one_beq_zero_false
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

attribute [local irreducible] Program.fetch Program.externAt?
  v1StateMergeJumpTablePlacedExpanded optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

private theorem v1Tag8_err_dec_body_1448_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    {fsp ptsPtr ptsCap : BitVec 64} (hsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_298).base + 1448#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 (Reg.gpr 22#5) = ptsPtr → s.readReg64 (Reg.gpr 23#5) = ptsCap →
      s.readReg64 (Reg.gpr 24#5) = cnt → s.readReg64 (Reg.gpr 25#5) = cur + 8#64 →
      SepWP ((blkPC_298).rebase (blkPl_298).base H)
        ((blkPl_298).base + 1436#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          sm.readReg64 (Reg.gpr 24#5) = cnt ∧ sm.readReg64 (Reg.gpr 25#5) = cur + 8#64) := by
  simp only [rustDeallocSpec] at hDealloc
  intro cur cnt bs s Frame hpc hrun hsp hx22 hx23 hx24 hx25
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_298).rebase (blkPl_298).base H) ((blkPl_298).base + 1436#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
        sm.readReg64 (Reg.gpr 24#5) = cnt ∧ sm.readReg64 (Reg.gpr 25#5) = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

private theorem v1Tag8_err_dec_loop_1448_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    {fsp ptsPtr ptsCap : BitVec 64} (hsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_298).base + 1448#64 →
      s.status = .Running → s.sp = fsp →
      s.readReg64 (Reg.gpr 22#5) = ptsPtr → s.readReg64 (Reg.gpr 23#5) = ptsCap →
      s.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 rest.length → s.readReg64 (Reg.gpr 25#5) = cur + 8#64 →
      SepWP ((blkPC_298).rebase (blkPl_298).base H)
        ((blkPl_298).base + 2072#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap) := by
  have hbody := v1Tag8_err_dec_body_1448_cl_placed (H := H) hDealloc (ptsPtr := ptsPtr) (ptsCap := ptsCap) hsp_align
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hsp hx22 hx23 hx24 hx25
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_298).base + 1436#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
        sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 (Reg.gpr 25#5) = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hsp hx22 hx23 hx24 hx25) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, ⟨htr1, hvregs1⟩, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx24_1 ⊢; wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx24_1
      refine seq_clean (mid := (blkPl_298).base + 1448#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
          sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
          sm.readReg64 (Reg.gpr 22#5) = ptsPtr ∧ sm.readReg64 (Reg.gpr 23#5) = ptsCap ∧
          sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 (Reg.gpr 25#5) = (cur + 24#64) + 8#64)
        (by rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done) ?_
      intro s2 hpc2 hrun2 ⟨hsp2, htr2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2⟩
      refine SepWP.mono (ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
        (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 (hsp2.trans hsp) hx22_2 hx23_2 hx24_2 hx25_2) ?_
      rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hx21_m, hx22_m, hx23_m⟩
      have hsplit := cons_len_mul bs (bs2 :: tl2) 24
      have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      refine ⟨Entails.trans hPm ?_, hspm.trans hsp2, htrm.trans htr2, hx21_m.trans hx21_2, hx22_m, hx23_m⟩
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
      exact Entails.refl _

private theorem v1Tag8_err_dec_1404_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    {s : State} {fsp : BitVec 64} {optDec : Option PolynomialDecoder} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1404#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoPolynomialDecoderAt A (fsp + 424#64) (optDec.map pbToProtoPolyDecoder) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 424#64) 40 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  cases optDec with
  | none =>
    have hnone40 : ((fsp + 424#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 432#64) 32 ⊢ memRegion (fsp + 424#64) 40 := by
      have h432 : (fsp + 424#64) + 8#64 = fsp + 432#64 := by bv_lin
      rw [← h432]; exact optProtoPolyDecoder_none_entails_memRegion_40 (fsp + 424#64)
    simp only [Option.map_none, optProtoPolynomialDecoderAt_none', show (fsp + 424#64) + 8#64 = fsp + 432#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone40 (by sep_focus); wp_done
  | some dec =>
    simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
    let pb := pbToProtoPolyDecoder dec
    apply SepWP.fold (protoPolyDecoderAt_entails_dealloc A (fsp + 424#64) pb) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro g; apply SepWP.pure_elim; rintro ⟨hpts_le, hpts_cap_lt, _hpts_ptr_ne⟩
    have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
    have hne_none : (g.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hpts_cap_pow
    have h432 : (fsp + 424#64) + 8#64 = fsp + 432#64 := by bv_lin
    have h440 : (fsp + 424#64) + 16#64 = fsp + 440#64 := by bv_lin
    have h448 : (fsp + 424#64) + 24#64 = fsp + 448#64 := by bv_lin
    have hhdr40 : ((fsp + 424#64) ↦₆₄ g.cap) ∗ ((fsp + 432#64) ↦₆₄ g.ptr) ∗
        ((fsp + 440#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (fsp + 448#64) 16 ⊢
        memRegion (fsp + 424#64) 40 := by
      rw [← h432, ← h440, ← h448]
      exact protoPolyDecoderHeaders_entails_memRegion_40 (fsp + 424#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
    rw [h432, h440, h448]
    refine seq_clean (mid := (blkPl_298).base + 2072#64)
      (P_mid := (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion (fsp + 424#64) 40 ∗ Frame))
      (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = g.ptr ∧ sm.readReg64 (Reg.gpr 23#5) = g.cap) ?_ ?_
    · generalize hxs : pb.pts = xs at hpts_le hhdr40 ⊢
      cases xs with
      | nil =>
        simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero, arrayAt, emp_sepConj] at hhdr40 ⊢
        wp_steps; apply SepWP.fold hhdr40 (by sep_focus); wp_done
      | cons bs tl =>
        have hlen_pos : 0 < (bs :: tl).length := by simp
        have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
          have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
        have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
        have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
        simp only [hcap_ne, ↓reduceIte]
        refine seq_clean (mid := (blkPl_298).base + 1448#64)
          (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗
            (A.live g.ptr (g.cap.toNat * 24) 8 ∗
              memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
              memRegion (fsp + 424#64) 40 ∗ Frame))
          (Q := fun sm => sm.sp = s.sp ∧ sm.v1TraceEq s ∧
            sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
            sm.readReg64 (Reg.gpr 22#5) = g.ptr ∧ sm.readReg64 (Reg.gpr 23#5) = g.cap ∧
            sm.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 (bs :: tl).length ∧
            sm.readReg64 (Reg.gpr 25#5) = g.ptr + 8#64)
          (by
            wp_steps; apply SepWP.fold hhdr40 (by sep_focus); wp_done) ?_
        intro s_loop hpc_loop hrun_loop ⟨hsp_loop, htr_loop, hx21_loop, hx22_loop, hx23_loop, hx24_loop, hx25_loop⟩
        refine SepWP.mono (v1Tag8_err_dec_loop_1448_cl_placed hDealloc (ptsPtr := g.ptr) (ptsCap := g.cap) hsp_align
          (bs :: tl) g.ptr s_loop _
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop (hsp_loop.trans hsp)
          hx22_loop hx23_loop hx24_loop hx25_loop) ?_
        rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hx21_m, hx22_m, hx23_m⟩
        have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        refine ⟨Entails.trans hPm ?_, hspm.trans hsp_loop, htrm.trans htr_loop, hx21_m.trans hx21_loop, hx22_m, hx23_m⟩
        conv_rhs =>
          arg 1; arg 2
          rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24)
                ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
        exact Entails.of_eq (by ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hx21_2, hx22_2, hx23_2⟩
      refine SepWP.mono (v1Tag8_err_pts_buf_2072_placed hDealloc hsp_align hpts_cap_lt hpc2 hrun2 (hsp2.trans hsp) hx22_2 hx23_2) ?_
      rintro sm Pm hpcm hrunm ⟨hPm, hspm, htrm, hx21_m⟩
      exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hspm.trans hsp2, htrm.trans htr2, hx21_m.trans hx21_2⟩

private theorem v1Tag8_err_uc_1364_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)))
    {s : State} {fsp : BitVec 64} {optUc : Option V1State.Unchunked.Ct1SentEkReceived} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1364#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1384#64) s
      (optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) optUc ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 128 ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  simp only [withLsCl, dropProtoUnchunkedCt1SentEkReceivedSpec] at hDropUc
  cases optUc with
  | none =>
    have hnone128 : ((fsp + 240#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 248#64) 120 ⊢ memRegion (fsp + 240#64) 128 := by
      have h248 : (fsp + 240#64) + 8#64 = fsp + 248#64 := by bv_lin
      rw [← h248]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A (fsp + 240#64)
    rw [optProtoUnchunkedCt1SentEkReceivedAt_none, show (fsp + 240#64) + 8#64 = fsp + 248#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone128 (by sep_focus); wp_done
  | some u =>
    rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_expose_cap A (fsp + 240#64) u) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps_lscl (lsmpl.base 286)
    apply SepWP.fold (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A (fsp + 240#64) cap ptr u) (by sep_focus)
    wp_apply; dsimp only [protoUnchunkedCt1SentEkReceivedSize]; wp_done

private theorem v1Tag8_err_enc_1384_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271) (withLsCl lsmpl (dropProtoPolyEncoderSpec A)))
    {s : State} {fsp : BitVec 64} {optEnc : Option PolynomialEncoder} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1384#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1404#64) s
      (optProtoPolynomialEncoderAt A (fsp + 368#64) (optEnc.map pbToProtoPolyEncoder) ∗
        A.pool ∗ stackAt fsp dropStack48 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 368#64) 56 ∗ A.pool ∗ stackAt fsp dropStack48 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  simp only [withLsCl, dropProtoPolyEncoderSpec] at hDropEnc
  cases optEnc with
  | none =>
    have hnone56 : ((fsp + 368#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 376#64) 48 ⊢ memRegion (fsp + 368#64) 56 := by
      have h376 : (fsp + 368#64) + 8#64 = fsp + 376#64 := by bv_lin
      rw [← h376]; exact optProtoPolyEncoder_none_entails_memRegion_56 (fsp + 368#64)
    simp only [Option.map_none, optProtoPolynomialEncoderAt_none', show (fsp + 368#64) + 8#64 = fsp + 376#64 by bv_lin]
    wp_steps; apply SepWP.fold hnone56 (by sep_focus); wp_done
  | some enc =>
    simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
    apply SepWP.fold (protoPolynomialEncoderAt_expose_cap A (fsp + 368#64) (pbToProtoPolyEncoder enc)) (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap; apply SepWP.exists_elim; intro ptr; apply SepWP.pure_elim; intro hcap_lt
    have hne_none : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_false hcap_lt
    wp_steps_lscl (lsmpl.base 271)
    apply SepWP.fold (protoPolynomialEncoderAt_unexpose_cap A (fsp + 368#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus)
    wp_apply; dsimp only [protoPolynomialEncoderSize]; wp_done

private theorem v1Tag8_err_1364_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286)
      (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271) (withLsCl lsmpl (dropProtoPolyEncoderSpec A)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    {s : State} {fsp : BitVec 64} {cs : V1State.Chunked.Ct1Sampled} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1364#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx25 : s.readReg64 (Reg.gpr 25#5) = fsp + 240#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (protoChunkedCt1SampledAt A (fsp + 240#64) cs ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 240#64) 224 ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5)) := by
  dsimp only [protoChunkedCt1SampledAt]
  have h368 : (fsp + 240#64) + 128#64 = fsp + 368#64 := by bv_lin
  have h424 : (fsp + 240#64) + 184#64 = fsp + 424#64 := by bv_lin
  have hjoin224 : memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 56 ∗ memRegion (fsp + 424#64) 40 ⊢
      memRegion (fsp + 240#64) 224 := by
    let k96 : Nat := 96
    let k40 : Nat := 40
    rw [memRegion_split' (b := fsp + 240#64) (b' := fsp + 368#64) (n := 128) (k := k96) (N := 224) rfl (by bv_lin) (by decide),
      memRegion_split' (b := fsp + 368#64) (b' := fsp + 424#64) (n := 56) (k := k40) (N := 96) rfl (by bv_lin) (by decide)]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre (P' :=
    optProtoUnchunkedCt1SentEkReceivedAt A (fsp + 240#64) (cs.uc.map ct1SentToCt1SentEkReceived) ∗ A.pool ∗ stackAt fsp dropStack32 ∗
      (optProtoPolynomialEncoderAt A (fsp + 368#64) (cs.sendingCt1.map pbToProtoPolyEncoder) ∗
        optProtoPolynomialDecoderAt A (fsp + 424#64) (cs.receivingEk.map pbToProtoPolyDecoder) ∗
        v1StateBelowRest fsp dropStack32 ∗ Frame))
    (Entails.of_eq (by rw [v1Tag8_optProtoUnchunkedCt1SentAt_eq, h368, h424, v1StateBelow_dropStack32 fsp]; ac_rfl)) ?_
  refine sepWP_seq_keep_lscl hcl (v1Tag8_err_uc_1364_cl_placed hDropUc hcl hsp_align hpc hrun hsp) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hP1, hsp1, htr1, hx21_1, hx25_1⟩
  apply SepWP.weaken_pre hP1; apply SepWP.fold (v1StateBelow_dropStack32_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialEncoderAt A (fsp + 368#64) (cs.sendingCt1.map pbToProtoPolyEncoder) ∗ A.pool ∗ stackAt fsp dropStack48 ∗
      (memRegion (fsp + 240#64) 128 ∗
        optProtoPolynomialDecoderAt A (fsp + 424#64) (cs.receivingEk.map pbToProtoPolyDecoder) ∗
        v1StateBelowRest fsp dropStack48 ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_dropStack48 fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag8_err_enc_1384_cl_placed hDropEnc hcl1 hsp_align hpc1 hrun1 (hsp1.trans hsp) (hx25_1.trans hx25)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, htr2, hx21_2⟩
  apply SepWP.weaken_pre hP2; apply SepWP.fold (v1StateBelow_dropStack48_entails fsp) (by sep_focus)
  refine SepWP.weaken_pre (P' :=
    optProtoPolynomialDecoderAt A (fsp + 424#64) (cs.receivingEk.map pbToProtoPolyDecoder) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
      (memRegion (fsp + 240#64) 128 ∗ memRegion (fsp + 368#64) 56 ∗ v1StateBelowRest fsp allocHookStack ∗ Frame))
    (Entails.of_eq (by rw [v1StateBelow_allocHook fsp]; ac_rfl)) ?_
  refine SepWP.seq (v1Tag8_err_dec_1404_cl_placed hDealloc hsp_align hpc2 hrun2 (hsp2.trans (hsp1.trans hsp))) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
  apply SepWP.weaken_pre hP3; apply SepWP.fold (v1StateBelow_allocHook_entails fsp) (by sep_focus)
  apply SepWP.fold hjoin224 (by sep_focus)
  exact SepWP.done hpc3 hrun3
    ⟨Entails.of_eq (by ac_rfl), hsp3.trans (hsp2.trans hsp1), htr3.trans (htr2.trans htr1), hx21_3.trans (hx21_2.trans hx21_1)⟩

private theorem v1Tag8_setup_1272_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {s : State} {fsp w_sp16 w_sp144 w_sp200 : BitVec 64} {restLen : Nat} {Frame : SepProp}
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1272#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 300) s
      (((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
        ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗
        ((fsp + 200#64) ↦₆₄ w_sp200) ∗ memRegion (fsp + 208#64) 32 ∗ Frame)
      (fun s1 P1 =>
        (P1 ⊢ chunkedCt1SampledPBCapAt A (fsp + 16#64) restLen default ∗ Frame) ∧
        s1.sp = s.sp ∧ s1.v1TraceEq s ∧ s1.readReg64 (Reg.gpr 0#5) = s.readReg64 (Reg.gpr 0#5) ∧
        s1.readReg64 (Reg.gpr 1#5) = fsp + 16#64 ∧ s1.readReg64 (Reg.gpr 2#5) = s.readReg64 (Reg.gpr 19#5) ∧
        s1.readReg64 Reg.lr = (blkPl_298).base + 1296#64 ∧
        s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧ s1.readReg64 (Reg.gpr 20#5) = s.readReg64 (Reg.gpr 20#5) ∧
        s1.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧ s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hdef : ((fsp + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 152#64) 48 ∗
      ((fsp + 200#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (fsp + 208#64) 32 ⊢
      chunkedCt1SampledPBCapAt A (fsp + 16#64) restLen default := by
    change _ ⊢ chunkedCt1SampledPBCapAt A (fsp + 16#64) restLen ⟨none, none, none⟩
    dsimp only [chunkedCt1SampledPBCapAt, optUnchunkedCt1SentPBCapAt, optPolynomialEncoderPBAt, optPolynomialDecoderPBAt, noneCap]
    have h24 : (fsp + 16#64) + 8#64 = fsp + 24#64 := by bv_lin
    have h144 : (fsp + 16#64) + 128#64 = fsp + 144#64 := by bv_lin
    have h152 : (fsp + 144#64) + 8#64 = fsp + 152#64 := by bv_lin
    have h200 : (fsp + 16#64) + 184#64 = fsp + 200#64 := by bv_lin
    have h208 : (fsp + 200#64) + 8#64 = fsp + 208#64 := by bv_lin
    rw [h24, h144, h152, h200, h208]; exact Entails.of_eq (by ac_rfl)
  wp_steps; apply SepWP.fold hdef (by sep_focus); wp_done

private theorem v1Tag8_copy_ok_1296_cl_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp464 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1296#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2508#64) s
      (v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ w_sp464) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
          memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = 0#64 ∧
        sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧ sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ sm.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5)) := by
  have hfold240 := v1Tag8_words28At_entails_memRegion_224 (fsp + 240#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
  conv => arg 4; rw [v1Tag8_memRegion_224_eq_words28 (fsp + 240#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15; apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11; apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17; apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v27
  apply SepWP.exists_elim; intro v26; apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v24; apply SepWP.exists_elim; intro v23
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold240 ⊢
  wp_steps; apply SepWP.fold hfold240 (by sep_focus); wp_done

private theorem v1Tag8_copy_err_1296_cl_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp mPtr w_sp464 : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 1296#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) ≠ 0#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 1364#64) s
      (v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ w_sp464) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 224 ∗
          v1Tag8_words28At (fsp + 240#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
          ((fsp + 464#64) ↦₆₄ mPtr) ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 0#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5)) := by
  have hfold16 := v1Tag8_words28At_entails_memRegion_224 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
  conv => arg 4; rw [v1Tag8_memRegion_224_eq_words28 (fsp + 240#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v15; apply SepWP.exists_elim; intro v14; apply SepWP.exists_elim; intro v13
  apply SepWP.exists_elim; intro v12; apply SepWP.exists_elim; intro v11; apply SepWP.exists_elim; intro v10; apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v18; apply SepWP.exists_elim; intro v17; apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v27
  apply SepWP.exists_elim; intro v26; apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v24; apply SepWP.exists_elim; intro v23
  have hbr : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag8_pre_drop_2508_cl_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64}
    {Frame : SepProp} (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2508#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr) (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2568#64) s
      (v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 480#64) 224 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 16#64) 224 ∗
          v1Tag8_words28At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 0#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧ sm.readReg64 (Reg.gpr 20#5) = mPtr ∧
        sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧ sm.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) ∧
        sm.readReg64 (Reg.gpr 23#5) = s.readReg64 (Reg.gpr 23#5) ∧ sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧
        sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧ sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
        sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧ sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧
        sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold16 := v1Tag8_words28At_entails_memRegion_224 (fsp + 16#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
  conv => arg 4; rw [v1Tag8_memRegion_224_eq_words28 (fsp + 480#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro u2; apply SepWP.exists_elim; intro u1; apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro u4; apply SepWP.exists_elim; intro u3; apply SepWP.exists_elim; intro u8; apply SepWP.exists_elim; intro u7
  apply SepWP.exists_elim; intro u6; apply SepWP.exists_elim; intro u15; apply SepWP.exists_elim; intro u14; apply SepWP.exists_elim; intro u13
  apply SepWP.exists_elim; intro u12; apply SepWP.exists_elim; intro u11; apply SepWP.exists_elim; intro u10; apply SepWP.exists_elim; intro u9
  apply SepWP.exists_elim; intro u22; apply SepWP.exists_elim; intro u21; apply SepWP.exists_elim; intro u20; apply SepWP.exists_elim; intro u19
  apply SepWP.exists_elim; intro u18; apply SepWP.exists_elim; intro u17; apply SepWP.exists_elim; intro u16; apply SepWP.exists_elim; intro u27
  apply SepWP.exists_elim; intro u26; apply SepWP.exists_elim; intro u25; apply SepWP.exists_elim; intro u24; apply SepWP.exists_elim; intro u23
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold16 ⊢
  wp_steps; apply SepWP.fold hfold16 (by sep_focus); wp_done

private theorem v1Tag8_post_drop_2568_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    {s : State} {fsp mPtr : BitVec 64}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : BitVec 64}
    {is : Option V1State.InnerState} {Frame : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 2568#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = mPtr) (hx20 : s.readReg64 (Reg.gpr 20#5) = mPtr)
    (hx29 : s.readReg64 (Reg.gpr 29#5) = fsp + 720#64) :
    SepWP ((blkPC_298).rebase (blkPl_298).base H)
      ((blkPl_298).base + 2700#64) s
      (optProtoInnerStateAt A mPtr is ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag8_words28At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ v1Tag8_words28At mPtr w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
          memRegion (fsp + 480#64) 224 ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗ Frame) ∧
        sm.sp = s.sp ∧ sm.v1TraceEq s ∧ sm.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
        sm.readReg64 (Reg.gpr 20#5) = mPtr ∧ sm.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) ∧
        sm.readReg64 (Reg.gpr 22#5) = 0x8000000000000000#64 ∧ sm.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 ∧
        sm.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ sm.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧
        sm.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧ sm.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧
        sm.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5) ∧ sm.readReg64 (Reg.gpr 29#5) = fsp + 720#64) := by
  have hfold480 := v1Tag8_words28At_entails_memRegion_224 (fsp + 480#64)
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27
  simp only [withLsCl, dropOptProtoInnerStatePlacedSpec] at hDropInner
  wp_steps_lscl (lsmpl.base 267)
  wp_apply; dsimp only [optProtoInnerStateSize]
  conv => arg 4; rw [v1Tag8_memRegion_224_eq_words28 mPtr]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro d2; apply SepWP.exists_elim; intro d1; apply SepWP.exists_elim; intro d0; apply SepWP.exists_elim; intro d5
  apply SepWP.exists_elim; intro d4; apply SepWP.exists_elim; intro d3; apply SepWP.exists_elim; intro d8; apply SepWP.exists_elim; intro d7
  apply SepWP.exists_elim; intro d6; apply SepWP.exists_elim; intro d15; apply SepWP.exists_elim; intro d14; apply SepWP.exists_elim; intro d13
  apply SepWP.exists_elim; intro d12; apply SepWP.exists_elim; intro d11; apply SepWP.exists_elim; intro d10; apply SepWP.exists_elim; intro d9
  apply SepWP.exists_elim; intro d22; apply SepWP.exists_elim; intro d21; apply SepWP.exists_elim; intro d20; apply SepWP.exists_elim; intro d19
  apply SepWP.exists_elim; intro d18; apply SepWP.exists_elim; intro d17; apply SepWP.exists_elim; intro d16; apply SepWP.exists_elim; intro d27
  apply SepWP.exists_elim; intro d26; apply SepWP.exists_elim; intro d25; apply SepWP.exists_elim; intro d24; apply SepWP.exists_elim; intro d23
  dsimp only [v1Tag8_words28At, words16At, words13At, words10At, words7At, words5At, words3At] at hfold480 ⊢
  wp_steps; apply SepWP.fold hfold480 (by sep_focus); wp_done

private theorem v1Tag8_discrFull_ct1Sampled {bsLen : Nat} {cs : V1State.Chunked.Ct1Sampled} {d : BitVec 64}
    (hd : InnerStateDiscrFull bsLen (some (.ct1Sampled cs)) d) :
    (d + 2#64 == 0#64) = false ∧ BitVec.sle d 0x800000000000000a#64 = false := by
  refine ⟨(discrFull_some_add2 hd).1, ?_⟩
  rcases cs with ⟨_ | u, _, _⟩
  · change d = noneCap at hd; subst hd; decide
  · have hlt : d.toNat < 2 ^ 63 := hd.1
    rw [BitVec.sle, decide_eq_false_iff_not]
    have hd_int : d.toInt = (d.toNat : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]; split_ifs <;> omega
    have hc_int : (0x800000000000000a#64 : BitVec 64).toInt = -9223372036854775798 := rfl
    omega

private theorem v1Tag8_discrFull_other {bsLen : Nat} {is : V1State.InnerState} {d : BitVec 64}
    (hne : ∀ v, is ≠ .ct1Sampled v) (hd : InnerStateDiscrFull bsLen (some is) d) :
    BitVec.sle d 0x800000000000000a#64 = true := by
  cases is with
  | ct1Sampled v => exact absurd rfl (hne v)
  | _ => subst hd; decide

private theorem v1Tag8_inplace_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 300)
      (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {cs : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_is : m.innerState = some (.ct1Sampled cs))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 516#64)
    (hcont : V1StateTagContClPlaced A H s0 x R 8 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  obtain ⟨honErr, honOk⟩ := hcont
  have hx9_cs : InnerStateDiscrFull rest.length (some (.ct1Sampled cs)) (s.readReg64 (Reg.gpr 9#5)) :=
    hm_is ▸ hx9
  obtain ⟨hbr1, hbr2⟩ := v1Tag8_discrFull_ct1Sampled hx9_cs
  obtain ⟨hpe, hpd⟩ : OptPolyEncoderBound cs.sendingCt1 rest.length ∧ OptPolyDecoderBound cs.receivingEk rest.length := by
    simpa only [hm_is] using ct1Sampled_polyBound_extract hpoly
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 300) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, hm_is, optProtoInnerStateCapAt, protoInnerStateCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  wp_steps; wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, x.msgPtr, cs, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 556#64) hCsCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [chunkedCt1SampledMergeSpec]; simp only [arm64_norm, hsp, hx0, hx20, hx19]; rfl)
    (⟨rfl, rfl, rfl, ((optPolyEncoderBound_iff _ _).mp hpe).1, ((optPolyEncoderBound_iff _ _).mp hpe).2, (optPolyDecoderBound_iff _ _).mp hpd⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧
        x.msgPtr = x.msgPtr ∧ x.bufRef = x.bufRef ∧
        optPolyEncoderPtsLen cs.sendingCt1 + rest.length < 2 ^ 56 ∧
        optPolyEncoderPolysLen cs.sendingCt1 + rest.length < 2 ^ 56 ∧
        optPolyDecoderPtsLen cs.receivingEk + rest.length < 2 ^ 56)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt1SampledMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hm_field := v1State_mergeField_tag8 m iwt rest 99
  rw [hm_is] at hm_field; dsimp only at hm_field
  cases hcs_res : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto iwt) cs rest 99).toOption with
  | none =>
    rw [hcs_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1SampledMergeSpec, hcs_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro cs'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hfold_is : chunkedCt1SampledPBAt A x.msgPtr cs' ⊢
        ∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is' := by
      rw [chunkedCt1SampledPBAt_eq_proto]
      exact optProtoInnerStateAt_entails_exists A x.msgPtr (some (.ct1Sampled cs'))
    apply SepWP.fold hfold_is (by sep_focus)
    wp_steps; wp_reach; intro hinv_e
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced]; ac_rfl))
    exact honErr hm_field _ (sm.readReg64 (Reg.gpr 0#5)) n_err
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 hn_err hinv_e
  | some p =>
    rcases p with ⟨cs', rest'⟩
    rw [hcs_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hcs_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Sampled cs')) :=
      innerStatePolyBound_of_ct1Sampled ⟨hpe, hpd⟩ hcs_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv =>
      arg 4
      simp only [chunkedCt1SampledMergeSpec, hcs_res, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps; wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct1Sampled cs') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, optProtoInnerStateCapAt, protoInnerStateCapAt]; ac_rfl))
    exact honOk { m with innerState := some (.ct1Sampled cs') } rest' _ hm_field hpoly' hrest'_le
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hsm0])
      ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m],
       by simp only [arm64_norm, hx22_m], by simp only [arm64_norm, hx23_m],
       by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hfp_m]⟩ hinv_n

private theorem v1Tag8_at_1272_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286) (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271) (withLsCl lsmpl (dropProtoPolyEncoderSpec A)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hm_not : ∀ cs, m.innerState ≠ some (.ct1Sampled cs))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 1272#64)
    (hcont : V1StateTagContClPlaced A H s0 x R 8 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hsp_align, hrest_le, _hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, _hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  let fsp : BitVec 64 := s0.sp - 816#64
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := by dsimp only [fsp]; simpa only [arm64_norm] using hsp_align
  have hfsp720 : fsp + 720#64 = s0.sp - 96#64 := by dsimp only [fsp]; bv_lin
  have hfsp240 : fsp + 240#64 = s0.sp - 576#64 := by dsimp only [fsp]; bv_lin
  have h56 : rest.length < 2 ^ 56 := optInnerStatePolyBound_lt_2_56 hpoly
  have hpe0 : OptPolyEncoderBound (default : V1State.Chunked.Ct1Sampled).sendingCt1 rest.length := optPolyEncoderBound_none h56
  have hpd0 : OptPolyDecoderBound (default : V1State.Chunked.Ct1Sampled).receivingEk rest.length := optPolyDecoderBound_none h56
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 300) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, show s0.sp - 816#64 = fsp from rfl,
      v1Tag8_memRegion_split_temp fsp, v1Tag8_memRegion_224_split_init fsp,
      sliceCursorAfter_eq_split hrest_le hrest_suf]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w_sp464; apply SepWP.exists_elim; intro w_sp200
  apply SepWP.exists_elim; intro w_sp144; apply SepWP.exists_elim; intro w_sp16
  refine SepWP.weaken_pre (P' :=
    ((fsp + 16#64) ↦₆₄ w_sp16) ∗ memRegion (fsp + 24#64) 120 ∗
      ((fsp + 144#64) ↦₆₄ w_sp144) ∗ memRegion (fsp + 152#64) 48 ∗
      ((fsp + 200#64) ↦₆₄ w_sp200) ∗ memRegion (fsp + 208#64) 32 ∗
      (stackAt fsp chunkedInlStack ∗ memRegion fsp 16 ∗
        memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ w_sp464) ∗
        memRegion (fsp + 472#64) 8 ∗ memRegion (fsp + 480#64) 224 ∗
        memRegion (fsp + 704#64) 16 ∗ v1StateJumpTablesPlacedAt ∗
        optProtoInnerStateCapAt A x.msgPtr rest.length m.innerState ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot restPtr rest ∗
        (x.ptr ↦ₛ x.bs.take (x.bs.length - rest.length)) ∗ A.pool ∗ v1StateSavedRegsAt s0.sp s0))
    (Entails.of_eq (by dsimp only [restPtr]; ac_rfl)) ?_
  refine SepWP.mono (v1Tag8_setup_1272_cl_placed (A := A) (restLen := rest.length) hfsp_align hpc hrun hsp hx23) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1,
    hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩ hinv_c
  rw [hsp] at hsp1; rw [hx19] at hx2_1 hx19_1; rw [hx20] at hx20_1
  rw [hx22] at hx22_1; rw [hx24] at hx24_1; rw [hx25] at hx25_1
  rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1
  have hx0_1' : (s1.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by rw [hx0_1, hx0]
  apply SepWPp.weaken_pre hP1
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := ⟨iwt, fsp + 16#64, default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_298).base + 1296#64) hCsCall
    hpc1 hrun1 (by simp only [State.spAligned, hsp1]; exact hfsp_align) hlr1
    (by dsimp only [chunkedCt1SampledMergeSpec]; simp only [hx0_1', hx1_1, hx2_1, hsp1]; rfl)
    (⟨rfl, rfl, rfl, ((optPolyEncoderBound_iff _ _).mp hpe0).1, ((optPolyEncoderBound_iff _ _).mp hpe0).2, (optPolyDecoderBound_iff _ _).mp hpd0⟩ :
      BitVec.ofNat 8 iwt.toNat = BitVec.ofNat 8 iwt.toNat ∧ fsp + 16#64 = fsp + 16#64 ∧ x.bufRef = x.bufRef ∧
        optPolyEncoderPtsLen (default : V1State.Chunked.Ct1Sampled).sendingCt1 + rest.length < 2 ^ 56 ∧
        optPolyEncoderPolysLen (default : V1State.Chunked.Ct1Sampled).sendingCt1 + rest.length < 2 ^ 56 ∧
        optPolyDecoderPtsLen (default : V1State.Chunked.Ct1Sampled).receivingEk + rest.length < 2 ^ 56)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [chunkedCt1SampledMergeSpec] at hpan; exact allowPanic_frame' (htr1.trans htr) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  rw [hsp1] at hspm
  rw [hx19_1] at hx19_m; rw [hx20_1] at hx20_m; rw [hx22_1] at hx22_m; rw [hx23_1] at hx23_m
  rw [hx24_1] at hx24_m; rw [hx25_1] at hx25_m; rw [hx26_1] at hx26_m; rw [hx27_1] at hx27_m
  rw [hx28_1] at hx28_m; rw [hx29_1] at hfp_m
  have hm_field : (V1State.mergeField m (BitVec.ofNat 32 8) (codecWireTypeToProto iwt) rest 99).toOption =
      (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption.map
        (fun (v', rest') => ({ m with innerState := some (.ct1Sampled v') }, rest')) := by
    rw [v1State_mergeField_tag8]
    rcases h : m.innerState with _ | st
    · rfl
    · cases st with
      | ct1Sampled cs => exact absurd h (hm_not cs)
      | _ => rfl
  cases hcs_res : (Proto.mergeMessage V1State.Chunked.Ct1Sampled.mergeField (codecWireTypeToProto iwt) default rest 99).toOption with
  | none =>
    rw [hcs_res, Option.map_none] at hm_field
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv => arg 4; simp only [chunkedCt1SampledMergeSpec, hcs_res, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.exists_elim; intro cs'; apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hcs_words : chunkedCt1SampledPBAt A (fsp + 16#64) cs' ⊢
        ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64,
        ∃∗ w12 : BitVec 64, ∃∗ w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w17 : BitVec 64,
        ∃∗ w18 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64, ∃∗ w23 : BitVec 64,
        ∃∗ w24 : BitVec 64, ∃∗ w25 : BitVec 64, ∃∗ w26 : BitVec 64, ∃∗ w27 : BitVec 64,
          v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
          v1Tag8_capHeap A 0 cs' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 :=
      Entails.trans (v1Tag8_chunkedCt1SampledPBAt_entails_cap_zero A (fsp + 16#64) cs') (v1Tag8_extract_words A (fsp + 16#64) 0 cs')
    apply SepWP.fold hcs_words (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9; apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13; apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17; apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21; apply SepWP.exists_elim; intro w22; apply SepWP.exists_elim; intro w23
    apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w25; apply SepWP.exists_elim; intro w26; apply SepWP.exists_elim; intro w27
    apply SepWP.fold (Entails.trans (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState)
      (optProtoInnerStateAt_entails_exists A x.msgPtr m.innerState)) (by sep_focus)
    rw [← hfsp240] at hx25_m
    let Frame_err : SepProp :=
      v1Tag8_capHeap A 0 cs' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
      A.pool ∗ stackAt fsp chunkedInlStack ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
      memRegion fsp 16 ∗ memRegion (fsp + 472#64) 8 ∗
      memRegion (fsp + 480#64) 224 ∗ memRegion (fsp + 704#64) 16 ∗ v1StateJumpTablesPlacedAt ∗
      (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
      (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ w_sp464) ∗ Frame_err)
      (Entails.of_eq (by dsimp only [Frame_err]; ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1Tag8_copy_err_1296_cl_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx21_2, hx25_2⟩
    apply SepWP.weaken_pre hP2; dsimp only [Frame_err]
    apply SepWP.fold (v1Tag8_words_entails_protoChunkedCt1Sampled A (fsp + 240#64) cs'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27) (by sep_focus)
    refine SepWP.weaken_pre (P' :=
      protoChunkedCt1SampledAt A (fsp + 240#64) cs' ∗ A.pool ∗ stackAt fsp chunkedInlStack ∗
        (memRegion (fsp + 16#64) 224 ∗ ((fsp + 464#64) ↦₆₄ x.msgPtr) ∗
          decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
          memRegion fsp 16 ∗ memRegion (fsp + 472#64) 8 ∗
          memRegion (fsp + 480#64) 224 ∗ memRegion (fsp + 704#64) 16 ∗ v1StateJumpTablesPlacedAt ∗
          (∃∗ is' : Option V1State.InnerState, optProtoInnerStateAt A x.msgPtr is') ∗
          (x.bufRef ↦₆₄ x.slot) ∗ memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs) ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag8_err_1364_cl_placed hDropUc hDropEnc hDealloc hcl2 hfsp_align hpc2 hrun2
      (hsp2.trans hspm) (hx25_2.trans hx25_m)) ?_
    rintro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, htr3, hx21_3⟩
    apply SepWP.weaken_pre hP3
    apply SepWP.fold (v1Tag8_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    refine SepWP.done hpc3 hrun3 (fun hinv3 => ?_)
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ stackAt (s0.sp - 816#64) chunkedInlStack ∗
        memRegion (s0.sp - 816#64) 720 ∗ v1StateErrFramePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (Entails.of_eq (by dsimp only [v1StateErrFramePlaced, fsp]; ac_rfl))
    exact hcont.onErr hm_field s3 (sm.readReg64 (Reg.gpr 0#5)) n_err hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm))
      (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr))))
      (hx21_3.trans hx21_2) hsm0 hn_err hinv3
  | some p =>
    rcases p with ⟨cs', rest'⟩
    rw [hcs_res, Option.map_some] at hm_field
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hcs_res
    have hpoly' : OptInnerStatePolyBound rest'.length (some (.ct1Sampled cs')) :=
      innerStatePolyBound_of_ct1Sampled ⟨hpe0, hpd0⟩ hcs_res
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 2700#64) hinv_m ?_
    conv => arg 4; simp only [chunkedCt1SampledMergeSpec, hcs_res, sepConj_assoc, arm64_norm, hsp1]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; replace htrm : sm.v1TraceEq _ := ⟨htrm, hvregs_m⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoInnerStateCapAt_entails_pb A x.msgPtr rest.length m.innerState) (by sep_focus)
    apply SepWP.fold (v1Tag8_extract_words A (fsp + 16#64) rest'.length cs') (by sep_focus)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1; apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5; apply SepWP.exists_elim; intro w6; apply SepWP.exists_elim; intro w7
    apply SepWP.exists_elim; intro w8; apply SepWP.exists_elim; intro w9; apply SepWP.exists_elim; intro w10; apply SepWP.exists_elim; intro w11
    apply SepWP.exists_elim; intro w12; apply SepWP.exists_elim; intro w13; apply SepWP.exists_elim; intro w14; apply SepWP.exists_elim; intro w15
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w17; apply SepWP.exists_elim; intro w18; apply SepWP.exists_elim; intro w19
    apply SepWP.exists_elim; intro w20; apply SepWP.exists_elim; intro w21; apply SepWP.exists_elim; intro w22; apply SepWP.exists_elim; intro w23
    apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w25; apply SepWP.exists_elim; intro w26; apply SepWP.exists_elim; intro w27
    rw [← hfsp720] at hfp_m; dsimp only [v1StateJumpTablesPlacedAt]
    let Frame_ok : SepProp :=
      v1Tag8_capHeap A rest'.length cs' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗
      (v1StateBelowRest fsp dropStack96 ∗ stackAt fsp dropStack96) ∗
      memRegion fsp 16 ∗ memRegion (fsp + 472#64) 8 ∗ memRegion (fsp + 704#64) 16 ∗
      v1StateMergeJumpTablePlacedExpanded ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗ v1StateSavedRegsAt s0.sp s0
    refine SepWP.weaken_pre (P' :=
      v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ w_sp464) ∗ (memRegion (fsp + 480#64) 224 ∗ Frame_ok))
      (Entails.of_eq (by dsimp only [Frame_ok]; rw [← v1StateBelow_dropStack96 fsp]; ac_rfl)) ?_
    refine sepWP_seq_keep_lscl hinv_m.1 (v1Tag8_copy_ok_1296_cl_placed hfsp_align hpcm hrunm hspm hsm0 hx20_m) ?_
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hx19_2, hx20_2, hx21_2, _hx22_2, _hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2⟩
    refine SepWP.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl :
      v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ x.msgPtr) ∗ (memRegion (fsp + 480#64) 224 ∗ Frame_ok) =
      v1Tag8_words28At (fsp + 16#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        memRegion (fsp + 480#64) 224 ∗ (memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ x.msgPtr) ∗ Frame_ok)))) ?_
    refine sepWP_seq_keep_lscl hcl2 (v1Tag8_pre_drop_2508_cl_placed hfsp_align hpc2 hrun2 (hsp2.trans hspm) hx20_2 (hx29_2.trans hfp_m)) ?_
    rintro s3 P3 hpc3 hrun3 hcl3 ⟨hP3, hsp3, htr3, hx0_3, hx19_3, hx20_3, hx21_3, _hx22_3, _hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3⟩
    apply SepWP.weaken_pre hP3; dsimp only [Frame_ok]
    refine SepWP.weaken_pre (P' :=
      optProtoInnerStateAt A x.msgPtr m.innerState ∗ A.pool ∗ optProtoInnerStateJumpTablePlacedAt ∗ stackAt fsp dropStack96 ∗
        v1Tag8_words28At (fsp + 480#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
        (memRegion (fsp + 16#64) 224 ∗ memRegion (fsp + 240#64) 224 ∗ ((fsp + 464#64) ↦₆₄ x.msgPtr) ∗
          v1Tag8_capHeap A rest'.length cs' w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 ∗
          v1StateBelowRest fsp dropStack96 ∗
          memRegion fsp 16 ∗ memRegion (fsp + 472#64) 8 ∗ memRegion (fsp + 704#64) 16 ∗
          v1StateMergeJumpTablePlacedExpanded ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest' ∗ v1StateSavedRegsAt s0.sp s0))
      (Entails.of_eq (by ac_rfl)) ?_
    refine SepWP.seq (v1Tag8_post_drop_2568_cl_placed hDropInner hcl3 hfsp_align hpc3 hrun3
      (hsp3.trans (hsp2.trans hspm)) hx0_3 hx20_3 hx29_3) ?_
    rintro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, htr4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4⟩
    apply SepWP.weaken_pre hP4
    apply SepWP.fold (v1StateBelow_dropStack96_entails fsp) (by sep_focus)
    apply SepWP.fold (v1Tag8_memRegion_fold_temp fsp x.msgPtr) (by sep_focus)
    apply SepWP.fold (v1Tag8_reconstruct_innerState A x.msgPtr rest'.length cs'
      w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27) (by sep_focus)
    refine SepWP.done hpc4 hrun4 (fun hinv4 => ?_)
    apply SepWPp.weaken_pre (P' :=
      v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr { m with innerState := some (.ct1Sampled cs') } x.bs rest')
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, fsp]; ac_rfl))
    exact hcont.onOk { m with innerState := some (.ct1Sampled cs') } rest' s4 hm_field hpoly' hrest'_le
      hpc4 hrun4 (hsp4.trans (hsp3.trans (hsp2.trans hspm)))
      (htr4.trans (htr3.trans (htr2.trans (htrm.trans (htr1.trans htr)))))
      (hx21_4.trans (hx21_3.trans hx21_2))
      ⟨hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_m)), hx20_4, hx22_4, hx23_4,
       hx24_4.trans (hx24_3.trans (hx24_2.trans hx24_m)), hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_m)),
       hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_m)), hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_m)),
       hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_m)), hx29_4.trans hfsp720⟩ hinv4

private theorem v1Tag8_branch_1272_cl_placed [LibsignalPlacement] {H : String → Option (State → State)}
    {s0 s : State} {x : V1StateMergeGhost} {m : V1State} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {P : SepProp} {post panic : State → SepProp → Prop}
    (hm_not : ∀ cs, m.innerState ≠ some (.ct1Sampled cs))
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 516#64)
    (hcont : ∀ s' : State, V1StateTagEntryHypPlaced H s0 x m rest iwt limit s' →
      s'.pc = (blkPl_298).base + 1272#64 →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s' P post panic) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s P post panic := by
  obtain ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
    hrun, hsp, htr, hx0, hx9, hregs, hinv⟩ := hentry
  obtain ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩ := hregs
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 1272#64) hinv ?_
  cases hm_is : m.innerState with
  | none =>
    have hx9_n : InnerStateDiscrFull rest.length none (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = true := (discrFull_none_add2 hx9_n).1
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])
  | some is =>
    have hne : ∀ cs, is ≠ .ct1Sampled cs := fun cs h => hm_not cs (by rw [hm_is, h])
    have hx9_s : InnerStateDiscrFull rest.length (some is) (s.readReg64 (Reg.gpr 9#5)) := hm_is ▸ hx9
    have hbr1 : (s.readReg64 (Reg.gpr 9#5) + 2#64 == 0#64) = false := (discrFull_some_add2 hx9_s).1
    have hbr2 : BitVec.sle (s.readReg64 (Reg.gpr 9#5)) 0x800000000000000a#64 = true := v1Tag8_discrFull_other hne hx9_s
    wp_steps; wp_reach; intro hinv'
    exact hcont _
      ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hpoly,
        by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp],
        by simp only [arm64_norm, htr], by simp only [arm64_norm]; exact hx0,
        by simp only [arm64_norm]; exact hx9,
        ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
         by simp only [arm64_norm, hx22], by simp only [arm64_norm, hx23],
         by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
         by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hx29]⟩, hinv'⟩
      (by simp only [arm64_norm])

theorem v1State_tag8_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hCsCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 300) (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A)))
    (hDropUc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 286) (withLsCl lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)))
    (hDropEnc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 271) (withLsCl lsmpl (dropProtoPolyEncoderSpec A)))
    (hDealloc : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropInner : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 267) (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec A)))
    {s0 s : State} {x : V1StateMergeGhost} {R : SepProp} {m : V1State}
    {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hentry : V1StateTagEntryHypPlaced H s0 x m rest iwt limit s)
    (hpc : s.pc = (blkPl_298).base + 516#64)
    (hcont : V1StateTagContClPlaced A H s0 x R 8 m rest iwt limit) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (v1StateMergePlacedSpec A) x R s0) (WppPanic R s0) := by
  by_cases hex : ∃ cs, m.innerState = some (.ct1Sampled cs)
  · rcases hex with ⟨cs, hm_is⟩
    exact v1Tag8_inplace_cl_placed hCsCall hm_is hentry hpc hcont
  · have hm_not : ∀ cs, m.innerState ≠ some (.ct1Sampled cs) := fun cs h => hex ⟨cs, h⟩
    refine v1Tag8_branch_1272_cl_placed hm_not hentry hpc fun s' hentry' hpc' => ?_
    exact v1Tag8_at_1272_cl_placed hCsCall hDropUc hDropEnc hDealloc hDropInner hm_not hentry' hpc' hcont

end CryptoVerification.SpqrV1.Prost.MessageMerge
