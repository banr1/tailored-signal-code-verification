/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF9PAuxWPlaced
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MF14AuxW
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.MergeField9PW
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable `[LibsignalPlacement]` `merge_field` on Tag 9P (Block `15`)

Verifies `mergeField9PW_spk_none_placed_ok`, `mergeField9PW_spk_some_placed_ok`,
`mergeField9PPendingW_placed_ok`, and `mergeField9PW_placed_ok` on `lsProg_15 H` (Block `15`) at
`mergeFieldStackX = 32768` with slice length `< 2 ^ 62`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (OkAt allocPanic)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] pendingB0_signExtend_1_x9p pendingB0_getLsbD_63_1_x9p
  pendingB0_signExtend_2_x9p pendingB0_getLsbD_63_2_x9p

theorem L1_MergeField9PWPlaced : True := trivial

/-! ## `GenFieldX.pendingSpk none` leaf (`mergeField9PW_spk_none_placed_ok`) -/

private theorem final_post_entails_spk_none_placed_x9pW (ss cap' ptr' v24 : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 288#64) ↦₃₂ spk ∗
      bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (ptr + 37#64) ↦ₛ encodeVarint (spk.signExtend 64) ∗
      (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
        (ptr + 2#64) ↦ₛ (33#8 :: k) ∗
        (ptr + 36#64) ↦₈ 24#8 ∗
        ((ss + 272#64) ↦₆₄ (v24 &&& (bv% (2 ^ 64 - 2 ^ 32)) ||| 0#64) ∗
          (ss + 280#64) ↦₆₄ 0#64 ∗
          memRegion (ss + 292#64) 4 ∗
          ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ∗
          (ptr + 1#64) ↦₈ 18#8 ∗
          (sp0 - 80#64) ↦₆₄ r29 ∗
          (sp0 - 72#64) ↦₆₄ r30 ∗
          (sp0 - 64#64) ↦₆₄ r25 ∗
          (sp0 - 56#64) ↦₆₄ w118 ∗
          (sp0 - 48#64) ↦₆₄ r24 ∗
          (sp0 - 40#64) ↦₆₄ r23 ∗
          (sp0 - 32#64) ↦₆₄ r22 ∗
          (sp0 - 24#64) ↦₆₄ r21 ∗
          (sp0 - 16#64) ↦₆₄ r20 ∗
          (sp0 - 8#64) ↦₆₄ r19 ∗
          memRegion (sp0 - 240#64) 160))) ⊢
    pendingAt9P A0 ss (v.apply (.pendingSpk none k spk)) ∗
      bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk none k spk).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_fold_spk_none_x9p slot ptr hk hspk tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 272#64) ↦₆₄ (v24 &&& (bv% (2 ^ 64 - 2 ^ 32)) ||| 0#64)) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 18#8) ∗
      ((ptr + 2#64) ↦ₛ (33#8 :: k)) ∗
      ((ptr + 36#64) ↦₈ 24#8) ∗
      ((ptr + 37#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((ptr + 37#64 + BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail)) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗
      (sp0 - 72#64) ↦₆₄ r30 ∗
      (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗
      (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗
      (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗
      memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX))
    (by apply Entails.of_eq; ac_rfl) ?_
  exact sepConj_mono (pendingAt9P_post_fold_spk_none A0 ss cap' ptr' v24 v k spk)
    (bufRef_and_stackAt_mergeFieldX_fold_x9pW bufRef slot sp0
      r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 _)

set_option maxHeartbeats 800000 in
theorem mergeField9PW_spk_none_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeField9PPendingPlacedOkW H (fun fl => ∃ k spk, fl = .pendingSpk none k spk) := by
  unfold MergeField9PPendingPlacedOkW
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  refine ⟨_, R, hpre_raw, ?_⟩
  clear hpre hpre_raw
  dsimp only [mergeField9PPendingRawSpecW]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, hfld, hOk, hFresh, hlen⟩ => ?_
  obtain ⟨k, spk, rfl⟩ := hfld
  obtain ⟨hk, hspk⟩ : k.length = 33 ∧ spk ≠ 0#32 := hOk
  obtain ⟨hp, _hpid, _hspk0⟩ := hFresh
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hm := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  rw [List.length_append, pendingSpk_none_payload_length_x9p hk hspk] at hlen
  rw [State.spAligned] at hsp_align
  obtain ⟨hcallI, hcallB⟩ := callee_subs_placed_x9pW hC
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64
      (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hl_ne0 := len_ne_zero_x9pW (a := 37 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 37 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 36 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW
    (L := 36 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 35 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega) (by omega)
  obtain ⟨hl3_s1, hl3_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (a' := (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length) (n := tail.length) (by omega) (by omega)
  conv =>
    arg 4
    rw [pendingAt9P_fresh_unfold A0 ss v hp,
        sliceCursorAt_unfold_spk_none_x9p slot ptr hk hspk tail,
        stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => SepWPp.exists_elim fun v80 =>
    SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
    SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
    SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
    SepWPp.exists_elim fun v8 => ?_
  have hlsb := pid_disc_lsb_x9p v24
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0
  apply sepWP_intro_rodata_tag9_placed_x9pW hcrl0
  wp_steps
  apply sepWP_drop_left_x9pW
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcrl2
  have hlen_b1 : 35 + (encodeVarint (spk.signExtend 64)).length + tail.length =
      34 + (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)).length := by
    simp only [List.length_cons, List.length_append]; omega
  refine call_frame_lscro_x9p
    (x := ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      ptr + 2#64, 33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
      ((ss + 272#64) ↦₆₄ (v24 &&& bv% (2 ^ 64 - 2 ^ 32) ||| 0#64) ∗
        (ss + 280#64) ↦₆₄ 0#64 ∗
        (ss + 288#64) ↦₃₂ 0#32 ∗
        memRegion (ss + 292#64) 4 ∗
        ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ∗
        (ptr + 1#64) ↦₈ 18#8 ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 56#64) ↦₆₄ w118 ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
        memRegion (s0.sp - 240#64) 160))
    hcallB hcrl2
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm]; rfl)
    (by simp only [List.length_cons, List.length_append, hk]; omega)
    (by
      rw [hlen_b1]
      rw [← List.cons_append (a := 33#8)]
      rw [← pre_to_bytesMerge_gen_x9pW ss bufRef slot (ptr + 2#64) s0.sp hk
          (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [Prost.X.bytesMergeRawSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm]) hm) ?_
  intro sf hpcf hrunf hspf hcsf hcrl3
  simp only [wp_norm, arm64_norm] at hpcf
  have hsp_sf : sf.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm] using hspf
  rw [post_of_bytesMerge_gen_x9pW ss bufRef slot (ptr + 2#64) s0.sp hk
      (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)) _ _ sf
      (by simp only [wp_norm, arm64_norm])]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun htr_b => SepWPp.pure_elim fun hx0_b => ?_
  have hlen_b2 : (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)).length =
      1 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    simp only [List.length_cons, List.length_append]; omega
  conv =>
    arg 4
    rw [hlen_b2, show ptr + 2#64 + 34#64 = ptr + 36#64 by bv_lin]
    rw [pointsToBytes_cons (a := ptr + 36#64), show ptr + 36#64 + 1#64 = ptr + 37#64 by bv_lin]
    simp only [sepConj_assoc]
  have hx19_b : sf.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.1
  have hx20_b : sf.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.1
  have hx21_b : sf.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
  have hx22_b : sf.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
  have hx23_b : sf.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.1
  have hx24_b : sf.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.1
  have hx25_b : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.1
  have hx26_b : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
  have hx27_b : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
  have hx28_b : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
  have hvregs_b : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 8) hcrl3
  iterate 33 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
  intro hcrl4
  refine call_frame_lscro_x9p
    (x := ⟨.varint, ss + 288#64, bufRef, slot, ptr + 37#64,
      encodeVarint (spk.signExtend 64) ++ tail⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
      (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
        (ptr + 2#64) ↦ₛ (33#8 :: k) ∗
        (ptr + 36#64) ↦₈ 24#8 ∗
        ((ss + 272#64) ↦₆₄ (v24 &&& bv% (2 ^ 64 - 2 ^ 32) ||| 0#64) ∗
          (ss + 280#64) ↦₆₄ 0#64 ∗
          memRegion (ss + 292#64) 4 ∗
          ptr ↦₈ BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ∗
          (ptr + 1#64) ↦₈ 18#8 ∗
          (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
          (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
          (s0.sp - 56#64) ↦₆₄ w118 ∗
          (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
          (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
          (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
          (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
          memRegion (s0.sp - 240#64) 160)))
    hcallI hcrl4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunf])
    (by rw [State.spAligned]; simp only [wp_norm, arm64_norm, hsp_sf]
        simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
    (by rw [List.length_append]; omega)
    (by
      refine Entails.trans ?_
        (pre_to_int32_gen_x9pW (ss + 288#64) bufRef slot (ptr + 37#64) s0.sp
          (spk.signExtend 64) tail _)
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.X.int32MergeSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_b]) hm) ?_
  intro sf2 hpcf2 hrunf2 hspf2 hcsf2 _
  simp only [wp_norm, arm64_norm] at hpcf2
  rw [post_of_int32_gen_x9pW (ss + 288#64) bufRef slot (ptr + 37#64) s0.sp
      (spk.signExtend 64) spk (setWidth32_signExtend64_x9p spk) tail _
      _ sf2 (by simp only [wp_norm, arm64_norm, hsp_sf])]
  refine SepWPp.pure_elim fun htr_sf => SepWPp.pure_elim fun hx0_sf => ?_
  have htr_sf' : sf2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htr_b] using htr_sf
  have hx0_sf' : sf2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf
  have hx21_sf : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21_b] using hcsf2.2.2.1
  have hx24_sf : sf2.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24_b] using hcsf2.2.2.2.2.2.1
  have hx26_sf : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26_b] using hcsf2.2.2.2.2.2.2.2.1
  have hx27_sf : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27_b] using hcsf2.2.2.2.2.2.2.2.2.1
  have hx28_sf : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28_b] using hcsf2.2.2.2.2.2.2.2.2.2.1
  have hvregs_sf : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sf := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregs_b
  have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
  have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      false := by
    simp [BitVec.ult]
  have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      true := by
    simp [BitVec.ule]
  apply SepWPp.of_sepWP_ret
  iterate 19 wp_step
  apply SepWP.fold (final_post_entails_spk_none_placed_x9pW ss cap' ptr' v24 v bufRef slot ptr hk hspk tail
      s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) w118
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
    (sepConj_emp _).symm
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf2])
  refine ⟨fun hmf => close_x9p (by simp only [wp_norm, arm64_norm, htr_sf'])
      (by simp only [wp_norm, arm64_norm]) hmf,
    by simp only [wp_norm, arm64_norm],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm, hx26_sf, hx27_sf,
      hx28_sf]; exact hvregs_sf⟩

/-! ## `GenFieldX.pendingSpk (some i)` leaf (`mergeField9PW_spk_some_placed_ok`) -/

private theorem final_post_entails_spk_some_placed_x9pW (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    ((ss + 288#64) ↦₃₂ spk ∗
      bufRef ↦₆₄ slot ∗
      slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ∗
      (slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length ∗
      (pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64) ∗
      (pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
        (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
        (pendingPtr2 ptr i + 35#64) ↦₈ 24#8 ∗
        ((ss + 276#64) ↦₃₂ i ∗
          (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
          pendingPtr2 ptr i ↦₈ 18#8 ∗
          ((ss + 272#64) ↦₃₂ 1#32 ∗
            (ss + 280#64) ↦₆₄ 0#64 ∗
            memRegion (ss + 292#64) 4 ∗
            ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
              (encodeVarint (spk.signExtend 64)).length) ∗
            (ptr + 1#64) ↦₈ 8#8 ∗
            (sp0 - 80#64) ↦₆₄ r29 ∗
            (sp0 - 72#64) ↦₆₄ r30 ∗
            (sp0 - 64#64) ↦₆₄ r25 ∗
            (sp0 - 56#64) ↦₆₄ w118 ∗
            (sp0 - 48#64) ↦₆₄ r24 ∗
            (sp0 - 40#64) ↦₆₄ r23 ∗
            (sp0 - 32#64) ↦₆₄ r22 ∗
            (sp0 - 24#64) ↦₆₄ r21 ∗
            (sp0 - 16#64) ↦₆₄ r20 ∗
            (sp0 - 8#64) ↦₆₄ r19 ∗
            memRegion (sp0 - 240#64) 160)))) ⊢
    pendingAt9P A0 ss (v.apply (.pendingSpk (some i) k spk)) ∗
      bufRef ↦₆₄ slot ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.pendingSpk (some i) k spk).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_fold_spk_some_x9p slot ptr i hk hspk tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (pendingPtr2 ptr i + 36#64 +
      BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length)) ∗
      ((ptr + 1#64) ↦₈ 8#8) ∗
      ((ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (pendingPtr2 ptr i ↦₈ 18#8) ∗
      ((pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k)) ∗
      ((pendingPtr2 ptr i + 35#64) ↦₈ 24#8) ∗
      ((pendingPtr2 ptr i + 36#64) ↦ₛ encodeVarint (spk.signExtend 64)) ∗
      ((pendingPtr2 ptr i + 36#64 +
        BitVec.ofNat 64 (encodeVarint (spk.signExtend 64)).length) ↦ₛ tail)) ∗
    ((sp0 - 80#64) ↦₆₄ r29 ∗
      (sp0 - 72#64) ↦₆₄ r30 ∗
      (sp0 - 64#64) ↦₆₄ r25 ∗
      (sp0 - 56#64) ↦₆₄ w118 ∗
      (sp0 - 48#64) ↦₆₄ r24 ∗
      (sp0 - 40#64) ↦₆₄ r23 ∗
      (sp0 - 32#64) ↦₆₄ r22 ∗
      (sp0 - 24#64) ↦₆₄ r21 ∗
      (sp0 - 16#64) ↦₆₄ r20 ∗
      (sp0 - 8#64) ↦₆₄ r19 ∗
      memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX))
    (by apply Entails.of_eq; ac_rfl) ?_
  exact sepConj_mono (pendingAt9P_post_fold_spk_some A0 ss cap' ptr' v i k spk)
    (bufRef_and_stackAt_mergeFieldX_fold_x9pW bufRef slot sp0
      r29 r30 r25 w118 r24 r23 r22 r21 r20 r19 _)

set_option maxHeartbeats 800000 in
theorem mergeField9PW_spk_some_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeField9PPendingPlacedOkW H (fun fl => ∃ i k spk, fl = .pendingSpk (some i) k spk) := by
  unfold MergeField9PPendingPlacedOkW
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  refine ⟨_, R, hpre_raw, ?_⟩
  clear hpre hpre_raw
  dsimp only [mergeField9PPendingRawSpecW]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, hfld, hOk, hFresh, hlen⟩ => ?_
  obtain ⟨i, k, spk, rfl⟩ := hfld
  obtain ⟨hk, hspk⟩ : k.length = 33 ∧ spk ≠ 0#32 := hOk
  obtain ⟨hp, _hpid, _hspk0⟩ := hFresh
  dsimp only [GenFieldX.tag, GenFieldX.wt, WireType.toNat] at hx1 hx2
  have hx1_tr : BitVec.truncate 32 (s0.readReg64 .x1) = 9#32 := hx1
  have hx4_tr : BitVec.truncate 32 (s0.readReg64 .x4) = 99#32 := hx4
  have hm1 := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hm2 := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  rw [List.length_append, pendingSpk_some_payload_length_x9p i hk hspk] at hlen
  rw [State.spAligned] at hsp_align
  obtain ⟨hcallI, hcallB⟩ := callee_subs_placed_x9pW hC
  have hx2_tr : (s0.readReg64 (Reg.gpr 2#5)).truncate 32 &&& 255#32 = 2#32 :=
    wt_and_ff_eq_mf14W (s0.readReg64 .x2) hx2
  have hx2_64 : BitVec.truncate 32 (BitVec.zeroExtend 64
      (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 2#5))) &&& 255#64) = 2#32 :=
    wt_and_ff_64_eq_mf14W (s0.readReg64 .x2) hx2
  have hl_ne0 := len_ne_zero_x9pW
    (a := 38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hl_s1, hl_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (a' := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) hlen
  obtain ⟨hsubL, hultL, huleL⟩ := subs_body_len_x9pW
    (L := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega)
  obtain ⟨hl2_s1, hl2_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (a' := 36 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult1, hule1, hult1', hsub1⟩ := cmp_gt_tail_x9pW
    (a := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hl3_s1, hl3_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (a' := 35 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult2, hule2, hult2', hsub2⟩ := cmp_gt_tail_x9pW
    (a := 36 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hl4_s1, hl4_a1⟩ := sub1_and_add_neg1_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (a' := (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  obtain ⟨hult3, hule3, hult3', hsub3⟩ := cmp_gt_tail_x9pW
    (a := 1 + (encodeVarint (spk.signExtend 64)).length)
    (n := tail.length) (by omega) (by omega)
  conv =>
    arg 4
    rw [pendingAt9P_fresh_unfold A0 ss v hp,
        sliceCursorAt_unfold_spk_some_x9p slot ptr i hk hspk tail,
        stackAt_mergeFieldX_unfold_x9pW s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w100 => SepWPp.exists_elim fun w108 =>
    SepWPp.exists_elim fun w110 => SepWPp.exists_elim fun w118 =>
    SepWPp.exists_elim fun w120 => SepWPp.exists_elim fun v80 =>
    SepWPp.exists_elim fun v72 => SepWPp.exists_elim fun v64 =>
    SepWPp.exists_elim fun v56 => SepWPp.exists_elim fun v48 =>
    SepWPp.exists_elim fun v40 => SepWPp.exists_elim fun v32 =>
    SepWPp.exists_elim fun v24 => SepWPp.exists_elim fun v16 =>
    SepWPp.exists_elim fun v8 => ?_
  have hlsb := pid_disc_lsb_x9p v24
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 8) hcrl0
  apply sepWP_intro_rodata_tag9_placed_x9pW hcrl0
  wp_steps
  apply sepWP_drop_left_x9pW
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrun])
  intro hcrl2
  have hlen_i1 : 36 + (encodeVarint (i.setWidth 64)).length +
      (encodeVarint (spk.signExtend 64)).length + tail.length =
      (encodeVarint (i.setWidth 64)).length +
        (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))).length := by
    simp only [List.length_cons, List.length_append, hk]; omega
  refine call_frame_lscro_x9p
    (x := ⟨.varint, ss + 276#64, bufRef, slot, ptr + 2#64,
      encodeVarint (i.setWidth 64) ++
        (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))))⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
      ((ss + 0xf8#64) ↦₆₄ 0#64 ∗ (ss + 0x100#64) ↦₆₄ 1#64 ∗ (ss + 0x108#64) ↦₆₄ 0#64) ∗
      (ss + 272#64) ↦₃₂ 1#32 ∗
      (ss + 280#64) ↦₆₄ 0#64 ∗
      (ss + 288#64) ↦₃₂ 0#32 ∗
      memRegion (ss + 292#64) 4 ∗
      ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
        (encodeVarint (spk.signExtend 64)).length) ∗
      (ptr + 1#64) ↦₈ 8#8 ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 56#64) ↦₆₄ w118 ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
      memRegion (s0.sp - 240#64) 160)
    hcallI hcrl2
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun])
    (by rw [State.spAligned]; simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm]; rfl)
    (by simp only [List.length_append, List.length_cons, hk]; omega)
    (by
      refine Entails.trans ?_
        (pre_to_int32_gen_x9pW (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
          (i.setWidth 64)
          (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))) _)
      rw [split_272_x9p ss, hlen_i1]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf _ hm => by
      dsimp only [Prost.X.int32MergeSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm]) hm) ?_
  intro sf hpcf hrunf hspf hcsf hcrl3
  simp only [wp_norm, arm64_norm] at hpcf
  have hsp_sf : sf.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm] using hspf
  rw [post_of_int32_gen_x9pW (ss + 276#64) bufRef slot (ptr + 2#64) s0.sp
      (i.setWidth 64) i (setWidth32_setWidth64_x9p i)
      (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))) _
      _ sf (by simp only [wp_norm, arm64_norm])]
  refine SepWPp.pure_elim fun htr_i => SepWPp.pure_elim fun hx0_i => ?_
  have hlen_i2 :
      (18#8 :: (33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)))).length =
      36 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    simp only [List.cons_append, List.length_cons, List.length_append, hk]; omega
  conv =>
    arg 4
    rw [hlen_i2, show ptr + 2#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length =
      pendingPtr2 ptr i from rfl,
      pointsToBytes_cons (a := pendingPtr2 ptr i)]
    simp only [sepConj_assoc]
  have hx19_i : sf.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.1
  have hx20_i : sf.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.1
  have hx21_i : sf.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.1
  have hx22_i : sf.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.1
  have hx23_i : sf.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.1
  have hx24_i : sf.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.1
  have hx25_i : sf.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.1
  have hx26_i : sf.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.1
  have hx27_i : sf.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.1
  have hx28_i : sf.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.1
  have hvregs_i : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf.2.2.2.2.2.2.2.2.2.2.2
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl3
  iterate 35 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf])
  intro hcrl4
  have hlen_b1 : 35 + (encodeVarint (spk.signExtend 64)).length + tail.length =
      34 + (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)).length := by
    simp only [List.length_cons, List.length_append]; omega
  refine call_frame_lscro_x9p
    (x := ⟨.lengthDelimited, ss + 248#64, 0#64, 1#64, [], bufRef, slot,
      pendingPtr2 ptr i + 1#64, 33#8 :: k ++ (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7648 ∗
      (ss + 276#64) ↦₃₂ i ∗
      (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
      pendingPtr2 ptr i ↦₈ 18#8 ∗
      ((ss + 272#64) ↦₃₂ 1#32 ∗
        (ss + 280#64) ↦₆₄ 0#64 ∗
        (ss + 288#64) ↦₃₂ 0#32 ∗
        memRegion (ss + 292#64) 4 ∗
        ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
          (encodeVarint (spk.signExtend 64)).length) ∗
        (ptr + 1#64) ↦₈ 8#8 ∗
        (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
        (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
        (s0.sp - 56#64) ↦₆₄ w118 ∗
        (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
        (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
        (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
        (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
        (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
        memRegion (s0.sp - 240#64) 160))
    hcallB hcrl4
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunf])
    (by rw [State.spAligned]; simp only [wp_norm, arm64_norm, hsp_sf]
        simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.bytesMergeRawSpecW, wp_norm, arm64_norm, hsp_sf]; rfl)
    (by simp only [List.length_cons, List.length_append, hk]; omega)
    (by
      rw [hlen_b1, ← List.cons_append (a := 33#8)]
      rw [← pre_to_bytesMerge_gen_x9pW ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk
          (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail))]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.X.bytesMergeRawSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_i]) hm) ?_
  intro sf2 hpcf2 hrunf2 hspf2 hcsf2 hcrl5
  simp only [wp_norm, arm64_norm] at hpcf2
  have hsp_sf2 : sf2.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hsp_sf] using hspf2
  rw [post_of_bytesMerge_gen_x9pW ss bufRef slot (pendingPtr2 ptr i + 1#64) s0.sp hk
      (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)) _
      _ sf2 (by simp only [wp_norm, arm64_norm, hsp_sf])]
  refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
    SepWPp.pure_elim fun htr_b => SepWPp.pure_elim fun hx0_b => ?_
  have htr_b' : sf2.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htr_i] using htr_b
  have hlen_b2 : (24#8 :: (encodeVarint (spk.signExtend 64) ++ tail)).length =
      1 + (encodeVarint (spk.signExtend 64)).length + tail.length := by
    simp only [List.length_cons, List.length_append]; omega
  conv =>
    arg 4
    rw [hlen_b2, show pendingPtr2 ptr i + 1#64 + 34#64 = pendingPtr2 ptr i + 35#64 by bv_lin,
      pointsToBytes_cons (a := pendingPtr2 ptr i + 35#64),
      show pendingPtr2 ptr i + 35#64 + 1#64 = pendingPtr2 ptr i + 36#64 by bv_lin]
    simp only [sepConj_assoc]
  have hx19_b : sf2.readReg64 (Reg.gpr 19#5) = ss + 248#64 := by
    simpa only [wp_norm, arm64_norm, hx19_i] using hcsf2.1
  have hx20_b : sf2.readReg64 (Reg.gpr 20#5) = 98#64 := by
    simpa only [wp_norm, arm64_norm, hx20_i] using hcsf2.2.1
  have hx21_b : sf2.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21_i] using hcsf2.2.2.1
  have hx22_b : sf2.readReg64 (Reg.gpr 22#5) = 1#64 := by
    simpa only [wp_norm, arm64_norm, hx22_i] using hcsf2.2.2.2.1
  have hx23_b : sf2.readReg64 (Reg.gpr 23#5) = ss := by
    simpa only [wp_norm, arm64_norm, hx23_i] using hcsf2.2.2.2.2.1
  have hx24_b : sf2.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24_i] using hcsf2.2.2.2.2.2.1
  have hx25_b : sf2.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) := by
    simpa only [wp_norm, arm64_norm, hx25_i] using hcsf2.2.2.2.2.2.2.1
  have hx26_b : sf2.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26_i] using hcsf2.2.2.2.2.2.2.2.1
  have hx27_b : sf2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27_i] using hcsf2.2.2.2.2.2.2.2.2.1
  have hx28_b : sf2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28_i] using hcsf2.2.2.2.2.2.2.2.2.2.1
  have hvregs_b : calleeSavedVRegs sf2 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sf2 = calleeSavedVRegs sf := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf2.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregs_i
  apply LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 8) hcrl5
  iterate 33 wp_step
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf2])
  intro hcrl6
  refine call_frame_lscro_x9p
    (x := ⟨.varint, ss + 288#64, bufRef, slot, pendingPtr2 ptr i + 36#64,
      encodeVarint (spk.signExtend 64) ++ tail⟩)
    (F := memRegion (s0.sp - 240#64 - 32528#64) 7792 ∗
      (vecU8At A0 (ss + 248#64) cap' ptr' k ∗
        (pendingPtr2 ptr i + 1#64) ↦ₛ (33#8 :: k) ∗
        (pendingPtr2 ptr i + 35#64) ↦₈ 24#8 ∗
        ((ss + 276#64) ↦₃₂ i ∗
          (ptr + 2#64) ↦ₛ encodeVarint (i.setWidth 64) ∗
          pendingPtr2 ptr i ↦₈ 18#8 ∗
          ((ss + 272#64) ↦₃₂ 1#32 ∗
            (ss + 280#64) ↦₆₄ 0#64 ∗
            memRegion (ss + 292#64) 4 ∗
            ptr ↦₈ BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
              (encodeVarint (spk.signExtend 64)).length) ∗
            (ptr + 1#64) ↦₈ 8#8 ∗
            (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
            (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
            (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
            (s0.sp - 56#64) ↦₆₄ w118 ∗
            (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
            (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
            (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
            (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
            (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
            (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5) ∗
            memRegion (s0.sp - 240#64) 160))))
    hcallI hcrl6
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrunf2])
    (by rw [State.spAligned]; simp only [wp_norm, arm64_norm, hsp_sf2]
        simpa only [wp_norm, arm64_norm] using hsp_align)
    rfl
    (by simp only [Prost.X.int32MergeSpecW, wp_norm, arm64_norm, hsp_sf2]; rfl)
    (by rw [List.length_append]; omega)
    (by
      refine Entails.trans ?_
        (pre_to_int32_gen_x9pW (ss + 288#64) bufRef slot (pendingPtr2 ptr i + 36#64) s0.sp
          (spk.signExtend 64) tail _)
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sf' _ hm => by
      dsimp only [Prost.X.int32MergeSpecW, allocPanic] at hm ⊢
      exact allowPanic_frame_trace_x9p (by simp only [wp_norm, arm64_norm, htr_b']) hm) ?_
  intro sf3 hpcf3 hrunf3 hspf3 hcsf3 _
  simp only [wp_norm, arm64_norm] at hpcf3
  rw [post_of_int32_gen_x9pW (ss + 288#64) bufRef slot (pendingPtr2 ptr i + 36#64) s0.sp
      (spk.signExtend 64) spk (setWidth32_signExtend64_x9p spk) tail _
      _ sf3 (by simp only [wp_norm, arm64_norm, hsp_sf2])]
  refine SepWPp.pure_elim fun htr_sf => SepWPp.pure_elim fun hx0_sf => ?_
  have htr_sf' : sf3.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, htr_b'] using htr_sf
  have hx0_sf' : sf3.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_sf
  have hx21_sf : sf3.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 tail.length := by
    simpa only [wp_norm, arm64_norm, hx21_b] using hcsf3.2.2.1
  have hx24_sf : sf3.readReg64 (Reg.gpr 24#5) = bufRef := by
    simpa only [wp_norm, arm64_norm, hx24_b] using hcsf3.2.2.2.2.2.1
  have hx26_sf : sf3.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) := by
    simpa only [wp_norm, arm64_norm, hx26_b] using hcsf3.2.2.2.2.2.2.2.1
  have hx27_sf : sf3.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
    simpa only [wp_norm, arm64_norm, hx27_b] using hcsf3.2.2.2.2.2.2.2.2.1
  have hx28_sf : sf3.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
    simpa only [wp_norm, arm64_norm, hx28_b] using hcsf3.2.2.2.2.2.2.2.2.2.1
  have hvregs_sf : calleeSavedVRegs sf3 = calleeSavedVRegs s0 := by
    have h1 : calleeSavedVRegs sf3 = calleeSavedVRegs sf2 := by
      simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hcsf3.2.2.2.2.2.2.2.2.2.2.2
    exact h1.trans hvregs_b
  have hsp_sf3 : sf3.sp = s0.sp - 240#64 := by
    simpa only [wp_norm, arm64_norm, hsp_sf2] using hspf3
  have htail_ult_self : BitVec.ult (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      false := by
    simp [BitVec.ult]
  have htail_ule_self : BitVec.ule (BitVec.ofNat 64 tail.length) (BitVec.ofNat 64 tail.length) =
      true := by
    simp [BitVec.ule]
  apply SepWPp.of_sepWP_ret
  iterate 19 wp_step
  apply SepWP.fold (final_post_entails_spk_some_placed_x9pW ss cap' ptr' v bufRef slot ptr i hk hspk tail
      s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
      (s0.readReg64 (Reg.gpr 25#5)) w118
      (s0.readReg64 (Reg.gpr 24#5)) (s0.readReg64 (Reg.gpr 23#5))
      (s0.readReg64 (Reg.gpr 22#5)) (s0.readReg64 (Reg.gpr 21#5))
      (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5)))
    (sepConj_emp _).symm
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hrunf3])
  refine ⟨fun hmf => close_x9p (by simp only [wp_norm, arm64_norm, htr_sf'])
      (by simp only [wp_norm, arm64_norm]) hmf,
    by simp only [wp_norm, arm64_norm],
    by simp only [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm, hx26_sf, hx27_sf,
      hx28_sf]; exact hvregs_sf⟩

/-! ## Combined tag-9P leaf contracts -/

theorem mergeField9PPendingW_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeField9PPendingPlacedOkW H
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) := by
  have h1 := mergeField9PW_id_placed_ok H hC
  have h2 := mergeField9PW_spk_none_placed_ok H hC
  have h3 := mergeField9PW_spk_some_placed_ok H hC
  refine mergeField9PPendingPlacedOkW_of_imp
    (mergeField9PPendingPlacedOkW_or h1 (mergeField9PPendingPlacedOkW_or h2 h3)) ?_
  intro fl hfl
  rcases hfl with ⟨i, k, rfl⟩ | ⟨o, k, spk, rfl⟩
  · exact Or.inl ⟨i, k, rfl⟩
  · cases o with
    | none => exact Or.inr (Or.inl ⟨k, spk, rfl⟩)
    | some i => exact Or.inr (Or.inr ⟨i, k, spk, rfl⟩)

theorem mergeField9PW_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks)
    (hC : DeserializeCalleesPlacedW H) :
    MergeField9PPlacedOkW H
      (fun fl => (∃ i k, fl = .pendingId i k) ∨ (∃ o k spk, fl = .pendingSpk o k spk)) :=
  mergeField9PPlacedOkW_of_pending (fun _ h => h) (mergeField9PPendingW_placed_ok H hC)

end Symbolic.Swarm.TRREF.B3DeserQ
