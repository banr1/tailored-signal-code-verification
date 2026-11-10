/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart5
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 5 (Relocatable)

Relocatable `[LibsignalPlacement]` proofs for the `<Ct1Sent>::recv_ek` call (`+11508 -> +11528`),
Path 5a (`recv_ek = .error`), `.ok uc_ek` staging (`+11528 -> +11620`), and Path 5b (`ack = false`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout
open Obj.MultiPlacedLib

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272
  sp_sub_4240_add_2752 sp_sub_4240_add_3696 sp_sub_4240_add_3832
  sp_sub_4240_add_3840 sp_sub_4240_add_3848
  lsmpl_base_332_eq

/-! ## 1. Calling `<Unchunked.SendCt.Ct1Sent>::recv_ek` (`+11508 -> +11528`) -/

theorem ct1Sampled_call_recv_ek_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K)))
    (s_in : State) (fsp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11508#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx20 : s_in.readReg64 .x20 = uc.epoch) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11528#64) s_in
      (memRegion (fsp + 1856#64) 128 ∗
        unchunkedCt1SentAt A (fsp + 3696#64) uc ∗
        vecU8 A (fsp + 3832#64) decoded ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          unchunkedCt1SentRecvEkResAt A (fsp + 1856#64) res ∗
          memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3832#64) 24 ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = uc.epoch ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hcall := subroutine_ok_withMemEq_of_withLsCodeLoaded hrecv_ek hcl
  have hsplit := stackAt_statesRecvCallee_eq_unchunkedRecvEk' s_in.sp
  dsimp only [lsProg_332, withMemEq, unchunkedCt1SentRecvEkSpec, BitVec.ofNat_eq_ofNat]
    at hpc hcall hsplit ⊢
  rw [hsplit, ← hx20]
  wp_steps
  wp_call hcall ⟨s_in.sp + 1856#64, s_in.sp + 3696#64, s_in.sp + 3832#64, uc, decoded, res⟩
  wp_done

/-! ## 2. Path 5a (`recv_ek = .error (.err err)`): `+11528 -> +15716 -> +19324` -/

theorem ct1Sampled_recv_ek_err_to_19324_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s_in : State) (fsp stA outA : BitVec 64)
    (vecs : List (List GF16)) (hvecs_len : vecs.length = NUM_POLYS)
    (dec' : PolyDecoder) (err : Error)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (herr : err = .erroneousDataReceived)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11528#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 19324#64) s_in
      (unchunkedCt1SentRecvEkResAt A (F := F) (fsp + 1856#64) (.error err) ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        vecGF16ListOf A (stA + 8#64) vecs ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗
        memRegion outA v1RecvSize ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.error (.err err)) ∗
          memRegion (fsp + 1856#64) 128 ∗
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 8#64) 384 ∗
          memRegion (fsp + 2752#64) 400 ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx19 herr
  have hout_split :
      memRegion (s_in.readReg64 .x19) v1RecvSize ⊢
        ∃∗ v0 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v24 : BitVec 64,
          ((s_in.readReg64 .x19) ↦₆₄ v0) ∗
          ((s_in.readReg64 .x19 + 8#64) ↦₆₄ v8) ∗
          ((s_in.readReg64 .x19 + 16#64) ↦₆₄ v16) ∗
          ((s_in.readReg64 .x19 + 24#64) ↦₆₄ v24) ∗
          memRegion (s_in.readReg64 .x19 + 32#64) 928 := by
    unfold v1RecvSize
    rw [ProofLib.memRegion_split (s_in.readReg64 .x19) 32 928 (by decide)]
    refine Entails.trans (sepConj_mono_left (memRegion_32_entails_words4 (s_in.readReg64 .x19))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro v24
    apply Entails.sepExists_elim; intro v16
    apply Entails.sepExists_elim; intro v8
    apply Entails.sepExists_elim; intro v0
    exact Entails.sepExists_right v0 (Entails.sepExists_right v8
      (Entails.sepExists_right v16 (Entails.sepExists_right v24 (Entails.refl _))))
  have hdec_entails :
      polyDecoderAt A (s_in.sp + 2752#64) dec' ⊢
        ∃∗ vecs_dec : List (List Pt),
          ⌜vecs_dec.length = NUM_POLYS⌝ ∗
          vecPtListOf A (s_in.sp + 2752#64) vecs_dec ∗
          memRegion (s_in.sp + 3136#64) 16 := by
    have h3136 : (s_in.sp + 2752#64) + 384#64 = s_in.sp + 3136#64 := by bv_omega
    have h := polyDecoderAt_entails_vecs_tail A (s_in.sp + 2752#64) dec'
    rwa [h3136] at h
  have hpre :
      unchunkedCt1SentRecvEkResAt A (F := F) (s_in.sp + 1856#64) (.error .erroneousDataReceived) ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        vecGF16ListOf A (stA + 8#64) vecs ∗
        polyDecoderAt A (s_in.sp + 2752#64) dec' ∗
        memRegion (s_in.readReg64 .x19) v1RecvSize ∗
        A.pool ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ bs7 : List (BitVec 8),
      ∃∗ vecs_dec : List (List Pt),
      ∃∗ v0 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v24 : BitVec 64,
        ⌜bs7.length = 7 ∧ unpack64 w8 = 12#8 :: bs7⌝ ∗
        ⌜vecs_dec.length = NUM_POLYS⌝ ∗
        (((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
          ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
          ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
          ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
          memRegion (s_in.sp + 1888#64) 96 ∗
          ((s_in.sp + 232#64) ↦₆₄ stA) ∗
          vecGF16ListOf A (stA + 8#64) vecs ∗
          vecPtListOf A (s_in.sp + 2752#64) vecs_dec ∗
          memRegion (s_in.sp + 3136#64) 16 ∗
          ((s_in.readReg64 .x19) ↦₆₄ v0) ∗
          ((s_in.readReg64 .x19 + 8#64) ↦₆₄ v8) ∗
          ((s_in.readReg64 .x19 + 16#64) ↦₆₄ v16) ∗
          ((s_in.readReg64 .x19 + 24#64) ↦₆₄ v24) ∗
          memRegion (s_in.readReg64 .x19 + 32#64) 928 ∗
          A.pool ∗
          stackAt s_in.sp statesRecvCalleeStackX ∗
          Rest) := by
    refine Entails.trans (sepConj_mono (unchunkedCt1SentRecvEkResAt_error_entails A (s_in.sp + 1856#64) .erroneousDataReceived)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hdec_entails (sepConj_mono_left hout_split))))) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w8
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w16
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro w24
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro bs7
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro vecs_dec
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v8
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v16
    rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v24
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right w8 (Entails.sepExists_right w16 (Entails.sepExists_right w24
      (Entails.sepExists_right bs7 (Entails.sepExists_right vecs_dec
        (Entails.sepExists_right v0 (Entails.sepExists_right v8
          (Entails.sepExists_right v16 (Entails.sepExists_right v24 ?_))))))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.exists_left; intro bs7
  apply ProofLib.SepWP.exists_left; intro vecs_dec
  apply ProofLib.SepWP.exists_left; intro v0
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v24
  wp_focus_pure; intro ⟨hlen7, hw8⟩
  wp_focus_pure; intro hvecs_dec_len
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        (((s_in.readReg64 .x19) ↦₆₄ noneCap) ∗
          ((s_in.readReg64 .x19 + 8#64) ↦₆₄ w8) ∗
          ((s_in.readReg64 .x19 + 16#64) ↦₆₄ w16) ∗
          ((s_in.readReg64 .x19 + 24#64) ↦₆₄ w24) ∗
          memRegion (s_in.readReg64 .x19 + 32#64) 928) ∗
        (((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
          ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
          ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
          ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
          memRegion (s_in.sp + 1888#64) 96) ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        memRegion (stA + 8#64) 384 ∗
        (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
        A.pool ∗
        (memRegion (s_in.sp - 19552#64) 15424 ∗ stackAt s_in.sp dropGluePoly16Stack) ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit]
    refine ct1Sampled_seq_clean_lscl hcl (mid := (blkPl_332).base + 15736#64)
      (P_mid := ((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
        ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
        ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
        ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
        memRegion (s_in.sp + 1888#64) 96 ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        memRegion (stA + 8#64) 384 ∗
        vecPtListOf A (s_in.sp + 2752#64) vecs_dec ∗
        memRegion (s_in.sp + 3136#64) 16 ∗
        ((s_in.readReg64 .x19) ↦₆₄ v0) ∗
        ((s_in.readReg64 .x19 + 8#64) ↦₆₄ v8) ∗
        ((s_in.readReg64 .x19 + 16#64) ↦₆₄ v16) ∗
        ((s_in.readReg64 .x19 + 24#64) ↦₆₄ v24) ∗
        memRegion (s_in.readReg64 .x19 + 32#64) 928 ∗
        A.pool ∗
        memRegion (s_in.sp - 19552#64) 15424 ∗
        stackAt s_in.sp dropGluePoly16Stack ∗
        Rest)
      (Q := fun sm => sm.sp = s_in.sp ∧
        sm.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sm.readReg64 .x20 = w16 ∧
        sm.readReg64 .x21 = w24 ∧
        sm.readReg64 .x25 = w8 ∧
        sm.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sm s_in) ?_ ?_
    · have hdrop_poly := drop_glue_poly16_mem_on
        (callerProg := lsProg_332 (Rust.withPanics ext)) hdealloc hcl
      dsimp only [lsProg_332, withMemEq, dropGluePoly16Spec, polyArrayBytes,
        noneCap, BitVec.ofNat_eq_ofNat] at hpc hdrop_poly ⊢
      wp_steps
      wp_call hdrop_poly ⟨stA + 8#64, vecs⟩
      wp_done
    · intro sm hpcm hrunm hclm ⟨hspm, hx19m, hx20m, hx21m, hx25m, hx29m, htrm⟩
      have hdrop_ss := drop_glue_sorted_set_pt16_mem_on
        (callerProg := lsProg_332 (Rust.withPanics ext)) hdealloc hclm
      dsimp only [lsProg_332, withMemEq, dropGlueSortedSetPt16Spec, polyArrayBytes,
        noneCap, BitVec.ofNat_eq_ofNat] at hpcm hdrop_ss ⊢
      rw [← hspm]
      wp_steps
      wp_call hdrop_ss ⟨sm.sp + 2752#64, vecs_dec⟩
      wp_steps
      rw [hspm]
      wp_done
  · rw [← hsplit]
    have herr_out := err_words_entails_resultV1RecvAt_erroneous A (F := F)
      (s_in.readReg64 .x19) w8 w16 w24 hlen7 hw8
    have h1856_mr :
        ((s_in.sp + 1856#64) ↦₆₄ noneCap) ∗
          ((s_in.sp + 1864#64) ↦₆₄ w8) ∗
          ((s_in.sp + 1872#64) ↦₆₄ w16) ∗
          ((s_in.sp + 1880#64) ↦₆₄ w24) ∗
          memRegion (s_in.sp + 1888#64) 96 ⊢
        memRegion (s_in.sp + 1856#64) 128 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 1856#64) (n := 8) (k := 120)
            (b' := s_in.sp + 1864#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 1864#64) (n := 8) (k := 112)
            (b' := s_in.sp + 1872#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 1872#64) (n := 8) (k := 104)
            (b' := s_in.sp + 1880#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 1880#64) (n := 8) (k := 96)
            (b' := s_in.sp + 1888#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))
    have h2752_mr :
        memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16 ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 2752#64) (n := 384) (k := 16)
            (b' := s_in.sp + 3136#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    exact sepConj_mono herr_out (sepConj_mono h1856_mr
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h2752_mr))))

/-! ## 3. `recv_ek = .ok uc_ek` Staging (`+11528 -> +11620`) -/

theorem ct1Sampled_recv_ek_ok_copy_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp vb0 : BitVec 64)
    (c_ek : Words16)
    (Rest : SepProp)
    (hcap : c_ek.w0.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11528#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11620#64) s_in
      (wordsAt (fsp + 1856#64) c_ek.toList ∗
        memRegion (fsp + 3856#64) 128 ∗
        ((fsp + 176#64) ↦₆₄ vb0) ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          wordsAt (fsp + 1856#64) c_ek.toList ∗
          wordsAt (fsp + 3856#64) c_ek.toList ∗
          ((fsp + 176#64) ↦₆₄ c_ek.w1) ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x8 = c_ek.w0 ∧
        sf.readReg64 .x9 = c_ek.w2 ∧
        sf.readReg64 .x10 = c_ek.w3 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = c_ek.w1 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hcmn := Recv.cap_add_one_beq_zero_false hcap
  have hpre :
      wordsAt (s_in.sp + 1856#64) c_ek.toList ∗
        memRegion (s_in.sp + 3856#64) 128 ∗
        ((s_in.sp + 176#64) ↦₆₄ vb0) ∗
        Rest ⊢
      ∃∗ c_dst : Words16,
        wordsAt (s_in.sp + 1856#64) c_ek.toList ∗
        wordsAt (s_in.sp + 3856#64) c_dst.toList ∗
        ((s_in.sp + 176#64) ↦₆₄ vb0) ∗
        Rest := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (memRegion_128_entails_words16 (s_in.sp + 3856#64)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro c_dst
    exact Entails.sepExists_right c_dst (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro c_dst
  dsimp only [lsProg_332, Words16.toList, BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  wp_done

theorem ct1Sampled_ok_branch_no_ack_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 11620#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 0#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 15760#64) s_in
      Rest
      (fun sf Pf =>
        (Pf ⊢ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x8 = s_in.readReg64 .x8 ∧
        sf.readReg64 .x9 = s_in.readReg64 .x9 ∧
        sf.readReg64 .x10 = s_in.readReg64 .x10 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

theorem ct1Sampled_ok_branch_ack_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 11620#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 1#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11624#64) s_in
      Rest
      (fun sf Pf =>
        (Pf ⊢ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x8 = s_in.readReg64 .x8 ∧
        sf.readReg64 .x9 = s_in.readReg64 .x9 ∧
        sf.readReg64 .x10 = s_in.readReg64 .x10 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  wp_done

/-! ## 4. Path 5b (`outMsg = some decoded, recv_ek = .ok uc_ek, ack = false`): `+15760 -> +18996` -/

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_some_no_ack_part1_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s_in : State) (fsp stA : BitVec 64)
    (vecs_dec : List (List Pt)) (hvecs_dec_len : vecs_dec.length = NUM_POLYS)
    (c_enc : Words50) (c_ek : Words16)
    (bs352_mid : List (BitVec 8)) (tail5_mid : Words5)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v976 v984 v992 vc90 vc98 v4096 v4104 v4112 : BitVec 64)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 15760#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx8 : s_in.readReg64 .x8 = c_ek.w0)
    (hx9 : s_in.readReg64 .x9 = c_ek.w2)
    (hx10 : s_in.readReg64 .x10 = c_ek.w3)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx23 : s_in.readReg64 .x23 = c_enc.c0.w0)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    let d := mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352_mid tail5_mid
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 16596#64) s_in
      (words50At stA c_enc ∗
        wordsAt (fsp + 3856#64) c_ek.toList ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        vecPtListOf A (fsp + 2752#64) vecs_dec ∗
        memRegion (fsp + 3136#64) 16 ∗
        copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗
        ((fsp + 984#64) ↦₆₄ v984) ∗
        ((fsp + 992#64) ↦₆₄ v992) ∗
        ((fsp + 3216#64) ↦₆₄ vc90) ∗
        ((fsp + 3224#64) ↦₆₄ vc98) ∗
        ((fsp + 4096#64) ↦₆₄ v4096) ∗
        ((fsp + 4104#64) ↦₆₄ v4104) ∗
        ((fsp + 4112#64) ↦₆₄ v4112) ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          words50At stA c_enc ∗
          memRegion (fsp + 3856#64) 128 ∗
          ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (fsp + 2752#64) 400 ∗
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          ((fsp + 976#64) ↦₆₄ c_ek.w13) ∗
          ((fsp + 984#64) ↦₆₄ c_ek.w14) ∗
          ((fsp + 992#64) ↦₆₄ c_ek.w15) ∗
          ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗
          ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
          memRegion (fsp + 4096#64) 24 ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x23 = 3#64 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = fsp + 4144#64 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      (Pf ⊢
        words50At stA c_enc ∗
        wordsAt (s_in.sp + 3856#64) c_ek.toList ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((s_in.sp + 976#64) ↦₆₄ c_ek.w13) ∗
        ((s_in.sp + 984#64) ↦₆₄ c_ek.w14) ∗
        ((s_in.sp + 992#64) ↦₆₄ c_ek.w15) ∗
        ((s_in.sp + 3216#64) ↦₆₄ c_ek.w10) ∗
        ((s_in.sp + 3224#64) ↦₆₄ c_ek.w11) ∗
        (((s_in.sp + 4096#64) ↦₆₄ c_ek.w13) ∗
          ((s_in.sp + 4104#64) ↦₆₄ c_ek.w14) ∗
          ((s_in.sp + 4112#64) ↦₆₄ c_ek.w15)) ∗
        A.pool ∗
        stackAt s_in.sp statesRecvCalleeStackX ∗
        Rest) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf.readReg64 .x23 = 3#64 ∧
      sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
      sf.readReg64 .x29 = s_in.sp + 4144#64 ∧
      TraceCalleeSaved sf s_in) ?_ (fun sf Pf _ _ ⟨hPf, hrest⟩ => ⟨Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit]
    refine ct1Sampled_seq_clean_lscl hcl (mid := lsmpl.base 264)
      (P_mid := words50At stA c_enc ∗
        wordsAt (s_in.sp + 3856#64) c_ek.toList ∗
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗
        vecPtListOf A (s_in.sp + 2752#64) vecs_dec ∗
        memRegion (s_in.sp + 3136#64) 16 ∗
        copyScratchStackAt s_in.sp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((s_in.sp + 976#64) ↦₆₄ c_ek.w13) ∗
        ((s_in.sp + 984#64) ↦₆₄ c_ek.w14) ∗
        ((s_in.sp + 992#64) ↦₆₄ c_ek.w15) ∗
        ((s_in.sp + 3216#64) ↦₆₄ c_ek.w10) ∗
        ((s_in.sp + 3224#64) ↦₆₄ c_ek.w11) ∗
        (((s_in.sp + 4096#64) ↦₆₄ c_ek.w13) ∗
          ((s_in.sp + 4104#64) ↦₆₄ c_ek.w14) ∗
          ((s_in.sp + 4112#64) ↦₆₄ c_ek.w15)) ∗
        A.pool ∗
        memRegion (s_in.sp - 19552#64) 15424 ∗
        stackAt s_in.sp dropGluePoly16Stack ∗
        Rest)
      (Q := fun sm => sm.sp = s_in.sp ∧
        sm.readReg64 .x0 = s_in.sp + 2752#64 ∧
        sm.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sm.readReg64 .x20 = 3#64 ∧
        sm.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sm.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sm.readReg64 .x29 = s_in.sp + 4144#64 ∧
        sm.readReg64 .x30 = (blkPl_332).base + 16176#64 ∧
        TraceCalleeSaved sm s_in) ?_ ?_
    · dsimp only [lsProg_332, d, mkSplit928EkReceivedCt1Sampled, copyScratchStackAt, copyFullScratch,
        epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At, Words16.toList,
        BitVec.ofNat_eq_ofNat]
        at hpc ⊢
      simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd,
        hx8, hx9, hx10, hx21, hx23, hx29]
      wp_steps
      wp_done
    · intro sm hpcm hrunm hclm ⟨hspm, hx0m, hx19m, hx20m, hx24m, hx28m, hx29m, hx30m, htrm⟩
      have hdrop := drop_glue_sorted_set_pt16_mem_on
        (callerProg := lsProg_332 (Rust.withPanics ext)) hdealloc hclm
      dsimp only [lsProg_332, withMemEq, dropGlueSortedSetPt16Spec, polyArrayBytes, BitVec.ofNat_eq_ofNat]
        at hpcm hdrop ⊢
      rw [← hspm]
      wp_call hdrop ⟨sm.sp + 2752#64, vecs_dec⟩
      wp_steps
      rw [hspm]
      wp_done
  · have h3856_mr := wordsAt_entails_memRegion c_ek.toList (s_in.sp + 3856#64) 128 rfl
    have h2752_mr :
        memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16 ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 2752#64) (n := 384) (k := 16)
            (b' := s_in.sp + 3136#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    have h4096_mr :
        ((s_in.sp + 4096#64) ↦₆₄ c_ek.w13) ∗
          ((s_in.sp + 4104#64) ↦₆₄ c_ek.w14) ∗
          ((s_in.sp + 4112#64) ↦₆₄ c_ek.w15) ⊢
        memRegion (s_in.sp + 4096#64) 24 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 4096#64) (n := 8) (k := 16)
            (b' := s_in.sp + 4104#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s_in.sp + 4104#64) (n := 8) (k := 8)
            (b' := s_in.sp + 4112#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (ProofLib.pointsTo64_entails_memRegion _ _))
    exact sepConj_mono_right (sepConj_mono h3856_mr (sepConj_mono_right (sepConj_mono h2752_mr
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left h4096_mr)))))))))))

theorem ct1Sampled_copy_some_no_ack_part2a_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s_in : State) (fsp : BitVec 64)
    (w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5)
    (Rest : SepProp)
    (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16596#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx23 : s_in.readReg64 .x23 = 3#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 16800#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
        wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗
        memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x8 = 2#64 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  have hmid376_len : (mid376Bytes w0 w8 w16 bs352_976).length = 376 :=
    mid376Bytes_length w0 w8 w16 h976_len
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w0 w8 w16 bs352_976,
      mid376At_eq_pointsToBytes (s_in.sp + 3272#64) w0 w8 w16 bs352_976,
      hsplit, show memRegion (s_in.sp + 3272#64) 376 = memRegion (s_in.sp + 3272#64) (mid376Bytes w0 w8 w16 bs352_976).length by rw [hmid376_len]]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [Words5.toList, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx23, hx28]
  wp_steps
  wp_call hmemcpy_raw (s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w0 w8 w16 bs352_976)
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_some_no_ack_part2b_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp stA outA : BitVec 64)
    (c_enc : Words50) (c_ek : Words16)
    (bs352_976 bs352_576 : List (BitVec 8))
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (v576 v584 v592 vf10 vf18 : BitVec 64)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16800#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx8 : s_in.readReg64 .x8 = 2#64)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    let d := mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352_576 k.tail
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        mid376At (fsp + 976#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
        ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗
        ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
        mid376At (fsp + 3272#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
        ((fsp + 3856#64) ↦₆₄ vf10) ∗
        ((fsp + 3864#64) ↦₆₄ vf18) ∗
        statesRecvRoPlacedAt ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          copyScratchStackAt fsp (copyFullScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          mid376At (fsp + 976#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
          ((fsp + 3216#64) ↦₆₄ c_ek.w10) ∗
          ((fsp + 3224#64) ↦₆₄ c_ek.w11) ∗
          mid376At (fsp + 3272#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_976 ∗
          ((fsp + 3856#64) ↦₆₄ c_ek.w10) ∗
          ((fsp + 3864#64) ↦₆₄ c_ek.w11) ∗
          statesRecvRoPlacedAt ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  intro d
  subst hsp hx19
  dsimp only [lsProg_332, statesRecvRoPlacedAt, Unchunked.unchunkedSendCt2PlacedRoAt,
    lsLogFilterAddr, BitVec.ofNat_eq_ofNat] at hpc ⊢
  dsimp only [epilogueStoreStackPart2At]
  rw [show (epilogueStackOfSplit928 d noneCap k.w200 k.w208).mid =
      mid376Bytes c_ek.w13 c_ek.w14 c_ek.w15 bs352_576 from rfl,
      ← mid376At_eq_pointsToBytes (s_in.sp + 576#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352_576]
  dsimp only [d, mkSplit928EkReceivedCt1Sampled, copyScratchStackAt, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, epilogueRegsEqSplit928,
    EpilogueStoreStack.tail, mid376At, noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx8, hx28]
  wp_steps
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct1Sampled_call_recv_ek_placed
  ct1Sampled_recv_ek_err_to_19324_placed
  ct1Sampled_recv_ek_ok_copy_placed
  ct1Sampled_ok_branch_no_ack_placed
  ct1Sampled_ok_branch_ack_placed
  ct1Sampled_copy_some_no_ack_part1_placed
  ct1Sampled_copy_some_no_ack_part2a_placed
  ct1Sampled_copy_some_no_ack_part2b_placed
)

end CryptoVerification.SpqrV1.States.Recv
