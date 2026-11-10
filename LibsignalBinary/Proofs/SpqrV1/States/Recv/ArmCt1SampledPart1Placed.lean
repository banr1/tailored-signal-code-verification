/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledDefsPlaced -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 1 (Relocatable)

Relocatable `[LibsignalPlacement]` shared direct epilogue (`+19324 -> s0.x30`), prologue,
jump-table dispatch, epoch comparison at `+1528`, and Path 1 (`Error::EpochOutOfRange`).
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Std
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Recv

set_option autoImplicit false
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
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Shared Direct Epilogue (`+19324 -> s0.x30`), Prologue, & Dispatch -/

theorem ct1Sampled_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  CryptoVerification.sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

theorem ct1Sampled_epilogue_19324_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_332).base + 19324#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  states_recv_epilogue_19324_placed s0 s1 Rest hsp0_align (by rwa [lsmpl_base_332_eq]) hrun1 hsp1 htr1

theorem ct1Sampled_prologue_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc0 : s0.pc = lsmpl.base 332)
    (hrun0 : s0.status = .Running) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 36#64)
      s0
      (stackAt s0.sp statesRecvStackX ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗
          Rest) ∧
        s1.sp = s0.sp - 4240#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        TraceCalleeSaved s1 s0) :=
  states_recv_prologue_placed s0 Rest hsp0_align hpc0 hrun0

theorem ct1Sampled_dispatch_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp st_ptr tag : BitVec 64) (Rest : SepProp)
    (htag : tag = 0#64 ∨ tag = 1#64)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 1528#64)
      s1
      ((st_ptr ↦₆₄ tag) ∗ statesRecvRoPlacedAt ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (st_ptr ↦₆₄ tag) ∗ statesRecvRoPlacedAt ∗ Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x0 = s1.readReg64 .x0 ∧
        s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧
        s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = 7#64 ∧
        s2.readReg64 .x12 = tag ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) := by
  rcases htag with rfl | rfl
  · exact states_recv_dispatch_placed s1 fsp st_ptr 0#64 Rest (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  · exact states_recv_dispatch_placed s1 fsp st_ptr 1#64 Rest (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1

/-! ## 2. Epoch Comparison at `+1528` (`0x55a4c..0x55a70`) -/

theorem ct1Sampled_epoch_cmp_gt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s2 : State) (selfA msgA st_ep msg_ep : BitVec 64) (Rest : SepProp)
    (hgt : msg_ep.toNat > st_ep.toNat)
    (hpc2 : s2.pc = (blkPl_332).base + 1528#64)
    (hrun2 : s2.status = .Running)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx24 : s2.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 1564#64)
      s2
      (((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest)
      (fun s3 P3 =>
        (P3 ⊢ ((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest) ∧
        s3.sp = s2.sp ∧
        s3.readReg64 .x1 = selfA ∧
        s3.readReg64 .x19 = s2.readReg64 .x19 ∧
        s3.readReg64 .x20 = msg_ep ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧
        s3.readReg64 .x24 = msgA ∧
        s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.readReg64 .x29 = s2.readReg64 .x29 ∧
        TraceCalleeSaved s3 s2) := by
  subst hx1 hx24
  have hcond1 := epoch_cmp_b_eq_of_gt hgt
  have hcond2 := epoch_cmp_b_ne_of_gt hgt
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  wp_steps
  wp_done

theorem ct1Sampled_epoch_cmp_lt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s2 : State) (selfA msgA st_ep msg_ep : BitVec 64) (Rest : SepProp)
    (hlt : msg_ep.toNat < st_ep.toNat)
    (hpc2 : s2.pc = (blkPl_332).base + 1528#64)
    (hrun2 : s2.status = .Running)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx24 : s2.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 10500#64)
      s2
      (((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest)
      (fun s3 P3 =>
        (P3 ⊢ ((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest) ∧
        s3.sp = s2.sp ∧
        s3.readReg64 .x0 = s2.readReg64 .x0 ∧
        s3.readReg64 .x1 = selfA ∧
        s3.readReg64 .x2 = s2.readReg64 .x2 ∧
        s3.readReg64 .x3 = s2.readReg64 .x3 ∧
        s3.readReg64 .x12 = s2.readReg64 .x12 ∧
        s3.readReg64 .x19 = s2.readReg64 .x19 ∧
        s3.readReg64 .x20 = msg_ep ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧
        s3.readReg64 .x24 = msgA ∧
        s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.readReg64 .x29 = s2.readReg64 .x29 ∧
        TraceCalleeSaved s3 s2) := by
  subst hx1 hx24
  have hcond1 := epoch_cmp_b_eq_of_lt hlt
  have hcond2 := epoch_cmp_b_ne_of_lt hlt
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  wp_steps
  wp_done

theorem ct1Sampled_epoch_cmp_eq_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s2 : State) (selfA msgA ep : BitVec 64) (Rest : SepProp)
    (hpc2 : s2.pc = (blkPl_332).base + 1528#64)
    (hrun2 : s2.status = .Running)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx24 : s2.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 7052#64)
      s2
      (((selfA + 520#64) ↦₆₄ ep) ∗ (msgA ↦₆₄ ep) ∗ Rest)
      (fun s3 P3 =>
        (P3 ⊢ ((selfA + 520#64) ↦₆₄ ep) ∗ (msgA ↦₆₄ ep) ∗ Rest) ∧
        s3.sp = s2.sp ∧
        s3.readReg64 .x0 = s2.readReg64 .x0 ∧
        s3.readReg64 .x1 = selfA ∧
        s3.readReg64 .x2 = s2.readReg64 .x2 ∧
        s3.readReg64 .x3 = s2.readReg64 .x3 ∧
        s3.readReg64 .x12 = s2.readReg64 .x12 ∧
        s3.readReg64 .x19 = s2.readReg64 .x19 ∧
        s3.readReg64 .x20 = ep ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧
        s3.readReg64 .x24 = msgA ∧
        s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.readReg64 .x29 = s2.readReg64 .x29 ∧
        TraceCalleeSaved s3 s2) := by
  subst hx1 hx24
  have hcond1 := epoch_cmp_b_eq_of_eq ep
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  wp_steps
  wp_done

/-! ## 3. Path 1: `msg.epoch > st.uc.epoch` (`Error::EpochOutOfRange`, `+1564 -> s0.x30`) -/

set_option maxHeartbeats 600000 in
theorem ct1Sampled_write_err_and_dealloc5_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s3 : State) (fsp outA selfA msg_ep : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (blkPl_332).base + 1564#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1 : s3.readReg64 .x1 = selfA)
    (hx19 : s3.readReg64 .x19 = outA)
    (hx20 : s3.readReg64 .x20 = msg_ep) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 1744#64)
      s3
      (memRegion outA v1RecvSize ∗
        unchunkedCt1SentAt A (selfA + 400#64) uc ∗
        A.pool ∗
        stackAt fsp allocHookStack ∗
        Rest)
      (fun s8 P8 =>
        (P8 ⊢
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          memRegion (selfA + 400#64) 128 ∗
          A.pool ∗
          stackAt fsp allocHookStack ∗
          Rest) ∧
        s8.sp = fsp ∧
        s8.readReg64 .x1 = selfA ∧
        TraceCalleeSaved s8 s3) := by
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [lsProg_332, lsρ, spqrDeallocSym, BitVec.ofNat_eq_ofNat] at hpc3 hdealloc_raw ⊢
  wp_conv_pre =>
    rw [memRegion_out_960_split_err outA]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v16_out
  apply ProofLib.SepWP.exists_left; intro b8_out
  apply ProofLib.SepWP.exists_left; intro v0_out
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        unchunkedCt1SentAt A (selfA + 400#64) uc ∗
        ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
         memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
         A.pool ∗ stackAt fsp allocHookStack ∗ Rest) by ac_rfl))
      (sepConj_mono_left (unchunkedCt1Sent400_entails_dealloc A selfA uc))) ?_
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro g
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := (blkPl_332).base + 1616#64)
    (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
      (fiveVec400HeadersAt selfA g ∗
       vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
       vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
       vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
       vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
    ?_ ?_
  · have hstep1 : SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
        ((blkPl_332).base + 1616#64) s3
        ((fiveVec400HeadersAt selfA g ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
         ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
          memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Rest))
        (fun sm Pm =>
          (Pm ⊢ (((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_ep) ∗
            memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936) ∗
            (fiveVec400HeadersAt selfA g ∗
             vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
             vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
             vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
             vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Rest) ∧
          (sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)) := by
      dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, noneCap]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; wp_steps; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp3]; ac_rfl)) ?_; wp_done
    exact SepWP.strengthen_entails_const
      (sepConj_mono_left (sepConj_mono_left
        (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg_ep)))
      hstep1
  · intro s4 hpc4 hrun4 ⟨hsp4, hx1_4, htr4⟩
    refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := (blkPl_332).base + 1648#64)
      (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
        (fiveVec400HeadersAt selfA g ∗
         vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
         vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
         vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
      ?_ ?_
    · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; wp_steps; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp4]; ac_rfl)) ?_; wp_done
    · intro s5 hpc5 hrun5 ⟨hsp5, hx1_5, htr5⟩
      refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := (blkPl_332).base + 1680#64)
        (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          (fiveVec400HeadersAt selfA g ∗
           vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
           vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
        ?_ ?_
      · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; wp_steps; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp5]; ac_rfl)) ?_; wp_done
      · intro s6 hpc6 hrun6 ⟨hsp6, hx1_6, htr6⟩
        refine CryptoVerification.SpqrV1.States.Recv.seq_clean (mid := (blkPl_332).base + 1712#64)
          (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            (fiveVec400HeadersAt selfA g ∗
             vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
          ?_ ?_
        · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp6]; ac_rfl)) ?_; wp_done
        · intro s7 hpc7 hrun7 ⟨hsp7, hx1_7, htr7⟩
          have hstep5 : SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
              ((blkPl_332).base + 1744#64) s7
              ((resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                (fiveVec400HeadersAt selfA g ∗
                 vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
              (fun s8 P8 =>
                (P8 ⊢ (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                  fiveVec400HeadersAt selfA g) ∗
                  A.pool ∗ stackAt fsp allocHookStack ∗ Rest) ∧
                s8.sp = fsp ∧
                s8.readReg64 .x1 = selfA ∧
                TraceCalleeSaved s8 s3) := by
            dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
            by_cases hc5 : (g.v5.cap == 0#64) = true <;>
              simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; wp_done
            · wp_steps; wp_apply; wp_steps; refine CryptoVerification.SpqrV1.States.Recv.align_pre (Entails.of_eq (by rw [hsp7]; ac_rfl)) ?_; wp_done
          exact SepWP.strengthen_entails_const
            (Entails.trans
              (sepConj_mono_left (sepConj_mono_right (fiveVec400HeadersAt_entails_memRegion_128 selfA g)))
              (Entails.of_eq (by ac_rfl)))
            hstep5

theorem ct1Sampled_drop_encoders_epilogue_placed [LibsignalPlacement]
    {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s0 s8 : State) (selfA : BitVec 64)
    (enc : PolyEncoder) (dec : PolyDecoder)
    (Rest : SepProp)
    (hcl8 : LibsignalCodeLoaded lsmpl s8.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc8 : s8.pc = (blkPl_332).base + 1744#64)
    (hrun8 : s8.status = .Running)
    (hsp8 : s8.sp = s0.sp - 4240#64)
    (hx1_8 : s8.readReg64 .x1 = selfA)
    (htr8 : TraceCalleeSaved s8 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s8
      (polyEncoderAt A selfA enc ∗
        memRegion (selfA + 400#64) 128 ∗
        polyDecoderAt A (selfA + 528#64) dec ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          memRegion selfA chunkedStatesSize ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        polyEncoderAt A selfA enc ∗
        polyDecoderAt A (selfA + 528#64) dec ∗
        (memRegion (selfA + 400#64) 128 ∗
         A.pool ∗
         stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         statesRecvSavedCells s0 ∗
         Rest) by ac_rfl))
      (sepConj_mono (polyEncoderAt_entails_tag_vecs_tail A selfA enc)
        (sepConj_mono_left (polyDecoderAt_entails_vecs_tail A (selfA + 528#64) dec)))) ?_
  wp_conv_pre =>
    rw [stackAt_statesRecvCallee_eq_dropGluePoly16' (s0.sp - 4240#64)]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro dec_vecs
  apply ProofLib.SepWP.exists_left; intro enc_tag
  apply ProofLib.SepWP.exists_left; intro enc_vecs
  wp_focus_pure; intro hdec_len
  wp_focus_pure; intro henc_len
  subst hx1_8
  have h912 : (s8.readReg64 .x1 + 528#64) + 384#64 = s8.readReg64 .x1 + 912#64 := by bv_omega
  refine ct1Sampled_seq_clean_lscl hcl8 (mid := (blkPl_332).base + 1760#64)
    (P_mid := memRegion (s8.readReg64 .x1 + 8#64) polyArrayBytes ∗ A.pool ∗
      stackAt (s0.sp - 4240#64) dropGluePoly16Stack ∗
      ((s8.readReg64 .x1 ↦₆₄ enc_tag) ∗ memRegion (s8.readReg64 .x1 + 392#64) 8 ∗
       vecPtListOf A (s8.readReg64 .x1 + 528#64) dec_vecs ∗ memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16 ∗
       memRegion (s8.readReg64 .x1 + 400#64) 128 ∗ memRegion (s0.sp - 23792#64) 15424 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ∗ Rest))
    (Q := fun s9 => s9.sp = s8.sp ∧ s9.readReg64 .x0 = s8.readReg64 .x1 + 528#64 ∧
      TraceCalleeSaved s9 s8) ?_ ?_
  · have hpoly16_raw := drop_glue_poly16_mem_on
      (callerProg := lsProg_332 (Rust.withPanics ext)) hdealloc hcl8
    dsimp only [lsProg_332, withMemEq, dropGluePoly16Spec, BitVec.ofNat_eq_ofNat] at hpc8 hpoly16_raw ⊢
    wp_steps
    wp_call hpoly16_raw ⟨s8.readReg64 .x1 + 8#64, enc_vecs⟩
    wp_steps
    refine CryptoVerification.SpqrV1.States.Recv.align_pre
      (Entails.of_eq (by rw [hsp8, h912])) ?_
    wp_done
  · intro s9 hpc9 hrun9 hcl9 ⟨hsp9, hx0_9, htr9⟩
    rw [hsp8] at hsp9
    have hstack_fold :
        memRegion (s0.sp - 23792#64) 15424 ∗ stackAt (s0.sp - 4240#64) dropGluePoly16Stack ⊢
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX := by
      have h := stackAt_statesRecvCallee_from_dropGluePoly16 (s0.sp - 4240#64)
      have heq : s0.sp - 4240#64 - 19552#64 = s0.sp - 23792#64 := by bv_omega
      rwa [heq] at h
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          ((s8.readReg64 .x1 ↦₆₄ enc_tag) ∗ memRegion (s8.readReg64 .x1 + 8#64) polyArrayBytes ∗
           memRegion (s8.readReg64 .x1 + 392#64) 8 ∗ memRegion (s8.readReg64 .x1 + 400#64) 128) ∗
          (memRegion (s0.sp - 23792#64) 15424 ∗ stackAt (s0.sp - 4240#64) dropGluePoly16Stack) ∗
          (memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ∗
           vecPtListOf A (s8.readReg64 .x1 + 528#64) dec_vecs ∗ A.pool ∗
           (memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16 ∗ Rest)) by ac_rfl))
        (sepConj_mono (chunked_400_join (s8.readReg64 .x1) enc_tag 128 528 rfl (by decide))
          (sepConj_mono_left hstack_fold))) ?_
    refine SepWP.weaken_pre
      (Entails.of_eq (show _ =
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        vecPtListOf A (s8.readReg64 .x1 + 528#64) dec_vecs ∗
        A.pool ∗
        (memRegion (s8.readReg64 .x1) 528 ∗ memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16 ∗ Rest) by ac_rfl)) ?_
    have htail := states_recv_tail_drop_sortedSetPt16_1760_placed
      (drop_glue_sorted_set_pt16_cl_on (callerProg := lsProg_332 (Rust.withPanics ext)) hdealloc)
      s0 s9 (s8.readReg64 .x1 + 528#64) dec_vecs henc_len
      (memRegion (s8.readReg64 .x1) 528 ∗ memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16 ∗ Rest)
      hsp0_align (by rwa [lsmpl_base_332_eq]) hrun9 hsp9 hx0_9 (htr9.trans htr8) hcl9
    refine SepWP.mono htail ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.trans
      (Entails.of_eq (show _ =
        (memRegion (s8.readReg64 .x1) 528 ∗ memRegion (s8.readReg64 .x1 + 528#64) polyArrayBytes ∗
         memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16) ∗
        (A.pool ∗ stackAt s0.sp statesRecvStackX ∗ Rest) by ac_rfl))
      (sepConj_mono_left (ct1Sampled_join_928 (s8.readReg64 .x1)))), hsp_f, hcs_f, htr_f⟩

theorem ct1Sampled_drop_epochOutOfRange_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s0 s3 : State) (outA selfA msg_ep : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (blkPl_332).base + 1564#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 4240#64)
    (hx1 : s3.readReg64 .x1 = selfA)
    (hx19 : s3.readReg64 .x19 = outA)
    (hx20 : s3.readReg64 .x20 = msg_ep)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ct1Sampled st) ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          memRegion selfA chunkedStatesSize ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
  wp_conv_pre =>
    rw [stackAt_statesRecvCallee_eq_allocHook' (s0.sp - 4240#64)]
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      memRegion outA v1RecvSize ∗
      unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
      A.pool ∗
      stackAt (s0.sp - 4240#64) allocHookStack ∗
      (polyEncoderAt A selfA st.sending_ct1 ∗
       polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
       memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0 ∗
       Rest) by ac_rfl)) ?_
  refine ct1Sampled_seq_clean_lscl hcl3
    (ct1Sampled_write_err_and_dealloc5_placed hdealloc s3 (s0.sp - 4240#64) outA selfA msg_ep st.uc
      (polyEncoderAt A selfA st.sending_ct1 ∗
       polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
       memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0 ∗
       Rest)
      hfsp_align hpc3 hrun3 hsp3 hx1 hx19 hx20) ?_
  intro s8 hpc8 hrun8 hcl8 ⟨hsp8, hx1_8, htr8⟩
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗ stackAt (s0.sp - 4240#64) allocHookStack) ∗
        (polyEncoderAt A selfA st.sending_ct1 ∗
         memRegion (selfA + 400#64) 128 ∗
         polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
         A.pool ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         statesRecvSavedCells s0 ∗
         (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗ Rest)) by ac_rfl))
      (sepConj_mono_left (stackAt_statesRecvCallee_from_allocHook (s0.sp - 4240#64)))) ?_
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      polyEncoderAt A selfA st.sending_ct1 ∗
      memRegion (selfA + 400#64) 128 ∗
      polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
      A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗ Rest) by ac_rfl)) ?_
  refine SepWP.mono
    (ct1Sampled_drop_encoders_epilogue_placed hdealloc s0 s8 selfA st.sending_ct1 st.receiving_ek
      (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗ Rest)
      hcl8 hsp0_align hpc8 hrun8 hsp8 hx1_8 (htr8.trans htr3)) ?_
  intro sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩
  refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct1Sampled_seq_clean_lscl
  ct1Sampled_epilogue_19324_placed
  ct1Sampled_prologue_placed
  ct1Sampled_dispatch_placed
  ct1Sampled_epoch_cmp_gt_placed
  ct1Sampled_epoch_cmp_lt_placed
  ct1Sampled_epoch_cmp_eq_placed
  ct1Sampled_write_err_and_dealloc5_placed
  ct1Sampled_drop_encoders_epilogue_placed
  ct1Sampled_drop_epochOutOfRange_placed
)

end CryptoVerification.SpqrV1.States.Recv
