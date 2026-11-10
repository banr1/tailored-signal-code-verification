/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 6 (`HeaderReceived`, `+1464`, Block `333`) — Part A

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant6a.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlaced

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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

/-! ## 1. Error Epilogue (`+10396`) & Decoder Deallocation (`+10316..+10396`) -/

set_option maxHeartbeats 800000 in
theorem v6hr_states_from_pb_err_10396_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64)
    (v80 v128 v136 v144 : BitVec 64) (d184 : BitVec 32)
    (v192 : BitVec 64) (d200 : BitVec 32)
    (v208 v216 v224 v232 : BitVec 64)
    (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 10396#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx25_1 : (s1.readReg64 .x25).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        v6hr_lowStackAt s0.sp v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232 ∗
        memRegion (s0.sp - 2160#64) 2064 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          Rest ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 60#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      (out ↦₆₄ v0) ∗
      ((out + 8#64) ↦₈ spqrErrorByte err) ∗
      memRegion (out + 9#64) 919 ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x8 = noneCap ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · unfold v6hr_lowStackAt
    simp only [sepConj_assoc]
    change s1.pc = (blkPl_333).base + 10396#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 60#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x25)
        (s1.readReg64 .x26) v216
      rw [hx25_1] at htail
      have hst := v6hr_lowStackAt_entails_memRegion_2304 s0.sp
        v80 v128 v136 v144 d184 v192 d200 v208 v216 v224 v232
      unfold v6hr_lowStackAt at hst
      simp only [sepConj_assoc] at hst
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((s0.sp - 2320#64) ↦₆₄ v80) ∗
           ((s0.sp - 2272#64) ↦₆₄ v128) ∗
           ((s0.sp - 2264#64) ↦₆₄ v136) ∗
           ((s0.sp - 2256#64) ↦₆₄ v144) ∗
           ((s0.sp - 2216#64) ↦₃₂ d184) ∗
           ((s0.sp - 2208#64) ↦₆₄ v192) ∗
           ((s0.sp - 2200#64) ↦₃₂ d200) ∗
           ((s0.sp - 2192#64) ↦₆₄ v208) ∗
           ((s0.sp - 2184#64) ↦₆₄ v216) ∗
           ((s0.sp - 2176#64) ↦₆₄ v224) ∗
           ((s0.sp - 2168#64) ↦₆₄ v232) ∗
           v6hr_lowStackGaps s0.sp ∗
           memRegion (s0.sp - 2160#64) 2064) ∗
          (((out + 8#64) ↦₆₄ s1.readReg64 .x25) ∗
           ((out + 16#64) ↦₆₄ s1.readReg64 .x26) ∗
           ((out + 24#64) ↦₆₄ v216) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hst (sepConj_mono_left htail)) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60_placed (A := A) (F := F) (ext := ext) s0 s2 out err v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

theorem v6hr_sub_ok_dealloc_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym)
      (rustDeallocSpec A) :=
  v1_dealloc_ok_at_statesFromPb_placed hA

theorem v6hr_proto_decoder_dealloc_body_10348_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = cnt →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10336#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          sm.readReg64 .x23 = cnt ∧
          sm.readReg64 .x20 = cur + 8#64) := by
  have hdealloc := v6hr_sub_ok_dealloc_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun hpres hx23 hx20
  rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  change s.pc = (blkPl_333).base + 10348#64 at hpc
  have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10336#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
        sm.readReg64 .x23 = cnt ∧
        sm.readReg64 .x20 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by rw [hsp]; ac_rfl)) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v6hr_proto_decoder_dealloc_loop_10348_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 10348#64 →
      s.status = .Running →
      v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val →
      s.readReg64 .x23 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x20 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 10372#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val) := by
  have hbody := v6hr_proto_decoder_dealloc_body_10348_placed (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x25_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx23 hx20
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 10336#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
        sm.readReg64 .x23 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x20 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx23 hx20) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx23_1, hx20_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx23_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx21_1, hx28_1, hx25_1, htrace_1⟩
      change s1.pc = (blkPl_333).base + 10336#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10372#64) s1 _ _
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx23_1
      refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 10348#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x20 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx21_1, hx28_1, hx25_1, htrace_1⟩
        change s1.pc = (blkPl_333).base + 10336#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10348#64) s1 _ _
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx23_2, hx20_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx23_2 hx20_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v6hr_states_from_pb_dealloc_proto_decoder_10324_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10324#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val) := by
  have hdealloc := v6hr_sub_ok_dealloc_placed (A := A) (ext := ext) hA
  have hloop := v6hr_proto_decoder_dealloc_loop_10348_placed (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x25_val hfsp_align
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 10372#64)
    (P_mid := (if ptsCap = 0#64 then emp
      else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx23 ⊢
      change s.pc = (blkPl_333).base + 10324#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 10372#64) s _ _
      wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [BitVec.ofNat_eq_ofNat, hcap_ne, ↓reduceIte]
      refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 10348#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
          sm.readReg64 .x23 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x20 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
        change s.pc = (blkPl_333).base + 10324#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 10348#64) s _ _
        wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx23_loop, hx20_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop (bs :: tl) ptsPtr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx23_loop hx20_loop)
        have hsplit : ptsCap.toNat * 24 =
            (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (bs :: tl).length * 24 + (ptsCap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        have hjoin : A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            memRegion ptsPtr ((bs :: tl).length * 24) ∗
            memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
              ((ptsCap.toNat - (bs :: tl).length) * 24) ⊢
            A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24) := by
          rw [hsplit, ProofLib.memRegion_split ptsPtr ((bs :: tl).length * 24)
            ((ptsCap.toNat - (bs :: tl).length) * 24) hbound]
          exact Entails.of_eq (by ac_rfl)
        refine Entails.trans
          (Entails.of_eq (show _ =
            (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
             memRegion ptsPtr ((bs :: tl).length * 24) ∗
             memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
               ((ptsCap.toNat - (bs :: tl).length) * 24)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame by ac_rfl))
          (sepConj_mono_left hjoin)
  · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx21_3, hx28_3, hx25_3, htrace_3⟩
    change s3.pc = (blkPl_333).base + 10372#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10396#64) s3 _ _
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx28_3 ⊢
      wp_steps; wp_done
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      wp_steps
      wp_apply
      wp_done

theorem v6hr_states_from_pb_dealloc_none_proto_decoder_10316_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x25_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 10316#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr noneCap x25_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr noneCap x25_val) := by
  rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
  dsimp only [noneCap] at hx28 ⊢
  change s.pc = (blkPl_333).base + 10316#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 10396#64) s P _
  wp_steps
  wp_done

theorem v6hr_states_from_pb_dealloc_some_proto_decoder_10316_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x25_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 10316#64)
    (hrun : s.status = .Running)
    (hpres : v6hr_Saved10324Preserved s0 s fsp out ptsPtr ptsCap x25_val)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 10396#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val) := by
  have h10324 := v6hr_states_from_pb_dealloc_proto_decoder_10324_placed
    hA s0
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 10324#64)
    (P_mid := (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v6hr_Saved10324Preserved s0 sm fsp out ptsPtr ptsCap x25_val ∧
      sm.readReg64 .x23 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rcases hpres with ⟨hsp, hx19, hx21, hx28, hx25, htrace⟩
    have hne : ¬((ptsCap + 1#64 == 0#64) = true) := cap_add_one_beq_zero_false (by omega)
    change s.pc = (blkPl_333).base + 10316#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10324#64) s _ _
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx23_1⟩
    exact h10324 s1 fsp out ptsPtr ptsCap x25_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx23_1

/-! ## 2. Header Load Step (`+1464 -> +1520` / `+3760`) -/

theorem v6hr_load_headers_1464_none_to_3760_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3760#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          Rest) ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w104 d112 d116 w120) := by
  unfold v6hr_headersAt
  dsimp only [noneCap]
  simp only [sepConj_assoc]
  change s1.pc = (blkPl_333).base + 1464#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 3760#64) s1 _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpb := v6hr_headersAt_entails_dealloc pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 noneCap w96 w104 d112 d116 w120
    unfold v6hr_headersAt at hpb
    dsimp only [noneCap] at hpb
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
         (((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
          ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗
          ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
          ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
          ((pbA + 88#64) ↦₆₄ noneCap) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
          ((pbA + 104#64) ↦₆₄ w104) ∗
          ((pbA + 112#64) ↦₃₂ d112) ∗ ((pbA + 116#64) ↦₃₂ d116) ∗
          ((pbA + 120#64) ↦₆₄ w120)) ∗
         memRegion (pbA + 128#64) 96) ∗
        (((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest) by dsimp only [noneCap]; ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
  · wp_done

theorem v6hr_load_headers_1464_some_eq_to_3760_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3760#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 576#32 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          Rest) ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 576#32 d116 w120) := by
  have hne_w88 := cap_add_one_beq_zero_false hw88
  unfold v6hr_headersAt
  simp only [sepConj_assoc]
  change s1.pc = (blkPl_333).base + 1464#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 3760#64) s1 _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpb := v6hr_headersAt_entails_dealloc pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 576#32 d116 w120
    unfold v6hr_headersAt at hpb
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
         (((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
          ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗
          ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
          ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
          ((pbA + 88#64) ↦₆₄ w88) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
          ((pbA + 104#64) ↦₆₄ w104) ∗
          ((pbA + 112#64) ↦₃₂ 576#32) ∗ ((pbA + 116#64) ↦₃₂ d116) ∗
          ((pbA + 120#64) ↦₆₄ w120)) ∗
         memRegion (pbA + 128#64) 96) ∗
        (((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
  · wp_done

theorem v6hr_load_headers_1464_some_ne_to_1520_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (out pbA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 : BitVec 64)
    (d112 d116 : BitVec 32) (w120 v232 : BitVec 64)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hw88 : w88.toNat < 2 ^ 63)
    (hd112 : (d112 == 576#32) = false)
    (hpc1 : s1.pc = lsmpl.base 333 + 1464#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 1520#64) s1
      (((s0.sp - 2168#64) ↦₆₄ v232) ∗
        (pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
        v6hr_headersAt pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120 ∗
        memRegion (pbA + 128#64) 96 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          ((s0.sp - 2168#64) ↦₆₄ w96) ∗
          memRegion pbA optProtoInnerStateSize ∗
          Rest) ∧
        v6hr_Regs1508 s0 sm out w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w104 d112 d116 w120) := by
  have hne_w88 := cap_add_one_beq_zero_false hw88
  have hd112_ne : ¬((d112 == 576#32) = true) := by rw [hd112]; decide
  unfold v6hr_headersAt
  simp only [sepConj_assoc]
  change s1.pc = (blkPl_333).base + 1464#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 1520#64) s1 _ _
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hpb := v6hr_headersAt_entails_dealloc pbA w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 d112 d116 w120
    unfold v6hr_headersAt at hpb
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ (1#64 <<< 63 ||| 6#64)) ∗
         (((pbA + 8#64) ↦₆₄ w8) ∗ ((pbA + 16#64) ↦₆₄ w16) ∗
          ((pbA + 24#64) ↦₆₄ w24) ∗ ((pbA + 32#64) ↦₆₄ w32) ∗
          ((pbA + 40#64) ↦₆₄ w40) ∗ ((pbA + 48#64) ↦₆₄ w48) ∗
          ((pbA + 56#64) ↦₆₄ w56) ∗ ((pbA + 64#64) ↦₆₄ w64) ∗
          ((pbA + 72#64) ↦₆₄ w72) ∗ ((pbA + 80#64) ↦₆₄ w80) ∗
          ((pbA + 88#64) ↦₆₄ w88) ∗ ((pbA + 96#64) ↦₆₄ w96) ∗
          ((pbA + 104#64) ↦₆₄ w104) ∗
          ((pbA + 112#64) ↦₃₂ d112) ∗ ((pbA + 116#64) ↦₃₂ d116) ∗
          ((pbA + 120#64) ↦₆₄ w120)) ∗
         memRegion (pbA + 128#64) 96) ∗
        (((s0.sp - 2168#64) ↦₆₄ w96) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hpb) (Entails.of_eq (by ac_rfl))
  · wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant6aPlaced (
  v6hr_states_from_pb_err_10396_placed
  v6hr_sub_ok_dealloc_placed
  v6hr_proto_decoder_dealloc_body_10348_placed
  v6hr_proto_decoder_dealloc_loop_10348_placed
  v6hr_states_from_pb_dealloc_proto_decoder_10324_placed
  v6hr_states_from_pb_dealloc_none_proto_decoder_10316_placed
  v6hr_states_from_pb_dealloc_some_proto_decoder_10316_placed
  v6hr_load_headers_1464_none_to_3760_placed
  v6hr_load_headers_1464_some_eq_to_3760_placed
  v6hr_load_headers_1464_some_ne_to_1520_placed
)

end CryptoVerification.SpqrV1.States.FromPb
