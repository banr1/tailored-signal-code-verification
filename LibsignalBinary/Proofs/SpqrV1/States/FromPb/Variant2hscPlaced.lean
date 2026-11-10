/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsc
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 2 (`HeaderSent`, `+508`) — Part C

Relocatable Block-`333` error exits (`+9224`, `+9228`), inline `ProtoPolynomialDecoder`
deallocation (`+4428..+4512`), and `+9152 -> +9228` cleanup chain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm] v2hsc_bv_add_add_lit

theorem v2hsc_sub_ok_dealloc_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
  v1_dealloc_ok_at_statesFromPb_placed hA

/-! ## Error Exit Tails (`+9228 -> s0.x30` and `+9224 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
theorem v2hsc_err_exit_9228_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9228#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
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
  · change s1.pc = (blkPl_333).base + 9228#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 60#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hbfm : ((s1.readReg64 .x23 &&& 255#64 |||
          (s1.readReg64 .x26 &&& 72057594037927935#64) <<< 8).extractLsb' 0 8) =
          spqrErrorByte err := by
        rw [v2hsc_bfm_loByte_eq, hx23_1]
      have htail := out_8_32_entails_err_tail out
        (s1.readReg64 .x23 &&& 255#64 ||| (s1.readReg64 .x26 &&& 72057594037927935#64) <<< 8)
        (s1.readReg64 .x25) (s1.readReg64 .x21)
      rw [hbfm] at htail
      refine Entails.trans (Entails.of_eq (show _ =
        (((out + 8#64) ↦₆₄ (s1.readReg64 .x23 &&& 255#64 |||
            (s1.readReg64 .x26 &&& 72057594037927935#64) <<< 8)) ∗
         ((out + 16#64) ↦₆₄ s1.readReg64 .x25) ∗
         ((out + 24#64) ↦₆₄ s1.readReg64 .x21) ∗
         memRegion (out + 32#64) 896) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗
         (out ↦₆₄ v0) ∗
         Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60_placed (A := A) (F := F) (ext := ext)
      s0 s2 out err v0 Rest hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

set_option maxHeartbeats 800000 in
theorem v2hsc_err_exit_9224_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9224#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : (s1.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
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
  have hsp_split : memRegion (s0.sp - 2400#64) 2304 =
      memRegion (s0.sp - 2400#64) 232 ∗
      (∃∗ w232 : BitVec 64, ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232)) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 := by
    rw [ProofLib.memRegion_split (s0.sp - 2400#64) 232 2072 (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 2400#64 + 232#64) (n := 8) (k := 2064)
          (b' := s0.sp - 2400#64 + 240#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (s0.sp - 2400#64 + 232#64)]
  rw [hsp_split]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w232
  have hm2304 : memRegion (s0.sp - 2400#64) 232 ∗
      ((s0.sp - 2400#64 + 232#64) ↦₆₄ w232) ∗
      memRegion (s0.sp - 2400#64 + 240#64) 2064 ⊢
      memRegion (s0.sp - 2400#64) 2304 :=
    collapse_top <| collapse_step0 (Entails.refl _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 9228#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 9224#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9228#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · simp only [arm64_norm] at hm2304 ⊢
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (s0.sp - 2400#64) 232 ∗
         ((s0.sp - 2168#64) ↦₆₄ w232) ∗
         memRegion (s0.sp - 2160#64) 2064) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm2304) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, htr2⟩
    exact v2hsc_err_exit_9228_placed (A := A) (F := F) (ext := ext)
      s0 s2 out err Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 htr2

/-! ## Shared `ProtoPolynomialDecoder` Deallocation (`+4428..+4512 -> +9228`) -/

theorem v2hsc_proto_decoder_dealloc_body_4460_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_333).base + 4460#64 →
      s.status = .Running →
      v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4448#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x24 = cur + 8#64) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun hpres hx21 hx24
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) ((blkPl_333).base + 4448#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        sm.readReg64 .x21 = cnt ∧
        sm.readReg64 .x24 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v2hsc_proto_decoder_dealloc_loop_4460_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_333).base + 4460#64 →
      s.status = .Running →
      v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4484#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hbody := v2hsc_proto_decoder_dealloc_body_4460_placed
    hA s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx21 hx24
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine Drop.seq_clean (mid := (blkPl_333).base + 4448#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x24 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx21 hx24) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx21_1, hx24_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx23_1, htrace_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine Drop.seq_clean (mid := (blkPl_333).base + 4460#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x24 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx23_1, htrace_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx21_2, hx24_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx21_2 hx24_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- `ProtoPolynomialDecoder` inline deallocation (`+4436 -> +4484`):
when `x22 = ptsCap`, `x20 = ptsPtr`, `x21 = BitVec.ofNat 64 pts.length`, deallocates all `Vec<u8>`
elements in `pts` and reaches `+4484`. -/
theorem v2hsc_dealloc_proto_decoder_4436_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4436#64)
    (hrun : s.status = .Running)
    (hpres : v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4484#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hloop := v2hsc_proto_decoder_dealloc_loop_4460_placed
    hA s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  change s.pc = (blkPl_333).base + 4436#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 4484#64) s _ _
  cases pts with
  | nil =>
    rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htrace⟩
    simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, arrayAt, emp_sepConj] at hx21 ⊢
    wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
  | cons bs tl =>
    have hlen_pos : 0 < (bs :: tl).length := by simp
    have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
      have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
      omega
    have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
    have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
    simp only [BitVec.ofNat_eq_ofNat, hcap_ne, ↓reduceIte]
    refine Drop.seq_clean (mid := (blkPl_333).base + 4460#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
           ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
         Frame))
      (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x24 = ptsPtr + 8#64)
      ?_ ?_
    · rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htrace⟩
      wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx21_loop, hx24_loop⟩
      refine SepWP.strengthen_entails_const ?_
        (hloop (bs :: tl) ptsPtr s_loop _
          (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
          hx21_loop hx24_loop)
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

/-- `ProtoPolynomialDecoder` inline deallocation (`+4484 -> +9228`):
loads `x21` from `[fsp + 232]`, deallocates the outer `pts` buffer if `ptsCap ≠ 0`, and jumps to `+9228`. -/
theorem v2hsc_dealloc_proto_decoder_4484_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4484#64)
    (hrun : s.status = .Running)
    (hpres : v2hsc_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s
      ((if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  change s.pc = (blkPl_333).base + 4484#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9228#64) s _ _
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htrace⟩
  by_cases hc : ptsCap = 0#64
  · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
    simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22 ⊢
    wp_steps; wp_done
  · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
    have hlsl := cap_mul_24 hpts_cap_lt
    simp only [hc, ↓reduceIte]
    wp_steps
    wp_apply
    wp_steps
    refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_
    wp_done

/-- Shared `Option<ProtoPolynomialDecoder>::Some` inline deallocation at `+4428 -> +9228`:
when `x22 = ptsCap` with `ptsCap.toNat * 24 < 2^63` and stack cells `[fsp + 1040] = ptsPtr`,
`[fsp + 1048] = BitVec.ofNat 64 pts.length`, `[fsp + 232] = w232`, deallocates `pts` and reaches `+9228`. -/
theorem v2hsc_dealloc_some_proto_decoder_4428_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsCap)
    (hx23 : s.readReg64 .x23 = x23_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s
      (((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (if ptsCap = 0 then emp
         else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
           memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
             ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
          ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = x23_val ∧
        TraceCalleeSaved sm s0) := by
  have h4436 := v2hsc_dealloc_proto_decoder_4436_placed hA s0
  have h4484 := v2hsc_dealloc_proto_decoder_4484_placed hA s0
  change s.pc = (blkPl_333).base + 4428#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9228#64) s _ _
  refine Drop.seq_clean (mid := (blkPl_333).base + 4436#64)
    (P_mid := (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 232#64) ↦₆₄ w232) ∗
         ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
    (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
      sm.readReg64 .x21 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx21_1⟩
    refine Drop.seq_clean (mid := (blkPl_333).base + 4484#64)
      (P_mid := (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
           ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
      (Q := fun sm => v2hsc_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val)
      ?_ ?_
    · have h1 := h4436 s1 fsp out ptsPtr ptsCap x23_val pts
        (((fsp + 232#64) ↦₆₄ w232) ∗
         ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
        hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx21_1
      exact SepWP.mono h1 fun sm Pm _ _ ⟨hPm, hpres_m⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hpres_m⟩
    · intro s2 hpc2 hrun2 hpres2
      have h2 := h4484 s2 fsp out ptsPtr ptsCap x23_val w232
        (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
        hfsp_align hpts_cap_lt hpc2 hrun2 hpres2
      refine SepWP.mono h2 fun sm Pm _ _ ⟨hPm, hsp_m, hx19_m, _, _, hx23_m, htr_m⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hsp_m, hx19_m, hx23_m, htr_m⟩

/-- Cleanup at `+9212 -> +9228`: sets `w23 = 0` (`spqrErrorByte .stateDecode = 0#8`),
deallocates `optDec` at `fsp + 1032..1072` if `some`, and reaches `+9228`. -/
theorem v2hsc_cleanup_9212_to_9228_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 w232 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9212#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
        v2hsc_optProtoPolyDecoderHeap A optDec d0 d8 d16 d24 d28 d32 ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  cases optDec with
  | none =>
    dsimp only [v2hsc_optProtoPolyDecoderHeap]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ⌜d0 = noneCap⌝ ∗
      (stackAt fsp encoderFromPbStack ∗
       v2hsc_optProtoPolyDecoderWordsAt (fsp + 1032#64) d0 d8 d16 d24 d28 d32 ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
    apply ProofLib.SepWP.pure_elim; intro hd0
    subst hd0
    dsimp only [noneCap] at hpc1 hx22_1 ⊢
    change s1.pc = (blkPl_333).base + 9212#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9228#64) s1 _ _
    wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  | some pb =>
    refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by ac_rfl))
        (v2hsc_optProtoDecoder_some_pre A fsp pb d0 d8 d16 d24 d28 d32 w232
          (memRegion (fsp - 5152#64) 1056 ∗ Frame))) ?_
    apply ProofLib.SepWP.pure_elim; rintro ⟨rfl, hpts_le, hpts_cap_lt⟩
    have hd0_ne := v2hsc_ptsCap_add_one_ne_zero hpts_cap_lt
    refine Drop.seq_clean
      (mid := lsmpl.base 333 + 4428#64)
      (P_mid :=
        ((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ d8) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        (if d0 = 0#64 then emp
         else A.live d8 (d0.toNat * 24) 8 ∗
           arrayAt (fun bs addr => vecU8 A addr bs) 24 d8 pb.pts ∗
           memRegion (d8 + BitVec.ofNat 64 (pb.pts.length * 24)) ((d0.toNat - pb.pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 1032#64) ↦₆₄ d0) ∗
         ((fsp + 1056#64) ↦₃₂ d24) ∗
         ((fsp + 1060#64) ↦₃₂ d28) ∗
         ((fsp + 1064#64) ↦₆₄ d32) ∗
         (memRegion (fsp - 5152#64) 1056 ∗ Frame)))
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 9212#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4428#64) s1 _ _
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx23_2, htr2⟩
      have h4428 := v2hsc_dealloc_some_proto_decoder_4428_placed hA s0 s2 fsp
        out d8 d0 0#64 w232 pb.pts
        (((fsp + 1032#64) ↦₆₄ d0) ∗
         ((fsp + 1056#64) ↦₃₂ d24) ∗
         ((fsp + 1060#64) ↦₃₂ d28) ∗
         ((fsp + 1064#64) ↦₆₄ d32) ∗
         (memRegion (fsp - 5152#64) 1056 ∗ Frame))
        hfsp_align hpts_le hpts_cap_lt hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 htr2
      refine SepWP.mono h4428 fun sm Pm _ _ ⟨hPm, hsp_m, hx19_m, hx23_m, htr_m⟩ => ?_
      refine ⟨Entails.trans hPm ?_, hsp_m, hx19_m, hx23_m, htr_m⟩
      have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
      dsimp only [v2hsc_optProtoPolyDecoderWordsAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 1032#64) ↦₆₄ d0) ∗
           ((fsp + 1040#64) ↦₆₄ d8) ∗
           ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           ((fsp + 1056#64) ↦₃₂ d24) ∗
           ((fsp + 1060#64) ↦₃₂ d28) ∗
           ((fsp + 1064#64) ↦₆₄ d32) ∗
           ((fsp + 232#64) ↦₆₄ w232) ∗
           A.pool ∗ Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hst) (Entails.of_eq (by ac_rfl))

/-- Deallocate `(ca3, pa3)` at `+9192 -> +9212` (`cbz x26, +9212; ldr x0, [sp, #176]; mov x1, x26; mov w2, #1; bl __rust_dealloc`). -/
theorem v2hsc_cleanup_9192_to_9212_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out d0 ca3 pa3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc] at ⊢
  change s1.pc = (blkPl_333).base + 9192#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9212#64) s1 _ _
  by_cases hca3 : (ca3 == 0#64) = true <;>
    simp only [hca3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine EncoderFromPb.align_pre (sepConj_mono_left hst) ?_
    wp_done
  · wp_steps
    wp_apply
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp1]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗ A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left hst
    · wp_done

/-- Deallocate non-empty `(ca2, pa2)` at `+9184 -> +9192` (`mov w2, #1; bl __rust_dealloc`). -/
theorem v2hsc_cleanup_9184_to_9192_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 : BitVec 64)
    (Frame : SepProp)
    (hca2 : (ca2 == 0#64) = false)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9184#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx1_1 : s1.readReg64 .x1 = ca2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9192#64) s1
      (stackAt fsp encoderFromPbStack ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x26 = ca3 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  refine SepWP.weaken_pre
    (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
  have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
  dsimp only [vecCapPtrDealloc] at ⊢
  change s1.pc = (blkPl_333).base + 9184#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9192#64) s1 _ _
  simp only [hca2, Bool.false_eq_true, ↓reduceIte]
  wp_steps
  wp_apply
  refine EncoderFromPb.align_pre ?_ ?_
  · rw [hsp1]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
        (A.pool ∗ Frame) by ac_rfl)) ?_
    exact sepConj_mono_left hst
  · wp_done

/-- Deallocate `(ca2, pa2)` and `(ca3, pa3)` at `+9176 -> +9212`. -/
theorem v2hsc_cleanup_9176_to_9212_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out d0 ca2 pa2 ca3 pa3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9176#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 9192#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗
      (((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · by_cases hca2 : (ca2 == 0#64) = true
    · dsimp only [vecCapPtrDealloc] at ⊢
      change s1.pc = (blkPl_333).base + 9176#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 9192#64) s1 _ _
      simp only [hca2, ↓reduceIte, emp_sepConj]
      wp_steps
      refine Drop.align_pre (by ac_rfl) ?_
      wp_done
    · have hca2_f : (ca2 == 0#64) = false := Bool.eq_false_iff.mpr hca2
      refine EncoderFromPb.seq_clean
        (mid := lsmpl.base 333 + 9184#64)
        (P_mid :=
          stackAt fsp encoderFromPbStack ∗
          vecCapPtrDealloc A ca2 pa2 ∗
          A.pool ∗
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A ca3 pa3 ∗
           (((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = pa2 ∧
          sm.readReg64 .x1 = ca2 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x22 = d0 ∧
          sm.readReg64 .x26 = ca3 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · change s1.pc = (blkPl_333).base + 9176#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 9184#64) s1 _ _
        wp_steps
        refine Drop.align_pre (by ac_rfl) ?_
        wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx22_2, hx26_2, htr2⟩
        have h9184 := v2hsc_cleanup_9184_to_9192_placed hA s0 s2 fsp out d0 ca2 pa2 ca3
          (((fsp + 176#64) ↦₆₄ pa3) ∗
           vecCapPtrDealloc A ca3 pa3 ∗
           (((fsp + 232#64) ↦₆₄ ca2) ∗ Frame))
          hca2_f hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx22_2 hx26_2 htr2
        exact SepWP.mono h9184 fun sm Pm _ _ ⟨hPm, hq⟩ =>
          ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9192 := v2hsc_cleanup_9192_to_9212_placed hA s0 s2 fsp out d0 ca3 pa3
      (((fsp + 232#64) ↦₆₄ ca2) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    exact SepWP.mono h9192 fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩

/-- Cleanup at `+9152 -> +9212` (`sendingEk = none`): deallocates `(ca1, pa1)` (`x25 = ca1`,
`[sp + 1272] = pa1`), `(ca2, pa2)` (`[sp + 232] = ca2`, `x0 / [sp + 184] = pa2`),
and `(ca3, pa3)` (`x26 = ca3`, `[sp + 176] = pa3`). -/
theorem v2hsc_cleanup_9152_to_9212_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9152#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = pa2)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = ca1)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  have hdealloc := v2hsc_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 9176#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗
      (((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗ Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x0 = pa2 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · refine SepWP.weaken_pre
      (sepConj_mono_left (v2hsc_stackAt_encoderFromPbStack_to_allocHook fsp)) ?_
    have hst := v2hsc_stackAt_allocHook_to_encoderFromPbStack fsp
    rw [show vecCapPtrDealloc A ca1 pa1 =
      (if (ca1 == 0#64) = true then emp else A.live pa1 ca1.toNat 1 ∗ memRegion pa1 ca1.toNat) from rfl]
    change s1.pc = (blkPl_333).base + 9152#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9176#64) s1 _ _
    by_cases hca1 : (ca1 == 0#64) = true <;>
      simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A ca2 pa2 ∗
             vecCapPtrDealloc A ca3 pa3 ∗
             A.pool ∗
             (((fsp + 1272#64) ↦₆₄ pa1) ∗
              ((fsp + 184#64) ↦₆₄ pa2) ∗ Frame)) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
    · wp_steps
      wp_apply
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [hsp1]
        refine Entails.trans
          (Entails.of_eq (show _ =
            (stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056) ∗
            (((fsp + 232#64) ↦₆₄ ca2) ∗
             ((fsp + 176#64) ↦₆₄ pa3) ∗
             vecCapPtrDealloc A ca2 pa2 ∗
             vecCapPtrDealloc A ca3 pa3 ∗
             A.pool ∗
             (((fsp + 1272#64) ↦₆₄ pa1) ∗
              ((fsp + 184#64) ↦₆₄ pa2) ∗ Frame)) by ac_rfl)) ?_
        exact sepConj_mono_left hst
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9176 := v2hsc_cleanup_9176_to_9212_placed hA s0 s2 fsp out d0 ca2 pa2 ca3 pa3
      (((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx0_2 hx19_2 hx22_2 hx26_2 htr2
    exact SepWP.mono h9176 fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlaced
  (v2hsc_sub_ok_dealloc_placed
   v2hsc_err_exit_9228_placed
   v2hsc_err_exit_9224_placed
   v2hsc_proto_decoder_dealloc_body_4460_placed
   v2hsc_proto_decoder_dealloc_loop_4460_placed
   v2hsc_dealloc_proto_decoder_4436_placed
   v2hsc_dealloc_proto_decoder_4484_placed
   v2hsc_dealloc_some_proto_decoder_4428_placed
   v2hsc_cleanup_9212_to_9228_placed
   v2hsc_cleanup_9192_to_9212_placed
   v2hsc_cleanup_9184_to_9192_placed
   v2hsc_cleanup_9176_to_9212_placed
   v2hsc_cleanup_9152_to_9212_placed)

end CryptoVerification.SpqrV1.States.FromPb
