/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 9 (`Ct1Acknowledged`, `+444`, Block `333`) — Part A

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant9a.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced

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

/-! ## 1. Relocatable Callee Contracts & Shared `Err(err)` Exit at `+7084` -/

theorem v9_sub_ok_dealloc_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
  v1_dealloc_ok_at_statesFromPb_placed hA

theorem v9_sub_ok_decoder_from_pb_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdec : DecoderFromPbPlacedOkExt A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (decoderFromPbSpec A)) :=
  hdec

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_286 (Rust.withPanics ext)) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 286)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_unchunked_ct1_sent_ek_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem v9_sub_ok_drop_proto_unchunked_ct1_sent_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)) :=
  ls_subroutine_ok_of_block (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hA.dealloc) (by decide)

theorem v9_sub_ok_drop_proto_unchunked_ct1_sent_mem_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 286)
      (withMemEq m (dropProtoUnchunkedCt1SentEkReceivedSpec A)) :=
  lscall_blk_cl (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hA.dealloc) hcl (by decide)

/-- Shared `Err(err)` exit at `+7084` (`+7084 -> +60 -> s0.x30`):
    when `x28` has low byte `spqrErrorByte err` and `x19 = out`, writes `x26, x24` to `[out + 16..32]`,
    sets `x8 = noneCap`, writes `x28` to `[out + 8]`, and branches to `+60`. -/
theorem v9_states_from_pb_err_7084_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7084#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx28_1 : (s1.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err)
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
  · change s1.pc = (blkPl_333).base + 7084#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 60#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x28)
        (s1.readReg64 .x26) (s1.readReg64 .x24)
      rw [hx28_1] at htail
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x28) ∗
           ((out + 16#64) ↦₆₄ s1.readReg64 .x26) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x24) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60_placed (A := A) (F := F) (ext := ext) s0 s2 out err v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

/-! ## 2. Shared `ProtoPolynomialDecoder` Deallocation Loop (`+5360..+5440 -> +7084`) -/

theorem v9_proto_decoder_dealloc_body_5392_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = cnt →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5380#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = cnt ∧
          sm.readReg64 .x23 = cur + 8#64) := by
  have hdealloc := v9_sub_ok_dealloc_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun hpres hx22 hx23
  rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  change s.pc = (blkPl_333).base + 5392#64 at hpc
  have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5380#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
        sm.readReg64 .x22 = cnt ∧
        sm.readReg64 .x23 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by rw [hsp]; ac_rfl)) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v9_proto_decoder_dealloc_loop_5392_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 5416#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hbody := v9_proto_decoder_dealloc_body_5392_placed (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 5380#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x23 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx22 hx23) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx22_1, hx23_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx22_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx21_1, hx28_1, htrace_1⟩
      change s1.pc = (blkPl_333).base + 5380#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5416#64) s1 _ _
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx22_1
      refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 5392#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x23 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx21_1, hx28_1, htrace_1⟩
        change s1.pc = (blkPl_333).base + 5380#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5392#64) s1 _ _
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx22_2, hx23_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx22_2 hx23_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Shared `ProtoPolynomialDecoder` inline deallocation at `+5368 -> +7084`:
    when `x21 = ptsCap`, `x20 = ptsPtr`, `x22 = BitVec.ofNat 64 pts.length`, deallocates all `Vec<u8>`
    elements in `pts` and the `pts` buffer itself, then jumps to `+7084`. -/
theorem v9_states_from_pb_dealloc_proto_decoder_5368_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hdealloc := v9_sub_ok_dealloc_placed (A := A) (ext := ext) hA
  have hloop := v9_proto_decoder_dealloc_loop_5392_placed (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 5416#64)
    (P_mid := (if ptsCap = 0#64 then emp
      else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx22 ⊢
      change s.pc = (blkPl_333).base + 5368#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 5416#64) s _ _
      wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [BitVec.ofNat_eq_ofNat, hcap_ne, ↓reduceIte]
      refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 5392#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x23 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
        change s.pc = (blkPl_333).base + 5368#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 5392#64) s _ _
        wp_steps; refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx22_loop, hx23_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop (bs :: tl) ptsPtr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx22_loop hx23_loop)
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
  · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx20_3, hx21_3, hx28_3, htrace_3⟩
    change s3.pc = (blkPl_333).base + 5416#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7084#64) s3 _ _
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx21_3 ⊢
      wp_steps; wp_done
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      wp_steps
      wp_apply
      wp_steps
      wp_done

/-- Shared `Option<ProtoPolynomialDecoder>` inline deallocation at `+5360 -> +7084` when `x21 = noneCap`. -/
theorem v9_states_from_pb_dealloc_none_proto_decoder_5360_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x28_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr noneCap x28_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr noneCap x28_val) := by
  rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
  change s.readReg64 .x21 = 0xffffffffffffffff#64 at hx21
  change s.pc = (blkPl_333).base + 5360#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7084#64) s _ _
  wp_steps
  wp_done

theorem v9_states_from_pb_dealloc_some_proto_decoder_5360_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have h5368 := v9_states_from_pb_dealloc_proto_decoder_5368_placed
    hA s0
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 5368#64)
    (P_mid := (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
    have hne := v9_ptsCap_add_one_ne_zero hpts_cap_lt
    change s.pc = (blkPl_333).base + 5360#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5368#64) s _ _
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx22_1⟩
    exact h5368 s1 fsp out ptsPtr ptsCap x28_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx22_1

/-! ## 3. Shared `uc` Cleanup Paths (`+7024`, `+6904`, `+8588`, `+488`, `+2768`) -/

/-- Cleanup at `+7024 -> +7084`: drops `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`)
    and `k1` (`cap = x13`, `ptr = x14`), sets `x28 = 0#64`, and falls through to `+7084`. -/
theorem v9_states_from_pb_drop_uc_7024_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 7024#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx13 : s.readReg64 .x13 = k1Cap)
    (hx14 : s.readReg64 .x14 = k1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A k1Cap k1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v9_Saved7084Preserved s0 sm fsp out) := by
  have hdealloc := v9_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 7060#64)
    (P_mid := ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      vecCapPtrDealloc A k1Cap k1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x13 = k1Cap ∧
      sm.readReg64 .x14 = k1Ptr ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s.pc = (blkPl_333).base + 7024#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7060#64) s _ _
    dsimp only [vecCapPtrDealloc]
    by_cases hct1 : (ct1Cap == 0#64) = true
    · simp only [hct1, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_done
    · have hct1_f : (ct1Cap == 0#64) = false := Bool.eq_false_iff.mpr hct1
      simp only [hct1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      wp_steps
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx13_1, hx14_1, hx19_1, htrace1⟩
    change s1.pc = (blkPl_333).base + 7060#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7084#64) s1 _ _
    dsimp only [vecCapPtrDealloc]
    by_cases hk1 : (k1Cap == 0#64) = true
    · simp only [hk1, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_done
    · have hk1_f : (k1Cap == 0#64) = false := Bool.eq_false_iff.mpr hk1
      simp only [hk1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      wp_steps
      wp_done

/-- Cleanup at `+6904 -> +7084`: drops `rootKey` (`cap = x10`, `ptr = x28`),
    `macKey` (`cap = x1`, `ptr = x0`), `ek` (`cap = [fsp + 152]`, `ptr = [fsp + 144]`),
    `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`), and `k1` (`cap = x13`, `ptr = x14`),
    sets `x28 = 0#64`, and falls through to `+7084`. -/
theorem v9_states_from_pb_drop_uc_6904_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 6904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr)
    (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap)
    (hx13 : s.readReg64 .x13 = k1Cap)
    (hx14 : s.readReg64 .x14 = k1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        vecCapPtrDealloc A rkCap rkPtr ∗
        vecCapPtrDealloc A mkCap mkPtr ∗
        vecCapPtrDealloc A ekCap ekPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A k1Cap k1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 144#64) ↦₆₄ ekPtr) ∗
          ((fsp + 152#64) ↦₆₄ ekCap) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v9_Saved7084Preserved s0 sm fsp out) := by
  have hdealloc := v9_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  have h7024 := v9_states_from_pb_drop_uc_7024_placed hA s0
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 6960#64)
    (P_mid := ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 144#64) ↦₆₄ ekPtr) ∗
      ((fsp + 152#64) ↦₆₄ ekCap) ∗
      vecCapPtrDealloc A mkCap mkPtr ∗
      vecCapPtrDealloc A ekCap ekPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr ∗
      vecCapPtrDealloc A k1Cap k1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = mkPtr ∧ sm.readReg64 .x1 = mkCap ∧
      sm.readReg64 .x13 = k1Cap ∧ sm.readReg64 .x14 = k1Ptr ∧
      sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = ekCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s.pc = (blkPl_333).base + 6904#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6960#64) s _ _
    dsimp only [vecCapPtrDealloc]
    by_cases hrk : (rkCap == 0#64) = true
    · simp only [hrk, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_done
    · have hrk_f : (rkCap == 0#64) = false := Bool.eq_false_iff.mpr hrk
      simp only [hrk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      wp_steps
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx13_1, hx14_1, hx19_1, hx20_1, htrace1⟩
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 6988#64)
      (P_mid := ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        vecCapPtrDealloc A ekCap ekPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A k1Cap k1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x13 = k1Cap ∧ sm.readReg64 .x14 = k1Ptr ∧
        sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = ekCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 6960#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 6988#64) s1 _ _
      dsimp only [vecCapPtrDealloc]
      by_cases hmk : (mkCap == 0#64) = true
      · simp only [hmk, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps
        wp_done
      · have hmk_f : (mkCap == 0#64) = false := Bool.eq_false_iff.mpr hmk
        simp only [hmk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        wp_steps
        wp_apply
        wp_steps
        wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx13_2, hx14_2, hx19_2, hx20_2, htrace2⟩
      refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 7024#64)
        (P_mid := ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          vecCapPtrDealloc A ct1Cap ct1Ptr ∗
          vecCapPtrDealloc A k1Cap k1Ptr ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (((fsp + 144#64) ↦₆₄ ekPtr) ∗ ((fsp + 152#64) ↦₆₄ ekCap) ∗ Frame))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x13 = k1Cap ∧ sm.readReg64 .x14 = k1Ptr ∧
          sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 6988#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 7024#64) s2 _ _
        dsimp only [vecCapPtrDealloc]
        by_cases hek : (ekCap == 0#64) = true
        · simp only [hek, ↓reduceIte, emp_sepConj, sepConj_emp]
          wp_steps
          wp_done
        · have hek_f : (ekCap == 0#64) = false := Bool.eq_false_iff.mpr hek
          simp only [hek_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
          wp_steps
          wp_apply
          wp_steps
          wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx13_3, hx14_3, hx19_3, htrace3⟩
        have hcall := h7024 s3 fsp out ct1Ptr ct1Cap k1Ptr k1Cap
          (((fsp + 144#64) ↦₆₄ ekPtr) ∗ ((fsp + 152#64) ↦₆₄ ekCap) ∗ Frame)
          hfsp_align hpc3 hrun3 hsp3 hx13_3 hx14_3 hx19_3 htrace3
        refine SepWP.mono hcall ?_
        intro sm Pm _ _ ⟨hPm, hpres⟩
        exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hpres⟩

/-- Cleanup at `+8588 -> +7084`: drops `rootKey` (`cap = [fsp + 56]`, `ptr = x28`),
    `macKey` (`cap = [fsp + 216]`, `ptr = [fsp + 136]`), `ek` (`cap = [fsp + 152]`, `ptr = [fsp + 144]`),
    `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`), and `k1` (`cap = [fsp + 48]`, `ptr = [fsp + 200]`),
    sets `x28 = 0#64`, and branches to `+7084`. -/
theorem v9_states_from_pb_drop_uc_8588_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 333 + 8588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7084#64) s
      (((fsp + 48#64) ↦₆₄ k1Cap) ∗
        ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A rkCap rkPtr ∗
        vecCapPtrDealloc A mkCap mkPtr ∗
        vecCapPtrDealloc A ekCap ekPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A k1Cap k1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 48#64) ↦₆₄ k1Cap) ∗
          ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 144#64) ↦₆₄ ekPtr) ∗
          ((fsp + 152#64) ↦₆₄ ekCap) ∗
          ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v9_Saved7084Preserved s0 sm fsp out) := by
  have hdealloc := v9_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 8608#64)
    (P_mid := ((fsp + 48#64) ↦₆₄ k1Cap) ∗
      ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 136#64) ↦₆₄ mkPtr) ∗
      ((fsp + 144#64) ↦₆₄ ekPtr) ∗
      ((fsp + 152#64) ↦₆₄ ekCap) ∗
      ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
      ((fsp + 216#64) ↦₆₄ mkCap) ∗
      vecCapPtrDealloc A mkCap mkPtr ∗
      vecCapPtrDealloc A ekCap ekPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr ∗
      vecCapPtrDealloc A k1Cap k1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s.pc = (blkPl_333).base + 8588#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 8608#64) s _ _
    dsimp only [vecCapPtrDealloc]
    by_cases hrk : (rkCap == 0#64) = true
    · simp only [hrk, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_done
    · have hrk_f : (rkCap == 0#64) = false := Bool.eq_false_iff.mpr hrk
      simp only [hrk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, htrace1⟩
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 8632#64)
      (P_mid := ((fsp + 48#64) ↦₆₄ k1Cap) ∗
        ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ ekPtr) ∗
        ((fsp + 152#64) ↦₆₄ ekCap) ∗
        ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A ekCap ekPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        vecCapPtrDealloc A k1Cap k1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = ekCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · change s1.pc = (blkPl_333).base + 8608#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 8632#64) s1 _ _
      dsimp only [vecCapPtrDealloc]
      by_cases hmk : (mkCap == 0#64) = true
      · simp only [hmk, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps
        wp_done
      · have hmk_f : (mkCap == 0#64) = false := Bool.eq_false_iff.mpr hmk
        simp only [hmk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        wp_steps
        wp_apply
        wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, htrace2⟩
      refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 8652#64)
        (P_mid := ((fsp + 48#64) ↦₆₄ k1Cap) ∗
          ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 144#64) ↦₆₄ ekPtr) ∗
          ((fsp + 152#64) ↦₆₄ ekCap) ∗
          ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗
          vecCapPtrDealloc A ct1Cap ct1Ptr ∗
          vecCapPtrDealloc A k1Cap k1Ptr ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · change s2.pc = (blkPl_333).base + 8632#64 at hpc2
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 8652#64) s2 _ _
        dsimp only [vecCapPtrDealloc]
        by_cases hek : (ekCap == 0#64) = true
        · simp only [hek, ↓reduceIte, emp_sepConj, sepConj_emp]
          wp_steps
          wp_done
        · have hek_f : (ekCap == 0#64) = false := Bool.eq_false_iff.mpr hek
          simp only [hek_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
          wp_steps
          wp_apply
          wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, htrace3⟩
        refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 8672#64)
          (P_mid := ((fsp + 48#64) ↦₆₄ k1Cap) ∗
            ((fsp + 56#64) ↦₆₄ rkCap) ∗
            ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
            ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
            ((fsp + 136#64) ↦₆₄ mkPtr) ∗
            ((fsp + 144#64) ↦₆₄ ekPtr) ∗
            ((fsp + 152#64) ↦₆₄ ekCap) ∗
            ((fsp + 200#64) ↦₆₄ k1Ptr) ∗
            ((fsp + 216#64) ↦₆₄ mkCap) ∗
            vecCapPtrDealloc A k1Cap k1Ptr ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
          ?_ ?_
        · change s3.pc = (blkPl_333).base + 8652#64 at hpc3
          change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
            ((blkPl_333).base + 8672#64) s3 _ _
          dsimp only [vecCapPtrDealloc]
          by_cases hct1 : (ct1Cap == 0#64) = true
          · simp only [hct1, ↓reduceIte, emp_sepConj, sepConj_emp]
            wp_steps
            wp_done
          · have hct1_f : (ct1Cap == 0#64) = false := Bool.eq_false_iff.mpr hct1
            simp only [hct1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
            wp_steps
            wp_apply
            wp_done
        · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, htrace4⟩
          change s4.pc = (blkPl_333).base + 8672#64 at hpc4
          change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
            ((blkPl_333).base + 7084#64) s4 _ _
          dsimp only [vecCapPtrDealloc]
          by_cases hk1 : (k1Cap == 0#64) = true
          · simp only [hk1, ↓reduceIte, emp_sepConj, sepConj_emp]
            wp_steps
            wp_done
          · have hk1_f : (k1Cap == 0#64) = false := Bool.eq_false_iff.mpr hk1
            simp only [hk1_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
            wp_steps
            wp_apply
            wp_steps
            wp_done

/-- Early error path `+488 -> +4516 -> +5368` when `receivingEk = some d` (`d.ptsNeeded ≠ 576#32`)
    and `uc = none` (`x8 = noneCap`). Sets `x28 = 2#64` (`spqrErrorByte .msgDecode`). -/
theorem v9_states_from_pb_drop_proto_uc_none_488_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x22_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = noneCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5368#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  change s.readReg64 .x8 = 0xffffffffffffffff#64 at hx8
  change s.pc = (blkPl_333).base + 488#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5368#64) s _ _
  wp_steps
  wp_done

/-- Error path `+2768 -> +4372 -> +5360` when `uc = none` (`x8 = noneCap`).
    Sets `x28 = 0#64` (`spqrErrorByte .stateDecode`) and branches to `+5360`. -/
theorem v9_states_from_pb_uc_none_2768_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x22_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 2768#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = noneCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5360#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  change s.readReg64 .x8 = 0xffffffffffffffff#64 at hx8
  change s.pc = (blkPl_333).base + 2768#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 5360#64) s _ _
  wp_steps
  wp_done

/-- Early error path `+488 -> +496 -> +500 -> +5368` when `receivingEk = some d`
    (`d.ptsNeeded ≠ 576#32`) and `uc = some u` (`hdrCap.toNat < 2^63`).
    Calls Block `279` (`drop_glue::<proto::unchunked::Ct1SentEkReceived>`, ICF-shared with `Ct1Sent`)
    with `x0 = ucA`, sets `x28 = 2#64`, and branches to `+5368`. -/
theorem v9_states_from_pb_drop_proto_uc_some_488_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ucA hdrCap ptsPtr ptsCap x22_val : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hhdr_lt : hdrCap.toNat < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = ucA)
    (hx8 : s.readReg64 .x8 = hdrCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 5368#64) s
      (protoUnchunkedCt1SentAt A ucA u ∗
        A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion ucA 128 ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  have hhdr_ne := cap_add_one_beq_zero_false hhdr_lt
  refine seq_clean_lscl hcl
    (mid := lsmpl.base 333 + 496#64)
    (P_mid := protoUnchunkedCt1SentEkReceivedAt A ucA
      { es := u.hdr, ek := u.es, ct1 := u.ct1, auth := u.auth, epoch := u.epoch } ∗
      A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = ucA ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = ptsPtr ∧ sm.readReg64 .x21 = ptsCap ∧
      sm.readReg64 .x22 = x22_val ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · change s.pc = (blkPl_333).base + 488#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 496#64) s
      (protoUnchunkedCt1SentEkReceivedAt A ucA
        { es := u.hdr, ek := u.es, ct1 := u.ct1, auth := u.auth, epoch := u.epoch } ∗
        A.pool ∗ stackAt fsp dropStack32 ∗ Frame) _
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1, htr1⟩
    have hdrop := v9_sub_ok_drop_proto_unchunked_ct1_sent_mem_placed hA hcl1
    simp only [withMemEq, dropProtoUnchunkedCt1SentEkReceivedSpec,
      protoUnchunkedCt1SentEkReceivedSize] at hdrop
    change s1.pc = (blkPl_333).base + 496#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 5368#64) s1 _ _
    wp_steps
    wp_call hdrop ⟨ucA, { es := u.hdr, ek := u.es, ct1 := u.ct1, auth := u.auth, epoch := u.epoch }⟩
    wp_steps
    wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9aPlaced (
  v9_sub_ok_dealloc_placed
  v9_sub_ok_decoder_from_pb_placed
  v9_sub_ok_drop_proto_unchunked_ct1_sent_placed
  v9_sub_ok_drop_proto_unchunked_ct1_sent_mem_placed
  v9_states_from_pb_err_7084_placed
  v9_proto_decoder_dealloc_body_5392_placed
  v9_proto_decoder_dealloc_loop_5392_placed
  v9_states_from_pb_dealloc_proto_decoder_5368_placed
  v9_states_from_pb_dealloc_none_proto_decoder_5360_placed
  v9_states_from_pb_dealloc_some_proto_decoder_5360_placed
  v9_states_from_pb_drop_uc_7024_placed
  v9_states_from_pb_drop_uc_6904_placed
  v9_states_from_pb_drop_uc_8588_placed
  v9_states_from_pb_drop_proto_uc_none_488_placed
  v9_states_from_pb_uc_none_2768_placed
  v9_states_from_pb_drop_proto_uc_some_488_placed
)

end CryptoVerification.SpqrV1.States.FromPb
