/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.UnchunkedFromPbClPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# SPQR V1 `<States>::from_pb`: Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part A

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant7a.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CryptoVerification.SpqrV1.States.FromPb

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
open CryptoVerification.SpqrV1.States.Recv
  (drop_glue_poly16_cl_on drop_glue_poly16_mem_on
   drop_glue_proto_poly_encoder_cl_on drop_glue_proto_poly_encoder_mem_on
   drop_glue_poly_encoder_local2_cl_on drop_glue_poly_encoder_local2_mem_on)
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

open CryptoVerification (blkPC_279 blkPl_279 lsProg_279 blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

variable [LibsignalPlacement]

/-! ## 1. Subroutine Call Bridges for Variant 7 -/

theorem v7_sub_ok_drop_proto_unchunked_ct1_sent_ek_received_placed
    {A : RustAlloc} {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)) :=
  drop_proto_unchunked_ct1_sent_ek_received_cl_on
    (callerProg := lsProg_333 (Rust.withPanics ext)) hA.dealloc

theorem v7_sub_ok_drop_proto_unchunked_ct1_sent_ek_received_mem_placed
    {A : RustAlloc} {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 286)
      (withMemEq m (dropProtoUnchunkedCt1SentEkReceivedSpec A)) :=
  drop_proto_unchunked_ct1_sent_ek_received_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v7_sub_ok_drop_proto_poly_encoder_placed
    {A : RustAlloc} {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec A)) :=
  drop_glue_proto_poly_encoder_cl_on
    (callerProg := lsProg_333 (Rust.withPanics ext)) hA.dealloc

theorem v7_sub_ok_drop_proto_poly_encoder_mem_placed
    {A : RustAlloc} {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 271)
      (withMemEq m (dropProtoPolyEncoderSpec A)) :=
  drop_glue_proto_poly_encoder_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v7_sub_ok_drop_poly16_placed
    {A : RustAlloc} {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec A)) :=
  drop_glue_poly16_cl_on
    (callerProg := lsProg_333 (Rust.withPanics ext)) hA.dealloc

theorem v7_sub_ok_drop_poly16_mem_placed
    {A : RustAlloc} {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 265)
      (withMemEq m (dropGluePoly16Spec A)) :=
  drop_glue_poly16_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v7_sub_ok_drop_poly_encoder_local2_placed
    {A : RustAlloc} {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec A)) :=
  drop_glue_poly_encoder_local2_cl_on
    (callerProg := lsProg_333 (Rust.withPanics ext)) hA.dealloc

theorem v7_sub_ok_drop_poly_encoder_local2_mem_placed
    {A : RustAlloc} {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 272)
      (withMemEq m (dropGluePolyEncoderSpec A)) :=
  drop_glue_poly_encoder_local2_mem_on
    (callerProg := (blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) hA.dealloc hcl

theorem v7_drop_unchunked_ct1_sent_local2_cl_placed_ok
    {A : RustAlloc} {F : ShaCompress} {H : String → Option (State → State)}
    (hdealloc : HookSat H EncoderFromPb.spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_279 H) (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 279)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_unchunked_ct1_sent_local2_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem v7_sub_ok_drop_unchunked_ct1_sent_local2_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec A F)) :=
  ls_subroutine_ok_of_block (v7_drop_unchunked_ct1_sent_local2_cl_placed_ok hA.dealloc) (by decide)

theorem v7_sub_ok_drop_unchunked_ct1_sent_local2_mem_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)} {m : Memory}
    (hA : FromPbAllocHooks A ext) (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 279)
      (withMemEq m (dropUnchunkedCt1SentSpec A F)) :=
  lscall_blk_cl (v7_drop_unchunked_ct1_sent_local2_cl_placed_ok hA.dealloc) hcl (by decide)

theorem v7_sub_ok_encoder_from_pb_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (henc : EncoderFromPbPlacedOkExt A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec A)) :=
  henc

/-- Placed contract hypothesis for `<Ct1Sent>::from_pb` (Block `339`) on `lsProg_333`. -/
def Ct1SentFromPbPlacedOkExt (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 339)
    (withLsCodeLoaded lsmpl (ct1SentFromPbSpec A F))

theorem v7_sub_ok_ct1_sent_from_pb_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hct1 : Ct1SentFromPbPlacedOkExt A F ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 339)
      (withLsCodeLoaded lsmpl (ct1SentFromPbSpec A F)) :=
  hct1

/-! ## 2. Error Exit at `+4632` (`bfi x28, x23, #8, #56; b +7084`) -/

@[local simp, local arm64_norm, local wp_norm]
private theorem v7_bfi_8_56_extractLsb_0_8 (x28 x23 : BitVec 64) :
    (x28 &&& 255#64 ||| (x23 &&& 72057594037927935#64) <<< 8).extractLsb' 0 8 =
      x28.extractLsb' 0 8 := by bv_kernel

/-- Placed error exit at `+4632` (`+4632 -> +7084 -> s0.x30`):
given `(s1.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err`, executes `bfi x28, x23, #8, #56`,
jumps to `+7084`, and returns `Err(err)`. -/
theorem v7_err_4632_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 4632#64)
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
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 7084#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗
      memRegion out chunkedStatesSize ∗
      Rest)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 4632#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7084#64) s1 _ _
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx28_2, htr2⟩
    exact v4_states_from_pb_err_7084_placed s0 s2 out err Rest hsp0_align hpc2 hrun2 hsp2 hx19_2 hx28_2 htr2

/-! ## 3. `ProtoPolynomialDecoder` Inline Deallocation at `+4548..+4632` -/

theorem v7_proto_decoder_dealloc_body_4584_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 4584#64 →
      s.status = .Running →
      v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x25 = cnt →
      s.readReg64 .x27 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 4572#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = cnt ∧
          sm.readReg64 .x27 = cur + 8#64) := by
  have hdealloc := v4_sub_ok_dealloc_125316_placed (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun hpres hx25 hx27
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx28, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  change s.pc = (blkPl_333).base + 4584#64 at hpc
  have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4572#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
        sm.readReg64 .x25 = cnt ∧
        sm.readReg64 .x27 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v7_proto_decoder_dealloc_loop_4584_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 4584#64 →
      s.status = .Running →
      v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x25 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x27 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 4608#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hbody := v7_proto_decoder_dealloc_body_4584_placed (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx25 hx27
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine Drop.seq_clean (mid := lsmpl.base 333 + 4572#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
        sm.readReg64 .x25 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x27 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx25 hx27) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx25_1, hx27_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx25_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx28_1, htrace_1⟩
      change s1.pc = (blkPl_333).base + 4572#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4608#64) s1 _ _
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx25_1
      refine Drop.seq_clean (mid := lsmpl.base 333 + 4584#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x27 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx22_1, hx28_1, htrace_1⟩
        rw [sep_push_body]
        change s1.pc = (blkPl_333).base + 4572#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4584#64) s1 _ _
        wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx25_2, hx27_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx25_2 hx27_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

theorem v7_proto_decoder_dealloc_4560_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 4560#64)
    (hrun : s.status = .Running)
    (hpres : v7_Saved4560Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hdealloc := v4_sub_ok_dealloc_125316_placed (A := A) (ext := ext) hA
  have hloop := v7_proto_decoder_dealloc_loop_4584_placed (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  simp only [rustDeallocSpec] at hdealloc
  refine Drop.seq_clean (mid := lsmpl.base 333 + 4608#64)
    (P_mid := (if ptsCap = 0#64 then emp
      else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx20, hx22, hx28, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx25 ⊢
      change s.pc = (blkPl_333).base + 4560#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 4608#64) s _ _
      wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      dsimp only [BitVec.ofNat_eq_ofNat]
      simp only [hcap_ne, ↓reduceIte]
      refine Drop.seq_clean (mid := lsmpl.base 333 + 4584#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v7_Saved4560Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x25 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x27 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx20, hx22, hx28, htrace⟩
        change s.pc = (blkPl_333).base + 4560#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 4584#64) s _ _
        wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx25_loop, hx27_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop (bs :: tl) ptsPtr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx25_loop hx27_loop)
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
  · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx20_3, hx22_3, hx28_3, htrace_3⟩
    change s3.pc = (blkPl_333).base + 4608#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4632#64) s3 _ _
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22_3 ⊢
      wp_steps; wp_done
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      wp_steps
      wp_apply
      wp_done

/-- Placed `ProtoPolynomialDecoder` deallocation at `pbA + 184#64` starting at `+4556`:
given `x27 = pbA` and `x22 = ptsCap`, loads `ptsPtr, pts.length`, runs the loop `+4560..+4632`,
and collapses `pbA + 184..224` into `memRegion (pbA + 184#64) 40`, reaching `+4632`. -/
theorem v7_proto_decoder_dealloc_4556_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA ptsCap ptsPtr x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 4556#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = ptsCap)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (((pbA + 184#64) ↦₆₄ ptsCap) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         (if ptsCap = 0 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
            arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
            memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
              ((ptsCap.toNat - pts.length) * 24)) ∗
         memRegion (pbA + 208#64) 16) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (sepConj_mono_left (v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64))) ?_
  refine EncoderFromPb.seq_clean
    (mid := lsmpl.base 333 + 4560#64)
    (P_mid :=
      (if ptsCap = 0 then emp
       else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
         memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
           ((ptsCap.toNat - pts.length) * 24)) ∗
      A.pool ∗
      stackAt (s0.sp - 2400#64) allocHookStack ∗
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       ((pbA + 184#64) ↦₆₄ ptsCap) ∗
       ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       memRegion (pbA + 208#64) 16 ∗
       Frame))
    (Q := fun sm =>
      v7_Saved4560Preserved s0 sm (s0.sp - 2400#64) out ptsPtr ptsCap x28_val ∧
      sm.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 4556#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 4560#64) s1 _ _
    wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  · intro s2 hpc2 hrun2 ⟨hpres2, hx25_2⟩
    have h4560 := v7_proto_decoder_dealloc_4560_placed hA s0 s2 (s0.sp - 2400#64) out ptsPtr ptsCap x28_val pts
      (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
       ((pbA + 184#64) ↦₆₄ ptsCap) ∗
       ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
       ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       memRegion (pbA + 208#64) 16 ∗
       Frame)
      hfsp_align hpts_le hpts_cap_lt hpc2 hrun2 hpres2 hx25_2
    refine SepWP.mono h4560 ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, _, _, hx28_f, htr_f⟩
    refine ⟨Entails.trans hPf ?_, hsp_f, hx19_f, hx28_f, htr_f⟩
    have hst := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
    have hhdr := protoPolyDecoderHeaders_entails_memRegion_40
      (pbA + 184#64) ptsCap ptsPtr (BitVec.ofNat 64 pts.length)
    have h192 : (pbA + 184#64) + 8#64 = pbA + 192#64 := by bv_omega
    have h200 : (pbA + 184#64) + 16#64 = pbA + 200#64 := by bv_omega
    have h208 : (pbA + 184#64) + 24#64 = pbA + 208#64 := by bv_omega
    rw [h192, h200, h208] at hhdr
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
        (((pbA + 184#64) ↦₆₄ ptsCap) ∗
         ((pbA + 192#64) ↦₆₄ ptsPtr) ∗
         ((pbA + 200#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         memRegion (pbA + 208#64) 16) ∗
        (A.pool ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hst (sepConj_mono_left hhdr)) (Entails.of_eq (by ac_rfl))

end CryptoVerification.SpqrV1.States.FromPb
