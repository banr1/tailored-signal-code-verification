/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5a
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpiloguePlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 5 (`NoHeaderReceived`, `+1344`) — Part A

Relocatable Block-`333` OOM cold path (`+11596`), `+6500` error exit, and inline
`ProtoPolynomialDecoder` deallocation (`+6420..+6500`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlaced

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
open CryptoVerification.SpqrV1
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Relocatable Callee Contracts & OOM Cold Path (`v5a_*_placed`) -/

theorem v5a_sub_ok_dealloc_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) :=
  v1_dealloc_ok_at_statesFromPb_placed hA

theorem v5a_sub_ok_decoder_from_pb_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdec : DecoderFromPbPlacedOkExt A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376)
      (withLsCodeLoaded lsmpl (decoderFromPbSpec A)) :=
  hdec

/-- Shared OOM cold path at `+11596` (`mov w0, #1; mov x1, x27; bl handle_error`). -/
theorem v5a_states_from_pb_oom_11596_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (target_pc : BitVec 64) (P R : SepProp)
    (Q : State → SepProp → Prop)
    (hpc : s.pc = lsmpl.base 333 + 11596#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_333 (Rust.withPanics ext)) target_pc s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  have hpanic := fromPb_externAt?_handleError hA
  change s.pc = (blkPl_333).base + 11596#64 at hpc
  change SepWPp ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext)) target_pc s P Q _
  apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
  unfold statesFromPbOnPanic
  exact Satisfies.mono
    (sepConj_mono_left (Entails.pure_right
      (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *]))
      (entails_anyHeap _))) hm

/-! ## Shared Error Exit at `+6500` & `ProtoPolynomialDecoder` Deallocation Loop (`+6420..+6500`) -/

set_option maxHeartbeats 800000 in
/-- Shared `Err(err)` exit at `+6500` (`+6500 -> +60 -> s0.x30`):
loads `x9` from `[sp, #216]`, sets `x8 = noneCap`, stores `x27` to `[out + 8]` and `x8, x9` to `[out + 16..32]`,
and branches to `+60`. -/
theorem v5a_states_from_pb_err_6500_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 6500#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : (s1.readReg64 .x27).extractLsb' 0 8 = spqrErrorByte err)
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
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (v5a_memRegion_2304_split_216 (s0.sp - 2400#64)))) ?_
  rw [memRegion_out_928_split_32 out]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v24
  apply ProofLib.SepWP.exists_left; intro v16
  apply ProofLib.SepWP.exists_left; intro v8
  apply ProofLib.SepWP.exists_left; intro v0
  apply ProofLib.SepWP.exists_left; intro w216
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
  · change s1.pc = (blkPl_333).base + 6500#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 60#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x27) noneCap w216
      rw [hx27_1] at htail
      have hstack := v5a_memRegion_2304_join_216 (s0.sp - 2400#64) w216
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x27) ∗
           ((out + 16#64) ↦₆₄ noneCap) ∗
           ((out + 24#64) ↦₆₄ w216) ∗
           memRegion (out + 32#64) 896) ∗
          (memRegion (s0.sp - 2400#64) 216 ∗
           (((s0.sp - 2400#64) + 216#64) ↦₆₄ w216) ∗
           memRegion ((s0.sp - 2400#64) + 224#64) 2080) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono htail (sepConj_mono_left hstack))
        (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60_placed (A := A) (F := F) (ext := ext)
      s0 s2 out err v0 Rest hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

theorem v5a_proto_decoder_dealloc_body_6452_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = lsmpl.base 333 + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = cnt →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 6440#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          sm.readReg64 .x28 = cnt ∧
          sm.readReg64 .x21 = cur + 8#64) := by
  have hdealloc := v5a_sub_ok_dealloc_placed hA
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun hpres hx28 hx21
  rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
  change s.pc = (blkPl_333).base + 6452#64 at hpc
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6440#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
        sm.readReg64 .x28 = cnt ∧
        sm.readReg64 .x21 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v5a_proto_decoder_dealloc_loop_6452_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = lsmpl.base 333 + 6452#64 →
      s.status = .Running →
      v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val →
      s.readReg64 .x28 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (lsProg_333 (Rust.withPanics ext))
        (lsmpl.base 333 + 6476#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val) := by
  have hbody := v5a_proto_decoder_dealloc_body_6452_placed hA s0 fsp out ptsPtr ptsCap x27_val hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx28 hx21
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine Drop.seq_clean (mid := lsmpl.base 333 + 6440#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x21 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx28 hx21) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx28_1, hx21_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx28_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx22_1, hx23_1, hx27_1, htrace_1⟩
      change s1.pc = (blkPl_333).base + 6440#64 at hpc1
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 6476#64) s1 _ _
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx28_1
      refine Drop.seq_clean (mid := lsmpl.base 333 + 6452#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x21 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx22_1, hx23_1, hx27_1, htrace_1⟩
        change s1.pc = (blkPl_333).base + 6440#64 at hpc1
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6452#64) s1 _ _
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx28_2, hx21_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx28_2 hx21_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Shared `ProtoPolynomialDecoder` inline deallocation at `+6428 -> +6500`:
when `x23 = ptsCap`, `x22 = ptsPtr`, `x28 = BitVec.ofNat 64 pts.length`, deallocates all `Vec<u8>`
elements in `pts` and the `pts` buffer itself, then reaches `+6500`. -/
theorem v5a_states_from_pb_dealloc_proto_decoder_6428_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6428#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val) := by
  have hdealloc := v5a_sub_ok_dealloc_placed hA
  have hloop := v5a_proto_decoder_dealloc_loop_6452_placed hA s0 fsp out ptsPtr ptsCap x27_val hfsp_align
  simp only [rustDeallocSpec] at hdealloc
  refine Drop.seq_clean (mid := lsmpl.base 333 + 6476#64)
    (P_mid := (if ptsCap = 0#64 then emp
      else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx28 ⊢
      change s.pc = (blkPl_333).base + 6428#64 at hpc
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 6476#64) s _ _
      wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [BitVec.ofNat_eq_ofNat, hcap_ne, ↓reduceIte]
      refine Drop.seq_clean (mid := lsmpl.base 333 + 6452#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
          sm.readReg64 .x28 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x21 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
        change s.pc = (blkPl_333).base + 6428#64 at hpc
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 6452#64) s _ _
        wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx28_loop, hx21_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop (bs :: tl) ptsPtr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx28_loop hx21_loop)
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
  · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx22_3, hx23_3, hx27_3, htrace_3⟩
    change s3.pc = (blkPl_333).base + 6476#64 at hpc3
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6500#64) s3 _ _
    by_cases hc : ptsCap = 0#64
    · have hc_beq : (ptsCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
      simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx23_3 ⊢
      wp_steps; wp_done
    · have hc_beq : ¬((ptsCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      have hlsl := cap_mul_24 hpts_cap_lt
      simp only [hc, ↓reduceIte]
      wp_steps
      wp_apply
      wp_done

theorem v5a_states_from_pb_dealloc_none_proto_decoder_6420_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x27_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = lsmpl.base 333 + 6420#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr noneCap x27_val) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr noneCap x27_val) := by
  rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
  dsimp only [noneCap] at hx23
  change s.pc = (blkPl_333).base + 6420#64 at hpc
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 6500#64) s P _
  wp_steps
  wp_done

theorem v5a_states_from_pb_dealloc_some_proto_decoder_6420_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x27_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = lsmpl.base 333 + 6420#64)
    (hrun : s.status = .Running)
    (hpres : v5a_Saved6428Preserved s0 s fsp out ptsPtr ptsCap x27_val)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 pts.length) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 6500#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val) := by
  have h6428 := v5a_states_from_pb_dealloc_proto_decoder_6428_placed hA s0
  refine Drop.seq_clean (mid := lsmpl.base 333 + 6428#64)
    (P_mid := (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v5a_Saved6428Preserved s0 sm fsp out ptsPtr ptsCap x27_val ∧
      sm.readReg64 .x28 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · rcases hpres with ⟨hsp, hx19, hx22, hx23, hx27, htrace⟩
    have hne := v5a_ptsCap_add_one_ne_zero hpts_cap_lt
    change s.pc = (blkPl_333).base + 6420#64 at hpc
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 6428#64) s _ _
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx28_1⟩
    exact h6428 s1 fsp out ptsPtr ptsCap x27_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx28_1

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlaced

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant5aPlaced (
  v5a_sub_ok_dealloc_placed
  v5a_sub_ok_decoder_from_pb_placed
  v5a_states_from_pb_oom_11596_placed
  v5a_states_from_pb_err_6500_placed
  v5a_proto_decoder_dealloc_body_6452_placed
  v5a_proto_decoder_dealloc_loop_6452_placed
  v5a_states_from_pb_dealloc_proto_decoder_6428_placed
  v5a_states_from_pb_dealloc_none_proto_decoder_6420_placed
  v5a_states_from_pb_dealloc_some_proto_decoder_6420_placed
)

end CryptoVerification.SpqrV1.States.FromPb
