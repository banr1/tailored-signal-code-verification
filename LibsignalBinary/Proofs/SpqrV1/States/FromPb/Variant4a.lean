/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 4 (`EkSentCt1Received`, `+248`) — Part A

Shared `+5348` error exit, inline `Option<ProtoPolynomialDecoder>` deallocation (`+5264..+5348`),
and `EkSentCt1Received` cleanup paths (`+304`, `+388`, `+6860`, `+8500`, `+8540`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## Shared `Err(err)` Exit at `+5348` -/

set_option maxHeartbeats 800000 in
/-- Shared `Err(err)` exit at `+5348` (`0x5b588 -> +5944 -> +60 -> s0.x30`):
when `x26` has low byte `spqrErrorByte err` and `x19 = out`, writes `x25, x22` to `[out + 16..32]`,
branches to `+5944`, sets `x8 = noneCap`, writes `x26` to `[out + 8]`, and branches to `+60`. -/
theorem v4_states_from_pb_err_5348
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx26_1 : (s1.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte err)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
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
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 60#64)
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
  · states_from_pb_fetches_range b (Rust.withPanics ext) 5348 8
    states_from_pb_fetches_range b (Rust.withPanics ext) 5944 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htail := out_8_32_entails_err_tail out (s1.readReg64 .x26)
        (s1.readReg64 .x25) (s1.readReg64 .x22)
      rw [hx26_1] at htail
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((out + 8#64) ↦₆₄ s1.readReg64 .x26) ∗
           ((out + 16#64) ↦₆₄ s1.readReg64 .x25) ∗
           ((out + 24#64) ↦₆₄ s1.readReg64 .x22) ∗
           memRegion (out + 32#64) 896) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           memRegion (s0.sp - 2400#64) 2304 ∗
           statesFromPbSavedCells s0 ∗
           (out ↦₆₄ v0) ∗
           Rest) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left htail) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, htr2⟩
    exact states_from_pb_epilogue_60 s0 s2 out err v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

/-! ## Shared `ProtoPolynomialDecoder` Deallocation Loop (`+5264..+5348`) -/

@[reducible]
def v4_Saved5276Preserved (s0 s : State) (fsp out ptsPtr ptsCap x26_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x23 = ptsPtr ∧
  s.readReg64 .x28 = ptsCap ∧
  s.readReg64 .x26 = x26_val ∧
  TraceCalleeSaved s s0

theorem v4_proto_decoder_dealloc_body_5300
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x26_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5300#64 →
      s.status = .Running →
      v4_Saved5276Preserved s0 s fsp out ptsPtr ptsCap x26_val →
      s.readReg64 .x20 = cnt →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5288#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
          sm.readReg64 .x20 = cnt ∧
          sm.readReg64 .x21 = cur + 8#64) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 5300 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro cur cnt bs s Frame hpc hrun hpres hx20 hx21
  rcases hpres with ⟨hsp, hx19, hx23, hx28, hx26, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 5288#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
        sm.readReg64 .x20 = cnt ∧
        sm.readReg64 .x21 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v4_proto_decoder_dealloc_loop_5300
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x26_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5300#64 →
      s.status = .Running →
      v4_Saved5276Preserved s0 s fsp out ptsPtr ptsCap x26_val →
      s.readReg64 .x20 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x21 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5324#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val) := by
  have hbody := v4_proto_decoder_dealloc_body_5300 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x26_val hfsp_align
  states_from_pb_fetches_range b (Rust.withPanics ext) 5288 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx20 hx21
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine Drop.seq_clean (mid := entry + 5288#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
        sm.readReg64 .x20 = BitVec.ofNat 64 (bs :: tl).length ∧
        sm.readReg64 .x21 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx20 hx21) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx20_1, hx21_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx20_1 ⊢
      rcases hpres1 with ⟨hsp_1, hx19_1, hx23_1, hx28_1, hx26_1, htrace_1⟩
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx20_1
      refine Drop.seq_clean (mid := entry + 5300#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x21 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx23_1, hx28_1, hx26_1, htrace_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx20_2, hx21_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx20_2 hx21_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-- Shared `ProtoPolynomialDecoder` inline deallocation at `+5276 -> +5348` (`0x5b540 -> 0x5b588`):
when `x28 = ptsCap`, `x23 = ptsPtr`, `x20 = BitVec.ofNat 64 pts.length`, deallocates all `Vec<u8>`
elements in `pts` and the `pts` buffer itself, then falls through to `+5348`. -/
theorem v4_states_from_pb_dealloc_proto_decoder_5276
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x26_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5276#64)
    (hrun : s.status = .Running)
    (hpres : v4_Saved5276Preserved s0 s fsp out ptsPtr ptsCap x26_val)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5348#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val) := by
  have hdealloc := v4_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  have hloop := v4_proto_decoder_dealloc_loop_5300 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x26_val hfsp_align
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 5276 12
  states_from_pb_fetches_range b (Rust.withPanics ext) 5324 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 5324#64)
    (P_mid := (if ptsCap = 0#64 then emp
      else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val)
    ?_ ?_
  · cases pts with
    | nil =>
      rcases hpres with ⟨hsp, hx19, hx23, hx28, hx26, htrace⟩
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj] at hx20 ⊢
      wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [hcap_ne, ↓reduceIte]
      refine Drop.seq_clean (mid := entry + 5300#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
           memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
             ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
           Frame))
        (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
          sm.readReg64 .x20 = BitVec.ofNat 64 (bs :: tl).length ∧
          sm.readReg64 .x21 = ptsPtr + 8#64)
        ?_ ?_
      · rcases hpres with ⟨hsp, hx19, hx23, hx28, hx26, htrace⟩
        wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx20_loop, hx21_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop (bs :: tl) ptsPtr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx20_loop hx21_loop)
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
  · intro s3 hpc3 hrun3 ⟨hsp_3, hx19_3, hx23_3, hx28_3, hx26_3, htrace_3⟩
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

/-- Shared `Option<ProtoPolynomialDecoder>` inline deallocation at `+5264 -> +5348`:
- when `x28 = noneCap` (`0xffffffffffffffff#64`), `cmn x28, #1; mov x23, x24; b.eq +5348` jumps directly to `+5348`;
- when `x28 = ptsCap` with `ptsCap.toNat * 24 < 2^63`, falls through to `+5276` and deallocates `pts`. -/
theorem v4_states_from_pb_dealloc_none_proto_decoder_5264
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x26_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = noneCap)
    (hx26 : s.readReg64 .x26 = x26_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5348#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr noneCap x26_val) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 5264 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  change s.readReg64 .x28 = 0xffffffffffffffff#64 at hx28
  wp_steps
  wp_done

theorem v4_states_from_pb_dealloc_some_proto_decoder_5264
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x26_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5264#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (hx26 : s.readReg64 .x26 = x26_val)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 pts.length)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5348#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val) := by
  have h5276 := v4_states_from_pb_dealloc_proto_decoder_5276
    hA s0
  states_from_pb_fetches_range b (Rust.withPanics ext) 5264 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at h5276 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 5276#64)
    (P_mid := (if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap x26_val ∧
      sm.readReg64 .x20 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx20_1⟩
    exact h5276 s1 fsp out ptsPtr ptsCap x26_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx20_1

def v4_Saved8540Preserved (s0 s : State) (fsp out : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x26 = 0#64 ∧
  TraceCalleeSaved s s0

/-- Shared cleanup at `+8540 -> +5348`: drops `dk` (`cap = x22`, `ptr = [fsp + 144]`) and
    `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`), sets `x26 = 0#64`, and branches to `+5348`. -/
theorem v4_states_from_pb_drop_uc_8540
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8540#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5348#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        vecCapPtrDealloc A dkCap dkPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 144#64) ↦₆₄ dkPtr) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved8540Preserved s0 sm fsp out) := by
  have hdealloc := v4_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 8540 48
  states_from_pb_fetches_range b (Rust.withPanics ext) 8688 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 8560#64)
    (P_mid := ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 144#64) ↦₆₄ dkPtr) ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
    by_cases hdk : (dkCap == 0#64) = true
    · simp only [hdk, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_done
    · have hdk_f : (dkCap == 0#64) = false := Bool.eq_false_iff.mpr hdk
      simp only [hdk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, htrace1⟩
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

/-- Cleanup at `+8500 -> +5348`: drops `rootKey` (`cap = [fsp + 56]`, `ptr = x26`),
    `macKey` (`cap = [fsp + 216]`, `ptr = [fsp + 136]`), `dk` (`cap = x22`, `ptr = [fsp + 144]`),
    and `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`), sets `x26 = 0#64`, and branches to `+5348`. -/
theorem v4_states_from_pb_drop_uc_8500
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx26 : s.readReg64 .x26 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5348#64) s
      (((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A rkCap rkPtr ∗
        vecCapPtrDealloc A mkCap mkPtr ∗
        vecCapPtrDealloc A dkCap dkPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 144#64) ↦₆₄ dkPtr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved8540Preserved s0 sm fsp out) := by
  have hdealloc := v4_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  have h8540 := v4_states_from_pb_drop_uc_8540 hA s0
  states_from_pb_fetches_range b (Rust.withPanics ext) 8500 40
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc h8540 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 8520#64)
    (P_mid := ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 136#64) ↦₆₄ mkPtr) ∗
      ((fsp + 144#64) ↦₆₄ dkPtr) ∗
      ((fsp + 216#64) ↦₆₄ mkCap) ∗
      vecCapPtrDealloc A mkCap mkPtr ∗
      vecCapPtrDealloc A dkCap dkPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = dkCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
    by_cases hrk : (rkCap == 0#64) = true
    · simp only [hrk, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_done
    · have hrk_f : (rkCap == 0#64) = false := Bool.eq_false_iff.mpr hrk
      simp only [hrk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx22_1, htrace1⟩
    refine Drop.seq_clean (mid := entry + 8540#64)
      (P_mid := ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗
        vecCapPtrDealloc A dkCap dkPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = dkCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc]
      by_cases hmk : (mkCap == 0#64) = true
      · simp only [hmk, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps
        wp_done
      · have hmk_f : (mkCap == 0#64) = false := Bool.eq_false_iff.mpr hmk
        simp only [hmk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        wp_steps
        wp_apply
        wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, htrace2⟩
      have hcall := h8540 s2 fsp out dkPtr dkCap ct1Ptr ct1Cap
        (((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗ Frame)
        hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htrace2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hcall ?_)
      intro sm Pm _ _ ⟨hPm, hpres⟩
      exact ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hpres⟩

/-- Cleanup at `+6860 -> +5348`: drops `rootKey` (`cap = x9`, `ptr = x26`),
    `macKey` (`cap = x1`, `ptr = x0`), `dk` (`cap = x22`, `ptr = [fsp + 144]`),
    and `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`), sets `x26 = 0#64`, and branches to `+5348`. -/
theorem v4_states_from_pb_drop_uc_6860
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6860#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr)
    (hx1 : s.readReg64 .x1 = mkCap)
    (hx9 : s.readReg64 .x9 = rkCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx26 : s.readReg64 .x26 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5348#64) s
      (((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        vecCapPtrDealloc A rkCap rkPtr ∗
        vecCapPtrDealloc A mkCap mkPtr ∗
        vecCapPtrDealloc A dkCap dkPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 144#64) ↦₆₄ dkPtr) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved8540Preserved s0 sm fsp out) := by
  have hdealloc := v4_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  have h8540 := v4_states_from_pb_drop_uc_8540 hA s0
  states_from_pb_fetches_range b (Rust.withPanics ext) 6860 44
  states_from_pb_fetches_range b (Rust.withPanics ext) 8532 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc h8540 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 6896#64)
    (P_mid := ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      ((fsp + 144#64) ↦₆₄ dkPtr) ∗
      vecCapPtrDealloc A mkCap mkPtr ∗
      vecCapPtrDealloc A dkCap dkPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = mkPtr ∧ sm.readReg64 .x1 = mkCap ∧
      sm.readReg64 .x19 = out ∧ sm.readReg64 .x22 = dkCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
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
  · intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx22_1, htrace1⟩
    refine Drop.seq_clean (mid := entry + 8540#64)
      (P_mid := ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
        ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
        ((fsp + 144#64) ↦₆₄ dkPtr) ∗
        vecCapPtrDealloc A dkCap dkPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = dkCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc]
      by_cases hmk : (mkCap == 0#64) = true
      · simp only [hmk, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps
        wp_done
      · have hmk_f : (mkCap == 0#64) = false := Bool.eq_false_iff.mpr hmk
        simp only [hmk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
        wp_steps
        wp_apply
        wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, htrace2⟩
      exact h8540 s2 fsp out dkPtr dkCap ct1Ptr ct1Cap Frame
        hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 htrace2

/-- Early error path `+304 -> +4380 -> +5276` when `receivingCt2 = some d` (`d.ptsNeeded ≠ 80#32`)
    and `uc = none` (`x22 = noneCap`). Sets `x26 = 2#64` (`spqrErrorByte .msgDecode`) and `x23 = ptsPtr`. -/
theorem v4_states_from_pb_drop_proto_uc_none_304
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x20_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx22 : s.readReg64 .x22 = noneCap)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5276#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 304 8
  states_from_pb_fetches_range b (Rust.withPanics ext) 4380 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  change s.readReg64 .x22 = 0xffffffffffffffff#64 at hx22
  wp_steps
  wp_done

/-- Early error path `+388 -> +5276`: drops `dk` (`x22 = dkCap`, `x11 = dkPtr`) and
    `ct1` (`x21 = ct1Cap`, `x12 = ct1Ptr`), sets `x26 = 2#64`, and branches to `+5276`. -/
theorem v4_states_from_pb_drop_proto_uc_388
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State)
    (fsp out ptsPtr ptsCap x20_val dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 388#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx11 : s.readReg64 .x11 = dkPtr)
    (hx12 : s.readReg64 .x12 = ct1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = ct1Cap)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx23 : s.readReg64 .x23 = ptsPtr)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5276#64) s
      (vecCapPtrDealloc A dkCap dkPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  have hdealloc := v4_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 388 56
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 416#64)
    (P_mid := vecCapPtrDealloc A ct1Cap ct1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x12 = ct1Ptr ∧
      sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = x20_val ∧
      sm.readReg64 .x21 = ct1Cap ∧ sm.readReg64 .x23 = ptsPtr ∧
      sm.readReg64 .x28 = ptsCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
    by_cases hdk : (dkCap == 0#64) = true
    · simp only [hdk, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps
      wp_done
    · have hdk_f : (dkCap == 0#64) = false := Bool.eq_false_iff.mpr hdk
      simp only [hdk_f, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      wp_steps
      wp_apply
      wp_steps
      wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx12_1, hx19_1, hx20_1, hx21_1, hx23_1, hx28_1, htrace1⟩
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

/-- Early error path `+304 -> +388 -> +5276` when `uc = some u` (`dkCap.toNat < 2^63`)
    and `u.auth = none` (`x1 = noneCap`). -/
theorem v4_states_from_pb_drop_proto_uc_none_auth_304
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State)
    (fsp out ptsPtr ptsCap x20_val dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hdk_lt : dkCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = noneCap)
    (hx11 : s.readReg64 .x11 = dkPtr)
    (hx12 : s.readReg64 .x12 = ct1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = ct1Cap)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5276#64) s
      (vecCapPtrDealloc A dkCap dkPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  have h388 := v4_states_from_pb_drop_proto_uc_388 hA s0
  have hdk_ne := cap_add_one_beq_zero_false hdk_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 304 20
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at h388 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  change s.readReg64 .x1 = 0xffffffffffffffff#64 at hx1
  refine Drop.seq_clean (mid := entry + 388#64)
    (P_mid := vecCapPtrDealloc A dkCap dkPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x11 = dkPtr ∧
      sm.readReg64 .x12 = ct1Ptr ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x21 = ct1Cap ∧
      sm.readReg64 .x22 = dkCap ∧ sm.readReg64 .x23 = ptsPtr ∧
      sm.readReg64 .x28 = ptsCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx11_1, hx12_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx28_1, htrace1⟩
    exact h388 s1 fsp out ptsPtr ptsCap x20_val dkPtr dkCap ct1Ptr ct1Cap Frame
      hfsp_align hpc1 hrun1 hsp1 hx11_1 hx12_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx28_1 htrace1

/-- Early error path `+304 -> +388 -> +5276` when `uc = some u` (`dkCap.toNat < 2^63`)
    and `u.auth = some auth` (`rkCap.toNat < 2^63`). -/
theorem v4_states_from_pb_drop_proto_uc_some_auth_304
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State)
    (fsp out ptsPtr ptsCap x20_val rkPtr rkCap mkPtr mkCap dkPtr dkCap ct1Ptr ct1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hdk_lt : dkCap.toNat < 2 ^ 63)
    (hrk_lt : rkCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 304#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = rkPtr)
    (hx1 : s.readReg64 .x1 = rkCap)
    (hx11 : s.readReg64 .x11 = dkPtr)
    (hx12 : s.readReg64 .x12 = ct1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_val)
    (hx21 : s.readReg64 .x21 = ct1Cap)
    (hx22 : s.readReg64 .x22 = dkCap)
    (hx24 : s.readReg64 .x24 = ptsPtr)
    (hx25 : s.readReg64 .x25 = mkPtr)
    (hx26 : s.readReg64 .x26 = mkCap)
    (hx28 : s.readReg64 .x28 = ptsCap)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5276#64) s
      (vecCapPtrDealloc A rkCap rkPtr ∗
        vecCapPtrDealloc A mkCap mkPtr ∗
        vecCapPtrDealloc A dkCap dkPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v4_Saved5276Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x20 = x20_val) := by
  have hdealloc := v4_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  have h388 := v4_states_from_pb_drop_proto_uc_388 hA s0
  have hdk_ne := cap_add_one_beq_zero_false hdk_lt
  have hrk_ne := cap_add_one_beq_zero_false hrk_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 304 84
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc h388 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 352#64)
    (P_mid := vecCapPtrDealloc A mkCap mkPtr ∗
      vecCapPtrDealloc A dkCap dkPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x11 = dkPtr ∧
      sm.readReg64 .x12 = ct1Ptr ∧ sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x21 = ct1Cap ∧
      sm.readReg64 .x22 = dkCap ∧ sm.readReg64 .x23 = ptsPtr ∧
      sm.readReg64 .x25 = mkPtr ∧ sm.readReg64 .x26 = mkCap ∧
      sm.readReg64 .x28 = ptsCap ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
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
  · intro s1 hpc1 hrun1 ⟨hsp1, hx11_1, hx12_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx28_1, htrace1⟩
    refine Drop.seq_clean (mid := entry + 388#64)
      (P_mid := vecCapPtrDealloc A dkCap dkPtr ∗
        vecCapPtrDealloc A ct1Cap ct1Ptr ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x11 = dkPtr ∧
        sm.readReg64 .x12 = ct1Ptr ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧ sm.readReg64 .x21 = ct1Cap ∧
        sm.readReg64 .x22 = dkCap ∧ sm.readReg64 .x23 = ptsPtr ∧
        sm.readReg64 .x28 = ptsCap ∧ TraceCalleeSaved sm s0)
      ?_ ?_
    · dsimp only [vecCapPtrDealloc]
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
    · intro s2 hpc2 hrun2 ⟨hsp2, hx11_2, hx12_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx28_2, htrace2⟩
      exact h388 s2 fsp out ptsPtr ptsCap x20_val dkPtr dkCap ct1Ptr ct1Cap Frame
        hfsp_align hpc2 hrun2 hsp2 hx11_2 hx12_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx28_2 htrace2

end CryptoVerification.SpqrV1.States.FromPb

