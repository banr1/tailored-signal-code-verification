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
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 9 (`Ct1Acknowledged`, `+444`) — Part A

Shared `+7084` `Err(err)` exit, inline `ProtoPolynomialDecoder` deallocation loop (`+5360..+5440 -> +7084`),
and `uc` error-cleanup paths (`+7024`, `+6904`, `+8588`, `+488`, `+2768`) for Variant 9.
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

theorem v9_sepWPp_seq_clean {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q_regs sm →
      SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _ hpc hrun ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hq))

theorem v9_onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : TraceCalleeSaved sm s0) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]
  apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢
  rw [htrace.1] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

theorem v9_sepWPp_call_ret {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v9_sub_ok_dealloc_125316
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff stubOff_rust_dealloc (by decide))
    hA.dealloc

theorem v9_sub_ok_decoder_from_pb
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderFromPbOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64)
      (decoderFromPbSpec A) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 35448) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_poly_decoder_from_pb (by decide))
    hdec

theorem v9_fnAddr_eq_sub_of_rel {P : Program} {n1 n2 : String} {k : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (hrel : (P.rebase b X).fnAddr n2 = (P.rebase b X).fnAddr n1 + BitVec.ofNat 64 k) :
    (P.rebase b X).fnAddr n1 = (P.rebase b X).fnAddr n2 - BitVec.ofNat 64 k := by
  rw [hrel, BitVec.add_sub_cancel]

theorem v9_stackAt_encoderFromPbStack_to_allocHook (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v9_stackAt_allocHook_to_encoderFromPbStack (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp encoderFromPbStack := by
  have h := ProofLib.stackAt_split_bottom fsp allocHookStack 1056 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Shared `Err(err)` exit at `+7084` (`0x5bc50 -> s0.x30`):
when `x28` has low byte `spqrErrorByte err` and `x19 = out`, writes `x26, x24` to `[out + 16..32]`,
sets `x8 = noneCap`, writes `x28` to `[out + 8]`, and branches to `+60`. -/
theorem v9_states_from_pb_err_7084
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx28_1 : (s1.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err)
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
  · states_from_pb_fetches_range b (Rust.withPanics ext) 7084 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
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
    exact states_from_pb_epilogue_60 s0 s2 out err v0 Rest
      hsp0_align hpc2 hrun2 hsp2 hx8_2 hx19_2 htr2

/-! ## 2. Shared `ProtoPolynomialDecoder` Deallocation Loop (`+5360..+5440 -> +7084`) -/

@[reducible]
def v9_Saved5368Preserved (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x20 = ptsPtr ∧
  s.readReg64 .x21 = ptsCap ∧
  s.readReg64 .x28 = x28_val ∧
  TraceCalleeSaved s s0

theorem v9_proto_decoder_dealloc_body_5392
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = cnt →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5380#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = cnt ∧
          sm.readReg64 .x23 = cur + 8#64) := by
  have hdealloc := v9_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 5392 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro cur cnt bs s Frame hpc hrun hpres hx22 hx23
  rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 5380#64) s
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
    · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v9_proto_decoder_dealloc_loop_5392
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5392#64 →
      s.status = .Running →
      v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x23 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5416#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hbody := v9_proto_decoder_dealloc_body_5392 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  states_from_pb_fetches_range b (Rust.withPanics ext) 5380 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx22 hx23
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine Drop.seq_clean (mid := entry + 5380#64)
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
      wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx22_1
      refine Drop.seq_clean (mid := entry + 5392#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (bs2 :: tl2).length ∧
          sm.readReg64 .x23 = (cur + 24#64) + 8#64)
        ?_ ?_
      · rcases hpres1 with ⟨hsp_1, hx19_1, hx20_1, hx21_1, hx28_1, htrace_1⟩
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

/-- Shared `ProtoPolynomialDecoder` inline deallocation at `+5368 -> +7084` (`0x5b59c -> 0x5bc50`):
when `x21 = ptsCap`, `x20 = ptsPtr`, `x22 = BitVec.ofNat 64 pts.length`, deallocates all `Vec<u8>`
elements in `pts` and the `pts` buffer itself, then jumps to `+7084`. -/
theorem v9_states_from_pb_dealloc_proto_decoder_5368
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have hdealloc := v9_sub_ok_dealloc_125316 (b := b) (A := A) (ext := ext) hA
  have hloop := v9_proto_decoder_dealloc_loop_5392 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x28_val hfsp_align
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 5368 12
  states_from_pb_fetches_range b (Rust.withPanics ext) 5416 28
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 5416#64)
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
      wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    | cons bs tl =>
      have hlen_pos : 0 < (bs :: tl).length := by simp
      have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
        have : (bs :: tl).length * 24 ≤ ptsCap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
        omega
      have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
      have hcap_ne : ptsCap ≠ 0#64 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
      simp only [hcap_ne, ↓reduceIte]
      refine Drop.seq_clean (mid := entry + 5392#64)
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
        wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
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

theorem v9_ptsCap_add_one_ne_zero {ptsCap : BitVec 64} (h : ptsCap.toNat * 24 < 2 ^ 63) :
    ¬((ptsCap + 1#64 == 0#64) = true) := by
  rw [beq_iff_eq]
  intro heq
  have h1 : (ptsCap + 1#64).toNat = 0 := by rw [heq]; rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
  omega

/-- Shared `Option<ProtoPolynomialDecoder>` inline deallocation at `+5360 -> +7084`:
- when `x21 = noneCap` (`0xffffffffffffffff#64`), `cmn x21, #1; b.eq +7084` jumps directly to `+7084`;
- when `x21 = ptsCap` with `ptsCap.toNat * 24 < 2^63`, falls through to `+5368` and deallocates `pts`. -/
theorem v9_states_from_pb_dealloc_none_proto_decoder_5360
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr x28_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr noneCap x28_val) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr noneCap x28_val) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 5360 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  rcases hpres with ⟨hsp, hx19, hx20, hx21, hx28, htrace⟩
  change s.readReg64 .x21 = 0xffffffffffffffff#64 at hx21
  wp_steps
  wp_done

theorem v9_states_from_pb_dealloc_some_proto_decoder_5360
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x28_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out ptsPtr ptsCap x28_val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s
      ((if ptsCap = 0 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap x28_val) := by
  have h5368 := v9_states_from_pb_dealloc_proto_decoder_5368
    hA s0
  states_from_pb_fetches_range b (Rust.withPanics ext) 5360 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at h5368 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 5368#64)
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
    wp_steps
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx22_1⟩
    exact h5368 s1 fsp out ptsPtr ptsCap x28_val pts Frame
      hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx22_1

def v9_Saved7084Preserved (s0 s : State) (fsp out : BitVec 64) : Prop :=
  s.sp = fsp ∧
  s.readReg64 .x19 = out ∧
  s.readReg64 .x28 = 0#64 ∧
  TraceCalleeSaved s s0

/-- Cleanup at `+7024 -> +7084`: drops `ct1` (`cap = [fsp + 128]`, `ptr = [fsp + 72]`)
    and `k1` (`cap = x13`, `ptr = x14`), sets `x28 = 0#64`, and falls through to `+7084`. -/
theorem v9_states_from_pb_drop_uc_7024
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7024#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx13 : s.readReg64 .x13 = k1Cap)
    (hx14 : s.readReg64 .x14 = k1Ptr)
    (hx19 : s.readReg64 .x19 = out)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s
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
  have hdealloc := v9_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 7024 60
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 7060#64)
    (P_mid := ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
      ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
      vecCapPtrDealloc A k1Cap k1Ptr ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x13 = k1Cap ∧
      sm.readReg64 .x14 = k1Ptr ∧ sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [vecCapPtrDealloc]
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
theorem v9_states_from_pb_drop_uc_6904
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6904#64)
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
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s
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
  have hdealloc := v9_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  have h7024 := v9_states_from_pb_drop_uc_7024 hA s0
  states_from_pb_fetches_range b (Rust.withPanics ext) 6904 120
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc h7024 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 6960#64)
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
  · intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx13_1, hx14_1, hx19_1, hx20_1, htrace1⟩
    refine Drop.seq_clean (mid := entry + 6988#64)
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
    · intro s2 hpc2 hrun2 ⟨hsp2, hx13_2, hx14_2, hx19_2, hx20_2, htrace2⟩
      refine Drop.seq_clean (mid := entry + 7024#64)
        (P_mid := ((fsp + 72#64) ↦₆₄ ct1Ptr) ∗
          ((fsp + 128#64) ↦₆₄ ct1Cap) ∗
          vecCapPtrDealloc A ct1Cap ct1Ptr ∗
          vecCapPtrDealloc A k1Cap k1Ptr ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (((fsp + 144#64) ↦₆₄ ekPtr) ∗ ((fsp + 152#64) ↦₆₄ ekCap) ∗ Frame))
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x13 = k1Cap ∧ sm.readReg64 .x14 = k1Ptr ∧
          sm.readReg64 .x19 = out ∧ TraceCalleeSaved sm s0)
        ?_ ?_
      · dsimp only [vecCapPtrDealloc]
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
theorem v9_states_from_pb_drop_uc_8588
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State)
    (fsp out rkPtr rkCap mkPtr mkCap ekPtr ekCap ct1Ptr ct1Cap k1Ptr k1Cap : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8588#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s
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
  have hdealloc := v9_sub_ok_dealloc_125316 hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 7064 20
  states_from_pb_fetches_range b (Rust.withPanics ext) 8588 100
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 8608#64)
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
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, htrace1⟩
    refine Drop.seq_clean (mid := entry + 8632#64)
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
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, htrace2⟩
      refine Drop.seq_clean (mid := entry + 8652#64)
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
      · dsimp only [vecCapPtrDealloc]
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
        refine Drop.seq_clean (mid := entry + 8672#64)
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
        · dsimp only [vecCapPtrDealloc]
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
theorem v9_states_from_pb_drop_proto_uc_none_488
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x22_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = noneCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5368#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 488 8
  states_from_pb_fetches_range b (Rust.withPanics ext) 4516 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  change s.readReg64 .x8 = 0xffffffffffffffff#64 at hx8
  wp_steps
  wp_done

/-- Error path `+2768 -> +4372 -> +5360` when `uc = none` (`x8 = noneCap`).
    Sets `x28 = 0#64` (`spqrErrorByte .stateDecode`) and branches to `+5360`. -/
theorem v9_states_from_pb_uc_none_2768
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out ptsPtr ptsCap x22_val : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2768#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx8 : s.readReg64 .x8 = noneCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64) s P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 0#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 2768 8
  states_from_pb_fetches_range b (Rust.withPanics ext) 4372 8
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  change s.readReg64 .x8 = 0xffffffffffffffff#64 at hx8
  wp_steps
  wp_done

theorem v9_sub_ok_drop_proto_unchunked_ct1_sent
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName - 53780#64)
      (dropProtoUnchunkedCt1SentEkReceivedSpec A) :=
  sub_ok_of_addr_eq
    (v9_fnAddr_eq_sub_of_rel
      (Program.fnAddr_rel (k := 53780) (b := b) (X := Rust.withPanics ext)
        fnOff_drop_proto_ct1_sent_ek_received statesFromPb_fnOff (by decide)))
    (drop_proto_unchunked_ct1_sent_ek_received_ok_ext hA.dealloc)

theorem v9_stackAt_allocHook_to_drop32 (fsp : BitVec 64) :
    stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 ⊢
      stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 := by
  refine Entails.trans (v9_stackAt_allocHook_to_encoderFromPbStack fsp) ?_
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  rw [h]
  exact Entails.of_eq (by ac_rfl)

theorem v9_stackAt_drop32_to_allocHook (fsp : BitVec 64) :
    stackAt fsp dropStack32 ∗ memRegion (fsp - 5152#64) 1024 ⊢
      stackAt fsp allocHookStack ∗ memRegion (fsp - 5152#64) 1056 := by
  have h := ProofLib.stackAt_split_bottom fsp dropStack32 1024 (by decide)
  change stackAt fsp encoderFromPbStack =
    memRegion (fsp - 5152#64) 1024 ∗ stackAt fsp dropStack32 at h
  refine Entails.trans ?_ (v9_stackAt_encoderFromPbStack_to_allocHook fsp)
  rw [h]
  exact Entails.of_eq (by ac_rfl)

/-- Early error path `+488 -> +496 -> +500 -> +5368` when `receivingEk = some d`
    (`d.ptsNeeded ≠ 576#32`) and `uc = some u` (`hdrCap.toNat < 2^63`).
    Calls `0x4ce90` (`drop_glue::<proto::unchunked::Ct1SentEkReceived>`, ICF-shared with `Ct1Sent`)
    with `x0 = ucA`, sets `x28 = 2#64`, and branches to `+5368`. -/
theorem v9_states_from_pb_drop_proto_uc_some_488
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out ucA hdrCap ptsPtr ptsCap x22_val : BitVec 64)
    (u : V1State.Unchunked.Ct1Sent) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hhdr_lt : hdrCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = ucA)
    (hx8 : s.readReg64 .x8 = hdrCap)
    (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = ptsPtr)
    (hx21 : s.readReg64 .x21 = ptsCap)
    (hx22 : s.readReg64 .x22 = x22_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5368#64) s
      (protoUnchunkedCt1SentAt A ucA u ∗
        A.pool ∗ stackAt fsp dropStack32 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion ucA 128 ∗ A.pool ∗ stackAt fsp dropStack32 ∗ Frame) ∧
        v9_Saved5368Preserved s0 sm fsp out ptsPtr ptsCap 2#64 ∧
        sm.readReg64 .x22 = x22_val) := by
  have hdrop := v9_sub_ok_drop_proto_unchunked_ct1_sent hA
  simp only [dropProtoUnchunkedCt1SentEkReceivedSpec, protoUnchunkedCt1SentEkReceivedSize] at hdrop
  have hhdr_ne := cap_add_one_beq_zero_false hhdr_lt
  states_from_pb_fetches_range b (Rust.withPanics ext) 488 20
  dsimp only [tripleRatchetProgAtExt, dropProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdrop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  change SepWP _ _ _
    (protoUnchunkedCt1SentEkReceivedAt A ucA
      { es := u.hdr, ek := u.es, ct1 := u.ct1, auth := u.auth, epoch := u.epoch } ∗
      A.pool ∗ stackAt fsp dropStack32 ∗ Frame) _
  wp_steps
  wp_apply
  wp_steps
  wp_done

theorem v9_stackAt_encoderFromPbStack_eq_decoderFromPb (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack =
      stackAt fsp decoderFromPbStack ∗
        memRegion (fsp - 5152#64) (encoderFromPbStack - decoderFromPbStack) := by
  have h := ProofLib.stackAt_split_bottom fsp decoderFromPbStack (encoderFromPbStack - decoderFromPbStack) (by decide)
  rw [show decoderFromPbStack + (encoderFromPbStack - decoderFromPbStack) = encoderFromPbStack by decide,
      show BitVec.ofNat 64 encoderFromPbStack = 5152#64 by decide, sepConj_comm] at h
  exact h

theorem v9_memRegion_loBytes7_gap_at (a o1 o2 : BitVec 64) (k : Nat)
    (ho : o1 + 7#64 = o2 := by rfl)
    (hk : 8 + k ≤ 2 ^ 64 := by decide) :
    ProofLib.memRegion (a + o1) (7 + (1 + k)) ⊢
      (∃∗ u0 : BitVec 64, ((a + o1) ↦ₛ EncoderFromPb.loBytes7 u0)) ∗
      ProofLib.memRegion (a + o2) (1 + k) := by
  have h1 : 7 + (1 + k) = 8 + k := by omega
  rw [h1, ProofLib.memRegion_split' (b := a + o1) (n := 8) (k := k)
    (b' := a + o1 + 8#64) rfl rfl hk,
    ProofLib.memRegion_eight (a + o1), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u0
  rw [pointsTo64_split_7_1 (a + o1) u0, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_right u0 (sepConj_mono_right ?_)
  have ha7 : a + o1 + 7#64 = a + o2 := by rw [BitVec.add_assoc, ho]
  have ha8 : a + o1 + 8#64 = a + o2 + 1#64 := by rw [← ha7]; bv_omega
  rw [ha7, ha8, ProofLib.memRegion_split' (b := a + o2) (n := 1) (k := k)
    (b' := a + o2 + 1#64) rfl rfl (by omega)]
  exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)

theorem v9_memRegion_entails_bs :
    ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 →
      ProofLib.memRegion a n ⊢
        ∃∗ bs : { l : List (BitVec 8) // l.length = n }, (a ↦ₛ bs.val)
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]
    refine Entails.sepExists_right ⟨[], rfl⟩ ?_
    rw [ProofLib.pointsToBytes_nil]; exact Entails.refl _
  | n + 1, a, hn => by
    have hsplit : n + 1 = 1 + n := by omega
    rw [hsplit, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a,
        sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    refine Entails.trans (sepConj_mono_right (v9_memRegion_entails_bs n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ⟨bs, hlen⟩
    refine Entails.sepExists_right ⟨b0 :: bs, by simp [hlen]; omega⟩ ?_
    rw [ProofLib.pointsToBytes_cons]; exact Entails.refl _

theorem v9_loBytes7_64_313_entails_bs328 (fsp u240 ep : BitVec 64) :
    ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 u240) ∗
      ((fsp + 247#64) ↦₆₄ ep) ∗
      memRegion (fsp + 255#64) 313 ⊢
    ∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val) := by
  refine Entails.trans ?_ (v9_memRegion_entails_bs 328 (fsp + 240#64) (by decide))
  exact collapse_top <|
    collapse_step (loBytes7_entails_memRegion_7 _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    Entails.refl _

theorem v9_memRegion_1888_split_none (fsp : BitVec 64) :
    memRegion fsp 1888 ⊢
      memRegion fsp 72 ∗ (∃∗ w72 : BitVec 64, ((fsp + 72#64) ↦₆₄ w72)) ∗
      memRegion (fsp + 80#64) 16 ∗ (∃∗ d96 : BitVec 32, ((fsp + 96#64) ↦₃₂ d96)) ∗
      memRegion (fsp + 100#64) 28 ∗ (∃∗ w128 : BitVec 64, ((fsp + 128#64) ↦₆₄ w128)) ∗
      memRegion (fsp + 136#64) 8 ∗ (∃∗ w144 : BitVec 64, ((fsp + 144#64) ↦₆₄ w144)) ∗
      (∃∗ w152 : BitVec 64, ((fsp + 152#64) ↦₆₄ w152)) ∗ memRegion (fsp + 160#64) 80 ∗
      (∃∗ w240 : BitVec 64, ((fsp + 240#64) ↦₆₄ w240)) ∗
      ((∃∗ w248 : BitVec 64, ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248)) ∗
       memRegion (fsp + 255#64) 1633) := by
  exact split_top <|
    split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem32_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem64_entails _) <| v9_memRegion_loBytes7_gap_at fsp 248#64 255#64 1632

theorem v9_memRegion_1888_split_some (fsp : BitVec 64) :
    memRegion fsp 1888 ⊢
      memRegion fsp 40 ∗ (∃∗ w40 : BitVec 64, ((fsp + 40#64) ↦₆₄ w40)) ∗
      (∃∗ w48 : BitVec 64, ((fsp + 48#64) ↦₆₄ w48)) ∗
      (∃∗ w56 : BitVec 64, ((fsp + 56#64) ↦₆₄ w56)) ∗
      memRegion (fsp + 64#64) 8 ∗ (∃∗ w72 : BitVec 64, ((fsp + 72#64) ↦₆₄ w72)) ∗
      (∃∗ w80 : BitVec 64, ((fsp + 80#64) ↦₆₄ w80)) ∗
      memRegion (fsp + 88#64) 8 ∗ (∃∗ d96 : BitVec 32, ((fsp + 96#64) ↦₃₂ d96)) ∗
      memRegion (fsp + 100#64) 28 ∗ (∃∗ w128 : BitVec 64, ((fsp + 128#64) ↦₆₄ w128)) ∗
      (∃∗ w136 : BitVec 64, ((fsp + 136#64) ↦₆₄ w136)) ∗
      (∃∗ w144 : BitVec 64, ((fsp + 144#64) ↦₆₄ w144)) ∗
      (∃∗ w152 : BitVec 64, ((fsp + 152#64) ↦₆₄ w152)) ∗
      memRegion (fsp + 160#64) 40 ∗ (∃∗ w200 : BitVec 64, ((fsp + 200#64) ↦₆₄ w200)) ∗
      memRegion (fsp + 208#64) 8 ∗ (∃∗ w216 : BitVec 64, ((fsp + 216#64) ↦₆₄ w216)) ∗
      memRegion (fsp + 224#64) 16 ∗ (∃∗ w240 : BitVec 64, ((fsp + 240#64) ↦₆₄ w240)) ∗
      ((∃∗ w248 : BitVec 64, ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248)) ∗
       memRegion (fsp + 255#64) 641) ∗
      memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 := by
  exact split_top <|
    split_step0 (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem32_entails _) <| split_step (Entails.refl _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <|
    split_step (v9_memRegion_loBytes7_gap_at fsp 248#64 255#64 640) <|
    split_step (Entails.refl _) <| Entails.refl _

theorem v9_memRegion_3044_collapse_err (fsp mkLen hdrLen u240 ep : BitVec 64) (d96 : BitVec 32) :
    (memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen)) ∗
      (((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 8 ∗
       ((fsp + 96#64) ↦₃₂ d96) ∗ memRegion (fsp + 100#64) 28) ∗
      (memRegion (fsp + 224#64) 16 ∗
       ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 u240) ∗ ((fsp + 247#64) ↦₆₄ ep) ∗
       memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
       memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 1888#64) 400 ∗
       memRegion (fsp + 2288#64) 16) ⊢
    memRegion fsp 48 ∗ memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 224#64) 2080 := by
  refine sepConj_mono ?_ (sepConj_mono ?_ ?_)
  · exact collapse_top <| collapse_step0 (Entails.refl _) <| Drop.pointsTo64_entails_memRegion _ _
  · exact collapse_top <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (pointsTo32_entails_memRegion_4 _ _) <| Entails.refl _
  · exact collapse_top <|
      collapse_step (Entails.refl _) <| collapse_step (loBytes7_entails_memRegion_7 _ _) <|
      collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
      collapse_step (Entails.refl _) <| Entails.refl _

theorem v9_memRegion_255_641_split_ok (fsp : BitVec 64) :
    memRegion (fsp + 255#64) 641 ⊢
      memRegion (fsp + 255#64) 313 ∗ memRegion (fsp + 568#64) 8 ∗
      (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗
      ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ q608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ q608)) ∗ (∃∗ q624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ q624)) ∗
      (∃∗ q640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ q640)) ∗ (∃∗ q656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ q656)) ∗
      (∃∗ q672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ q672)) ∗ (∃∗ q688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ q688)) ∗
      (∃∗ q704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ q704)) ∗ (∃∗ q720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ q720)) ∗
      (∃∗ q736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ q736)) ∗ (∃∗ q752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ q752)) ∗
      (∃∗ q768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ q768)) ∗ (∃∗ q784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ q784)) ∗
      (∃∗ q800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ q800)) ∗ (∃∗ q816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ q816)) ∗
      (∃∗ w832 : BitVec 64, ((fsp + 832#64) ↦₆₄ w832)) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ q848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ q848)) ∗
      ((∃∗ w864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864)) ∗ memRegion (fsp + 871#64) 9) ∗
      (∃∗ w880 : BitVec 64, ((fsp + 880#64) ↦₆₄ w880)) ∗
      ((∃∗ w888 : BitVec 64, ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888)) ∗ memRegion (fsp + 895#64) 1) := by
  exact split_top <|
    split_step (Entails.refl _) <| split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (v9_memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem128_entails _) <| split_step (v9_memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <|
    split_step (mem64_entails _) <| v9_memRegion_loBytes7_gap_at fsp 888#64 895#64 0

end CryptoVerification.SpqrV1.States.FromPb

