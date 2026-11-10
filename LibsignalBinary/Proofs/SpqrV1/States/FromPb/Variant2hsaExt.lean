/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsa
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant2hsa` -/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open V1State.Chunked
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

open CryptoVerification.SpqrV1.Alloc

namespace Ext4K

private theorem sub_ok_dealloc_125316_4k
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName +
        (bv% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) :=
  hA.dealloc_ok_at statesFromPbName
    (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "__rustc::__rust_dealloc"))

theorem v2hs_proto_decoder_dealloc_body_4460
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4460#64 →
      s.status = .Running →
      v2hs_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4448#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x24 = cur + 8#64) := by
  have hdealloc := sub_ok_dealloc_125316_4k (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 4460 24
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro cur cnt bs s Frame hpc hrun hpres hx21 hx24
  rcases hpres with ⟨hsp, hx19, hx20, hx22, hx23, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap
  apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 4448#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗
        vecCapPtrDealloc A cap vptr) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
        sm.readReg64 .x21 = cnt ∧
        sm.readReg64 .x24 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const
    (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

theorem v2hs_proto_decoder_dealloc_loop_4460
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4460#64 →
      s.status = .Running →
      v2hs_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x24 = cur + 8#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4484#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hbody := v2hs_proto_decoder_dealloc_body_4460 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  states_from_pb_fetches_range b (Rust.withPanics ext) 4448 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hbody ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx21 hx24
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine Drop.seq_clean (mid := entry + 4448#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
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
      refine Drop.seq_clean (mid := entry + 4460#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
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
theorem v2hs_states_from_pb_dealloc_proto_decoder_4436
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4436#64)
    (hrun : s.status = .Running)
    (hpres : v2hs_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 pts.length) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4484#64) s
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
        v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hloop := v2hs_proto_decoder_dealloc_loop_4460 (b := b) (A := A) (ext := ext)
    hA s0 fsp out ptsPtr ptsCap x23_val hfsp_align
  states_from_pb_fetches_range b (Rust.withPanics ext) 4436 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
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
    simp only [hcap_ne, ↓reduceIte]
    refine Drop.seq_clean (mid := entry + 4460#64)
      (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr (bs :: tl) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
         memRegion (ptsPtr + BitVec.ofNat 64 ((bs :: tl).length * 24))
           ((ptsCap.toNat - (bs :: tl).length) * 24) ∗
         Frame))
      (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
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
theorem v2hs_states_from_pb_dealloc_proto_decoder_4484
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4484#64)
    (hrun : s.status = .Running)
    (hpres : v2hs_Saved4436Preserved s0 s fsp out ptsPtr ptsCap x23_val) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s
      ((if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 232#64) ↦₆₄ w232) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val) := by
  have hdealloc := sub_ok_dealloc_125316_4k (b := b) (A := A) (ext := ext) hA
  simp only [rustDeallocSpec] at hdealloc
  states_from_pb_fetches_range b (Rust.withPanics ext) 4484 32
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
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

/-- Shared `Option<ProtoPolynomialDecoder>::Some` inline deallocation at `+4420 -> +9228`:
when `x22 = ptsCap` with `ptsCap.toNat * 24 < 2^63` and stack cells `[fsp + 1040] = ptsPtr`,
`[fsp + 1048] = BitVec.ofNat 64 pts.length`, `[fsp + 232] = w232`, deallocates `pts` and reaches `+9228`. -/
theorem v2hs_states_from_pb_dealloc_some_proto_decoder_4420
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (s0 s : State) (fsp out ptsPtr ptsCap x23_val w232 : BitVec 64)
    (pts : List (List (BitVec 8))) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpts_le : pts.length ≤ ptsCap.toNat)
    (hpts_cap_lt : ptsCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4420#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out)
    (hx22 : s.readReg64 .x22 = ptsCap)
    (hx23 : s.readReg64 .x23 = x23_val)
    (htrace : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s
      (((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
        (if ptsCap = 0#64 then emp
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
  have h4436 := v2hs_states_from_pb_dealloc_proto_decoder_4436 hA s0
  have h4484 := v2hs_states_from_pb_dealloc_proto_decoder_4484 hA s0
  states_from_pb_fetches_range b (Rust.withPanics ext) 4420 16
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at h4436 h4484 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine Drop.seq_clean (mid := entry + 4436#64)
    (P_mid := (if ptsCap = 0#64 then emp
        else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗
          arrayAt (fun bs addr => vecU8 A addr bs) 24 ptsPtr pts ∗
          memRegion (ptsPtr + BitVec.ofNat 64 (pts.length * 24))
            ((ptsCap.toNat - pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 232#64) ↦₆₄ w232) ∗
         ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
    (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val ∧
      sm.readReg64 .x21 = BitVec.ofNat 64 pts.length)
    ?_ ?_
  · have hne := v4_ptsCap_add_one_ne_zero hpts_cap_lt
    wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx21_1⟩
    refine Drop.seq_clean (mid := entry + 4484#64)
      (P_mid := (if ptsCap = 0#64 then emp
          else A.live ptsPtr (ptsCap.toNat * 24) 8 ∗ memRegion ptsPtr (ptsCap.toNat * 24)) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
           ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame))
      (Q := fun sm => v2hs_Saved4436Preserved s0 sm fsp out ptsPtr ptsCap x23_val)
      ?_ ?_
    · have h1 := h4436 s1 fsp out ptsPtr ptsCap x23_val pts
        (((fsp + 232#64) ↦₆₄ w232) ∗
         ((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
        hfsp_align hpts_le hpts_cap_lt hpc1 hrun1 hpres1 hx21_1
      exact SepWP.strengthen_entails_const (Entails.of_eq (by ac_rfl)) h1
    · intro s2 hpc2 hrun2 hpres2
      have h2 := h4484 s2 fsp out ptsPtr ptsCap x23_val w232
        (((fsp + 1040#64) ↦₆₄ ptsPtr) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame)
        hfsp_align hpts_cap_lt hpc2 hrun2 hpres2
      refine SepWP.mono h2 fun sm Pm _ _ ⟨hPm, hsp_m, hx19_m, _, _, hx23_m, htr_m⟩ =>
        ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hsp_m, hx19_m, hx23_m, htr_m⟩

/-- Shared error epilogue from `+4420 -> s0.x30`:
deallocates `receivingCt1` (`optDec`) at `fsp + 1032..1072`, writes `Err(err)` to `out`,
restores callee-saved registers and stack, and returns. -/
theorem v2hs_epilogue_4420_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (out : BitVec 64) (err : LibsignalSpqrV1.Error)
    (optDec : Option ProtoPolynomialDecoder) (d_w0 d_w8 d_w16 d_w24 d_w32 : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4420#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64)
    (hx19 : s.readReg64 .x19 = out) (hx22 : s.readReg64 .x22 = d_w0)
    (hx23 : s.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 1032 ∗
        v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        v2hs_optProtoDecoderHeap A optDec d_w0 d_w8 d_w16 d_w24 d_w32 ∗
        memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          A.pool ∗ Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  have hx23_lo : ((spqrErrorByte err).zeroExtend 64).extractLsb' 0 8 = spqrErrorByte err := by bv_kernel
  cases optDec with
  | none =>
    dsimp only [v2hs_optProtoDecoderHeap, v4b_optProtoPolyDecoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; intro hd_w0; subst hd_w0
    have hcol := v2hs_collapse_frame_2304 (s0.sp - 2400#64) noneCap d_w8 d_w16 d_w24 d_w32
    have hpre_ent :
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 1032 ∗
         v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) noneCap d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (s0.sp - 2400#64 + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ A.pool ∗ Rest) ⊢
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) := by
      refine Entails.trans (Entails.of_eq (show _ =
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        (memRegion (s0.sp - 2400#64) 1032 ∗
         v2hs_optProtoDecoderWordsAt (s0.sp - 2400#64 + 1032#64) noneCap d_w8 d_w16 d_w24 d_w32 ∗
         memRegion (s0.sp - 2400#64 + 1072#64) 1232) ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) by ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hcol)
    refine SepWP.weaken_pre hpre_ent ?_
    have h4420 := v2hs_states_from_pb_dealloc_none_proto_decoder_4420 s0 s
      (s0.sp - 2400#64) out ((spqrErrorByte err).zeroExtend 64)
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest))
      hpc hrun hsp hx19 hx22 hx23 htr
    refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9224#64)
      (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest))
      (Q := fun sm => sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
      h4420 ?_
    intro sm hpcm hrunm ⟨hspm, hx19m, hx23m, htrm⟩
    have hx23m_lo : (sm.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err := by rw [hx23m, hx23_lo]
    have h9224 := v2hs_err_cleanup_9224 (A := A) (F := F) s0 sm out err
      (A.pool ∗ Rest) hsp0_align hpcm hrunm hspm hx19m hx23m_lo htrm
    refine SepWP.mono h9224 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩
  | some pb =>
    dsimp only [v2hs_optProtoDecoderHeap, v4b_optProtoPolyDecoderHeap]
    wp_simp_pre [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, sepConj_comm _ ⌜_⌝]
    apply SepWP.pure_elim; rintro ⟨hd_w16, _, _, hpts_le, hpts_cap_lt, _, _⟩; subst hd_w16
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left (v2hs_memRegion_1032_split_232 (s0.sp - 2400#64)))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w232
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
    let fsp := s0.sp - 2400#64
    let Frame4420 : SepProp :=
      ((fsp + 1032#64) ↦₆₄ d_w0) ∗ ((fsp + 1056#64) ↦₆₄ d_w24) ∗ ((fsp + 1064#64) ↦₆₄ d_w32) ∗
      memRegion fsp 232 ∗ memRegion (fsp + 240#64) 792 ∗ memRegion (fsp - 5152#64) 1056 ∗
      memRegion (fsp + 1072#64) 1232 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ Rest
    have hpre_eq :
        ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗ memRegion fsp 232 ∗
         (((fsp + 232#64) ↦₆₄ w232) ∗ (memRegion (fsp + 240#64) 792 ∗
           (v2hs_optProtoDecoderWordsAt (fsp + 1032#64)
              d_w0 d_w8 (BitVec.ofNat 64 pb.pts.length) d_w24 d_w32 ∗
            ((if d_w0 = 0#64 then emp
              else A.live d_w8 (d_w0.toNat * 24) 8 ∗
                arrayAt (fun bs addr => vecU8 A addr bs) 24 d_w8 pb.pts ∗
                memRegion (d_w8 + BitVec.ofNat 64 (pb.pts.length * 24))
                  ((d_w0.toNat - pb.pts.length) * 24)) ∗
             (memRegion (fsp + 1072#64) 1232 ∗ (statesFromPbSavedCells s0 ∗
               (memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest))))))))) =
        (((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
          ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if d_w0 = 0#64 then emp
           else A.live d_w8 (d_w0.toNat * 24) 8 ∗
             arrayAt (fun bs addr => vecU8 A addr bs) 24 d_w8 pb.pts ∗
             memRegion (d_w8 + BitVec.ofNat 64 (pb.pts.length * 24))
               ((d_w0.toNat - pb.pts.length) * 24)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame4420) := by
      dsimp only [v2hs_optProtoDecoderWordsAt, Frame4420, fsp]
      simp only [arm64_norm]; ac_rfl
    refine SepWP.weaken_pre (Entails.of_eq hpre_eq) ?_
    have h4420 := v2hs_states_from_pb_dealloc_some_proto_decoder_4420 hA s0 s
      fsp out d_w8 d_w0 ((spqrErrorByte err).zeroExtend 64) w232 pb.pts Frame4420
      hfsp_align hpts_le hpts_cap_lt hpc hrun hsp hx19 hx22 hx23 htr
    refine Drop.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64)
      (P_mid := ((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
        ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame4420)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = (spqrErrorByte err).zeroExtend 64 ∧ TraceCalleeSaved sm s0)
      h4420 ?_
    intro sm hpcm hrunm ⟨hspm, hx19m, hx23m, htrm⟩
    have hpost_ent :
        (((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
         ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
         A.pool ∗ stackAt fsp allocHookStack ∗ Frame4420) ⊢
        stackAt fsp encoderFromPbStack ∗ memRegion fsp 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest) := by
      have hre :
          (((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 1040#64) ↦₆₄ d_w8) ∗
           ((fsp + 1048#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
           A.pool ∗ stackAt fsp allocHookStack ∗ Frame4420) =
          ((memRegion (fsp - 5152#64) 1056 ∗ stackAt fsp allocHookStack) ∗
           ((memRegion fsp 232 ∗ ((fsp + 232#64) ↦₆₄ w232) ∗ memRegion (fsp + 240#64) 792) ∗
            v2hs_optProtoDecoderWordsAt (fsp + 1032#64)
              d_w0 d_w8 (BitVec.ofNat 64 pb.pts.length) d_w24 d_w32 ∗
            memRegion (fsp + 1072#64) 1232) ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (A.pool ∗ Rest)) := by
        dsimp only [v2hs_optProtoDecoderWordsAt, Frame4420]
        simp only [arm64_norm]; ac_rfl
      rw [← stackAt_encoderFromPb_split_allocHook fsp] at hre
      refine Entails.trans (Entails.of_eq hre) ?_
      have h1032 := v2hs_memRegion_1032_unsplit_232 fsp w232
      have h2304 := v2hs_collapse_frame_2304 fsp d_w0 d_w8 (BitVec.ofNat 64 pb.pts.length) d_w24 d_w32
      exact sepConj_mono_right (sepConj_mono_left (Entails.trans (sepConj_mono_left h1032) h2304))
    refine SepWP.weaken_pre hpost_ent ?_
    have hx23m_lo : (sm.readReg64 .x23).extractLsb' 0 8 = spqrErrorByte err := by rw [hx23m, hx23_lo]
    have h9228 := v2hs_err_cleanup_9228 (A := A) (F := F) s0 sm out err
      (A.pool ∗ Rest) hsp0_align hpcm hrunm hspm hx19m hx23m_lo htrm
    refine SepWP.mono h9228 fun sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
