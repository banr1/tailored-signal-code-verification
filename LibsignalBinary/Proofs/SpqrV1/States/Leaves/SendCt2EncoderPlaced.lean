/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Proof
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::v1::chunked::send_ct::send_ct2_encoder` (Relocatable, Block `382`)

Relocatable `[LibsignalPlacement]` contracts on `lsProg_382 (Rust.withPanics ext)` (`85` instructions):
`send_ct2_encoder_placed_cl_ext` (parameterized by Blocks `320` and `417`) and closed
`send_ct2_encoder_placed_ok_x`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

private theorem hookSat_sessionShim_of_noAllocShim {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym noAllocShimSpec) :
    HookSat H sym sessionShimSpec :=
  HookSat.mono h fun x R _ hpre => ⟨x, R, hpre, fun _ hpost => hpost⟩

private theorem hookSat_sessionMemcpy_of_region {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym sessionMemcpyRegionSpec) :
    HookSat H sym sessionMemcpySpec := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre => ?_
  refine ⟨(dst, src, bs), stackAt s0.sp 4096 ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [sessionMemcpySpec, sessionMemcpyRegionSpec] at hpost ⊢
    ac_nf at hpost ⊢

private theorem encodeBytesSpecX_cl_of_encodeBytesSpec_cl [LibsignalPlacement]
    {P : Program} {addr : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (encodeBytesSpec A))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (encodeBytesSpecX A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcl, hpre0⟩ := extract_withLsCodeLoaded hpre
  have hle : encodeBytesStack ≤ encodeBytesStackX := by decide
  have hsplit : stackAt s0.sp encodeBytesStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
        (encodeBytesStackX - encodeBytesStack) ∗
        stackAt s0.sp encodeBytesStack := by
    have h1 := stackAt_split_bottom s0.sp encodeBytesStack
      (encodeBytesStackX - encodeBytesStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
      (encodeBytesStackX - encodeBytesStack) ∗ R
  have hpre0' : s0.mem ⊨ (encodeBytesSpec A).pre x s0 ∗ R' := by
    dsimp only [encodeBytesSpecX, encodeBytesSpec, R'] at hpre0 ⊢
    rw [hsplit] at hpre0
    ac_nf at hpre0 ⊢
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (encodeBytesSpec A)).pre x s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre0'⟩
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, encodeBytesSpecX, encodeBytesSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeLoaded, encodeBytesSpecX, encodeBytesSpec, R'] at hpost ⊢
    have h1 : (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
          (encodeBytesStackX - encodeBytesStack) ∗ R) ⊢
        (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      rw [sepConj_assoc, sepConj_assoc, ← sepConj_assoc anyHeap]
      exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))
    exact Satisfies.mono h1 hpost
  · dsimp only [withLsCodeLoaded, encodeBytesSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem call_doReserve7Raw_cl [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (doReserveRawSpec A)))
    (v cap ptr : BitVec 64) (bs : Bytes) (additional : Nat)
    (hlen : bs.length ≤ cap.toNat) (hptr : ptr ≠ 0#64)
    (h0 : cap = 0#64 → bs = [])
    (hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = v)
    (hx1 : (s.readReg64 Reg.x1).toNat = bs.length)
    (hx2 : (s.readReg64 Reg.x2).toNat = additional)
    (hx3 : s.readReg64 Reg.x3 = 1#64)
    (hx4 : s.readReg64 Reg.x4 = 1#64)
    (hsplit : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs ∗
      A.pool ∗ stackAt sp_call doReserveStack) ∗ Frame)
    (hnext : ∀ (sf : State) (p' : BitVec 64),
      let newCap := reserveCap cap.toNat bs.length additional
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      p' ≠ 0#64 →
      SepWP prog next_pc sf
        (((v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          A.live p' newCap 1 ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (newCap - bs.length) ∗
          A.pool ∗ stackAt sp_call doReserveStack) ∗ Frame)
        (fun sm Pm =>
          LibsignalCodeLoaded lsmpl sm.mem →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := ⟨v, cap, ptr, bs, additional⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, doReserveRawSpec]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [← slice_and_vecU8Tail_eq_doReserveBuf A cap ptr bs h0]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [withLsCodeLoaded, doReserveRawSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply of_sepWP_lscl hcl_sf (mid := next_pc)
    wp_pull_exists; rename_i p'
    wp_focus_pure; intro hp'
    have hassoc :
        ((v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool ∗ stackAt sp_call doReserveStack) ∗ Frame =
        (v ↦₆₄ BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)) ∗
          ((v + 8#64) ↦₆₄ p') ∗
          A.live p' (reserveCap cap.toNat bs.length additional) 1 ∗
          (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length)
            (reserveCap cap.toNat bs.length additional - bs.length) ∗
          A.pool ∗ stackAt sp_call doReserveStack ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf p' hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hp'

private theorem call_encodeBytesX_cl [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeBytesSpecX A)))
    (out msgA : BitVec 64) (msg : Bytes) (outEnc : PolyEncoder)
    (henc : encodeBytesResult msg = .ok outEnc) (hlen_lt : msg.length < 2 ^ 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = out)
    (hx0 : s.readReg64 Reg.x0 = msgA)
    (hx1 : s.readReg64 Reg.x1 = BitVec.ofNat 64 msg.length)
    (hsplit : P = (memRegion out 400 ∗ (msgA ↦ₛ msg) ∗
      A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine SepWPp.call hcall (x := ⟨out, false, msgA, msg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, encodeBytesSpecX, polyEncoderSize, bytesAt]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hx1, hlen_lt⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [withLsCodeLoaded, encodeBytesSpecX]
    rw [henc, resultPolyEncoderAt, hsp, sepConj_assoc]
    change SepWPp prog (s0.readReg64 Reg.lr) sf
      (⌜sf.trace = s.trace⌝ ∗
        ((polyEncoderAt A out outEnc ∗
          ((msgA ↦ₛ msg) ∗ (A.pool ∗ stackAt sp_call encodeBytesStackX))) ∗ Frame)) post _
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (polyEncoderAt A out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool ∗ stackAt sp_call encodeBytesStackX) ∗ Frame =
        (polyEncoderAt A out outEnc ∗
          ((msgA ↦ₛ msg) ∗ (A.pool ∗ stackAt sp_call encodeBytesStackX))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

private theorem send_ct2_encoder_finish_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (henc_call : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpecX A)))
    (hmemcpy : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (hdealloc : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (outEnc : PolyEncoder)
    (cap ptr w24 d56 : BitVec 64)
    (henc_res : encodeBytesResult (ct2 ++ mac) = .ok outEnc)
    (hlen_le : (ct2 ++ mac).length ≤ 1048576)
    (hcap_le : (ct2 ++ mac).length ≤ cap.toNat)
    (hcap_lt : cap.toNat < 2 ^ 63)
    {s0 s : State} {P R : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_382).base + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 512#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 mac.length)
    (hx21 : s.readReg64 .x21 = ptr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ct2.length)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 400 ∗
       (ct2Ptr ↦ₛ ct2) ∗
       (macPtr ↦ₛ mac) ∗
       (ptr ↦ₛ (ct2 ++ mac)) ∗
       vecU8Tail A cap ptr (ct2 ++ mac) ∗
       ((s0.sp - 504#64) ↦₆₄ cap) ∗
       ((s0.sp - 496#64) ↦₆₄ ptr) ∗
       ((s0.sp - 488#64) ↦₆₄ w24) ∗
       memRegion (s0.sp - 512#64) 8 ∗
       memRegion (s0.sp - 480#64) 400 ∗
       sendCt2SavedCells s0 d56 ∗
       A.pool ∗
       stackAt (s0.sp - 512#64) encodeBytesStackX) ∗ emp) :
    SepWPp ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            polyEncoderAt A outA outEnc ∗
            (ct2Ptr ↦ₛ ct2) ∗
            (macPtr ↦ₛ mac) ∗
            A.pool ∗
            stackAt s0.sp sendCt2EncoderStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  rw [hP, sepConj_emp]
  have hadd_len :
      BitVec.ofNat 64 ct2.length + BitVec.ofNat 64 mac.length =
        BitVec.ofNat 64 (ct2 ++ mac).length := by
    rw [List.length_append, BitVec.ofNat_add]
  have hlen_lt64 : (ct2 ++ mac).length < 2 ^ 64 := by omega
  apply of_sepWP_lscl hcl (mid := lsmpl.base 417)
  wp_steps
  refine call_encodeBytesX_cl henc_call
    (s0.sp - 480#64) ptr (ct2 ++ mac) outEnc henc_res hlen_lt64
    (ret_pc := (blkPl_382).base + 120#64) (sp_call := s0.sp - 512#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
    (by simp only [Reg.x8, arm64_norm, hsp])
    (by simp only [Reg.x0, arm64_norm, hx21])
    (by simp only [Reg.x1, arm64_norm, hx22, hx20, hadd_len])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx22, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  obtain ⟨tag, htag01, encRest, henc_split⟩ := polyEncoderAt_split_tag A (s0.sp - 480#64) outEnc
  rcases htag01 with rfl | rfl
  · wp_conv_pre => rw [henc_split]
    wp_steps
    wp_conv_pre => rw [← henc_split]
    refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
      (Relocatable.of_polyEncoderAt A outEnc) outA (s0.sp - 480#64)
      (ret_pc := (blkPl_382).base + 148#64) (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
      (by simp only [Reg.x0, arm64_norm, hx19_1])
      (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm])
      (by sep_focus)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
    simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
    refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A cap ptr (ct2 ++ mac) hcap_le hcap_lt)
      (by sep_focus) ?_
    dsimp only [vecCapPtrDealloc, sendCt2SavedCells]
    by_cases hcap0 : (cap == 0#64) = true <;>
      simp only [hcap0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · have hcap_eq0 : cap = 0#64 := eq_of_beq hcap0
      subst hcap_eq0
      wp_steps
      refine SepWP.fold (stackAt_512_recompose s0 0#64 ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      wp_done
    · have hcap_ne0 : cap ≠ 0#64 := ne_of_beq_false (Bool.eq_false_iff.mpr hcap0)
      have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero fun h0 =>
        hcap_ne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hlay_dealloc : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
      wp_steps
      refine SepWP.fold (stackAt_512_recompose s0 cap ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      refine SepWP.fold (stackAt_sendCt2Encoder_to_allocHook s0.sp) (by sep_focus) ?_
      wp_apply
      refine SepWP.fold (stackAt_sendCt2Encoder_from_allocHook s0.sp) (by sep_focus) ?_
      wp_done
  · wp_conv_pre => rw [henc_split]
    wp_steps
    wp_conv_pre => rw [← henc_split]
    refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
      (Relocatable.of_polyEncoderAt A outEnc) outA (s0.sp - 480#64)
      (ret_pc := (blkPl_382).base + 148#64) (sp_call := s0.sp - 512#64)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
      (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
      (by simp only [Reg.x0, arm64_norm, hx19_1])
      (by simp only [Reg.x1, arm64_norm, hsp1])
      (by simp only [Reg.x2, arm64_norm])
      (by sep_focus)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
    rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
    simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
    refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A cap ptr (ct2 ++ mac) hcap_le hcap_lt)
      (by sep_focus) ?_
    dsimp only [vecCapPtrDealloc, sendCt2SavedCells]
    by_cases hcap0 : (cap == 0#64) = true <;>
      simp only [hcap0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · have hcap_eq0 : cap = 0#64 := eq_of_beq hcap0
      subst hcap_eq0
      wp_steps
      refine SepWP.fold (stackAt_512_recompose s0 0#64 ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      wp_done
    · have hcap_ne0 : cap ≠ 0#64 := ne_of_beq_false (Bool.eq_false_iff.mpr hcap0)
      have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero fun h0 =>
        hcap_ne0 (BitVec.eq_of_toNat_eq (by simpa using h0))
      have hlay_dealloc : LayoutOk cap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
      wp_steps
      refine SepWP.fold (stackAt_512_recompose s0 cap ptr (BitVec.ofNat 64 (ct2 ++ mac).length) d56)
        (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
      refine SepWP.fold (stackAt_sendCt2Encoder_to_allocHook s0.sp) (by sep_focus) ?_
      wp_apply
      refine SepWP.fold (stackAt_sendCt2Encoder_from_allocHook s0.sp) (by sep_focus) ?_
      wp_done

private theorem send_ct2_encoder_mac_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdr7 : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec A)))
    (henc_call : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpecX A)))
    (hmemcpy : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (hdealloc : subroutine_ok ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (outEnc : PolyEncoder)
    (cap ptr d56 : BitVec 64)
    (henc_res : encodeBytesResult (ct2 ++ mac) = .ok outEnc)
    (hlen_le : (ct2 ++ mac).length ≤ 1048576)
    (hcap_eq : cap.toNat = ct2.length)
    (hptr_ne : ptr ≠ 0#64)
    {s0 s : State} {P R : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_382).base + 208#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 512#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 mac.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 ct2.length)
    (hx23 : s.readReg64 .x23 = macPtr)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 400 ∗
       (ct2Ptr ↦ₛ ct2) ∗
       (macPtr ↦ₛ mac) ∗
       (ptr ↦ₛ ct2) ∗
       vecU8Tail A cap ptr ct2 ∗
       ((s0.sp - 504#64) ↦₆₄ cap) ∗
       ((s0.sp - 496#64) ↦₆₄ ptr) ∗
       ((s0.sp - 488#64) ↦₆₄ BitVec.ofNat 64 ct2.length) ∗
       memRegion (s0.sp - 512#64) 8 ∗
       memRegion (s0.sp - 480#64) 400 ∗
       sendCt2SavedCells s0 d56 ∗
       A.pool ∗
       stackAt (s0.sp - 512#64) encodeBytesStackX) ∗ emp) :
    SepWPp ((blkPC_382).rebase (blkPl_382).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            polyEncoderAt A outA outEnc ∗
            (ct2Ptr ↦ₛ ct2) ∗
            (macPtr ↦ₛ mac) ∗
            A.pool ∗
            stackAt s0.sp sendCt2EncoderStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)) := by
  rw [hP, sepConj_emp]
  have h_finish := send_ct2_encoder_finish_placed henc_call hmemcpy hdealloc
  have hlen_app : (ct2 ++ mac).length = ct2.length + mac.length := List.length_append
  have hct2_lt : ct2.length < 2 ^ 64 := by omega
  have hmac_lt : mac.length < 2 ^ 64 := by omega
  have hct2_toNat : (BitVec.ofNat 64 ct2.length).toNat = ct2.length :=
    Nat.mod_eq_of_lt hct2_lt
  have hmac_toNat : (BitVec.ofNat 64 mac.length).toNat = mac.length :=
    Nat.mod_eq_of_lt hmac_lt
  have h0_imp : cap = 0#64 → ct2 = [] := fun hc0 => by
    subst hc0; exact List.eq_nil_of_length_eq_zero hcap_eq.symm
  let newCap := reserveCap cap.toNat ct2.length mac.length
  have hnew_bound : newCap + 1 ≤ 2 ^ 63 := by
    dsimp [newCap, reserveCap]; omega
  have hnew_ge : ct2.length + mac.length ≤ newCap := by
    dsimp [newCap, reserveCap]; omega
  have hnew_pos : 0 < newCap := by
    dsimp [newCap, reserveCap]; omega
  have hnew_lt63 : newCap < 2 ^ 63 := by omega
  have hnew_toNat : (BitVec.ofNat 64 newCap).toNat = newCap :=
    Nat.mod_eq_of_lt (by omega)
  have hnew_ne0 : BitVec.ofNat 64 newCap ≠ 0#64 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [hnew_toNat] at this
    change newCap = 0 at this
    omega
  apply of_sepWP_lscl hcl (mid := lsmpl.base 320)
  wp_steps
  refine SepWP.fold (stackAt_encodeBytesX_to_doReserve (s0.sp - 512#64)) (by sep_focus) ?_
  refine call_doReserve7Raw_cl hdr7
    (s0.sp - 504#64) cap ptr ct2 mac.length
    (by omega) hptr_ne h0_imp hnew_bound
    (ret_pc := (blkPl_382).base + 232#64) (next_pc := (blkPl_382).base + 100#64) (sp_call := s0.sp - 512#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
    (by simp only [Reg.x0, arm64_norm, hsp])
    (by simp only [Reg.x1, arm64_norm, hx22, hct2_toNat])
    (by simp only [Reg.x2, arm64_norm, hx20, hmac_toNat])
    (by simp only [Reg.x3, arm64_norm])
    (by simp only [Reg.x4, arm64_norm])
    (by sep_focus)
    (fun sf1 p' hpc1 hrun1 hsp1 hcs1 htr1 hp'_ne => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx22, hx23, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (stackAt_encodeBytesX_from_doReserve (s0.sp - 512#64)) (by sep_focus) ?_
  have hmem_split :
      memRegion (p' + BitVec.ofNat 64 ct2.length) (newCap - ct2.length) ⊢
      memRegion (p' + BitVec.ofNat 64 ct2.length) mac.length ∗
      memRegion (p' + BitVec.ofNat 64 (ct2 ++ mac).length) (newCap - (ct2 ++ mac).length) := by
    rw [ProofLib.memRegion_split'
      (b := p' + BitVec.ofNat 64 ct2.length)
      (n := mac.length)
      (k := newCap - (ct2 ++ mac).length)
      (b' := p' + BitVec.ofNat 64 (ct2 ++ mac).length)
      (by omega)
      (by rw [List.length_append, BitVec.ofNat_add, BitVec.add_assoc])
      (by omega)]
    exact Entails.refl _
  refine SepWP.fold hmem_split (by sep_focus) ?_
  wp_steps; wp_apply; wp_steps
  have hjoin_mac :
      A.live p' newCap 1 ∗
        (p' ↦ₛ ct2) ∗
        ((p' + BitVec.ofNat 64 ct2.length) ↦ₛ mac) ∗
        memRegion (p' + BitVec.ofNat 64 (ct2 ++ mac).length) (newCap - (ct2 ++ mac).length) ⊢
      (p' ↦ₛ (ct2 ++ mac)) ∗ vecU8Tail A (BitVec.ofNat 64 newCap) p' (ct2 ++ mac) := by
    have hcb : (BitVec.ofNat 64 newCap == 0#64) = false := beq_false_of_ne hnew_ne0
    unfold vecU8Tail
    simp only [hcb, Bool.false_eq_true, ↓reduceIte, hnew_toNat, pointsToBytes_append]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.fold hjoin_mac (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hcl2
  exact h_finish
    outA ct2Ptr macPtr ct2 mac outEnc
    (BitVec.ofNat 64 newCap) p' (BitVec.ofNat 64 ct2.length) d56
    henc_res hlen_le (by rw [hnew_toNat]; omega) (by rw [hnew_toNat]; omega)
    hcl2 hsp0_align hfsp_align
    (by wp_norm_goal)
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, hsp1, *])
    (by simp only [Reg.x19, arm64_norm, hx19_1, *])
    (by simp only [Reg.x20, arm64_norm, hx20_1, *])
    (by simp only [Reg.x21, arm64_norm, *])
    (by simp only [Reg.x22, arm64_norm, *])
    (by simp only [Reg.x25, arm64_norm, hx25_1, *])
    (by simp only [Reg.x26, arm64_norm, hx26_1, *])
    (by simp only [Reg.x27, arm64_norm, hx27_1, *])
    (by simp only [arm64_norm, htr1, *])
    (by simp only [arm64_norm, hvregs_1, *])
    (by sep_focus)

/-- Relocatable `spqr::v1::chunked::send_ct::send_ct2_encoder` (Block `382`, 85 instructions)
    given `withLsCodeLoaded` contracts for `do_reserve_7` (Block `320`) and `encode_bytes` (Block `417`). -/
theorem send_ct2_encoder_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdr7 : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 320) (withLsCodeLoaded lsmpl (doReserveRawSpec A)))
    (henc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A)))
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec) :
    SendCt2EncoderPlacedOkX A ext := by
  unfold SendCt2EncoderPlacedOkX
  have hshim : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec :=
    spqr_hook_ok_of_mem (sym := spqrRustNoAllocShimSym) hshim_sat
  have halloc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustAllocSpec A) :=
    spqr_hook_ok_of_mem (sym := spqrRustAllocSym) halloc_sat
  have hdealloc : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc_sat
  have hmemcpy : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec :=
    spqr_hook_ok_of_mem (sym := "memcpy") hmemcpy_sat
  have haerr : (lsProg_382 (Rust.withPanics ext)).externAt? (lsρ spqrHandleErrorSym) =
      some Rust.panicked :=
    (spqr_externAt?_of_mem (prog := lsProg_382 (Rust.withPanics ext))).trans h_panic
  have henc_call : subroutine_ok (lsProg_382 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpecX A)) :=
    encodeBytesSpecX_cl_of_encodeBytesSpec_cl henc
  apply subroutine_ok_withLsCodeLoaded_of_left
  simp only [lsProg_382] at hdr7 henc_call hshim halloc hdealloc hmemcpy haerr ⊢
  unfold sendCt2EncoderSpec
  conv => arg 3; arg 1; ext x s; simp only [stackAt_sendCt2Encoder_split]
  cells_unfold
  wpp_init x s0
  conv => arg 6; ext sf P_f; rw [sepConj_assoc]
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  obtain ⟨outA, ct2Ptr, ct2, macPtr, mac, outEnc⟩ := x
  have h_finish := send_ct2_encoder_finish_placed henc_call hmemcpy hdealloc
  have h_mac := send_ct2_encoder_mac_placed hdr7 henc_call hmemcpy hdealloc
  dsimp only [BitVec.ofNat_eq_ofNat] at *
  obtain ⟨henc_res, hlen_le⟩ := encodeBytesResult_of_expectEncodeBytes_ok
    ‹Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc›
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := ‹(s0.sp &&& 15#64 == 0#64) = true›
  have hfsp_align : ((s0.sp - 512#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 512#64 hsp0_align (by decide)
  have hlen_app : (ct2 ++ mac).length = ct2.length + mac.length := List.length_append
  by_cases hct2_nil : ct2 = []
  · subst hct2_nil
    have hct2_z : (BitVec.ofNat 64 ([] : Bytes).length == 0#64) = true := rfl
    have henc_nil :
        emp ⊢ ((1#64 : BitVec 64) ↦ₛ ([] : Bytes)) ∗ vecU8Tail A 0#64 1#64 [] := by
      unfold vecU8Tail
      simp [pointsToBytes_nil]
      exact Entails.refl emp
    by_cases hmac_nil : mac = []
    · subst hmac_nil
      have hmac_z : (BitVec.ofNat 64 ([] : Bytes).length == 0#64) = true := rfl
      apply of_sepWP_lscl hcl0 (mid := (blkPl_382).base + 100#64)
      wp_steps
      refine SepWP.fold (Entails.trans (Entails.of_eq (emp_sepConj _).symm)
        (sepConj_mono_left henc_nil)) (sepConj_emp _).symm ?_
      rw [sepConj_emp]
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl1
      exact h_finish
        outA ct2Ptr macPtr [] [] outEnc
        0#64 1#64 0#64 _
        henc_res hlen_le (by decide) (by decide)
        hcl1 hsp0_align hfsp_align
        (by wp_norm_goal)
        (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [List.append_nil]; sep_focus)
    · have hmac_pos : 0 < mac.length := List.length_pos_iff.mpr hmac_nil
      have hmac_ne0 : BitVec.ofNat 64 mac.length ≠ 0#64 := by
        intro h0
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        change mac.length = 0 at this
        omega
      have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = false := beq_false_of_ne hmac_ne0
      apply of_sepWP_lscl hcl0 (mid := (blkPl_382).base + 208#64)
      wp_steps
      refine SepWP.fold (Entails.trans (Entails.of_eq (emp_sepConj _).symm)
        (sepConj_mono_left henc_nil)) (sepConj_emp _).symm ?_
      rw [sepConj_emp]
      refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl1
      exact h_mac
        outA ct2Ptr macPtr [] mac outEnc
        0#64 1#64 _
        henc_res hlen_le rfl (by decide)
        hcl1 hsp0_align hfsp_align
        (by wp_norm_goal)
        (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, *])
        (by simp only [Reg.x19, arm64_norm, *])
        (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x23, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *])
        (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (by sep_focus)
  · have hct2_pos : 0 < ct2.length := List.length_pos_iff.mpr hct2_nil
    have hct2_toNat : (BitVec.ofNat 64 ct2.length).toNat = ct2.length :=
      Nat.mod_eq_of_lt (by omega)
    have hct2_ne0 : BitVec.ofNat 64 ct2.length ≠ 0#64 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [hct2_toNat] at this
      change ct2.length = 0 at this
      omega
    have hct2_z : (BitVec.ofNat 64 ct2.length == 0#64) = false := beq_false_of_ne hct2_ne0
    have hlay_ct2 : LayoutOk ct2.length 1 := ⟨hct2_pos, ⟨0, rfl⟩, by omega⟩
    apply of_sepWP_lscl hcl0 (mid := (blkPl_382).base + 68#64)
    wp_steps; wp_apply; wp_steps
    refine SepWP.fold (stackAt_encodeBytesX_to_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
    refine call_rustAlloc halloc ct2.length 1 hlay_ct2
      (s0 := s0) (ret_pc := (blkPl_382).base + 68#64) (sp_call := s0.sp - 512#64)
      rfl (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hfsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, hct2_toNat, *])
      (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hcl1
    by_cases hoom : sf1.readReg64 (Reg.gpr 0#5) = 0
    · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_elim fun htr_oom => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, htr_ok⟩ => ?_
      have hoom_false : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_false_of_ne hoom
      have hjoin_ct2 :
          A.live (sf1.readReg64 (Reg.gpr 0#5)) ct2.length 1 ∗
            (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ ct2) ⊢
          (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ ct2) ∗
            vecU8Tail A (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) ct2 := by
        unfold vecU8Tail
        simp only [hct2_z, Bool.false_eq_true, ↓reduceIte, hct2_toNat, Nat.sub_self,
          ProofLib.memRegion_zero, sepConj_emp]
        exact Entails.of_eq (sepConj_comm _ _)
      by_cases hmac_nil : mac = []
      · have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = true := by
          subst hmac_nil; rfl
        apply of_sepWP_lscl hcl1 (mid := (blkPl_382).base + 100#64)
        refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
        wp_steps; wp_apply; wp_steps
        subst hmac_nil
        refine SepWP.fold hjoin_ct2 (by sep_focus) ?_
        refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        intro hcl2
        exact h_finish
          outA ct2Ptr macPtr ct2 [] outEnc
          (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) (BitVec.ofNat 64 ct2.length) _
          henc_res hlen_le (by rw [List.append_nil, hct2_toNat]) (by rw [hct2_toNat]; omega)
          hcl2 hsp0_align hfsp_align
          (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, arm64_norm, *])
          (by simp only [Reg.x19, arm64_norm, *])
          (by simp only [Reg.x20, arm64_norm, *])
          (by simp only [Reg.x21, arm64_norm, *])
          (by simp only [Reg.x22, arm64_norm, *])
          (by simp only [Reg.x25, arm64_norm, *])
          (by simp only [Reg.x26, arm64_norm, *])
          (by simp only [Reg.x27, arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [List.append_nil]; sep_focus)
      · have hmac_pos : 0 < mac.length := List.length_pos_iff.mpr hmac_nil
        have hmac_ne0 : BitVec.ofNat 64 mac.length ≠ 0#64 := by
          intro h0
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          change mac.length = 0 at this
          omega
        have hmac_z : (BitVec.ofNat 64 mac.length == 0#64) = false := beq_false_of_ne hmac_ne0
        apply of_sepWP_lscl hcl1 (mid := (blkPl_382).base + 208#64)
        refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 512#64)) (by sep_focus) ?_
        wp_steps; wp_apply; wp_steps
        refine SepWP.fold hjoin_ct2 (by sep_focus) ?_
        refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        intro hcl2
        exact h_mac
          outA ct2Ptr macPtr ct2 mac outEnc
          (BitVec.ofNat 64 ct2.length) (sf1.readReg64 (Reg.gpr 0#5)) _
          henc_res hlen_le hct2_toNat hoom
          hcl2 hsp0_align hfsp_align
          (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, arm64_norm, *])
          (by simp only [Reg.x19, arm64_norm, *])
          (by simp only [Reg.x20, arm64_norm, *])
          (by simp only [Reg.x22, arm64_norm, *])
          (by simp only [Reg.x23, arm64_norm, *])
          (by simp only [Reg.x25, arm64_norm, *])
          (by simp only [Reg.x26, arm64_norm, *])
          (by simp only [Reg.x27, arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by sep_focus)

/-- Closed `[LibsignalPlacement]` contract for `spqr::v1::chunked::send_ct::send_ct2_encoder`
    (Block `382`), discharging both `do_reserve_and_handle [local#7]` (Block `320`) and
    `<PolyEncoder as Encoder>::encode_bytes` (Block `417`) from `HookSat` hypotheses. -/
theorem send_ct2_encoder_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustReallocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec) :
    SendCt2EncoderPlacedOkX A ext :=
  send_ct2_encoder_placed_cl_ext
    (ls_subroutine_ok_of_block (i := 382) (j := 320)
      (do_reserve_7_raw_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (i := 382) (j := 417)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (encode_bytes_placed_ok_ext h_panic
          (hookSat_sessionShim_of_noAllocShim hshim)
          halloc
          (hookSat_sessionMemcpy_of_region hmemcpy))))
    h_panic hshim halloc hdealloc hmemcpy

end CryptoVerification.SpqrV1.States.Leaves
