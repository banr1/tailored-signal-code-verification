/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Proof
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1Chunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (Block `370`)

Relocatable `[LibsignalPlacement]` verification of `<KeysSampled>::recv_ct1_chunk` (Block `370`,
107 instructions), proving `keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees` and
`keys_sampled_recv_ct1_chunk_placed_cl_ext` (`KeysSampledRecvCt1ChunkPlacedOkX`).
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
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local irreducible] addChunkTotal emptyPolyDecoder
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  sp_sub_80_sub_896 sp_sub_976_add_896 sp_sub_80_sub_80 sp_sub_80_sub_16
  sp_sub_80_add_16' sp_sub_80_add_24' sp_sub_80_add_32' sp_sub_80_add_40'
  sp_sub_80_add_48' sp_sub_80_add_56' sp_sub_80_add_64' sp_sub_80_add_72'
  sp_sub_80_add_80'

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
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
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
  refine (h.to_outcome x R' s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
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

private theorem call_encodeBytesX_cl [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeBytesSpecX A)))
    (out msgA : BitVec 64) (msg : Bytes) (outEnc : PolyEncoder)
    (henc : encodeBytesResult msg = .ok outEnc)
    (hlen : msg.length < 2 ^ 64)
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
      LibsignalCodeLoaded lsmpl sf.mem →
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
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := ⟨out, false, msgA, msg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, encodeBytesSpecX, polyEncoderSize, bytesAt]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hx1, hlen⟩, hm⟩
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
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hcl_sf

set_option maxHeartbeats 600000 in
private theorem keys_sampled_recv_ct1_chunk_tail_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly16 : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec A)))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec : PolyDecoder)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout_eq : outSt = { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
                         sending_ek := outSt.sending_ek,
                         receiving_ct1 := dec })
    (g : AuthWords) (gdk : VecWords)
    (ekCap ekPtr d56 : BitVec 64)
    (hek_le : st.uc.ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63)
    {s0 sf2 : State} {P : SepProp}
    (hcl2 : LibsignalCodeLoaded lsmpl sf2.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 976#64) &&& 15#64 == 0#64) = true)
    (hpc2 : sf2.pc = (blkPl_370).base + 280#64)
    (hrun2 : sf2.status = .Running)
    (hsp2 : sf2.sp = s0.sp - 976#64)
    (hx19_2 : sf2.readReg64 .x19 = stA)
    (hx20_2 : sf2.readReg64 .x20 = st.uc.epoch)
    (hx21_2 : sf2.readReg64 .x21 = outA)
    (hx22_2 : sf2.readReg64 .x22 = ekCap)
    (hx23_2 : sf2.readReg64 .x23 = ekPtr)
    (hx24_2 : sf2.readReg64 .x24 = s0.sp - 160#64)
    (hx25_2 : sf2.readReg64 .x25 = s0.readReg64 .x25)
    (hx26_2 : sf2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_2 : sf2.readReg64 .x27 = s0.readReg64 .x27)
    (hfp_2 : sf2.readReg64 .fp = s0.sp - 80#64)
    (htr2 : sf2.trace = s0.trace)
    (hvregs_2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hP : P = (
      (polyDecoderAt A (outA + 480#64) dec ∗
        memRegion (s0.sp - 960#64) 400) ∗
      (polyEncoderAt A outA outSt.sending_ek ∗ memRegion (s0.sp - 560#64) 400 ∗
       memRegion (outA + 400#64) 80 ∗
       polyEncoderAt A stA st.sending_hdr ∗ memRegion (stA + 400#64) 104 ∗
       chunkAt chunkA chunk ∗
       (ekPtr ↦ₛ st.uc.ek) ∗ vecU8Tail A ekCap ekPtr st.uc.ek ∗
       relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
       relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
       wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
       memRegion (s0.sp - 976#64) 8 ∗ ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
       memRegion (s0.sp - 88#64) 8 ∗ sendCt2SavedCells s0 d56 ∗
       A.pool ∗ stackAt (s0.sp - 976#64) encodeBytesStackX))) :
    SepWP ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf2 P
      (fun sf P_f =>
        (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            chunkedHeaderSentAt A outA outSt ∗
            memRegion stA 504 ∗
            chunkAt chunkA chunk ∗
            A.pool ∗
            stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 265)
  have hsp_words :
      wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) =
      (((s0.sp - 160#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 152#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 144#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 136#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 128#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 120#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 112#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 104#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 96#64) ↦₆₄ gdk.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_9, arm64_norm]
  have hout_auth_words :
      wordsAt (outA + 400#64) (authWordsList g) =
      (((outA + 400#64) ↦₆₄ g.v1.w0) ∗ ((outA + 408#64) ↦₆₄ g.v1.w1) ∗
       ((outA + 416#64) ↦₆₄ g.v1.w2) ∗ ((outA + 424#64) ↦₆₄ g.v2.w0) ∗
       ((outA + 432#64) ↦₆₄ g.v2.w1) ∗ ((outA + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]
    simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hout_dk_words :
      wordsAt (outA + 448#64) (vecWordsList gdk) =
      (((outA + 448#64) ↦₆₄ gdk.w0) ∗ ((outA + 456#64) ↦₆₄ gdk.w1) ∗
       ((outA + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  refine SepWP.fold (cells_10_unfold (outA + 400#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [hsp_words]; simp only [wordsAt_10, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_auth_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_dk_words.symm) (by sep_focus) ?_
  refine SepWP.fold (outA_headerSent_recompose A outA s0.sp st.uc.auth st.uc.dk st.uc.epoch
    outSt.sending_ek dec outSt hout_eq g gdk) (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A ekCap ekPtr st.uc.ek hek_le hek_lt)
    (by sep_focus) ?_
  refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A stA st.sending_hdr) (by sep_focus) ?_
  wp_pull_exists; rename_i hdrTag vecs
  wp_focus_pure; intro hvecs_len
  dsimp only [vecCapPtrDealloc, sendCt2SavedCells]
  by_cases hcap0 : (ekCap == 0#64) = true <;>
    simp only [hcap0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine SepWP.fold (stackAt_976_to_dropPoly16 s0 st.uc.epoch d56)
      (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
    refine call_dropGluePoly16_cl hpoly16 (stA + 8#64) vecs
      (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp2]) (by assumption)
      (by simp only [Reg.lr, arm64_norm, hsp2])
      (by simp only [trace_writeVReg128, arm64_norm, htr2])
      (by simp only [Reg.x0, arm64_norm, hx19_2]) hvecs_len (by sep_focus)
      (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
    refine SepWP.fold (chunked_400_join stA hdrTag 104 504 rfl (by decide)) (by sep_focus) ?_
    refine SepWP.fold (stackAt_976_from_dropPoly16 s0.sp) (by sep_focus) ?_
    refine SepWP.done hpc3 hrun3 ⟨fun R hm => ?_, hsp3,
      CalleeSavedPreserved.trans
        (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp,
          arm64_norm, hx25_2, hx26_2, hx27_2, hsp2, hvregs_2]) hcs3⟩
    simp only [htr3, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_ac (by ac_rfl) hm
  · wp_steps
    refine SepWP.fold (stackAt_encodeBytesX_to_allocHook (s0.sp - 976#64)) (by sep_focus) ?_
    refine call_rustDealloc_cs hdealloc ekPtr ekCap.toNat 1
      (ret_pc := (blkPl_370).base + 324#64) (sp_call := s0.sp - 976#64)
      rfl (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
      (by simp only [Reg.lr, arm64_norm])
      htr2
      (by simp only [Reg.x0, arm64_norm, hx23_2])
      (by simp only [Reg.x1, arm64_norm, hx22_2])
      (by simp only [Reg.x2, arm64_norm])
      (by sep_focus)
      (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
    simp only [arm64_norm, hx19_2, hx25_2, hx26_2, hx27_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
    refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 976#64)) (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (stackAt_976_to_dropPoly16 s0 st.uc.epoch d56)
      (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
    refine call_dropGluePoly16_cl hpoly16 (stA + 8#64) vecs
      (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp3]) (by assumption)
      (by simp only [Reg.lr, arm64_norm, hsp3]) (by simp only [arm64_norm, htr3])
      (by simp only [Reg.x0, arm64_norm, hx19_3]) hvecs_len (by sep_focus)
      (fun sf4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
    refine SepWP.fold (chunked_400_join stA hdrTag 104 504 rfl (by decide)) (by sep_focus) ?_
    refine SepWP.fold (stackAt_976_from_dropPoly16 s0.sp) (by sep_focus) ?_
    refine SepWP.done hpc4 hrun4 ⟨fun R hm => ?_, hsp4,
      CalleeSavedPreserved.trans
        (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp,
          arm64_norm, hx25_3, hx26_3, hx27_3, hsp3, hvregs_3]) hcs4⟩
    simp only [htr4, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_ac (by ac_rfl) hm

set_option maxHeartbeats 600000 in
private theorem keys_sampled_recv_ct1_chunk_finish_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (hdealloc : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hpoly16 : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec A)))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec : PolyDecoder)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout_eq : outSt = { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
                         sending_ek := outSt.sending_ek,
                         receiving_ct1 := dec })
    (g : AuthWords) (gdk : VecWords)
    (ekCap ekPtr d56 : BitVec 64)
    (hek_le : st.uc.ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63)
    {s0 s : State} {P : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 976#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_370).base + 236#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 976#64)
    (hx19 : s.readReg64 .x19 = stA)
    (hx20 : s.readReg64 .x20 = st.uc.epoch)
    (hx21 : s.readReg64 .x21 = outA)
    (hx22 : s.readReg64 .x22 = ekCap)
    (hx23 : s.readReg64 .x23 = ekPtr)
    (hx24 : s.readReg64 .x24 = s0.sp - 160#64)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hfp : s.readReg64 .fp = s0.sp - 80#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 880 ∗
      polyEncoderAt A stA st.sending_hdr ∗
      memRegion (stA + 400#64) 104 ∗
      chunkAt chunkA chunk ∗
      polyDecoderAt A (s0.sp - 960#64) dec ∗
      polyEncoderAt A (s0.sp - 560#64) outSt.sending_ek ∗
      (ekPtr ↦ₛ st.uc.ek) ∗
      vecU8Tail A ekCap ekPtr st.uc.ek ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
      memRegion (s0.sp - 976#64) 8 ∗
      ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (s0.sp - 88#64) 8 ∗
      sendCt2SavedCells s0 d56 ∗
      A.pool ∗
      stackAt (s0.sp - 976#64) encodeBytesStackX)) :
    SepWP ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            chunkedHeaderSentAt A outA outSt ∗
            memRegion stA 504 ∗
            chunkAt chunkA chunk ∗
            A.pool ∗
            stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  have h_tail := keys_sampled_recv_ct1_chunk_tail_placed (F := F) hdealloc hpoly16
  apply sepWP_seq_lscl hcl (mid := (blkPl_370).base + 280#64)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := outA) (n := 400) (k := 480) (b' := outA + 400#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 400#64) (n := 80) (k := 400) (b' := outA + 480#64) rfl (by bv_omega) (by decide)]
  obtain ⟨tag, htag01, encRest, henc_split⟩ := polyEncoderAt_split_tag A (s0.sp - 560#64) outSt.sending_ek
  suffices h_mc1 : ∀ sf1 : State,
      sf1.pc = (blkPl_370).base + 264#64 → sf1.status = .Running →
      sf1.sp = s0.sp - 976#64 → CalleeSavedPreserved s sf1 → sf1.trace = s0.trace →
      SepWP ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext)) ((blkPl_370).base + 280#64) sf1
        ((polyEncoderAt A outA outSt.sending_ek ∗ memRegion (s0.sp - 560#64) 400) ∗
          (memRegion (outA + 400#64) 80 ∗ memRegion (outA + 480#64) 400 ∗
           polyEncoderAt A stA st.sending_hdr ∗ memRegion (stA + 400#64) 104 ∗
           chunkAt chunkA chunk ∗ polyDecoderAt A (s0.sp - 960#64) dec ∗
           (ekPtr ↦ₛ st.uc.ek) ∗ vecU8Tail A ekCap ekPtr st.uc.ek ∗
           relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
           relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
           wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
           memRegion (s0.sp - 976#64) 8 ∗ ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
           memRegion (s0.sp - 88#64) 8 ∗ sendCt2SavedCells s0 d56 ∗
           A.pool ∗ stackAt (s0.sp - 976#64) encodeBytesStackX))
        (fun sm Pm =>
          LibsignalCodeLoaded lsmpl sm.mem →
          SepWP ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sm Pm
            (fun sf P_f =>
              (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
                sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
                  chunkedHeaderSentAt A outA outSt ∗
                  memRegion stA 504 ∗
                  chunkAt chunkA chunk ∗
                  A.pool ∗
                  stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) by
    rcases htag01 with rfl | rfl
    · wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
        (Relocatable.of_polyEncoderAt A outSt.sending_ek) outA (s0.sp - 560#64)
        (ret_pc := (blkPl_370).base + 264#64) (sp_call := s0.sp - 976#64)
        rfl (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
        (by simp only [Reg.x0, arm64_norm, hx21])
        (by simp only [Reg.x1, arm64_norm, hsp])
        (by simp only [Reg.x2, arm64_norm])
        (by sep_focus)
        (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 =>
          sepWP_congr_pre (by ac_rfl) (h_mc1 sf1 hpc1 hrun1 hsp1 (CalleeSavedPreserved.trans
            (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm]) hcs1) htr1))
    · wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
        (Relocatable.of_polyEncoderAt A outSt.sending_ek) outA (s0.sp - 560#64)
        (ret_pc := (blkPl_370).base + 264#64) (sp_call := s0.sp - 976#64)
        rfl (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
        (by simp only [Reg.x0, arm64_norm, hx21])
        (by simp only [Reg.x1, arm64_norm, hsp])
        (by simp only [Reg.x2, arm64_norm])
        (by sep_focus)
        (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 =>
          sepWP_congr_pre (by ac_rfl) (h_mc1 sf1 hpc1 hrun1 hsp1 (CalleeSavedPreserved.trans
            (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm]) hcs1) htr1))
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hfp, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  wp_steps
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyDecoderAt A dec) (outA + 480#64) (s0.sp - 960#64)
    (ret_pc := (blkPl_370).base + 280#64) (sp_call := s0.sp - 976#64)
    rfl (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx21_1])
    (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hfp_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  apply SepWP.done hpc2 hrun2
  intro hcl2
  exact h_tail outA stA chunkA st chunk dec outSt
    hout_eq g gdk ekCap ekPtr d56 hek_le hek_lt hcl2 hsp0_align hfsp_align
    hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hfp_2 htr2 hvregs_2 (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Relocatable `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (Block `370`, 107 insns)
    parameterized by `withLsCodeLoaded` contracts for `add_chunk` (Block `419`),
    `encode_bytes` (Block `417`), and `drop_glue::<[Poly; 16]>` (Block `265`). -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec A)))
    (henc : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A)))
    (hpoly16 : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec A))) :
    KeysSampledRecvCt1ChunkPlacedOkX A F ext := by
  unfold KeysSampledRecvCt1ChunkPlacedOkX
  have hdealloc : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc_sat
  have hmemcpy : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec :=
    spqr_hook_ok_of_mem (sym := "memcpy") hmemcpy_sat
  have henc_raw : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpecX A)) :=
    encodeBytesSpecX_cl_of_encodeBytesSpec_cl henc
  apply subroutine_ok_withLsCodeLoaded_of_left
  simp only [lsProg_370] at hdealloc hmemcpy hadd henc_raw hpoly16 ⊢
  unfold keysSampledRecvCt1ChunkSpec
  wpp_init x s0
  conv => arg 6; ext sf P_f; rw [sepConj_assoc]
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  rcases x with ⟨outA, stA, chunkA, st, chunk, outSt⟩
  have h_finish := keys_sampled_recv_ct1_chunk_finish_placed (F := F) hmemcpy hdealloc hpoly16
  dsimp only [chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  obtain ⟨henc_res, hek_len_le, hout_eq⟩ := keys_sampled_recv_ct1_chunk_ok_elim (by assumption)
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hfsp_align : ((s0.sp - 976#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 976#64 hsp0_align (by decide)
  apply of_sepWP_lscl hcl0 (mid := lsmpl.base 419)
  wp_conv_pre =>
    rw [stackAt_976_split s0.sp]
    unfold chunkedKeysSampledAt
    rw [unchunkedHeaderSentAt_400_eq A (s0.readReg64 (Reg.gpr 1#5)) st.uc]
  refine SepWP.fold (cells_1_unfold (s0.sp - 968#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 960#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 832#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 704#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 576#64)) (by sep_focus) ?_
  refine SepWP.fold (byte_1_unfold (s0.sp - 568#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_10_unfold (s0.sp - 80#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [wordsAt_16, wordsAt_10, arm64_norm]
  wp_steps
  refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
  have hdec0_1 :
      (((s0.sp - 960#64) ↦₆₄ 0#64) ∗ ((s0.sp - 952#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 944#64) ↦₆₄ 0#64) ∗ ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 928#64) ↦₆₄ 2#64) ∗ ((s0.sp - 920#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 912#64) ↦₆₄ 0#64) ∗ ((s0.sp - 904#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 896#64) ↦₆₄ 0#64) ∗ ((s0.sp - 888#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 880#64) ↦₆₄ 2#64) ∗ ((s0.sp - 872#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 864#64) ↦₆₄ 0#64) ∗ ((s0.sp - 856#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 848#64) ↦₆₄ 0#64) ∗ ((s0.sp - 840#64) ↦₆₄ 0#64)) =
      wordsAt (s0.sp - 960#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_2 :
      (((s0.sp - 832#64) ↦₆₄ 2#64) ∗ ((s0.sp - 824#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 816#64) ↦₆₄ 0#64) ∗ ((s0.sp - 808#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 800#64) ↦₆₄ 0#64) ∗ ((s0.sp - 792#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 784#64) ↦₆₄ 2#64) ∗ ((s0.sp - 776#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 752#64) ↦₆₄ 0#64) ∗ ((s0.sp - 744#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 736#64) ↦₆₄ 2#64) ∗ ((s0.sp - 728#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 720#64) ↦₆₄ 0#64) ∗ ((s0.sp - 712#64) ↦₆₄ 2#64)) =
      wordsAt ((s0.sp - 960#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_3 :
      (((s0.sp - 704#64) ↦₆₄ 0#64) ∗ ((s0.sp - 696#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 688#64) ↦₆₄ 2#64) ∗ ((s0.sp - 680#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 672#64) ↦₆₄ 0#64) ∗ ((s0.sp - 664#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 656#64) ↦₆₄ 0#64) ∗ ((s0.sp - 648#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 640#64) ↦₆₄ 2#64) ∗ ((s0.sp - 632#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 624#64) ↦₆₄ 0#64) ∗ ((s0.sp - 616#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 608#64) ↦₆₄ 0#64) ∗ ((s0.sp - 600#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 592#64) ↦₆₄ 2#64) ∗ ((s0.sp - 584#64) ↦₆₄ 0#64)) =
      wordsAt ((s0.sp - 960#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  refine SepWP.fold (Entails.of_eq hdec0_1) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_2) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_3) (by sep_focus) ?_
  have hdec_recomp :
      wordsAt (s0.sp - 960#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] ∗
      wordsAt ((s0.sp - 960#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] ∗
      wordsAt ((s0.sp - 960#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] ∗
      ((s0.sp - 576#64) ↦₆₄ 480#64) ∗ ((s0.sp - 568#64) ↦₈ 0#8) ∗ memRegion (s0.sp - 567#64) 7 ⊢
      polyDecoderAt A (s0.sp - 960#64) (emptyPolyDecoder 480) := by
    simpa only [arm64_norm] using emptyPolyDecoder_recompose A (s0.sp - 960#64) 480 (by decide)
  refine SepWP.fold hdec_recomp (by sep_focus) ?_
  refine call_addChunk_cl hadd
    (s0.sp - 960#64) (s0.readReg64 (Reg.gpr 3#5)) (emptyPolyDecoder 480) chunk
    (emptyPolyDecoder_strictSorted 480)
    (ret_pc := (blkPl_370).base + 184#64) (sp_call := s0.sp - 976#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 _ hcl1 => ?_)
  generalize (addChunkTotal (emptyPolyDecoder 480) chunk) = dec1 at hout_eq ⊢
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  apply of_sepWP_lscl hcl1 (mid := lsmpl.base 417)
  refine SepWP.fold (stackAt_976_addChunk_to_encodeBytesX s0.sp) (by sep_focus) ?_
  refine SepWP.fold (authenticatorAt_extract A (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.readReg64 (Reg.gpr 1#5) + 448#64) st.uc.ek)
    (by sep_focus) ?_
  wp_pull_exists; rename_i ekCap ekPtr
  wp_focus_pure; rintro ⟨hek_le, hek_lt, hek_ne⟩
  refine SepWP.fold (vecU8_extract A (s0.readReg64 (Reg.gpr 1#5) + 472#64) st.uc.dk)
    (by sep_focus) ?_
  wp_pull_exists; rename_i gdk
  refine SepWP.fold (cells_9_unfold (s0.sp - 160#64)) (by sep_focus) ?_
  wp_pull_exists
  have hst_auth_words :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (authWordsList g) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]
    simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk_words :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 472#64) (vecWordsList gdk) =
      (((s0.readReg64 (Reg.gpr 1#5) + 472#64) ↦₆₄ gdk.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 480#64) ↦₆₄ gdk.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 488#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) =
      (((s0.sp - 160#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 152#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 144#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 136#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 128#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 120#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 112#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 104#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 96#64) ↦₆₄ gdk.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_9, arm64_norm]
  wp_conv_pre =>
    rw [hst_auth_words, hst_dk_words]
    simp only [wordsAt_9, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_auth_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk_words.symm) (by sep_focus) ?_
  refine SepWP.fold (stA_400_104_fold (s0.readReg64 (Reg.gpr 1#5)) g
    ekCap ekPtr (BitVec.ofNat 64 st.uc.ek.length) gdk st.uc.epoch) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  have hek_lt64 : st.uc.ek.length < 2 ^ 64 := by omega
  refine call_encodeBytesX_cl henc_raw
    (s0.sp - 560#64) ekPtr st.uc.ek outSt.sending_ek henc_res hek_lt64
    (ret_pc := (blkPl_370).base + 236#64) (sp_call := s0.sp - 976#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x8, arm64_norm, hsp1])
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hcl2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx24_1, hx25_1, hx26_1, hx27_1, hfp_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.mono (h_finish
    (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
    st chunk dec1 outSt hout_eq g gdk ekCap ekPtr _ hek_le hek_lt
    hcl2 hsp0_align hfsp_align hpc2 hrun2 hsp2
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hfp_2 htr2 hvregs_2
    (by ac_rfl)) ?_
  intro sf P_f _ _ ⟨hmem, hsp_sf, hcs_sf⟩
  refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
  have h1 := hmem R hm
  simp only [sepConj_assoc, satisfies_pure_sepConj] at h1 ⊢
  exact h1

/-- `[LibsignalPlacement]` contract for `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk`
    (Block `370`), discharging `encode_bytes` (Block `417`) and `drop_glue::<[Poly; 16]>` (Block `265`)
    from `HookSat` hypotheses and taking `add_chunk` (Block `419`). -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec A))) :
    KeysSampledRecvCt1ChunkPlacedOkX A F ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees
    hdealloc hmemcpy hadd
    (ls_subroutine_ok_of_block (i := 370) (j := 417)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (encode_bytes_placed_ok_ext h_panic
          (hookSat_sessionShim_of_noAllocShim hshim)
          halloc
          (hookSat_sessionMemcpy_of_region hmemcpy))))
    (ls_subroutine_ok_of_block (i := 370) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

end CryptoVerification.SpqrV1.States.Leaves
