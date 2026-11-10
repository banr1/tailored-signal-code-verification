/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 1

**Checked by Lean.** Callee stack-budget splits, shared direct epilogue (`+19324 -> s0.x30`),
epoch comparison at `+1528` (`0x55a4c`), and Path 1 (`msg.epoch > st.uc.epoch`,
`Error::EpochOutOfRange`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv")
  (ls_stub% "memcpy")

@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_3856 (sp : BitVec 64) : (sp - 4240#64) + 3856#64 = sp - 384#64 := by bv_omega

@[local arm64_norm, local wp_norm]
theorem sp_sub_4240_add_3272 (sp : BitVec 64) : (sp - 4240#64) + 3272#64 = sp - 968#64 := by bv_omega

/-! ## 1. Callee Stack Splits & Shared Direct Epilogue (`+19324 -> s0.x30`) -/

theorem stackAt_statesRecvCallee_eq_allocHook' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15456 ∗ stackAt fsp allocHookStack :=
  stackAt_split_bottom fsp allocHookStack 15456 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack32' (fsp : BitVec 64) :

    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropStack32 :=
  stackAt_split_bottom fsp dropStack32 15424 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack48' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15408 ∗ stackAt fsp dropStack48 :=
  stackAt_split_bottom fsp dropStack48 15408 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStack80' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15376 ∗ stackAt fsp dropStack80 :=
  stackAt_split_bottom fsp dropStack80 15376 (by decide)

theorem stackAt_statesRecvCallee_eq_dropStackPoly64' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15392 ∗ stackAt fsp dropStackPoly64 :=
  stackAt_split_bottom fsp dropStackPoly64 15392 (by decide)

theorem stackAt_statesRecvCallee_eq_dropGluePoly16' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropGluePoly16Stack :=
  stackAt_split_bottom fsp dropGluePoly16Stack 15424 (by decide)

theorem stackAt_statesRecvCallee_eq_addChunk' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 3072 ∗ stackAt fsp SpqrV1.Poly.AddChunk.addChunkStackX :=
  stackAt_split_bottom fsp SpqrV1.Poly.AddChunk.addChunkStackX 3072 (by decide)

theorem stackAt_statesRecvCallee_eq_polyDecodedMessage' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2496 ∗ stackAt fsp RecvCt2Chunk.polyDecodedMessageStackX :=
  stackAt_split_bottom fsp RecvCt2Chunk.polyDecodedMessageStackX 2496 (by decide)

theorem stackAt_statesRecvCallee_eq_unchunkedRecvEk' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2960 ∗ stackAt fsp unchunkedRecvEkStack :=
  stackAt_split_bottom fsp unchunkedRecvEkStack 2960 (by decide)

theorem stackAt_statesRecvCallee_eq_unchunkedSendCt2' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2832 ∗ stackAt fsp unchunkedSendCt2Stack :=
  stackAt_split_bottom fsp unchunkedSendCt2Stack 2832 (by decide)

theorem stackAt_statesRecvCallee_eq_sendCt2Encoder' (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 2096 ∗ stackAt fsp sendCt2EncoderStack :=
  stackAt_split_bottom fsp sendCt2EncoderStack 2096 (by decide)

theorem sub_ok_at_statesRecv {α : Type} {b : BitVec 64} {ext : String → Option (State → State)}
    {callee : String} {off : BitVec 64} {spec : Spec α}
    (hoff : (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + off =
      (tripleRatchetProgAtExt b ext).fnAddr callee)
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr callee) spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + off) spec :=
  hoff.symm ▸ h

theorem dealloc_raw_ok_at_statesRecv {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        (bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) := by
  refine Drop.sub_ok_of_addr_eq ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_stub% "__rustc::__rust_dealloc"]
  bv_omega

theorem unchunkedCt1Sent400_entails_dealloc (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A (a + 400#64) st ⊢
      ∃∗ g : FiveVecGhost,
        fiveVec400HeadersAt a g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr := by
  refine Entails.trans (unchunkedCt1SentAt_entails_dealloc A (a + 400#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [fiveVec128HeadersAt_400_eq]
  exact Entails.refl _

theorem dropPoly16_ok_at_statesRecv {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709513320#64)
      (dropGluePoly16Spec A) := by
  refine Drop.sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
  dsimp only [tripleRatchetProgAtExt, statesRecvName, dropPoly16Name]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::encoding::polynomial::Poly; 16]>",
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv"]
  bv_omega

theorem dropSortedSetPt16_ok_at_statesRecv {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18446744073709512900#64)
      (dropGlueSortedSetPt16Spec A) := by
  refine Drop.sub_ok_of_addr_eq ?_ (drop_glue_sorted_set_pt16_ok_ext hdealloc)
  dsimp only [tripleRatchetProgAtExt, statesRecvName, dropSortedSetPt16Name]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>",
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv"]
  bv_omega

theorem polyDecodedMsg_ok_at_statesRecv {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 91948#64)
      (polyDecoderDecodedMessageSpec A b) := by
  refine sub_ok_at_statesRecv ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, polyDecoderDecodedMessageName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::decoded_message"]
  bv_omega

theorem unchunkedRecvEk_ok_at_statesRecv {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A F K)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 34412#64)
      (unchunkedCt1SentRecvEkSpec A F K) := by
  refine sub_ok_at_statesRecv ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, unchunkedCt1SentRecvEkName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek"]
  bv_omega

theorem unchunkedSendCt2_ok_at_statesRecv {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36780#64)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b) := by
  refine sub_ok_at_statesRecv ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, unchunkedCt1SentEkReceivedSendCt2Name]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"]
  bv_omega

theorem sendCt2Encoder_ok_at_statesRecv {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sendCt2EncoderName)
      (sendCt2EncoderSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 59092#64)
      (sendCt2EncoderSpec A) := by
  refine sub_ok_at_statesRecv ?_ h
  dsimp only [tripleRatchetProgAtExt, statesRecvName, sendCt2EncoderName]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      ls_lemma% fnOff "<spqr::v1::chunked::states::States>::recv",
      ls_lemma% fnOff "spqr::v1::chunked::send_ct::send_ct2_encoder"]
  bv_omega

/-- Shared direct epilogue at `+19324` (`0x59fd0 -> 0x59ff0`):
    restores `sp = s0.sp` and `x19..x30` from `statesRecvSavedCells s0`, folds the stack back into
    `stackAt s0.sp statesRecvStackX`, and returns to `s0.readReg64 .x30`. -/
theorem ct1Sampled_epilogue_19324
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  states_recv_fetches_range b (Rust.withPanics ext) 19324 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  unfold statesRecvSavedCells
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun1) ?_
  refine And.intro ?_ (And.intro (by simp only [State.sp, arm64_norm])
    (And.intro ?_ (by simp only [arm64_norm, htr1.1])))
  · have hrest := stack_restore_statesRecv s0
    unfold statesRecvSavedCells at hrest
    refine Entails.trans
      (Entails.of_eq (show _ =
        Rest ∗
        (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) by ac_rfl))
      (sepConj_mono_right hrest)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [arm64_norm, htr1.2]

/-- Prologue of `States::recv` (`+0 -> +36`, `0x55454 -> 0x55478`). -/
theorem ct1Sampled_prologue
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc0 : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
    (hrun0 : s0.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36#64)
      s0
      (stackAt s0.sp statesRecvStackX ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗
          Rest) ∧
        s1.sp = s0.sp - 4240#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        TraceCalleeSaved s1 s0) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hsp4192_align : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4192#64 hsp0_align (by decide)
  states_recv_fetches_range b (Rust.withPanics ext) 0 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc0 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [stackAt_statesRecv_split_96 s0.sp, stackAt_statesRecv_split_fsp s0.sp,
        memRegion_4144_split_cell48 (s0.sp - 4240#64)]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sp_sub_4240_add_48]
  apply ProofLib.SepWP.exists_left; intro v48
  apply ProofLib.SepWP.exists_left; intro v_fp
  apply ProofLib.SepWP.exists_left; intro v_lr
  apply ProofLib.SepWP.exists_left; intro v_x28
  apply ProofLib.SepWP.exists_left; intro v_x27
  apply ProofLib.SepWP.exists_left; intro v_x26
  apply ProofLib.SepWP.exists_left; intro v_x25
  apply ProofLib.SepWP.exists_left; intro v_x24
  apply ProofLib.SepWP.exists_left; intro v_x23
  apply ProofLib.SepWP.exists_left; intro v_x22
  apply ProofLib.SepWP.exists_left; intro v_x21
  apply ProofLib.SepWP.exists_left; intro v_x20
  apply ProofLib.SepWP.exists_left; intro v_x19
  wp_steps
  have hjoin4144 := cell48_4088_entails_memRegion_4144 (s0.sp - 4240#64) 0#64
  rw [sp_sub_4240_add_48] at hjoin4144
  have h4184 : (s0.sp - 4240#64) + 56#64 = s0.sp - 4184#64 := by bv_omega
  rw [h4184] at hjoin4144 ⊢
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun0) ?_
  refine ⟨?_, by simp only [State.sp, arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [TraceCalleeSaved, arm64_norm]⟩
  unfold statesRecvSavedCells
  refine Entails.trans
    (Entails.of_eq (show _ =
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      (memRegion (s0.sp - 4240#64) 48 ∗
       ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 4184#64) 4088) ∗
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
       ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
       ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
       ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
       ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
       ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
       ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
      Rest by
        dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
          Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
        ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_left hjoin4144)

/-- Jump-table dispatch specialized to `.ct1Sampled` (`tag = 0#64 ∨ tag = 1#64`, `+36 -> +1528`, `0x55478 -> 0x55a4c`). -/
theorem ct1Sampled_dispatch
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (s1 : State) (fsp st_ptr tag : BitVec 64) (Rest : SepProp)
    (htag : tag = 0#64 ∨ tag = 1#64)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1528#64)
      s1
      ((st_ptr ↦₆₄ tag) ∗ statesRecvRoAt b ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (st_ptr ↦₆₄ tag) ∗ statesRecvRoAt b ∗ Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x0 = s1.readReg64 .x0 ∧
        s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧
        s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = 7#64 ∧
        s2.readReg64 .x12 = tag ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) := by
  subst hsp1 hx1_1
  have hadrp := fnAddr_adrp_5549c (b := b) (H := Rust.withPanics ext) hb
  states_recv_fetches_range b (Rust.withPanics ext) 36 60
  dsimp only [tripleRatchetProgAtExt, statesRecvName, statesRecvRoAt,
    statesRecvJumpTableAt, BitVec.ofNat_eq_ofNat] at hpc1 hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  rcases htag with rfl | rfl <;>
  · wp_steps
    wp_done

/-! ## 2. Epoch Comparison at `+1528` (`0x55a4c..0x55a70`) -/

theorem unchunkedCt1SentAt_epoch_expose (A : RustAlloc) {F : ShaCompress}
    (selfA : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A (selfA + 400#64) uc =
      (authenticatorAt A (selfA + 400#64) uc.auth ∗
       vecU8 A (selfA + 448#64) uc.hdr ∗
       vecU8 A (selfA + 472#64) uc.es ∗
       vecU8 A (selfA + 496#64) uc.ct1) ∗
      ((selfA + 520#64) ↦₆₄ uc.epoch) := by
  dsimp only [unchunkedCt1SentAt]
  have h448 : (selfA + 400#64) + 48#64 = selfA + 448#64 := by bv_omega
  have h472 : (selfA + 400#64) + 72#64 = selfA + 472#64 := by bv_omega
  have h496 : (selfA + 400#64) + 96#64 = selfA + 496#64 := by bv_omega
  have h520 : (selfA + 400#64) + 120#64 = selfA + 520#64 := by bv_omega
  rw [h448, h472, h496, h520]
  ac_rfl

theorem epoch_cmp_b_eq_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = false := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_b_ne_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) != 1#32) = false := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_b_eq_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = false := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem epoch_cmp_b_ne_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) != 1#32) = true := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem epoch_cmp_b_eq_of_eq (ep : BitVec 64) :
    (BitVec.truncate 32 ((if ep.ule ep = true then if ep.ule ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = true := by
  have h1 : ep.ule ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  simp [h1]

theorem ct1Sampled_epoch_cmp_gt
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s2 : State) (selfA msgA st_ep msg_ep : BitVec 64) (Rest : SepProp)
    (hgt : msg_ep.toNat > st_ep.toNat)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1528#64)
    (hrun2 : s2.status = .Running)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx24 : s2.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1564#64)
      s2
      (((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest)
      (fun s3 P3 =>
        (P3 ⊢ ((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest) ∧
        s3.sp = s2.sp ∧
        s3.readReg64 .x1 = selfA ∧
        s3.readReg64 .x19 = s2.readReg64 .x19 ∧
        s3.readReg64 .x20 = msg_ep ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧
        s3.readReg64 .x24 = msgA ∧
        s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.readReg64 .x29 = s2.readReg64 .x29 ∧
        TraceCalleeSaved s3 s2) := by
  subst hx1 hx24
  have hcond1 := epoch_cmp_b_eq_of_gt hgt
  have hcond2 := epoch_cmp_b_ne_of_gt hgt
  states_recv_fetches_range b (Rust.withPanics ext) 1528 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem ct1Sampled_epoch_cmp_lt
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s2 : State) (selfA msgA st_ep msg_ep : BitVec 64) (Rest : SepProp)
    (hlt : msg_ep.toNat < st_ep.toNat)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1528#64)
    (hrun2 : s2.status = .Running)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx24 : s2.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 10500#64)
      s2
      (((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest)
      (fun s3 P3 =>
        (P3 ⊢ ((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest) ∧
        s3.sp = s2.sp ∧
        s3.readReg64 .x0 = s2.readReg64 .x0 ∧
        s3.readReg64 .x1 = selfA ∧
        s3.readReg64 .x2 = s2.readReg64 .x2 ∧
        s3.readReg64 .x3 = s2.readReg64 .x3 ∧
        s3.readReg64 .x12 = s2.readReg64 .x12 ∧
        s3.readReg64 .x19 = s2.readReg64 .x19 ∧
        s3.readReg64 .x20 = msg_ep ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧
        s3.readReg64 .x24 = msgA ∧
        s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.readReg64 .x29 = s2.readReg64 .x29 ∧
        TraceCalleeSaved s3 s2) := by
  subst hx1 hx24
  have hcond1 := epoch_cmp_b_eq_of_lt hlt
  have hcond2 := epoch_cmp_b_ne_of_lt hlt
  states_recv_fetches_range b (Rust.withPanics ext) 1528 36
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem ct1Sampled_epoch_cmp_eq
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s2 : State) (selfA msgA ep : BitVec 64) (Rest : SepProp)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1528#64)
    (hrun2 : s2.status = .Running)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx24 : s2.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 7052#64)
      s2
      (((selfA + 520#64) ↦₆₄ ep) ∗ (msgA ↦₆₄ ep) ∗ Rest)
      (fun s3 P3 =>
        (P3 ⊢ ((selfA + 520#64) ↦₆₄ ep) ∗ (msgA ↦₆₄ ep) ∗ Rest) ∧
        s3.sp = s2.sp ∧
        s3.readReg64 .x0 = s2.readReg64 .x0 ∧
        s3.readReg64 .x1 = selfA ∧
        s3.readReg64 .x2 = s2.readReg64 .x2 ∧
        s3.readReg64 .x3 = s2.readReg64 .x3 ∧
        s3.readReg64 .x12 = s2.readReg64 .x12 ∧
        s3.readReg64 .x19 = s2.readReg64 .x19 ∧
        s3.readReg64 .x20 = ep ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧
        s3.readReg64 .x24 = msgA ∧
        s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.readReg64 .x29 = s2.readReg64 .x29 ∧
        TraceCalleeSaved s3 s2) := by
  subst hx1 hx24
  have hcond1 := epoch_cmp_b_eq_of_eq ep
  states_recv_fetches_range b (Rust.withPanics ext) 1528 28
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-! ## 3. Path 1: `msg.epoch > st.uc.epoch` (`Error::EpochOutOfRange`, `+1564 -> s0.x30`) -/

theorem stackAt_statesRecvStackX_from_dropGluePoly16 (sp : BitVec 64) :
    memRegion (sp - 23792#64) 19664 ∗ stackAt sp dropGluePoly16Stack ⊢
      stackAt sp statesRecvStackX := by
  rw [← stackAt_statesRecvStackX_eq_dropGluePoly16 sp]
  exact Entails.refl _

theorem stackAt_statesRecvCallee_from_allocHook (fsp : BitVec 64) :
    memRegion (fsp - 19552#64) 15456 ∗ stackAt fsp allocHookStack ⊢
      stackAt fsp statesRecvCalleeStackX := by
  rw [← stackAt_statesRecvCallee_eq_allocHook' fsp]
  exact Entails.refl _

theorem stackAt_statesRecvCallee_from_dropGluePoly16 (fsp : BitVec 64) :
    memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropGluePoly16Stack ⊢
      stackAt fsp statesRecvCalleeStackX := by
  rw [← stackAt_statesRecvCallee_eq_dropGluePoly16' fsp]
  exact Entails.refl _

theorem ct1Sampled_join_928 (selfA : BitVec 64) :
    memRegion selfA 528 ∗ memRegion (selfA + 528#64) polyArrayBytes ∗
      memRegion ((selfA + 528#64) + 384#64) 16 ⊢
    memRegion selfA chunkedStatesSize := by
  have hdec := polyDecoder_post_join (selfA + 528#64)
  refine Entails.trans (sepConj_mono_right hdec) ?_
  unfold chunkedStatesSize polyDecoderSize
  rw [ProofLib.memRegion_split' (b := selfA) (n := 528) (k := 400)
    (b' := selfA + 528#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

set_option maxHeartbeats 600000 in
/-- Writes `Err(EpochOutOfRange(msg_ep))` to `outA` and deallocates the 5 `Vec<u8>`s of `st.uc`
    at `selfA + 400#64..+528#64` (`+1564 -> +1744`, `0x55a70 -> 0x55b24`). -/
theorem ct1Sampled_write_err_and_dealloc5
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s3 : State) (fsp outA selfA msg_ep : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1564#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1 : s3.readReg64 .x1 = selfA)
    (hx19 : s3.readReg64 .x19 = outA)
    (hx20 : s3.readReg64 .x20 = msg_ep) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1744#64)
      s3
      (memRegion outA v1RecvSize ∗
        unchunkedCt1SentAt A (selfA + 400#64) uc ∗
        A.pool ∗
        stackAt fsp allocHookStack ∗
        Rest)
      (fun s8 P8 =>
        (P8 ⊢
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          memRegion (selfA + 400#64) 128 ∗
          A.pool ∗
          stackAt fsp allocHookStack ∗
          Rest) ∧
        s8.sp = fsp ∧
        s8.readReg64 .x1 = selfA ∧
        TraceCalleeSaved s8 s3) := by
  have hdealloc_raw := dealloc_raw_ok_at_statesRecv hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  states_recv_fetches_range b (Rust.withPanics ext) 1564 180
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc3 hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [memRegion_out_960_split_err outA]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v16_out
  apply ProofLib.SepWP.exists_left; intro b8_out
  apply ProofLib.SepWP.exists_left; intro v0_out
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        unchunkedCt1SentAt A (selfA + 400#64) uc ∗
        ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
         memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
         A.pool ∗ stackAt fsp allocHookStack ∗ Rest) by ac_rfl))
      (sepConj_mono_left (unchunkedCt1Sent400_entails_dealloc A selfA uc))) ?_
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro g
  refine seq_clean (mid := entry + 1616#64)
    (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
      (fiveVec400HeadersAt selfA g ∗
       vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
       vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
       vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
       vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
      A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
    ?_ ?_
  · have hstep1 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 1616#64) s3
        ((fiveVec400HeadersAt selfA g ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A g.v5.cap g.v5.ptr) ∗
         ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
          memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Rest))
        (fun sm Pm =>
          (Pm ⊢ (((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_ep) ∗
            memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936) ∗
            (fiveVec400HeadersAt selfA g ∗
             vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
             vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
             vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
             vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Rest) ∧
          (sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)) := by
      dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, noneCap]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; wp_steps; refine align_pre (Entails.of_eq (by rw [hsp3]; ac_rfl)) ?_; wp_done
    exact SepWP.strengthen_entails_const
      (sepConj_mono_left (sepConj_mono_left
        (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg_ep)))
      hstep1
  · intro s4 hpc4 hrun4 ⟨hsp4, hx1_4, htr4⟩
    refine seq_clean (mid := entry + 1648#64)
      (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
        (fiveVec400HeadersAt selfA g ∗
         vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
         vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
         vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
      (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
      ?_ ?_
    · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; wp_steps; refine align_pre (Entails.of_eq (by rw [hsp4]; ac_rfl)) ?_; wp_done
    · intro s5 hpc5 hrun5 ⟨hsp5, hx1_5, htr5⟩
      refine seq_clean (mid := entry + 1680#64)
        (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          (fiveVec400HeadersAt selfA g ∗
           vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
           vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
        (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
        ?_ ?_
      · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; wp_steps; refine align_pre (Entails.of_eq (by rw [hsp5]; ac_rfl)) ?_; wp_done
      · intro s6 hpc6 hrun6 ⟨hsp6, hx1_6, htr6⟩
        refine seq_clean (mid := entry + 1712#64)
          (P_mid := (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            (fiveVec400HeadersAt selfA g ∗
             vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
          (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
          ?_ ?_
        · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps; refine align_pre (Entails.of_eq (by rw [hsp6]; ac_rfl)) ?_; wp_done
        · intro s7 hpc7 hrun7 ⟨hsp7, hx1_7, htr7⟩
          have hstep5 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 1744#64) s7
              ((resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                (fiveVec400HeadersAt selfA g ∗
                 vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Rest)
              (fun s8 P8 =>
                (P8 ⊢ (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                  fiveVec400HeadersAt selfA g) ∗
                  A.pool ∗ stackAt fsp allocHookStack ∗ Rest) ∧
                s8.sp = fsp ∧
                s8.readReg64 .x1 = selfA ∧
                TraceCalleeSaved s8 s3) := by
            dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc]
            by_cases hc5 : (g.v5.cap == 0#64) = true <;>
              simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; wp_done
            · wp_steps; wp_apply; wp_steps; refine align_pre (Entails.of_eq (by rw [hsp7]; ac_rfl)) ?_; wp_done
          exact SepWP.strengthen_entails_const
            (Entails.trans
              (sepConj_mono_left (sepConj_mono_right (fiveVec400HeadersAt_entails_memRegion_128 selfA g)))
              (Entails.of_eq (by ac_rfl)))
            hstep5

/-- Calls `drop_glue::<[Poly; 16]>` on `selfA + 8`, restores the stack frame and callee-saved
    registers, and tail-calls `drop_glue::<[SortedSet<Pt>; 16]>` on `selfA + 528`
    (`+1744 -> s0.x30`, `0x55b24 -> 0x55b58`). -/
theorem ct1Sampled_drop_encoders_epilogue
    {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s8 : State) (selfA : BitVec 64)
    (enc : PolyEncoder) (dec : PolyDecoder)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc8 : s8.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1744#64)
    (hrun8 : s8.status = .Running)
    (hsp8 : s8.sp = s0.sp - 4240#64)
    (hx1_8 : s8.readReg64 .x1 = selfA)
    (htr8 : TraceCalleeSaved s8 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s8
      (polyEncoderAt A selfA enc ∗
        memRegion (selfA + 400#64) 128 ∗
        polyDecoderAt A (selfA + 528#64) dec ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          memRegion selfA chunkedStatesSize ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpoly16_raw := dropPoly16_ok_at_statesRecv hdealloc
  have hpt16_raw := dropSortedSetPt16_ok_at_statesRecv hdealloc
  states_recv_fetches_range b (Rust.withPanics ext) 1744 52
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc8 hpoly16_raw hpt16_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        polyEncoderAt A selfA enc ∗
        polyDecoderAt A (selfA + 528#64) dec ∗
        (memRegion (selfA + 400#64) 128 ∗
         A.pool ∗
         stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         statesRecvSavedCells s0 ∗
         Rest) by ac_rfl))
      (sepConj_mono (polyEncoderAt_entails_tag_vecs_tail A selfA enc)
        (sepConj_mono_left (polyDecoderAt_entails_vecs_tail A (selfA + 528#64) dec)))) ?_
  wp_conv_pre =>
    rw [stackAt_statesRecvCallee_eq_dropGluePoly16' (s0.sp - 4240#64)]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro dec_vecs
  apply ProofLib.SepWP.exists_left; intro enc_tag
  apply ProofLib.SepWP.exists_left; intro enc_vecs
  wp_focus_pure; intro hdec_len
  wp_focus_pure; intro henc_len
  wp_steps
  wp_call hpoly16_raw ⟨selfA + 8#64, enc_vecs⟩
  have h912 : (selfA + 528#64) + 384#64 = selfA + 912#64 := by bv_omega
  have hstack_fold :
      memRegion (s0.sp - 23792#64) 15424 ∗ stackAt (s0.sp - 4240#64) dropGluePoly16Stack ⊢
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX := by
    have h := stackAt_statesRecvCallee_from_dropGluePoly16 (s0.sp - 4240#64)
    have heq : s0.sp - 4240#64 - 19552#64 = s0.sp - 23792#64 := by bv_omega
    rwa [heq] at h
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        ((selfA ↦₆₄ enc_tag) ∗ memRegion (selfA + 8#64) polyArrayBytes ∗
         memRegion (selfA + 392#64) 8 ∗ memRegion (selfA + 400#64) 128) ∗
        (memRegion (s0.sp - 23792#64) 15424 ∗ stackAt (s0.sp - 4240#64) dropGluePoly16Stack) ∗
        (vecPtListOf A (selfA + 528#64) dec_vecs ∗
         memRegion ((selfA + 528#64) + 384#64) 16 ∗
         A.pool ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         statesRecvSavedCells s0 ∗ Rest) by rw [hsp8, h912]; ac_rfl))
      (sepConj_mono (chunked_400_join selfA enc_tag 128 528 rfl (by decide))
        (sepConj_mono_left hstack_fold))) ?_
  unfold statesRecvSavedCells
  wp_steps
  have hrest_stack := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest_stack
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
        (vecPtListOf A (selfA + 528#64) dec_vecs ∗
         A.pool ∗
         memRegion selfA 528 ∗
         memRegion ((selfA + 528#64) + 384#64) 16 ∗
         Rest) by rw [h912]; ac_rfl))
      (sepConj_mono_left hrest_stack)) ?_
  wp_conv_pre =>
    rw [stackAt_statesRecvStackX_eq_dropGluePoly16 s0.sp]
  wp_call hpt16_raw ⟨selfA + 528#64, dec_vecs⟩
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (memRegion selfA 528 ∗ memRegion (selfA + 528#64) polyArrayBytes ∗
         memRegion ((selfA + 528#64) + 384#64) 16) ∗
        A.pool ∗
        (memRegion (s0.sp - 23792#64) 19664 ∗ stackAt s0.sp dropGluePoly16Stack) ∗
        Rest by rw [h912]; ac_rfl))
      (sepConj_mono (ct1Sampled_join_928 selfA)
        (sepConj_mono_right (sepConj_mono_left
          (stackAt_statesRecvStackX_from_dropGluePoly16 s0.sp))))) ?_
  wp_done

/-- Combined `EpochOutOfRange` tail (`+1564 -> s0.x30`, `0x55a70 -> 0x55b58`). -/
theorem ct1Sampled_drop_epochOutOfRange
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s0 s3 : State) (outA selfA msg_ep : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 1564#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 4240#64)
    (hx1 : s3.readReg64 .x1 = selfA)
    (hx19 : s3.readReg64 .x19 = outA)
    (hx20 : s3.readReg64 .x20 = msg_ep)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s3
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ct1Sampled st) ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          memRegion selfA chunkedStatesSize ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
  wp_conv_pre =>
    rw [stackAt_statesRecvCallee_eq_allocHook' (s0.sp - 4240#64)]
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      memRegion outA v1RecvSize ∗
      unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
      A.pool ∗
      stackAt (s0.sp - 4240#64) allocHookStack ∗
      (polyEncoderAt A selfA st.sending_ct1 ∗
       polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
       memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0 ∗
       Rest) by ac_rfl)) ?_
  refine SepWP.seq
    (ct1Sampled_write_err_and_dealloc5 hdealloc s3 (s0.sp - 4240#64) outA selfA msg_ep st.uc
      (polyEncoderAt A selfA st.sending_ct1 ∗
       polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
       memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0 ∗
       Rest)
      hfsp_align hpc3 hrun3 hsp3 hx1 hx19 hx20) ?_
  intro s8 P8 hpc8 hrun8 ⟨hP8, hsp8, hx1_8, htr8⟩
  refine SepWP.weaken_pre hP8 ?_
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗ stackAt (s0.sp - 4240#64) allocHookStack) ∗
        (polyEncoderAt A selfA st.sending_ct1 ∗
         memRegion (selfA + 400#64) 128 ∗
         polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
         A.pool ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         statesRecvSavedCells s0 ∗
         (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗ Rest)) by ac_rfl))
      (sepConj_mono_left (stackAt_statesRecvCallee_from_allocHook (s0.sp - 4240#64)))) ?_
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      polyEncoderAt A selfA st.sending_ct1 ∗
      memRegion (selfA + 400#64) 128 ∗
      polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
      A.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗ Rest) by ac_rfl)) ?_
  refine SepWP.mono
    (ct1Sampled_drop_encoders_epilogue hdealloc s0 s8 selfA st.sending_ct1 st.receiving_ek
      (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗ Rest)
      hsp0_align hpc8 hrun8 hsp8 hx1_8 (htr8.trans htr3)) ?_
  intro sf Pf _ _ ⟨hPf, hspf, hcsf, htrf⟩
  refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hspf, hcsf, htrf⟩

end CryptoVerification.SpqrV1.States.Recv

