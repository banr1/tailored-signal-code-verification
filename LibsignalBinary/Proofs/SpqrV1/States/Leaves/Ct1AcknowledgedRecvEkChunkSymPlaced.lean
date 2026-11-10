/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkSym
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (Block `349`): Relocatable Symbolic Helpers

Relocatable `[LibsignalPlacement]` framed call rules, shared epilogue
(`ct1_ack_recv_ek_epilogue_244_placed`), error branch (`ct1_ack_recv_ek_err_branch_placed`),
and `decoded? = none` branch (`ct1_ack_recv_ek_none_branch_placed`) for Block `349`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16 CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt unchunkedCt1SentEkReceivedSendCt2PlacedSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff addChunkTotal
attribute [-arm64_norm] Expand.sp_sub_496_eq_esp Expand.sp_add_neg496_eq_esp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Relocatable Framed Call Rules -/

/-- Framed relocatable call rule for `withLsCodeLoaded lsmpl (addChunkSpec A)` (Block `419`)
    continuing to `next_pc` while preserving `LibsignalCodeRoLoaded lsmpl`. -/
theorem ct1AckEk_call_addChunk_cro [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addChunkSpec A)))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = decA) (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
        (fun sm Pm =>
          LibsignalCodeRoLoaded lsmpl sm.mem →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcro
  refine sepWPp_call_frozen
    (fun _ _ h hkf => h.of_keepsFrozen hkf) hcro
    hcall (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcro_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, addChunkSpec]; rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩
  · dsimp only [withLsCodeLoaded, addChunkSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    apply of_sepWP_lscro hcro_sf (mid := next_pc)
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStack))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted'

/-- Framed relocatable call rule for `withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)`
    (Block `418`), preserving `LibsignalCodeRoLoaded lsmpl`. -/
theorem ct1AckEk_call_decodedMessage_cro [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)))
    (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec) (hdm : spqrPolyApi.decoded_message dec = .ok outMsg)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx8 : s.readReg64 Reg.x8 = outA) (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A decA dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
      stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
          stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
        post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcro
  refine sepWPp_call_frozen
    (fun _ _ h hkf => h.of_keepsFrozen hkf) hcro
    hcall (x := ⟨outA, decA, dec, outMsg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcro_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpec]; rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hsorted, hdm⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢; rw [htrace] at haf htr_sub; exact ⟨haf, htr_sub⟩
  · dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hassoc :
        (optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
          stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame =
        (optVecU8At A outA outMsg ∗
          (polyDecoderAt A decA dec ∗
            (tokenInitPlacedAt ∗ (reduceTablePlacedAt ∗
              (A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hcro_sf

/-- Framed relocatable call rule for `withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K)`
    (Block `338`), preserving `LibsignalCodeLoaded lsmpl`. -/
theorem ct1AckEk_call_unchunkedRecvEk_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {prog : Program}
    {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K)))
    (outA stA ekA : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (ek : Bytes)
    (ucRes : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (hrecv : st.recv_ek K st.epoch ek = StatesResult.ofError ucRes)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.epoch) (hx3 : s.readReg64 Reg.x3 = ekA)
    (hsplit : P = (memRegion outA 128 ∗ unchunkedCt1SentAt A stA st ∗
      vecU8 A ekA ek ∗ A.pool ∗ stackAt sp_call unchunkedRecvEkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog (s0.readReg64 Reg.lr) sf
        ((unchunkedCt1SentRecvEkResAt A outA ucRes ∗ memRegion stA 128 ∗
          memRegion ekA 24 ∗ A.pool ∗ stackAt sp_call unchunkedRecvEkStack) ∗ Frame)
        post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen
    (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := ⟨outA, stA, ekA, st, ek, ucRes⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => False.elim ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ hmem => by rw [sepConj_assoc] at hmem; exact False.elim ((satisfies_pure_sepConj _ _ _).mp hmem).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm; rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, unchunkedCt1SentRecvEkSpec]; rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hrecv⟩, hm⟩
  · dsimp only [withLsCodeLoaded, unchunkedCt1SentRecvEkSpec]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    have hassoc :
        (unchunkedCt1SentRecvEkResAt A outA ucRes ∗ memRegion stA 128 ∗
          memRegion ekA 24 ∗ A.pool ∗ stackAt sp_call unchunkedRecvEkStack) ∗ Frame =
        (unchunkedCt1SentRecvEkResAt A outA ucRes ∗
          (memRegion stA 128 ∗
            (memRegion ekA 24 ∗ (A.pool ∗ stackAt sp_call unchunkedRecvEkStack)))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hcl_sf

/-- Framed relocatable call rule for `withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)`
    (Block `264`). -/
theorem ct1AckEk_call_dropGlueSortedSetPt16_cl [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
    {s0 s : State} (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (arrA : BitVec 64) (vecs : List (List Pt))
    {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = arrA) (hlen : vecs.length = NUM_POLYS)
    (hsplit : P = (vecPtListOf A arrA vecs ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := ⟨arrA, vecs⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withLsCodeLoaded, dropGlueSortedSetPt16Spec]; rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hlen⟩, hm⟩
  · dsimp only [withLsCodeLoaded, dropGlueSortedSetPt16Spec]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_
    have hassoc :
        (memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame =
        (memRegion arrA polyArrayBytes ∗ (A.pool ∗ stackAt sp_call dropGluePoly16Stack)) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 2. Shared Epilogue (`+0x248..+0x260`) -/

/-- Relocatable shared epilogue at `+0x248..+0x260` (starting at `lsmpl.base 264` right after
    `bl drop_glue::<[SortedSet<Pt>; 16]>` jumps to the callee, returning to `+588`):
    drops `receivingEk` at `s0.sp - 1624#64`, restores callee-saved registers, and returns. -/
theorem ct1_ack_recv_ek_epilogue_244_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hsortedSet16_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
    (outA stA chunkA : BitVec 64)
    (chunk : Chunk) (receivingEk : PolyDecoder)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (s0 s : State) (R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = lsmpl.base 264)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64)
    (hlr : s.readReg64 Reg.lr = (blkPl_349).base + 588#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = s0.sp - 1624#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (ct1AcknowledgedRecvEkChunkResAt A outA res ∗
        memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 1160 ∗
        ct1AckSavedRegs s0 ∗ A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2PlacedRoAt ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 hsp0_align (by decide)
  refine SepWP.fold (polyDecoderAt_entails_vecs_tail A (s0.sp - 1624#64) receivingEk)
    (by sep_focus) ?_
  wp_pull_exists; rename_i vecs
  wp_focus_pure; intro hvecs_len
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_dropSortedSetPt16 (s0.sp - 1760#64)))
    (by sep_focus) ?_
  refine ct1AckEk_call_dropGlueSortedSetPt16_cl hsortedSet16_raw hcl (s0.sp - 1624#64) vecs
    (ret_pc := (blkPl_349).base + 588#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    hpc (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, hlr]) (by simp only [arm64_norm, htr])
    (by simp only [Reg.x0, arm64_norm, hx0]) hvecs_len (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx24, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (polyDecoder_post_join (s0.sp - 1624#64)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_sendCt2Encoder_eq_dropSortedSetPt16 (s0.sp - 1760#64)).symm)
    (by sep_focus) ?_
  wp_conv_pre => unfold ct1AckSavedRegs
  wp_steps
  refine SepWP.fold (fold_ct1AckSavedRegs s0) (by sep_focus) ?_
  refine SepWP.fold (stackAt_1760_exit_rejoin s0) (by sep_focus) ?_
  wp_done

/-! ## 3. Branch 1: `uc.recv_ek = .error e` (`+0x098..+0x0b4`, `+0x22c..+0x244`, then `+0x248`) -/

set_option maxHeartbeats 600000 in
/-- Relocatable error branch of `<Ct1Acknowledged>::recv_ek_chunk` (`uc.recv_ek = .error e`). -/
theorem ct1_ack_recv_ek_err_branch_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hsortedSet16_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
    (outA stA chunkA : BitVec 64)
    (chunk : Chunk) (receivingEk : PolyDecoder) (e : Error)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hres : res = .error e) (s0 s : State) (R : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = (blkPl_349).base + 152#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = outA)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA 528 ∗ memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        memRegion (s0.sp - 1760#64) 136 ∗ memRegion (s0.sp - 1224#64) 632 ∗
        unchunkedCt1SentRecvEkResAt A (F := F) (s0.sp - 592#64) (.error e) ∗
        memRegion (s0.sp - 464#64) 400 ∗ ct1AckSavedRegs s0 ∗
        A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2PlacedRoAt ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  subst hres
  have hepilogue := ct1_ack_recv_ek_epilogue_244_placed (F := F) hsortedSet16_raw
    outA stA chunkA chunk receivingEk (.error e) s0
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 264)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := outA) (n := 32) (k := 496) (b' := outA + 32#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 24) (k := 608) (b' := s0.sp - 1200#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 24) (k := 584) (b' := s0.sp - 1176#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (unchunkedRecvEk_err_expose A (F := F) s0.sp e) (by sep_focus) ?_
  wp_pull_exists; rename_i w1; wp_focus_pure; intro hw1
  refine SepWP.fold (cells_4_unfold outA) (by sep_focus) ?_
  refine SepWP.fold (cells_3_unfold (s0.sp - 1200#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_2_unfold (s0.sp - 576#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (hw1 (outA + 8#64)) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_err_outA_recompose A (F := F) outA e _ _) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_err_stack_1160_rejoin s0.sp _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) fun hcl_ep => ?_
  apply ct1AckEk_sepWP_congr_pre
  · refine hepilogue _ R hcl_ep hsp0_align (by simp only [arm64_norm]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [arm64_norm] using hrun
    · simp only [State.sp, arm64_norm, hsp]
    · simp only [Reg.lr, arm64_norm]
    · simp only [arm64_norm, htr]
    · simp only [Reg.x0, arm64_norm, hsp]
    · simp only [arm64_norm, hx24]
    · simp only [arm64_norm, hx25]
    · simp only [arm64_norm, hx26]
    · simp only [arm64_norm, hx27]
    · simp only [arm64_norm, hvregs]
  · ac_rfl
  · funext sf P_f; simp only [sepConj_assoc]

/-! ## 4. Branch 2: `decoded? = none` (`+0x078..+0x080`, `+0x188..+0x228`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable `decoded? = none` branch of `<Ct1Acknowledged>::recv_ek_chunk`. -/
theorem ct1_ack_recv_ek_none_branch_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext))
      (lsmpl.ρ "memcpy") sessionMemcpyRegionSpec)
    (outA stA chunkA : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (chunk : Chunk) (receivingEk : PolyDecoder) (g_uc : FiveVecWords)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hres : res = .ok (.stillReceiving { uc := uc, receiving_ek := receivingEk }))
    (s0 s : State) (R : SepProp)
    (hsp0_align : s0.spAligned = true)
    (hpc : s.pc = (blkPl_349).base + 120#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1760#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = outA) (hx20 : s.readReg64 (Reg.gpr 20#5) = stA)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 1624#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5))
    (hx25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5))
    (hx26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5))
    (hx27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5))
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_349).rebase (blkPl_349).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA 528 ∗
        wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ∗
        relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
          (wordsBytes (fiveVecWordsList g_uc uc.epoch)) ∗
        chunkAt chunkA chunk ∗ unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        wordsAt (s0.sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗
        memRegion (s0.sp - 1632#64) 8 ∗ polyDecoderAt A (s0.sp - 1624#64) receivingEk ∗
        optVecU8At A (s0.sp - 1224#64) none ∗ memRegion (s0.sp - 1200#64) 1136 ∗
        ct1AckSavedRegs s0 ∗ A.pool ∗ stackAt (s0.sp - 1760#64) sendCt2EncoderStack)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            ct1AcknowledgedRecvEkChunkResAt A outA res ∗ memRegion stA 528 ∗
            chunkAt chunkA chunk ∗ unchunkedSendCt2PlacedRoAt ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool ∗ stackAt s0.sp ct1AcknowledgedRecvEkChunkStack) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hfsp_align : ((s0.sp - 1760#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1760#64 hsp0_align (by decide)
  wp_conv_pre =>
    dsimp only [optVecU8At]
    rw [ProofLib.memRegion_split' (b := s0.sp - 1200#64) (n := 152) (k := 984) (b' := s0.sp - 1048#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1048#64) (n := 456) (k := 528) (b' := s0.sp - 592#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 592#64) (n := 120) (k := 408) (b' := s0.sp - 472#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 472#64) (n := 400) (k := 8) (b' := s0.sp - 72#64) rfl (by bv_omega) (by decide)]
  wp_steps
  have h1224_fold :
      ((s0.sp - 1224#64) ↦₆₄ noneCap) ∗ memRegion ((s0.sp - 1224#64) + 8#64) 16 ⊢
      memRegion (s0.sp - 1224#64) 24 := by
    refine Entails.trans (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (s0.sp - 1224#64) noneCap)) ?_
    rw [← ProofLib.memRegion_split' (b := s0.sp - 1224#64) (n := 8) (k := 16) (b' := (s0.sp - 1224#64) + 8#64) rfl rfl (by decide)]
    exact Entails.refl _
  refine SepWP.fold h1224_fold (by sep_focus) ?_
  refine SepWP.fold (polyDecoderAt_extract_336_64 A (s0.sp - 1624#64) receivingEk) (by sep_focus) ?_
  wp_pull_exists; rename_i bs1 d0 d1 d2 d3 d4 d5 d6 d7
  wp_focus_pure; intro hbs1
  refine SepWP.fold (Entails.of_eq (dec_slice_400_combine (s0.sp - 1624#64) bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7))
    (by sep_focus) ?_
  have hlen400 : (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]).length = 400 := by simp [hbs1]
  refine call_memcpy_bytes_cs hmemcpy_raw (s0.sp - 472#64) (s0.sp - 1624#64)
    (bs1 ++ wordsBytes [d0, d1, d2, d3, d4, d5, d6, d7]) hlen400
    (ret_pc := (blkPl_349).base + 412#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    rfl (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx23, hx24, hx25, hx26, hx27, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (dec_slice_400_split_dst s0.sp bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7) (by sep_focus) ?_
  refine SepWP.fold (dec_slice_400_split_src s0.sp bs1 hbs1 d0 d1 d2 d3 d4 d5 d6 d7) (by sep_focus) ?_
  refine SepWP.fold (cells_15_unfold (s0.sp - 592#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre =>
    rw [wordsAt_fiveVec stA g_uc uc.epoch, wordsAt_sp1760_fiveVec s0.sp g_uc uc.epoch]
    simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq (wordsAt_fiveVec stA g_uc uc.epoch).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp1760_fiveVec s0.sp g_uc uc.epoch).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (wordsAt_sp592_fiveVecTail15 s0.sp g_uc uc.epoch).symm) (by sep_focus) ?_
  have hstA_528 :
      wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ⊢
      memRegion stA 528 := by
    refine Entails.trans (sepConj_mono_left (wordsAt_entails_memRegion _ stA 128 rfl)) ?_
    rw [← ProofLib.memRegion_split' (b := stA) (n := 128) (k := 400) (b' := stA + 128#64) rfl rfl (by decide)]
    exact Entails.refl _
  have hsp1760_136 :
      wordsAt (s0.sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (s0.sp - 1632#64) 8 ⊢
      memRegion (s0.sp - 1760#64) 136 := by
    refine Entails.trans (sepConj_mono_left (wordsAt_entails_memRegion _ (s0.sp - 1760#64) 128 rfl)) ?_
    rw [← ProofLib.memRegion_split' (b := s0.sp - 1760#64) (n := 128) (k := 8) (b' := s0.sp - 1632#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine SepWP.fold hstA_528 (by sep_focus) ?_
  refine SepWP.fold hsp1760_136 (by sep_focus) ?_
  refine SepWP.fold (tail15_and_bs1_combine s0.sp uc g_uc bs1) (by sep_focus) ?_
  have hlen456 : (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1).length = 456 := by
    rw [List.length_append, length_wordsBytes, length_fiveVecTail15, hbs1]
  refine call_memcpy_bytes_cs hmemcpy_raw (s0.sp - 1048#64) (s0.sp - 592#64)
    (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1) hlen456
    (ret_pc := (blkPl_349).base + 496#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    rfl (by simpa only [arm64_norm] using hrun1)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  have h592_mem :
      ((s0.sp - 592#64) ↦ₛ (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1)) ⊢
      memRegion (s0.sp - 592#64) 456 := by
    rw [← hlen456]; exact pointsToBytes_entails_memRegion (s0.sp - 592#64) _
  refine SepWP.fold h592_mem (by sep_focus) ?_
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 520) (b' := outA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 8#64) (n := 456) (k := 64) (b' := outA + 464#64) rfl (by bv_omega) (by decide)]
  refine SepWP.fold (cells_1_unfold outA) (by sep_focus) ?_
  wp_pull_exists
  wp_steps
  refine call_memcpy_bytes_cs hmemcpy_raw (outA + 8#64) (s0.sp - 1048#64)
    (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1) hlen456
    (ret_pc := (blkPl_349).base + 516#64) (sp_call := s0.sp - 1760#64) (s0 := s0)
    rfl (by simpa only [arm64_norm] using hrun2)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm, hsp2])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  have h1048_mem :
      ((s0.sp - 1048#64) ↦ₛ (wordsBytes (fiveVecTail15 g_uc uc.epoch) ++ bs1)) ⊢
      memRegion (s0.sp - 1048#64) 456 := by
    rw [← hlen456]; exact pointsToBytes_entails_memRegion (s0.sp - 1048#64) _
  refine SepWP.fold h1048_mem (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (outA + 464#64)) (by sep_focus) ?_
  wp_pull_exists
  have hd_1288 :
      wordsAt (s0.sp - 1288#64) [d0, d1, d2, d3, d4, d5, d6, d7] =
      (((s0.sp - 1288#64) ↦₆₄ d0) ∗ ((s0.sp - 1280#64) ↦₆₄ d1) ∗
       ((s0.sp - 1272#64) ↦₆₄ d2) ∗ ((s0.sp - 1264#64) ↦₆₄ d3) ∗
       ((s0.sp - 1256#64) ↦₆₄ d4) ∗ ((s0.sp - 1248#64) ↦₆₄ d5) ∗
       ((s0.sp - 1240#64) ↦₆₄ d6) ∗ ((s0.sp - 1232#64) ↦₆₄ d7)) := by
    simp only [wordsAt_8, arm64_norm]
  have hd_out464 :
      wordsAt (outA + 464#64) [d0, d1, d2, d3, d4, d5, d6, d7] =
      (((outA + 464#64) ↦₆₄ d0) ∗ ((outA + 472#64) ↦₆₄ d1) ∗
       ((outA + 480#64) ↦₆₄ d2) ∗ ((outA + 488#64) ↦₆₄ d3) ∗
       ((outA + 496#64) ↦₆₄ d4) ∗ ((outA + 504#64) ↦₆₄ d5) ∗
       ((outA + 512#64) ↦₆₄ d6) ∗ ((outA + 520#64) ↦₆₄ d7)) := by
    simp only [wordsAt_8, BitVec.add_assoc, arm64_norm]
  wp_conv_pre =>
    unfold ct1AckSavedRegs
    rw [hd_1288]
    simp only [BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hd_1288.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hd_out464.symm) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_none_outA_recompose A outA uc receivingEk g_uc bs1 hbs1
    d0 d1 d2 d3 d4 d5 d6 d7 res hres) (by sep_focus) ?_
  refine SepWP.fold (fold_ct1AckSavedRegs s0) (by sep_focus) ?_
  refine SepWP.fold (ct1Ack_none_stack_rejoin s0 d0 d1 d2 d3 d4 d5 d6 d7) (by sep_focus) ?_
  wp_done

end CryptoVerification.SpqrV1.States.Leaves
