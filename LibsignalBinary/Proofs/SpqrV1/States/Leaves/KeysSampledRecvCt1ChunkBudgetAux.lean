/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1Chunk
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpochBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (Block `370`, `RustCliAllocBudget` Core Proof)

Relocatable `[LibsignalPlacement]` framed call helpers and verification of
`<KeysSampled>::recv_ct1_chunk` (Block `370`, 107 instructions) under `RustCliAllocBudget M`,
in two-envelope, single-envelope, and canonical forms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPl_370 blkPC_370
  lsProg_370 lsmpl lsρ ls_subroutine_ok_of_block
  sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes Chunk PolyDecoder PolyEncoder SortedSetPt spqrAuthApi spqrPolyApi
)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (HeaderSent KeysSampled)
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.SpqrV1.Alloc (
  spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Auth (authenticatorAt)
open CryptoVerification.SpqrV1.Drop (
  chunkedHeaderSentAt chunkedHeaderSentSize chunkedKeysSampledAt chunked_400_join
  dropGluePoly16Stack polyEncoderAt_entails_tag_vecs_tail vecCapPtrDealloc
)
open CryptoVerification.SpqrV1.Poly (
  chunkAt polyDecoderAt polyEncoderAt polyEncoderSize resultPolyEncoderAt
)
open CryptoVerification.SpqrV1.Poly.AddChunk (
  PolyDecoderStrictSorted addChunkStack addChunkTotal
)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (
  bytesAt encodeBytesResult encodeBytesStackX
)
open CryptoVerification.SpqrV1.States.Leaves (
  AuthWords KeysSampledRecvCt1ChunkGhost Relocatable VecWords authWordsList
  authenticatorAt_extract bv_sub_sub byte_1_unfold cells_10_unfold cells_16_unfold
  cells_1_unfold cells_9_unfold emptyPolyDecoder emptyPolyDecoder_recompose
  emptyPolyDecoder_strictSorted fold_sendCt2SavedCells keysSampledRecvCt1ChunkStack
  keys_sampled_recv_ct1_chunk_ok_elim of_sepWP_lscl outA_headerSent_recompose
  polyEncoderAt_split_tag relocatedHeap satisfies_ac sendCt2SavedCells
  sepWP_congr_pre sepWPp_call_frozen slice_and_tail_entails_vecCapPtrDealloc
  sp_sub_80_add_16' sp_sub_80_add_24' sp_sub_80_add_32' sp_sub_80_add_40'
  sp_sub_80_add_48' sp_sub_80_add_56' sp_sub_80_add_64' sp_sub_80_add_72'
  sp_sub_80_add_80' sp_sub_80_sub_16 sp_sub_80_sub_80 sp_sub_80_sub_896
  sp_sub_976_add_896 stA_400_104_fold stackAt_976_addChunk_to_encodeBytesX
  stackAt_976_from_dropPoly16 stackAt_976_split stackAt_976_to_dropPoly16
  stackAt_encodeBytesX_from_allocHook stackAt_encodeBytesX_to_allocHook
  subroutine_ok_withLsCodeLoaded_of_left trace_writeVReg128
  unchunkedHeaderSentAt_400_eq vecU8Tail vecU8_entails_slice_and_tail
  vecU8_extract vecWordsList wordsAt wordsAt_10 wordsAt_16 wordsAt_6 wordsAt_9
  wordsAt_cons_off wordsAt_nil wordsBytes
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget fitsEvents_append rustCliAllocBudgetSpec
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (
  dropGluePoly16Spec drop_glue_poly16_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkEnv AddChunkPlacedOkExt AddChunkSlotsEnv addChunkSpec
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (
  EncodeBytesEnv encodeBytesAllocEvents encodeBytesSpec encodeBytesSpecX
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget (
  encode_bytes_placed_ok_ext
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  KeysSampledRecvCt1ChunkEnv KeysSampledRecvCt1ChunkPlacedOkX
  KeysSampledRecvCt1ChunkPlacedOkXOfEnv KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv
  KeysSampledRecvCt1ChunkPostEnv KeysSampledRecvCt1ChunkPreEnv
  keysSampledRecvCt1ChunkSpec keysSampledRecvCt1ChunkSpecOfEnv
  keysSampledRecvCt1ChunkSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsBudget (call_dropGluePoly16_cl)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux (
  call_memcpy_relocate_cs_budget call_rustDealloc_budget
  encodeBytesSpecX_cl_of_encodeBytesSpec_cl
  hookSat_sessionMemcpyBudget_of_region hookSat_sessionShimBudget_of_noAllocShim
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
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

/-! ## 1. Envelope Composition & Framed Budget Call Helpers -/

theorem emptyPolyDecoder_pts (ptsNeeded : Nat) :
    (emptyPolyDecoder ptsNeeded).pts = List.replicate 16 SortedSetPt.new := rfl

attribute [local irreducible] addChunkTotal emptyPolyDecoder

theorem keysSampledRecvCt1ChunkPreEnv_of_parts {F : ShaCompress}
    (x : KeysSampledRecvCt1ChunkGhost F) (evs1 : List AllocEvent)
    (h1 : AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1) :
    KeysSampledRecvCt1ChunkPreEnv x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) :=
  Or.inr ⟨evs1, encodeBytesAllocEvents x.st.uc.ek.length, rfl, h1, rfl⟩

theorem keysSampledRecvCt1ChunkPostEnv_of_parts {F : ShaCompress}
    (x : KeysSampledRecvCt1ChunkGhost F) (evs1 evs_free : List AllocEvent)
    (h1 : AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1)
    (hf : FreeOnlyEvs evs_free) :
    KeysSampledRecvCt1ChunkPostEnv x
      ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free) :=
  Or.inr ⟨evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length, evs_free, rfl,
    keysSampledRecvCt1ChunkPreEnv_of_parts x evs1 h1, hf⟩

theorem call_addChunk_cl_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk) (st : M.σ)
    (hsorted : PolyDecoderStrictSorted dec)
    (hfit : FitsEnv M lim st (AddChunkEnv ⟨decA, chunkA, dec, chunk⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = decA)
    (hx1 : s.readReg64 .x1 = chunkA)
    (hsplit : P = (polyDecoderAt A.repAlloc decA dec ∗ chunkAt chunkA chunk ∗
      A.pool lim st s ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs1 : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      AddChunkEnv ⟨decA, chunkA, dec, chunk⟩ evs1 →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog next_pc sf
        ((polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs1 st) sf ∗ stackAt sp_call addChunkStack) ∗ Frame)
        (fun sm Pm =>
          LibsignalCodeLoaded lsmpl sm.mem →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨decA, chunkA, dec, chunk⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [withLsCodeLoaded, addChunkSpec] at h
      exact not_satisfies_false_sepConj h)
    (fun _ _ hmem => by
      dsimp only [withLsCodeLoaded, addChunkSpec] at hmem
      exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hmem)))
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, addChunkSpec]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted, hfit⟩, hm⟩
  · dsimp only [withLsCodeLoaded, addChunkSpec]
    rw [hsp]
    apply of_sepWP_lscl hcl_sf (mid := next_pc)
    rw [sepExists_sepConj_left]
    wp_pull_exists; rename_i evs1
    refine SepWP.pure_elim fun ⟨htr, _, hevs1, hsorted'⟩ => ?_
    exact sepWP_congr_pre (by sep_ac_rfl)
      (hnext sf evs1 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)
        hevs1 hsorted' hcl_sf)

theorem call_addChunk_next_budget
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (addChunkSpec M A lim))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk) (st : M.σ)
    (hsorted : PolyDecoderStrictSorted dec)
    (hfit : FitsEnv M lim st (AddChunkEnv ⟨decA, chunkA, dec, chunk⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = decA)
    (hx1 : s.readReg64 .x1 = chunkA)
    (hsplit : P = (polyDecoderAt A.repAlloc decA dec ∗ chunkAt chunkA chunk ∗
      A.pool lim st s ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs1 : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      AddChunkEnv ⟨decA, chunkA, dec, chunk⟩ evs1 →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs1 st) sf ∗ stackAt sp_call addChunkStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := (⟨decA, chunkA, dec, chunk⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [addChunkSpec] at h
      exact not_satisfies_false_sepConj h)
    (fun _ _ hmem => by
      dsimp only [addChunkSpec] at hmem
      exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hmem)))
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [addChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted, hfit⟩, hm⟩
  · dsimp only [addChunkSpec]
    rw [hsp]
    apply SepWPp.of_sepWP (mid := next_pc)
    rw [sepExists_sepConj_left]
    wp_pull_exists; rename_i evs1
    refine SepWP.pure_elim fun ⟨htr, _, hevs1, hsorted'⟩ => ?_
    exact sepWP_congr_pre (by sep_ac_rfl)
      (hnext sf evs1 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)
        hevs1 hsorted')

theorem call_encodeBytesX_lscl_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeBytesSpecX A lim)))
    (out msgA : BitVec 64) (msg : Bytes) (outEnc : PolyEncoder) (st : M.σ)
    (henc : encodeBytesResult msg = .ok outEnc) (hlen_lt : msg.length < 2 ^ 64)
    (hfit : FitsEvents M lim st (encodeBytesAllocEvents msg.length))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = out)
    (hx0 : s.readReg64 .x0 = msgA)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 msg.length)
    (hsplit : P = (memRegion out 400 ∗ (msgA ↦ₛ msg) ∗
      A.pool lim st s ∗ stackAt sp_call encodeBytesStackX) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((polyEncoderAt A.repAlloc out outEnc ∗ (msgA ↦ₛ msg) ∗
          A.pool lim (M.stepEvents (encodeBytesAllocEvents msg.length) st) sf ∗
          stackAt sp_call encodeBytesStackX) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine sepWPp_call_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    hcall (x := (⟨out, false, msgA, msg⟩, st)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [withLsCodeLoaded, encodeBytesSpecX,
        LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv] at h
      exact not_satisfies_false_sepConj h)
    (fun _ _ hmem => by
      dsimp only [withLsCodeLoaded, encodeBytesSpecX,
        LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv] at hmem
      exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hmem)))
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcl_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, encodeBytesSpecX,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv,
      polyEncoderSize, bytesAt]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    have hfit_env : FitsEnv M lim st (EncodeBytesEnv msg.length) :=
      fun _ hev => hev ▸ hfit
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hx1, hlen_lt, hfit_env⟩, hm⟩
  · dsimp only [withLsCodeLoaded, encodeBytesSpecX,
      LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget.encodeBytesSpecXOfEnv, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [henc, resultPolyEncoderAt, hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hex_pull :
        ((polyEncoderAt A.repAlloc out outEnc ∗
          ((msgA ↦ₛ msg) ∗
            ((∃∗ evs : List AllocEvent,
              ⌜EncodeBytesEnv msg.length evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
              stackAt sp_call encodeBytesStackX))) ∗ Frame) =
        (∃∗ evs : List AllocEvent,
          ⌜EncodeBytesEnv msg.length evs⌝ ∗
            ((polyEncoderAt A.repAlloc out outEnc ∗ (msgA ↦ₛ msg) ∗
              A.pool lim (M.stepEvents evs st) sf ∗
              stackAt sp_call encodeBytesStackX) ∗ Frame)) := by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      exact congrArg sepExists (funext fun evs => by sep_ac_rfl)
    rw [hex_pull]
    wp_pull_exists; rename_i evs_enc
    refine SepWP.pure_elim fun hevs => ?_
    unfold EncodeBytesEnv at hevs
    subst hevs
    simpa only [sepConj_assoc] using
      hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hcl_sf

/-! ## 2. Relocatable Block-`370` Proofs (`[LibsignalPlacement]`) -/

set_option maxHeartbeats 800000 in
private theorem keys_sampled_recv_ct1_chunk_tail_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hpoly16 : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)))
    (outA stA chunkA : BitVec 64)
    (st : KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec : PolyDecoder)
    (outSt : HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout_eq : outSt = { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
                         sending_ek := outSt.sending_ek,
                         receiving_ct1 := dec })
    (st0 st2 : M.σ) (evs_pre : List AllocEvent)
    (PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop)
    (hPost : ∀ evs_free, FreeOnlyEvs evs_free →
      PostEnv ⟨outA, stA, chunkA, st, chunk, outSt⟩ (evs_pre ++ evs_free))
    (hst2_eq : st2 = M.stepEvents evs_pre st0)
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
      (polyDecoderAt A.repAlloc (outA + 480#64) dec ∗
        memRegion (s0.sp - 960#64) 400) ∗
      (polyEncoderAt A.repAlloc outA outSt.sending_ek ∗ memRegion (s0.sp - 560#64) 400 ∗
       memRegion (outA + 400#64) 80 ∗
       polyEncoderAt A.repAlloc stA st.sending_hdr ∗ memRegion (stA + 400#64) 104 ∗
       chunkAt chunkA chunk ∗
       (ekPtr ↦ₛ st.uc.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr st.uc.ek ∗
       relocatedHeap (fun dst => authenticatorAt A.repAlloc dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
       relocatedHeap (fun dst => vecU8 A.repAlloc dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
       wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
       memRegion (s0.sp - 976#64) 8 ∗ ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
       memRegion (s0.sp - 88#64) 8 ∗ sendCt2SavedCells s0 d56 ∗
       A.pool lim st2 sf2 ∗ stackAt (s0.sp - 976#64) encodeBytesStackX)))
    (hlr_ls : LsRetAddr624 (s0.readReg64 Reg.lr)) :
    SepWP ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf2 P
      (fun sf P_f =>
        (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (∃∗ evs : List AllocEvent,
              ⌜sf.trace = s0.trace ∧
                PostEnv ⟨outA, stA, chunkA, st, chunk, outSt⟩ evs⌝ ∗
              chunkedHeaderSentAt A.repAlloc outA outSt ∗
              memRegion stA 504 ∗
              chunkAt chunkA chunk ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  dsimp only [spqrPolyApi] at *
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
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc ekCap ekPtr st.uc.ek hek_le hek_lt)
    (by sep_focus) ?_
  refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A.repAlloc stA st.sending_hdr) (by sep_focus) ?_
  wp_pull_exists; rename_i hdrTag vecs
  wp_focus_pure; intro hvecs_len
  refine SepWP.fold (cells_10_unfold (outA + 400#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [hsp_words]; simp only [wordsAt_10, BitVec.add_assoc, arm64_norm]
  dsimp only [vecCapPtrDealloc, sendCt2SavedCells, RustCliAllocBudget.repAlloc]
  by_cases hcap0 : (ekCap == 0#64) = true <;>
    simp only [hcap0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps_sync_pool (lsmpl.base 265)
    refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq hout_auth_words.symm) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq hout_dk_words.symm) (by sep_focus) ?_
    refine SepWP.fold (outA_headerSent_recompose A.repAlloc outA s0.sp st.uc.auth st.uc.dk st.uc.epoch
      outSt.sending_ek dec outSt hout_eq g gdk) (by sep_focus) ?_
    refine SepWP.fold (stackAt_976_to_dropPoly16 s0 st.uc.epoch d56)
      (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
    refine call_dropGluePoly16_cl hpoly16 (stA + 8#64) vecs st2
      (s0 := s0) (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp2]) hsp0_align
      (by simp only [Reg.lr, arm64_norm, hsp2])
      (by simp only [trace_writeVReg128, arm64_norm, htr2])
      (by simp only [Reg.x0, arm64_norm, hx19_2]) hvecs_len (by sep_focus)
      (fun sf3 evs_drop hpc3 hrun3 hsp3 hcs3 htr3 _hacp hfree_drop => ?_)
    refine SepWP.fold (chunked_400_join stA hdrTag 104 504 rfl (by decide)) (by sep_focus) ?_
    refine SepWP.fold (stackAt_976_from_dropPoly16 s0.sp) (by sep_focus) ?_
    have hst_tot : M.stepEvents evs_drop st2 = M.stepEvents (evs_pre ++ evs_drop) st0 := by
      rw [hst2_eq, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    rw [hst_tot]
    refine SepWP.done hpc3 hrun3 ⟨fun R hm => ?_, hsp3,
      CalleeSavedPreserved.trans
        (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp,
          arm64_norm, hx25_2, hx26_2, hx27_2, hsp2, hvregs_2]) hcs3⟩
    rw [satisfies_sepExists]
    refine ⟨evs_pre ++ evs_drop, ?_⟩
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨htr3, hPost evs_drop hfree_drop⟩, satisfies_ac (by sep_ac_rfl) hm⟩
  · wp_steps_sync_pool (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq hout_auth_words.symm) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq hout_dk_words.symm) (by sep_focus) ?_
    refine SepWP.fold (outA_headerSent_recompose A.repAlloc outA s0.sp st.uc.auth st.uc.dk st.uc.epoch
      outSt.sending_ek dec outSt hout_eq g gdk) (by sep_focus) ?_
    refine SepWP.fold (stackAt_encodeBytesX_to_allocHook (s0.sp - 976#64)) (by sep_focus) ?_
    refine call_rustDealloc_budget hdealloc ekPtr ekCap.toNat 1 st2
      (s0 := s0) (ret_pc := (blkPl_370).base + 324#64) (target_pc := lsmpl.base 265)
      (sp_call := s0.sp - 976#64)
      rfl (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
      (by simp only [Reg.lr, arm64_norm])
      (by simp only [trace_writeVReg128, arm64_norm, htr2])
      (by simp only [Reg.x0, arm64_norm, hx23_2])
      (by simp only [Reg.x1, arm64_norm, hx22_2])
      (by simp only [Reg.x2, arm64_norm])
      (by sep_focus)
      (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
    simp only [arm64_norm, hx19_2, hx25_2, hx26_2, hx27_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
    refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 976#64)) (by sep_focus) ?_
    wp_steps_sync_pool (lsmpl.base 265)
    refine SepWP.fold (stackAt_976_to_dropPoly16 s0 st.uc.epoch d56)
      (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
    refine call_dropGluePoly16_cl hpoly16 (stA + 8#64) vecs
      (M.stepEvents (rustDeallocEvents ekCap.toNat 1) st2)
      (s0 := s0) (ret_pc := s0.readReg64 Reg.lr) (sp_call := s0.sp)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp3]) hsp0_align
      (by simp only [Reg.lr, arm64_norm, hsp3])
      (by simp only [trace_writeVReg128, arm64_norm, htr3])
      (by simp only [Reg.x0, arm64_norm, hx19_3]) hvecs_len (by sep_focus)
      (fun sf4 evs_drop hpc4 hrun4 hsp4 hcs4 htr4 _hacp hfree_drop => ?_)
    refine SepWP.fold (chunked_400_join stA hdrTag 104 504 rfl (by decide)) (by sep_focus) ?_
    refine SepWP.fold (stackAt_976_from_dropPoly16 s0.sp) (by sep_focus) ?_
    let evs_free := rustDeallocEvents ekCap.toNat 1 ++ evs_drop
    have hfree_tot : FreeOnlyEvs evs_free :=
      (FreeOnlyEvs.singleton 1 ekCap.toNat).append hfree_drop
    have hst_tot :
        M.stepEvents evs_drop (M.stepEvents (rustDeallocEvents ekCap.toNat 1) st2) =
          M.stepEvents (evs_pre ++ evs_free) st0 := by
      simp only [evs_free, hst2_eq, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
    rw [hst_tot]
    refine SepWP.done hpc4 hrun4 ⟨fun R hm => ?_, hsp4,
      CalleeSavedPreserved.trans
        (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp,
          arm64_norm, hx25_3, hx26_3, hx27_3, hsp3, hvregs_3]) hcs4⟩
    rw [satisfies_sepExists]
    refine ⟨evs_pre ++ evs_free, ?_⟩
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨htr4, hPost evs_free hfree_tot⟩, satisfies_ac (by sep_ac_rfl) hm⟩

set_option maxHeartbeats 800000 in
private theorem keys_sampled_recv_ct1_chunk_finish_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec)
    (hdealloc : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hpoly16 : subroutine_ok ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)))
    (outA stA chunkA : BitVec 64)
    (st : KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec : PolyDecoder)
    (outSt : HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout_eq : outSt = { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
                         sending_ek := outSt.sending_ek,
                         receiving_ct1 := dec })
    (st0 st2 : M.σ) (evs_pre : List AllocEvent)
    (PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop)
    (hPost : ∀ evs_free, FreeOnlyEvs evs_free →
      PostEnv ⟨outA, stA, chunkA, st, chunk, outSt⟩ (evs_pre ++ evs_free))
    (hst2_eq : st2 = M.stepEvents evs_pre st0)
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
      polyEncoderAt A.repAlloc stA st.sending_hdr ∗
      memRegion (stA + 400#64) 104 ∗
      chunkAt chunkA chunk ∗
      polyDecoderAt A.repAlloc (s0.sp - 960#64) dec ∗
      polyEncoderAt A.repAlloc (s0.sp - 560#64) outSt.sending_ek ∗
      (ekPtr ↦ₛ st.uc.ek) ∗
      vecU8Tail A.repAlloc ekCap ekPtr st.uc.ek ∗
      relocatedHeap (fun dst => authenticatorAt A.repAlloc dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      relocatedHeap (fun dst => vecU8 A.repAlloc dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
      memRegion (s0.sp - 976#64) 8 ∗
      ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (s0.sp - 88#64) 8 ∗
      sendCt2SavedCells s0 d56 ∗
      A.pool lim st2 s ∗
      stackAt (s0.sp - 976#64) encodeBytesStackX))
    (hlr_ls : LsRetAddr624 (s0.readReg64 Reg.lr)) :
    SepWP ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (∃∗ evs : List AllocEvent,
              ⌜sf.trace = s0.trace ∧
                PostEnv ⟨outA, stA, chunkA, st, chunk, outSt⟩ evs⌝ ∗
              chunkedHeaderSentAt A.repAlloc outA outSt ∗
              memRegion stA 504 ∗
              chunkAt chunkA chunk ∗
              A.pool lim (M.stepEvents evs st0) sf ∗
              stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  dsimp only [spqrPolyApi] at *
  apply sepWP_seq_lscl hcl (mid := (blkPl_370).base + 280#64)
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := outA) (n := 400) (k := 480) (b' := outA + 400#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 400#64) (n := 80) (k := 400) (b' := outA + 480#64) rfl (by bv_omega) (by decide)]
  obtain ⟨tag, htag01, encRest, henc_split⟩ :=
    polyEncoderAt_split_tag A.repAlloc (s0.sp - 560#64) outSt.sending_ek
  suffices h_mc1 : ∀ sf1 : State,
      sf1.pc = (blkPl_370).base + 264#64 → sf1.status = .Running →
      sf1.sp = s0.sp - 976#64 → CalleeSavedPreserved s sf1 → sf1.trace = s0.trace →
      SepWP ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext)) ((blkPl_370).base + 280#64) sf1
        ((polyEncoderAt A.repAlloc outA outSt.sending_ek ∗ memRegion (s0.sp - 560#64) 400) ∗
          (memRegion (outA + 400#64) 80 ∗ memRegion (outA + 480#64) 400 ∗
           polyEncoderAt A.repAlloc stA st.sending_hdr ∗ memRegion (stA + 400#64) 104 ∗
           chunkAt chunkA chunk ∗ polyDecoderAt A.repAlloc (s0.sp - 960#64) dec ∗
           (ekPtr ↦ₛ st.uc.ek) ∗ vecU8Tail A.repAlloc ekCap ekPtr st.uc.ek ∗
           relocatedHeap (fun dst => authenticatorAt A.repAlloc dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
           relocatedHeap (fun dst => vecU8 A.repAlloc dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
           wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
           memRegion (s0.sp - 976#64) 8 ∗ ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
           memRegion (s0.sp - 88#64) 8 ∗ sendCt2SavedCells s0 d56 ∗
           A.pool lim st2 sf1 ∗ stackAt (s0.sp - 976#64) encodeBytesStackX))
        (fun sm Pm =>
          LibsignalCodeLoaded lsmpl sm.mem →
          SepWP ((blkPC_370).rebase (blkPl_370).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sm Pm
            (fun sf P_f =>
              (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
                sf.mem ⊨
                  (∃∗ evs : List AllocEvent,
                    ⌜sf.trace = s0.trace ∧
                      PostEnv ⟨outA, stA, chunkA, st, chunk, outSt⟩ evs⌝ ∗
                    chunkedHeaderSentAt A.repAlloc outA outSt ∗
                    memRegion stA 504 ∗
                    chunkAt chunkA chunk ∗
                    A.pool lim (M.stepEvents evs st0) sf ∗
                    stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) by
    rcases htag01 with rfl | rfl
    · wp_conv_pre => rw [henc_split]
      wp_steps_sync_pool (lsρ "memcpy")
      refine SepWP.fold (Entails.of_eq henc_split.symm) (by sep_focus) ?_
      refine call_memcpy_relocate_cs_budget hmemcpy
        (Relocatable.of_polyEncoderAt A.repAlloc outSt.sending_ek) outA (s0.sp - 560#64) st2
        (s0 := s0) (ret_pc := (blkPl_370).base + 264#64) (target_pc := (blkPl_370).base + 280#64)
        (sp_call := s0.sp - 976#64)
        rfl (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
        (by simp only [Reg.x0, arm64_norm, hx21])
        (by simp only [Reg.x1, arm64_norm, hsp])
        (by simp only [Reg.x2, arm64_norm])
        (by sep_focus)
        (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 =>
          sepWP_congr_pre (by sep_ac_rfl) (h_mc1 sf1 hpc1 hrun1 hsp1 (CalleeSavedPreserved.trans
            (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm]) hcs1) htr1))
    · wp_conv_pre => rw [henc_split]
      wp_steps_sync_pool (lsρ "memcpy")
      refine SepWP.fold (Entails.of_eq henc_split.symm) (by sep_focus) ?_
      refine call_memcpy_relocate_cs_budget hmemcpy
        (Relocatable.of_polyEncoderAt A.repAlloc outSt.sending_ek) outA (s0.sp - 560#64) st2
        (s0 := s0) (ret_pc := (blkPl_370).base + 264#64) (target_pc := (blkPl_370).base + 280#64)
        (sp_call := s0.sp - 976#64)
        rfl (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
        (by simp only [Reg.x0, arm64_norm, hx21])
        (by simp only [Reg.x1, arm64_norm, hsp])
        (by simp only [Reg.x2, arm64_norm])
        (by sep_focus)
        (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 =>
          sepWP_congr_pre (by sep_ac_rfl) (h_mc1 sf1 hpc1 hrun1 hsp1 (CalleeSavedPreserved.trans
            (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm]) hcs1) htr1))
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hfp, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  wp_steps_sync_pool (lsρ "memcpy")
  refine call_memcpy_relocate_cs_budget hmemcpy
    (Relocatable.of_polyDecoderAt A.repAlloc dec) (outA + 480#64) (s0.sp - 960#64) st2
    (s0 := s0) (ret_pc := (blkPl_370).base + 280#64) (target_pc := (blkPl_370).base + 280#64)
    (sp_call := s0.sp - 976#64)
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
  exact keys_sampled_recv_ct1_chunk_tail_placed_budget (F := F) hdealloc hpoly16
    outA stA chunkA st chunk dec outSt
    hout_eq st0 st2 evs_pre PostEnv hPost hst2_eq g gdk ekCap ekPtr d56 hek_le hek_lt
    hcl2 hsp0_align hfsp_align
    hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hfp_2 htr2 hvregs_2 (by sep_ac_rfl) hlr_ls

set_option maxHeartbeats 800000 in
/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable `<KeysSampled>::recv_ct1_chunk` (Block `370`)
    parameterized by `withLsCodeLoaded` contracts for `add_chunk` (Block `419`),
    `encode_bytes` (Block `417`), and `drop_glue::<[Poly; 16]>` (Block `265`). -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      PreEnv x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free →
      PostEnv x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (henc : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hpoly16 : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext := by
  unfold KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv
  have hdealloc : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc_sat
  have hmemcpy : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec :=
    spqr_hook_ok_of_mem (sym := "memcpy") hmemcpy_sat
  have henc_raw : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpecX A lim)) :=
    encodeBytesSpecX_cl_of_encodeBytesSpec_cl henc
  apply subroutine_ok_withLsCodeLoaded_of_left
  simp only [lsProg_370] at hdealloc hmemcpy hadd henc_raw hpoly16 ⊢
  unfold keysSampledRecvCt1ChunkSpecOfPrePostEnv
  wpp_init x_st s0
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  rcases x_st with ⟨⟨outA, stA, chunkA, st, chunk, outSt⟩, st0⟩
  dsimp only [spqrPolyApi] at *
  dsimp only [chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  obtain ⟨henc_res, hek_len_le, hout_eq⟩ := keys_sampled_recv_ct1_chunk_ok_elim (by assumption)
  have hFit : FitsEnv M lim st0
      (PreEnv ⟨s0.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 1#5),
        s0.readReg64 (Reg.gpr 3#5), st, chunk, outSt⟩) := by assumption
  have hfit_add : FitsEnv M lim st0
      (AddChunkEnv ⟨s0.sp - 960#64, s0.readReg64 (Reg.gpr 3#5), emptyPolyDecoder 480, chunk⟩) := by
    intro evs1 hevs1
    rw [AddChunkEnv, emptyPolyDecoder_pts] at hevs1
    exact ((fitsEvents_append M lim evs1 (encodeBytesAllocEvents st.uc.ek.length) st0).mp
      (hFit _ (hPre _ evs1 hevs1))).1
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hfsp_align : ((s0.sp - 976#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 976#64 hsp0_align (by decide)
  apply of_sepWP_lscl hcl0 (mid := lsmpl.base 419)
  wp_conv_pre =>
    rw [stackAt_976_split s0.sp]
    unfold chunkedKeysSampledAt
    rw [unchunkedHeaderSentAt_400_eq A.repAlloc (s0.readReg64 (Reg.gpr 1#5)) st.uc]
  refine SepWP.fold (cells_1_unfold (s0.sp - 968#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 960#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 832#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 704#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 576#64)) (by sep_focus) ?_
  refine SepWP.fold (byte_1_unfold (s0.sp - 568#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_10_unfold (s0.sp - 80#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [wordsAt_16, wordsAt_10, arm64_norm]
  wp_steps_sync_pool (lsmpl.base 419)
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
      polyDecoderAt A.repAlloc (s0.sp - 960#64) (emptyPolyDecoder 480) := by
    simpa only [arm64_norm] using emptyPolyDecoder_recompose A.repAlloc (s0.sp - 960#64) 480 (by decide)
  refine SepWP.fold hdec_recomp (by sep_focus) ?_
  refine call_addChunk_cl_budget hadd
    (s0.sp - 960#64) (s0.readReg64 (Reg.gpr 3#5)) (emptyPolyDecoder 480) chunk st0
    (emptyPolyDecoder_strictSorted 480) hfit_add
    (s0 := s0) (ret_pc := (blkPl_370).base + 184#64) (next_pc := lsmpl.base 417)
    (sp_call := s0.sp - 976#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 evs1 hpc1 hrun1 hsp1 hcs1 htr1 hevs1 _ hcl1 => ?_)
  have hevs1_slots : AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 := by
    rwa [AddChunkEnv, emptyPolyDecoder_pts] at hevs1
  have hfit_enc : FitsEvents M lim (M.stepEvents evs1 st0) (encodeBytesAllocEvents st.uc.ek.length) :=
    ((fitsEvents_append M lim evs1 (encodeBytesAllocEvents st.uc.ek.length) st0).mp
      (hFit _ (hPre _ evs1 hevs1_slots))).2
  generalize (addChunkTotal (emptyPolyDecoder 480) chunk) = dec1 at hout_eq ⊢
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (stackAt_976_addChunk_to_encodeBytesX s0.sp) (by sep_focus) ?_
  refine SepWP.fold (authenticatorAt_extract A.repAlloc (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.fold (vecU8_entails_slice_and_tail A.repAlloc (s0.readReg64 (Reg.gpr 1#5) + 448#64) st.uc.ek)
    (by sep_focus) ?_
  wp_pull_exists; rename_i ekCap ekPtr
  wp_focus_pure; rintro ⟨hek_le, hek_lt, hek_ne⟩
  refine SepWP.fold (vecU8_extract A.repAlloc (s0.readReg64 (Reg.gpr 1#5) + 472#64) st.uc.dk)
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
  wp_steps_sync_pool (lsmpl.base 417)
  refine SepWP.fold (Entails.of_eq hst_auth_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk_words.symm) (by sep_focus) ?_
  refine SepWP.fold (stA_400_104_fold (s0.readReg64 (Reg.gpr 1#5)) g
    ekCap ekPtr (BitVec.ofNat 64 st.uc.ek.length) gdk st.uc.epoch) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  have hek_lt64 : st.uc.ek.length < 2 ^ 64 := by omega
  refine call_encodeBytesX_lscl_budget henc_raw
    (s0.sp - 560#64) ekPtr st.uc.ek outSt.sending_ek (M.stepEvents evs1 st0)
    henc_res hek_lt64 hfit_enc
    (s0 := s0) (ret_pc := (blkPl_370).base + 236#64) (sp_call := s0.sp - 976#64)
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
  have hst2_eq :
      M.stepEvents (encodeBytesAllocEvents st.uc.ek.length) (M.stepEvents evs1 st0) =
        M.stepEvents (evs1 ++ encodeBytesAllocEvents st.uc.ek.length) st0 := by
    rw [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
  refine SepWP.mono (keys_sampled_recv_ct1_chunk_finish_placed_budget (F := F) hmemcpy hdealloc hpoly16
    (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
    st chunk dec1 outSt hout_eq st0 _ (evs1 ++ encodeBytesAllocEvents st.uc.ek.length)
    PostEnv (fun evs_free hf => by
      simpa only [List.append_assoc] using hPost ⟨_, _, _, st, chunk, outSt⟩ evs1 evs_free hevs1_slots hf) hst2_eq
    g gdk ekCap ekPtr _ hek_le hek_lt
    hcl2 hsp0_align hfsp_align hpc2 hrun2 hsp2
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hfp_2 htr2 hvregs_2
    (by sep_ac_rfl) (by dsimp only [Reg.lr, Reg.x30] at *; assumption)) ?_
  intro sf P_f _ _ ⟨hmem, hsp_sf, hcs_sf⟩
  refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
  simpa only [sepExists_sepConj_left, sepConj_assoc] using hmem R hm

/-- Single-envelope (`Env`) relocatable `<KeysSampled>::recv_ct1_chunk` (Block `370`)
    parameterized by `withLsCodeLoaded` callee contracts. -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      Env x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free →
      Env x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (henc : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hpoly16 : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkXOfEnv M A lim F Env ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv
    hPre hPost hdealloc_sat hmemcpy_sat hadd henc hpoly16

/-- Canonical relocatable `<KeysSampled>::recv_ct1_chunk` (Block `370`)
    parameterized by `withLsCodeLoaded` callee contracts. -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_sat : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim)))
    (henc : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeLoaded lsmpl (encodeBytesSpec A lim)))
    (hpoly16 : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 265) (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv
    keysSampledRecvCt1ChunkPreEnv_of_parts
    keysSampledRecvCt1ChunkPostEnv_of_parts
    hdealloc_sat hmemcpy_sat hadd henc hpoly16

/-- Two-envelope (`PreEnv` / `PostEnv`) `[LibsignalPlacement]` contract for
    `<KeysSampled>::recv_ct1_chunk` (Block `370`), discharging `encode_bytes` (Block `417`) and
    `drop_glue::<[Poly; 16]>` (Block `265`) from `HookSat` hypotheses and taking `add_chunk`. -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      PreEnv x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free →
      PostEnv x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_of_callees_ofPrePostEnv
    hPre hPost hdealloc hmemcpy hadd
    (ls_subroutine_ok_of_block (i := 370) (j := 417)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (encode_bytes_placed_ok_ext
          (hookSat_sessionShimBudget_of_noAllocShim hshim)
          halloc
          (hookSat_sessionMemcpyBudget_of_region hmemcpy))))
    (ls_subroutine_ok_of_block (i := 370) (j := 265)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

/-- Single-envelope (`Env`) `[LibsignalPlacement]` contract for `<KeysSampled>::recv_ct1_chunk`
    (Block `370`). -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      Env x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free →
      Env x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkXOfEnv M A lim F Env ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_ofPrePostEnv
    hPre hPost hshim halloc hdealloc hmemcpy hadd

/-- Canonical `[LibsignalPlacement]` contract for `<KeysSampled>::recv_ct1_chunk` (Block `370`). -/
theorem keys_sampled_recv_ct1_chunk_placed_cl_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : subroutine_ok (lsProg_370 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec M A lim))) :
    KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_ofPrePostEnv
    keysSampledRecvCt1ChunkPreEnv_of_parts
    keysSampledRecvCt1ChunkPostEnv_of_parts
    hshim halloc hdealloc hmemcpy hadd

/-- Two-envelope (`PreEnv` / `PostEnv`) `[LibsignalPlacement]` contract taking `AddChunkPlacedOkExt`. -/
theorem keys_sampled_recv_ct1_chunk_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {PreEnv PostEnv : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      PreEnv x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free →
      PostEnv x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : AddChunkPlacedOkExt M A lim ext) :
    KeysSampledRecvCt1ChunkPlacedOkXOfPrePostEnv M A lim F PreEnv PostEnv ext :=
  keys_sampled_recv_ct1_chunk_placed_cl_ext_ofPrePostEnv
    hPre hPost hshim halloc hdealloc hmemcpy
    (ls_subroutine_ok_of_block (i := 370) (j := 419)
      (subroutine_ok_withLsCodeLoaded_of_plain hadd))

/-- Single-envelope (`Env`) `[LibsignalPlacement]` contract taking `AddChunkPlacedOkExt`. -/
theorem keys_sampled_recv_ct1_chunk_placed_ok_x_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    {Env : KeysSampledRecvCt1ChunkGhost F → List AllocEvent → Prop}
    (hPre : ∀ x evs1,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      Env x (evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length))
    (hPost : ∀ x evs1 evs_free,
      AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs1 →
      FreeOnlyEvs evs_free →
      Env x ((evs1 ++ encodeBytesAllocEvents x.st.uc.ek.length) ++ evs_free))
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : AddChunkPlacedOkExt M A lim ext) :
    KeysSampledRecvCt1ChunkPlacedOkXOfEnv M A lim F Env ext :=
  keys_sampled_recv_ct1_chunk_placed_ok_x_ofPrePostEnv
    hPre hPost hshim halloc hdealloc hmemcpy hadd

/-- Canonical `[LibsignalPlacement]` contract taking `AddChunkPlacedOkExt`. -/
theorem keys_sampled_recv_ct1_chunk_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
      (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionBudgetSpec)
    (hadd : AddChunkPlacedOkExt M A lim ext) :
    KeysSampledRecvCt1ChunkPlacedOkX M A lim F ext :=
  keys_sampled_recv_ct1_chunk_placed_ok_x_ofPrePostEnv
    keysSampledRecvCt1ChunkPreEnv_of_parts
    keysSampledRecvCt1ChunkPostEnv_of_parts
    hshim halloc hdealloc hmemcpy hadd

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1ChunkBudgetAux
