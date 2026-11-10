/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.Kdf.Defs

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Contract-Backed Stack & Callee Bridges

Postcondition `recvCt2ChunkPostQExt` (`20,272`-byte stack), bottom `720`-byte stack framing,
and `.inImage img` bridges for `hkdf_to_slice` and `Authenticator::update`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

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
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts SplitBytes NewFacts

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Contract-backed (`*Ext`) postcondition abbreviation for `recv_ct2_chunk`, matching
`recvCt2ChunkPostQ` with `recvCt2ChunkSpecExt` (`recvCt2ChunkStackExt = 20272`B). -/
abbrev recvCt2ChunkPostQExt (img : Obj.Image) (K : MlKem) (F : ShaCompress) (A : RustAlloc)
    (x : RecvCt2ChunkGhost F) (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (((img.base + bv% (ls_xref% 0x59a38 0x59a3c)) ↦ᵣ sckaKeyInfoPrefix) ∗
          ((img.base + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964")) ↦ᵣ List.replicate 32 0#8) ∗
          ((img.base + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
          (recvCt2ChunkSpecExt K F A img.base).post x s0 sf) ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Frame the bottom `720` stack bytes `memRegion (s0.sp - 20272#64) 720` out of a terminal
`SepWPp` segment so any segment proved against `recvCt2ChunkPostQ` (`recvCt2ChunkStackX = 19552`B)
lifts directly to `recvCt2ChunkPostQExt` (`recvCt2ChunkStackExt = 20272`B). -/
theorem sepWPp_frame_recvCt2_ext {prog : Program} {img : Obj.Image} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {x : RecvCt2ChunkGhost F} {s0 s : State} {P R : SepProp}
    (h : SepWPp prog (s0.readReg64 .x30) s P
      (recvCt2ChunkPostQ img K F A x s0 (memRegion (s0.sp - 20272#64) 720 ∗ R))
      (recvCt2ChunkPostQp K F A img.base x s0 (memRegion (s0.sp - 20272#64) 720 ∗ R))) :
    SepWPp prog (s0.readReg64 .x30) s (P ∗ memRegion (s0.sp - 20272#64) 720)
      (recvCt2ChunkPostQExt img K F A x s0 R)
      (recvCt2ChunkPostQp K F A img.base x s0 R) := by
  intro R_in hmem hcode
  have hmem' : s.mem ⊨ P ∗ (memRegion (s0.sp - 20272#64) 720 ∗ R_in) := by
    simpa only [sepConj_assoc] using hmem
  obtain ⟨sf, hsteps, hout⟩ := h (memRegion (s0.sp - 20272#64) 720 ∗ R_in) hmem' hcode
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpc, hrun, P_f, hPf_in, ⟨hQ, hsp, hcs⟩⟩ | ⟨hpan, P_f, hPf_in, hQp⟩ | ⟨_, hfalse⟩
  · refine Or.inl ⟨hpc, hrun, P_f ∗ memRegion (s0.sp - 20272#64) 720, ?_, ?_⟩
    · simpa only [sepConj_assoc] using hPf_in
    · refine ⟨fun hPf_R => ?_, hsp, hcs⟩
      have hPf_R' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 20272#64) 720 ∗ R) := by
        simpa only [sepConj_assoc] using hPf_R
      have hpost := hQ hPf_R'
      dsimp only [recvCt2ChunkSpecExt]
      dsimp only [recvCt2ChunkSpec] at hpost
      rw [stackAt_recvCt2ChunkExt_eq_X s0.sp]
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, P_f ∗ memRegion (s0.sp - 20272#64) 720, ?_, ?_⟩)
    · simpa only [sepConj_assoc] using hPf_in
    · intro hPf_R
      have hPf_R' : sf.mem ⊨ P_f ∗ (memRegion (s0.sp - 20272#64) 720 ∗ R) := by
        simpa only [sepConj_assoc] using hPf_R
      have hpan_post := hQp hPf_R'
      dsimp only [recvCt2ChunkSpec] at hpan_post ⊢
      rw [← sepConj_assoc] at hpan_post
      exact allowPanic_frame id hpan_post
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem hkdfToSlice_ok_ext_at_recvCt2 {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} (h : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + bv% (0x5de8c - 0x59834))
      ((hkdfToSliceSpqrSpecExt (spqrHkdfWith F)).inImage img) :=
  sub_ok_at_recvCt2 (callee := Kdf.hkdfToSliceName)
    (by rw [recvCt2Chunk_fnOff, hkdfToSlice_fnOff]; rfl) h

theorem authUpdate_ok_ext_at_recvCt2 {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : AuthUpdateOkExt img F A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recvCt2ChunkName + (0x58ac4#64 - 0x59834#64))
      ((authUpdateSpecExt F A).inImage img) :=
  sub_ok_at_recvCt2 (callee := authUpdateName)
    (by rw [recvCt2Chunk_fnOff, authUpdate_fnOff]; rfl) h

theorem stackAt_extHook_eq_authUpdateExt (sp : BitVec 64) :
    memRegion (sp - 20272#64) 720 ∗
      (memRegion (sp - 19552#64) 672 ∗ stackAt (sp - 2496#64) extHookStack) =
      stackAt (sp - 2496#64) authUpdateStackExt := by
  have h1 := stackAt_polyDecodedMessage_eq_extHook (sp - 2496#64)
  have h2 := stackAt_authUpdateExt_eq_poly (sp - 2496#64)
  have hsub1 : (sp - 2496#64) - 17056#64 = sp - 19552#64 := by bv_kernel
  have hsub2 : (sp - 2496#64) - 17776#64 = sp - 20272#64 := by bv_kernel
  rw [hsub1] at h1
  rw [hsub2] at h2
  rw [← h1, ← h2]

theorem stackAt_hkdfToSliceExt_eq_authUpdateExt (sp : BitVec 64) :
    memRegion (sp - 20272#64) 160 ∗ stackAt (sp - 2496#64) hkdfToSliceStackExt =
      stackAt (sp - 2496#64) authUpdateStackExt := by
  have h := stackAt_authUpdateExt_eq_hkdfExt (sp - 2496#64)
  have hsub : (sp - 2496#64) - 17776#64 = sp - 20272#64 := by bv_kernel
  rw [hsub] at h
  exact h.symm

theorem stackAt_extHook_eq_hkdfToSliceExt (sp : BitVec 64) :
    memRegion (sp - 20272#64) 720 ∗
      (memRegion (sp - 19552#64) 672 ∗ stackAt (sp - 2496#64) extHookStack) =
      memRegion (sp - 20272#64) 160 ∗ stackAt (sp - 2496#64) hkdfToSliceStackExt := by
  rw [stackAt_extHook_eq_authUpdateExt sp, stackAt_hkdfToSliceExt_eq_authUpdateExt sp]

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
