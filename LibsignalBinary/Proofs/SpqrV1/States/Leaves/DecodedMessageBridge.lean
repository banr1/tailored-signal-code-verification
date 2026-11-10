/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Proof
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt1Chunk

/-!
# `<PolyDecoder as Decoder>::decoded_message` Bridge & `<HeaderSent>::recv_ct1_chunk`

**Checked by Lean.**

Bridges `Poly.DecodedMessage.polyDecoderDecodedMessage_ok` (`decodedMessageSpec A b`) to
`Leaves.polyDecoderDecodedMessageSpec A b`, and discharges `add_chunk_ok_ext`,
`polyDecoderDecodedMessage_ok_ext`, and `hA.dealloc` in `<HeaderSent>::recv_ct1_chunk` (`0x5d8fc`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

theorem optVecU8Of_eq_optVecU8At (A : RustAlloc) (a : BitVec 64) (opt : Option Bytes) :
    optVecU8Of A a opt = optVecU8At A a opt := by
  cases opt <;> rfl

theorem polyDecoderDecodedMessage_ok_of_decodedMessage
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (h : DecodedMessageOkExt b A ext) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hpre_pts : s0.mem ⊨
      (⌜b &&& 0xfff#64 = 0#64 ∧
          s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec ∧
          spqrPolyApi.decoded_message x.dec = .ok x.outMsg⌝ ∗
        memRegion x.outA 24 ∗
        (⌜x.dec.pts.length = 16⌝ ∗ polyDecoderAt A x.decA x.dec) ∗
        tokenInitAt b ∗
        reduceTableAt b ∗
        A.pool ∗
        stackAt s0.sp polyDecoderDecodedMessageStack) ∗ R := by
    refine Satisfies.mono ?_ hpre
    dsimp only [polyDecoderDecodedMessageSpec]
    exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (polyDecoderAt_dup_pts_len A x.decA x.dec))))
  have hpts_sort :
      x.dec.pts.length = 16 ∧ PolyDecoderStrictSorted x.dec ∧
        spqrPolyApi.decoded_message x.dec = .ok x.outMsg := by
    have h1 : s0.mem ⊨
        ⌜x.dec.pts.length = 16⌝ ∗
        ⌜b &&& 0xfff#64 = 0#64 ∧
          s0.readReg64 .x8 = x.outA ∧
          s0.readReg64 .x0 = x.decA ∧
          PolyDecoderStrictSorted x.dec ∧
          spqrPolyApi.decoded_message x.dec = .ok x.outMsg⌝ ∗
        (memRegion x.outA 24 ∗
          polyDecoderAt A x.decA x.dec ∗
          tokenInitAt b ∗
          reduceTableAt b ∗
          A.pool ∗
          stackAt s0.sp polyDecoderDecodedMessageStack ∗ R) := by
      refine Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre_pts
    rw [satisfies_pure_sepConj] at h1
    rcases h1 with ⟨hlen, h2⟩
    rw [satisfies_pure_sepConj] at h2
    exact ⟨hlen, h2.1.2.2.2.1, h2.1.2.2.2.2⟩
  have hdec_eq := decodedMessage_eq_ok x.dec hpts_sort.1 hpts_sort.2.1
  have hout_eq : x.outMsg = decodedMessageTotal x.dec := by
    have hdm := hpts_sort.2.2
    dsimp only [spqrPolyApi] at hdm
    rw [hdec_eq] at hdm
    exact (Except.ok.inj hdm).symm
  let x' : DecodedMessageGhost := { out := x.outA, decA := x.decA, dec := x.dec }
  have hpre' : s0.mem ⊨ (decodedMessageSpec A b).pre x' s0 ∗ R := by
    dsimp only [polyDecoderDecodedMessageSpec, decodedMessageSpec, x', Poly.vecHeaderBytes,
      polyDecoderDecodedMessageStack, decodedMessageStack] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.1⟩, hpre.2⟩
  refine h.mono_outcome x' R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [decodedMessageSpec, x'] at hpost
    dsimp only [polyDecoderDecodedMessageSpec, polyDecoderDecodedMessageStack]
    rw [hout_eq, ← optVecU8Of_eq_optVecU8At]
    exact hpost
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

/-- `<PolyDecoder as Decoder>::decoded_message` (`0x6bb80`) satisfies `polyDecoderDecodedMessageSpec A b`
    on `leavesProgAtExt b ext` given `AllocContracts b A ext`. -/
theorem polyDecoderDecodedMessage_ok_ext
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b) :=
  polyDecoderDecodedMessage_ok_of_decodedMessage (polyDecoderDecodedMessage_ok hA)

/-- `<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk` (`0x5d8fc`, 113 instructions)
    satisfies `headerSentRecvCt1ChunkSpec A F b` given `AllocContracts b A ext` and `hmemcpy`. -/
theorem header_sent_recv_ct1_chunk_ok
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName)
      (headerSentRecvCt1ChunkSpec A F b) :=
  header_sent_recv_ct1_chunk_ok_ext hA.dealloc hmemcpy
    (add_chunk_ok_ext hA) (polyDecoderDecodedMessage_ok_ext hA)

/-- `<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk` (`0x5d8fc`, 113 instructions)
    satisfies `headerSentRecvCt1ChunkSpec A F b` given only `AllocContracts b A ext`. -/
theorem header_sent_recv_ct1_chunk_ok_alloc
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr headerSentRecvCt1ChunkName)
      (headerSentRecvCt1ChunkSpec A F b) :=
  header_sent_recv_ct1_chunk_ok hA hA.session_memcpy_region

end CryptoVerification.SpqrV1.States.Leaves
