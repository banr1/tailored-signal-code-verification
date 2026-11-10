/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.LeavesCodeSymB
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Relocatable Specifications

Relocatable `[LibsignalPlacement]` `.rodata` bundle `recvCt2ChunkRoPlacedAt` and top-level
contracts (`RecvCt2ChunkPlacedOkExt`, `RecvCt2ChunkPlacedOkX`) for Block `350`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.RecvCt2Chunk

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.ChainProofs
open NextKeyInternalFacts

/-- `.rodata` symbol for `sckaKeyInfoPrefix` (`"Signal_PQCKA_V1_MLKEM768:SCKA Key"`, 33 bytes). -/
abbrev sckaKeyInfoPrefixSym : String := "spqr:.rodata..Lanon.144"

/-- `.rodata` symbol for `Authenticator.ctLabel` (`"Signal_PQCKA_V1_MLKEM768:ciphertext"`, 35 bytes). -/
abbrev ctLabelSym : String := "spqr:.rodata..Lanon.137"

/-- `.rodata` symbol for 32 zero bytes (`"spqr:.rodata.cst32+0x0"`, 32 bytes). -/
abbrev zeros32Sym : String := "spqr:.rodata.cst32+0x0"

/-- Relocatable callee specification of `<PolyDecoder as Decoder>::decoded_message` (Block `418`). -/
def polyDecodedMessagePlacedSpec [LibsignalPlacement] (A : RustAlloc) : Spec PolyDecodedMessageCall where
  pre := fun x s =>
    ⌜s.readReg64 .x8 = x.outA ∧
      s.readReg64 .x0 = x.decA ∧
      PolyDecoderStrictSorted x.dec⌝ ∗
      memRegion x.outA vecHeaderBytes ∗
      polyDecoderAt A x.decA x.dec ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗
      stackAt s.sp polyDecodedMessageStackX
  post := fun x s0 sf =>
    (∃∗ opt : Option Bytes,
      ⌜x.dec.decodedMessage = .ok opt ∧ sf.trace = s0.trace⌝ ∗
        optKeyBytesAt A x.outA opt) ∗
      polyDecoderAt A x.decA x.dec ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗
      stackAt s0.sp polyDecodedMessageStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable contract for `<PolyDecoder as Decoder>::decoded_message` (Block `418`)
    wrapped with `withLsCodeRoLoaded lsmpl`. -/
def PolyDecodedMessagePlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    (blkPl_418).base
    (withLsCodeRoLoaded lsmpl (polyDecodedMessagePlacedSpec A))

/-- Relocatable specification of `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`). -/
def recvCt2ChunkPlacedSpec [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress) (A : RustAlloc) :
    Spec (RecvCt2ChunkGhost F) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_ct2 ∧
      x.self.uc.auth.rootKey.length + 32 < 2 ^ 63⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗
      stackAt s.sp recvCt2ChunkStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedRecvChunkResultAt A x.outA (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
      memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool ∗
      stackAt s0.sp recvCt2ChunkStackX
  onPanic := fun x s0 sf =>
    ⌜((x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true ∨
        allocFailedIn s0 sf) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Relocatable contract for `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`)
    wrapped with `withLsCodeRoLoaded lsmpl`. -/
def RecvCt2ChunkPlacedOkX [LibsignalPlacement] (K : MlKem) (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_350 (Rust.withPanics ext))
    (blkPl_350).base
    (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F A))

/-- `.rodata` slice at `lsρ "spqr:.rodata..Lanon.144"` (`33` bytes): `sckaKeyInfoPrefix`. -/
theorem rodata_sckaKeyInfoPrefix_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ sckaKeyInfoPrefixSym) ↦ᵣ sckaKeyInfoPrefix) ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

/-- `.rodata` slice at `lsρ "spqr:.rodata..Lanon.137"` (`35` bytes): `Authenticator.ctLabel`. -/
theorem rodata_ctLabel_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ ctLabelSym) ↦ᵣ Authenticator.ctLabel) ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

/-- `.rodata` slice at `lsρ "spqr:.rodata.cst32+0x0"` (`32` zero bytes). -/
theorem rodata_zeros32_placed' [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((lsρ zeros32Sym) ↦ᵣ List.replicate 32 0#8) ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

theorem subroutine_ok_withLsCodeRoLoaded_rodata3_keep {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Arm64.Obj.MultiPlacement}
    {s1 s2 s3 : String} {b1 b2 b3 : List (BitVec 8)} {spec : Spec α}
    (h1 : lsroCheck s1 b1 = true) (h2 : lsroCheck s2 b2 = true) (h3 : lsroCheck s3 b3 = true)
    (h : subroutine_ok prog entry
      { spec with
        pre := fun x s => ⌜LibsignalCodeRoLoaded pl s.mem⌝ ∗
          (pl.ρ s1 ↦ᵣ b1) ∗ (pl.ρ s2 ↦ᵣ b2) ∗ (pl.ρ s3 ↦ᵣ b3) ∗ spec.pre x s
        post := fun x s0 sf =>
          (pl.ρ s1 ↦ᵣ b1) ∗ (pl.ρ s2 ↦ᵣ b2) ∗ (pl.ρ s3 ↦ᵣ b3) ∗ spec.post x s0 sf }) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) := by
  refine subroutine_ok_withLsCodeRoLoaded_of_withRoSlice h1 ?_
  refine subroutine_ok_withLsCodeRoLoaded_of_withRoSlice h2 ?_
  refine subroutine_ok_withLsCodeRoLoaded_of_withRoSlice h3 ?_
  refine subroutine_ok_mono h ?_ (fun _ _ _ _ hq => by
    dsimp only [withRoSlice] at hq ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq)
  intro x R s0 hp
  obtain ⟨hfr, hp⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [withRoSlice] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfr, Satisfies.mono (Entails.of_eq (by ac_rfl)) hp⟩

end CryptoVerification.SpqrV1.States.RecvCt2Chunk
