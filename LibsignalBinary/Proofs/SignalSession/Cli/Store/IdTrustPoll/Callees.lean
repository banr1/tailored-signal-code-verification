/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Layout
import LibsignalBinary.Proofs.Common.InImageKit

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoGames.LibsignalSessionApi CryptoVerification.RecordCodecs
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

/-! ## Callee cell-friendly wrappers at `calleeStk` -/

abbrev DirGetCellsGhost :=
  BitVec 64 × BitVec 64 × DirGhost × BitVec 64 × List (BitVec 8) × BitVec 64

def dirGetCellsSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) : Spec DirGetCellsGhost where
  pre := fun (ret, self, dir, nameA, name, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nameA ∧
      (s.readReg64 .x3).toNat = name.length ∧ s.sp = fsp ∧
      name.length < 2 ^ 32 ∧ dir.path.length < 2 ^ 32 ∧ pathOk (pathOf dir.path name)⌝ ∗
      dirAt A self dir ∗ (nameA ↦ₛ name) ∗ memRegion ret 48 ∗ stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, self, dir, nameA, name, fsp) s0 sf =>
    (∃∗ r : Except Unit (List (BitVec 8)),
      ⌜r = dir.get rd s0.fs.files name ∧ sf.trace = s0.trace⌝ ∗
        getResultAt A ret r) ∗
      dirAt A self dir ∗ (nameA ↦ₛ name) ∗ stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem dirGet_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk calleeStk : Nat}
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      ((dirGetCellsSpec rd pathOk A calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨ret, self, dir, nameA, name, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (dirGetCellsSpec rd pathOk A calleeStk).pre (ret, self, dir, nameA, name, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [dirGetCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnl, hpl, hpok⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost := ⟨ret, self, dir, nameA, name, false⟩
  have hpre0 : s0.mem ⊨ (dirGetSpec rd pathOk A img getStk).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [dirGetSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnl, hpl, hpok⟩, ?_⟩
    have hif : (if false = true then (nameA ↦ᵣ name) else (nameA ↦ₛ name)) = (nameA ↦ₛ name) := rfl
    dsimp only [SpqrV1.ChainProofs.bytesAt, stkRem]
    rw [hif]
    convert hmem using 1; ac_rfl
  refine hGet.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hif : (if false = true then (nameA ↦ᵣ name) else (nameA ↦ₛ name)) = (nameA ↦ₛ name) := rfl
    dsimp only [Spec.inImage, dirGetSpec, dirGetCellsSpec, SpqrV1.ChainProofs.bytesAt, callG] at hq ⊢
    rw [hif] at hq
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, dirGetSpec, dirGetCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [dirGetSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

abbrev IkDecodeCellsGhost :=
  BitVec 64 × List (BitVec 8) × BitVec 64 × IdentityKey × BitVec 64

def ikDecodeCellsSpec (img : Obj.Image) (calleeStk : Nat) :
    Spec IkDecodeCellsGhost where
  pre := fun (bytesA, bytes, ret, ik, fsp) s =>
    ⌜s.readReg64 .x0 = bytesA ∧ (s.readReg64 .x1).toNat = bytes.length ∧
      s.readReg64 .x8 = ret ∧ s.sp = fsp ∧ decodeIdentityKey bytes = .ok ik⌝ ∗
      (bytesA ↦ₛ bytes) ∗ memRegion ret 48 ∗ logOff img ∗ stackAt fsp calleeStk
  post := fun (bytesA, bytes, ret, ik, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦₆₄ okTagVec) ∗ ((ret + 8#64) ↦ₛ ik.publicKey.bytes.toList) ∗
      memRegion (ret + 40#64) 8 ∗
      (bytesA ↦ₛ bytes) ∗ logOff img ∗ stackAt fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem ikDecode_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr RecordCodecsBinary.identityKeyDecodeName)
      (RecordCodecsBinary.identityKeyDecodeSpec A img))
    (hle : 0x60 ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr RecordCodecsBinary.identityKeyDecodeName)
      ((ikDecodeCellsSpec img calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨bytesA, bytes, ret, ik, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (ikDecodeCellsSpec img calleeStk).pre (bytesA, bytes, ret, ik, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [ikDecodeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hfsp, hdec⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - 0x60)
  let callG : RecordCodecsBinary.DecodeGhost := ⟨bytesA, bytes, ret⟩
  have hpre0 : s0.mem ⊨ (RecordCodecsBinary.identityKeyDecodeSpec A img).pre callG s0 ∗
      (stkRem ∗ R) := by
    dsimp only [RecordCodecsBinary.identityKeyDecodeSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine hDec.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, RecordCodecsBinary.identityKeyDecodeSpec,
      ikDecodeCellsSpec, callG] at hq ⊢
    rw [hdec] at hq
    dsimp only [RecordCodecsBinary.identityKeyResultAt] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [Spec.inImage, RecordCodecsBinary.identityKeyDecodeSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [RecordCodecsBinary.identityKeyDecodeSpec, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

abbrev DeallocVecBufGhost := BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64

def deallocVecBufSpec (A : RustAlloc) (calleeStk : Nat) : Spec DeallocVecBufGhost where
  pre := fun (bPtr, bCap, bs, fsp) s =>
    ⌜s.readReg64 .x0 = bPtr ∧ s.readReg64 .x1 = bCap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp ∧ bs.length ≤ bCap.toNat ∧ bCap.toNat < 2 ^ 63 ∧ bCap ≠ 0#64⌝ ∗
      (bPtr ↦ₛ bs) ∗ vecU8BufRest A bCap bPtr bs.length ∗ A.pool ∗ stackAt fsp calleeStk
  post := fun (_bPtr, _bCap, _bs, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem deallocVecBuf_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hC : AllocContractsX img A ext)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((deallocVecBufSpec A calleeStk).inImage img) := by
  have hDealloc := dealloc_ok_at_norm_ext_x hC (name := idTrustPollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity::{closure#0}"
      "__rustc::__rust_dealloc"))
    dealloc_fnOff_rel
  refine subroutine_ok_outcome_intro fun ⟨bPtr, bCap, bs, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (deallocVecBufSpec A calleeStk).pre (bPtr, bCap, bs, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [deallocVecBufSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen, hlt, hnz⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  dsimp only [vecU8BufRest] at hmem
  simp only [hnz, ↓reduceIte] at hmem
  have hreg : (bPtr ↦ₛ bs) ∗ memRegion (bPtr + BitVec.ofNat 64 bs.length) (bCap.toNat - bs.length) ⊢
      memRegion bPtr bCap.toNat := by
    have hsplit : memRegion bPtr bCap.toNat =
        memRegion bPtr bs.length ∗
        memRegion (bPtr + BitVec.ofNat 64 bs.length) (bCap.toNat - bs.length) := by
      have heq : bCap.toNat = bs.length + (bCap.toNat - bs.length) := by omega
      conv_lhs => rw [heq]
      rw [memRegion_split bPtr bs.length (bCap.toNat - bs.length) (by omega)]
    rw [hsplit]
    exact sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsToBytes bPtr bs))
  have hlay : LayoutOk bCap.toNat 1 := ⟨by bv_omega, ⟨0, rfl⟩, by omega⟩
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hmem_reg : s0.mem ⊨
      memRegion bPtr bCap.toNat ∗
      (A.live bPtr bCap.toNat 1 ∗ A.pool ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left hreg) ?_
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hpre0 : s0.mem ⊨ ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
      (bPtr, bCap.toNat, 1) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by rw [hx1], by rw [hx2]; rfl, hlay⟩, ?_⟩
    convert hmem_reg using 1; ac_rfl
  refine hDealloc.mono_outcome (bPtr, bCap.toNat, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, rustDeallocExternSpecWithStack, deallocVecBufSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [Spec.inImage, rustDeallocExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [rustDeallocExternSpecWithStack, Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

abbrev PkEqCellsGhost := BitVec 64 × IdentityKey × BitVec 64 × IdentityKey × BitVec 64

noncomputable def pkEqCellsSpec (calleeStk : Nat) : Spec PkEqCellsGhost where
  pre := fun (p1, ik1, p2, ik2, fsp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = fsp⌝ ∗
      (p1 ↦ₛ ik1.publicKey.bytes.toList) ∗ (p2 ↦ₛ ik2.publicKey.bytes.toList) ∗
      stackAt fsp calleeStk
  post := fun (p1, ik1, p2, ik2, fsp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if decide (ik1 = ik2) then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ ik1.publicKey.bytes.toList) ∗ (p2 ↦ₛ ik2.publicKey.bytes.toList) ∗
      stackAt fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem pkEq_cells_ok {img : Obj.Image}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hEq : Getters.PublicKeyEqOkExt img.base ext)
    (hle : 64 ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.publicKeyEqName)
      ((pkEqCellsSpec calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨p1, ik1, p2, ik2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (pkEqCellsSpec calleeStk).pre (p1, ik1, p2, ik2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hinv, hpre⟩
  simp only [pkEqCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - 64)
  have hpre0 : s0.mem ⊨ Getters.publicKeyEqSpec.pre
      (p1, ik1.publicKey, p2, ik2.publicKey, s0.sp) s0 ∗ (stkRem ∗ R) := by
    dsimp only [Getters.publicKeyEqSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, rfl⟩, ?_⟩
    rw [← stackAt_64_eq_pkEq_frames s0.sp]
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine subroutine_ok.mono_outcome hEq (p1, ik1.publicKey, p2, ik2.publicKey, s0.sp) (stkRem ∗ R)
    s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, Getters.publicKeyEqSpec, pkEqCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hr0, htr⟩, hq⟩
    rw [publicKey_beq_eq_decide] at hr0
    refine ⟨⟨hr0, htr⟩, ?_⟩
    rw [← stackAt_64_eq_pkEq_frames s0.sp] at hq
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [Getters.publicKeyEqSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Getters.publicKeyEqSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Getters.publicKeyEqSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem pkEq_cells_ok_ext32 {img : Obj.Image}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hEq : Getters.PublicKeyEqOkExt32 img.base ext)
    (hle : Getters.publicKeyEqStackExt ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Getters.publicKeyEqName)
      ((pkEqCellsSpec calleeStk).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨p1, ik1, p2, ik2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (pkEqCellsSpec calleeStk).pre (p1, ik1, p2, ik2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hinv, hpre⟩
  simp only [pkEqCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk)
    (calleeStk - Getters.publicKeyEqStackExt)
  have hpre0 : s0.mem ⊨ Getters.publicKeyEqSpecExt.pre
      (p1, ik1.publicKey, p2, ik2.publicKey, s0.sp) s0 ∗ (stkRem ∗ R) := by
    dsimp only [Getters.publicKeyEqSpecExt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, rfl⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  refine subroutine_ok.mono_outcome hEq (p1, ik1.publicKey, p2, ik2.publicKey, s0.sp) (stkRem ∗ R)
    s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, Getters.publicKeyEqSpecExt, pkEqCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hr0, htr⟩, hq⟩
    rw [publicKey_beq_eq_decide] at hr0
    refine ⟨⟨hr0, htr⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [Getters.publicKeyEqSpecExt] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Getters.publicKeyEqSpecExt] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Getters.publicKeyEqSpecExt] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## Inner poll spec & outer wrapper (`idTrustPoll_of_inner`) -/

def cliIdTrustPollInnerSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (calleeStk : Nat) : Spec IdPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.call.fut ∧ s.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.peers.path x.call.call.addr.name.bytes) ∧
      (∀ bs, x.peers.get rd s.fs.files x.call.call.addr.name.bytes = .ok bs → IdFileWf bs) ∧
      x.call.call.addr.name.bytes.length ≤ x.call.call.addr.name.cap.toNat ∧
      x.call.call.addr.name.cap.toNat < 2 ^ 63 ∧ x.call.call.addr.name.ptr ≠ 0#64⌝ ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
      dirAt A (x.self + 40#64) x.peers ∗ memRegion x.call.out 48 ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
      A.pool ∗ stackAt (s.sp - 192#64) calleeStk ∗ cells (s.sp - 192#64) 24
  post := fun x s0 sf =>
    (∃∗ gr : Except Unit (List (BitVec 8)),
      ∃∗ p : Except Unit (Option IdentityKey),
      ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.name.bytes ∧ sf.trace = s0.trace) ∧
        IdPeerAns gr p⌝ ∗
      idTrustOutAt A x.call.out (idTrustOf p x.call.call.key)) ∗
      (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
      ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
      dirAt A (x.self + 40#64) x.peers ∗
      (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
      ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
      ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
      (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
      A.pool ∗ stackAt (s0.sp - 192#64) calleeStk ∗ cells (s0.sp - 192#64) 24
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem idTrustPoll_of_inner {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName)
        ((cliIdTrustPollInnerSpec rd pathOk A img calleeStk).inImage img))
    (hstk : 0xc0 + calleeStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustPollName)
      (idTrustPollSpec rd pathOk A img stk) := by
  refine subroutine_ok_outcome_intro fun ⟨x, d⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (⌜s0.readReg64 .x0 = x.call.fut ∧ s0.readReg64 .x8 = x.call.out ∧
      x.call.call.addr.name.bytes.length < 2 ^ 32 ∧ x.peers.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.peers.path x.call.call.addr.val.name) ∧
      ∀ bs, x.peers.get rd s0.fs.files x.call.call.addr.val.name = .ok bs → IdFileWf bs⌝ ∗
      idTrustBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 d ∗
      dirAt A (x.self + 0x28#64) x.peers ∗ memRegion x.call.out 48 ∗
      protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
      A.pool ∗ stackAt s0.sp stk)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hpath, hpok, hwf⟩, hmem⟩
  dsimp only [idTrustBoxAt, AddrGhost.val] at hpok hwf hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.call.fut) (v := x.self)
      (R := ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 0x10#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 0x18#64) ↦₈ 0#8) ∗
        ((x.call.fut + 0x19#64) ↦₈ d) ∗ memRegion (x.call.fut + 0x1a#64) 6 ∗
        dirAt A (x.self + 0x28#64) x.peers ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
        A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 192 ≤ 2 ^ 64 := by omega
  rw [protocolAddressAt_eq_expose A x.call.call.addr x.call.call.addrA] at hmem
  have hmem' : s0.mem ⊨
      ⌜x.call.call.addr.name.bytes.length ≤ x.call.call.addr.name.cap.toNat ∧
        x.call.call.addr.name.cap.toNat < 2 ^ 63 ∧ x.call.call.addr.name.ptr ≠ 0#64⌝ ∗
      ((x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        ((x.call.fut + 25#64) ↦₈ d) ∗ memRegion (x.call.fut + 26#64) 6 ∗
        dirAt A (x.self + 40#64) x.peers ∗ memRegion x.call.out 48 ∗
        (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
        ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
        ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
        (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
        vecU8BufRest A x.call.call.addr.name.cap x.call.call.addr.name.ptr
          x.call.call.addr.name.bytes.length ∗
        ((x.call.call.addrA + 24#64) ↦₈ x.call.call.addr.device) ∗
        memRegion (x.call.call.addrA + 25#64) 7 ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
        A.pool ∗ stackAt s0.sp stk ∗ R) := by
    convert hmem using 1; ac_rfl
  rw [satisfies_pure_sepConj] at hmem'
  rcases hmem' with ⟨⟨hncap, hnlt, hnptr⟩, hmem⟩
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 192) (by omega) hstk_hi,
    stackAt_idTrustPoll_frame s0.sp hframe_hi] at hmem
  let F_extra :=
    ((x.call.fut + 25#64) ↦₈ d) ∗ memRegion (x.call.fut + 26#64) 6 ∗
      vecU8BufRest A x.call.call.addr.name.cap x.call.call.addr.name.ptr
        x.call.call.addr.name.bytes.length ∗
      ((x.call.call.addrA + 24#64) ↦₈ x.call.call.addr.device) ∗
      memRegion (x.call.call.addrA + 25#64) 7 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 192))
  have hpre_in : s0.mem ⊨ ((cliIdTrustPollInnerSpec rd pathOk A img calleeStk).inImage img).pre
      x s0 ∗ (F_extra ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [cliIdTrustPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, hpath, hpok, hwf, hncap, hnlt, hnptr⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  refine (hInner hcal_hi).mono_outcome x (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, cliIdTrustPollInnerSpec, idTrustPollSpec, idTrustBoxAt,
      AddrGhost.val] at hq ⊢
    rw [protocolAddressAt_eq_expose A x.call.call.addr x.call.call.addrA,
        stackAt_sub_split s0.sp (subStk := calleeStk + 192) (by omega) hstk_hi,
        stackAt_idTrustPoll_frame s0.sp hframe_hi]
    have hq_pure : sf.mem ⊨
        ⌜x.call.call.addr.name.bytes.length ≤ x.call.call.addr.name.cap.toNat ∧
          x.call.call.addr.name.cap.toNat < 2 ^ 63 ∧ x.call.call.addr.name.ptr ≠ 0#64⌝ ∗
        (((∃∗ gr : Except Unit (List (BitVec 8)), ∃∗ p : Except Unit (Option IdentityKey),
            ⌜(gr = x.peers.get rd s0.fs.files x.call.call.addr.name.bytes ∧ sf.trace = s0.trace) ∧
              IdPeerAns gr p⌝ ∗
            idTrustOutAt A x.call.out (idTrustOf p x.call.call.key)) ∗
          (x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
          ((x.call.fut + 16#64) ↦₆₄ x.call.call.keyA) ∗ ((x.call.fut + 24#64) ↦₈ 1#8) ∗
          dirAt A (x.self + 40#64) x.peers ∗
          (x.call.call.addrA ↦₆₄ x.call.call.addr.name.cap) ∗
          ((x.call.call.addrA + 8#64) ↦₆₄ x.call.call.addr.name.ptr) ∗
          ((x.call.call.addrA + 16#64) ↦₆₄ BitVec.ofNat 64 x.call.call.addr.name.bytes.length) ∗
          (x.call.call.addr.name.ptr ↦ₛ x.call.call.addr.name.bytes) ∗
          (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗ logOff img ∗
          A.pool ∗ stackAt (s0.sp - 192#64) calleeStk ∗ cells (s0.sp - 192#64) 24) ∗
        (F_extra ∗ R)) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hncap, hnlt, hnptr⟩, hq⟩
    dsimp only [F_extra] at hq_pure
    convert hq_pure using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, cliIdTrustPollInnerSpec, idTrustPollSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [Spec.inImage] at hq
    exact (not_satisfies_false_sepConj hq).elim

end CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
