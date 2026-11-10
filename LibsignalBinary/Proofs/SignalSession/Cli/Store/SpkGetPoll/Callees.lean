/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.Layout
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Specifications.AsmConstants

/-!
# Callee Cell Wrappers and Inner Specification for `get_signed_pre_key::{closure#0}`

Cell-level wrappers for `decimal`, `Dir::get`, `decode_kyber_pre_key` (`decodeSignedPreKeySpec`),
`__rust_dealloc`, and `dropSpeWordSpec`, together with the inner poll specification
`spkGetPollInnerSpec` and outer framing bridge `spkGetPoll_of_inner`.
-/

/-!
# Callee Cell Wrappers and Inner Specification for `get_signed_pre_key::{closure#0}`

Cell-level wrappers for `decimal`, `Dir::get`, `decode_kyber_pre_key` (`decodeSignedPreKeySpec`),
`__rust_dealloc`, and `dropSpeWordSpec`, together with the inner poll specification
`spkGetPollInnerSpec` and outer framing bridge `spkGetPoll_of_inner`.
-/

/-!
# Callee Cell Wrappers and Inner Specification for `get_signed_pre_key::{closure#0}`

Cell-level wrappers for `decimal`, `Dir::get`, `decode_kyber_pre_key` (`decodeSignedPreKeySpec`),
`__rust_dealloc`, and `dropSpeWordSpec`, together with the inner poll specification
`spkGetPollInnerSpec` and outer framing bridge `spkGetPoll_of_inner`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession.Cli

/-! ## 1. Cell-level wrapper for `decimal` carrying `FsInv` -/

abbrev DecimalCellsGhost :=
  BitVec 32 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def decimalCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DecimalCellsGhost where
  pre := fun (id, ret, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg32 .x1 = id ∧ s.sp = fsp⌝ ∗
    (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (id, ret, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ nCap : BitVec 64, ∃∗ nPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.fs.files = s0.fs.files⌝ ∗
      (ret ↦₆₄ nCap) ∗ ((ret + 8#64) ↦₆₄ nPtr) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (keyName id).length) ∗
      SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName id) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem decimal_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {decStk calleeStk : Nat}
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hle : decStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName + decimalRelOff)
      ((decimalCellsSpec A calleeStk).inImage img) := by
  rw [← decimal_fnAddr_eq]
  refine subroutine_ok_outcome_intro fun ⟨id, ret, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (decimalCellsSpec A calleeStk).pre (id, ret, o0, o1, o2, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [decimalCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - decStk)
  let callG : DecimalGhost := ⟨id, ret⟩
  have hpre_base : s0.mem ⊨ (decimalSpec A img decStk).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [decimalSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hpre_fs := withFsInv_pre_intro (withFsInv_entry s0) hpre_base
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  refine hDecFs.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre_fs hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfs_sf, hq⟩ := withFsInv_post_elim hq
    dsimp only [Spec.inImage, decimalSpec, decimalCellsSpec, callG, keyName] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    have hfiles : sf.fs.files = s0.fs.files :=
      files_eq_at_callback hfs_sf (evs := []) (by rw [htr, List.append_nil]) (by simp [NoFsEv])
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨nCap, nPtr, hq⟩
    refine ⟨nCap, nPtr, ?_⟩
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hfiles⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withFsInv, Spec.inImage, decimalSpec, decimalCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact allowPanic_frame (F := stkRem) (fun h => h) (by simpa only [sepConj_assoc] using hq.2)
  · dsimp only [withFsInv] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact False.elim (allowPanic_not_exited hq.2)
  · dsimp only [withFsInv, decimalSpec, Spec.inImage] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact False.elim (not_satisfies_false_sepConj hq.2)

/-! ## 2. Cell-level wrapper for `Dir::get` -/

def dirGetDetached (A : RustAlloc) :
    Except Unit (List (BitVec 8)) →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | .error (), g0, g1, g2, g3, g4, g5 =>
    ⌜g0 = speWord 1⌝ ∗ speDetached A (utf8 "read") g0 g1 g2 g3 g4 g5 .invalidState
  | .ok bs, g0, g1, g2, g3, _, _ =>
    ⌜g0 = okTagVec ∧ g3 = BitVec.ofNat 64 bs.length⌝ ∗ SpqrV1.Alloc.vecU8Buf A g1 g2 bs

private theorem getResultAt_unpack (A : RustAlloc) (ret : BitVec 64)
    (gr : Except Unit (List (BitVec 8))) :
    getResultAt A ret gr ⊢
      ∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64,
      ∃∗ g3 : BitVec 64, ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64,
        words6At ret g0 g1 g2 g3 g4 g5 ∗ dirGetDetached A gr g0 g1 g2 g3 g4 g5 := by
  cases gr with
  | error u =>
    cases u
    dsimp only [getResultAt, dirGetDetached]
    refine Entails.trans (speAt_unpack A (utf8 "read") ret .invalidState) ?_
    refine Entails.sepExists_elim fun g0 => Entails.sepExists_elim fun g1 =>
      Entails.sepExists_elim fun g2 => Entails.sepExists_elim fun g3 =>
      Entails.sepExists_elim fun g4 => Entails.sepExists_elim fun g5 => ?_
    refine Entails.sepExists_right g0 (Entails.sepExists_right g1
      (Entails.sepExists_right g2 (Entails.sepExists_right g3
      (Entails.sepExists_right g4 (Entails.sepExists_right g5 ?_)))))
    dsimp only [speDetached]
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    have hpull :
        (words6At ret g0 g1 g2 g3 g4 g5 ∗
          ⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read")) =
        (⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          words6At ret g0 g1 g2 g3 g4 g5 ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read")) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨hg0, hg3, hg5⟩ => ?_
    have hgoal :
        words6At ret g0 g1 g2 g3 g4 g5 ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read") ⊢
        ⌜g0 = speWord 1⌝ ∗
          ⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          words6At ret g0 g1 g2 g3 g4 g5 ∗
          SpqrV1.Alloc.vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read") :=
      Entails.pure_right hg0 (Entails.pure_right ⟨hg0, hg3, hg5⟩ (Entails.refl _))
    exact Entails.trans hgoal (Entails.of_eq (by ac_rfl))
  | ok bs =>
    dsimp only [getResultAt, vecResultAt, dirGetDetached, words6At]
    have h8 : asm64% decResultVecOff = 8#64 := rfl
    have h32 : asm64% (decResultVecOff + vecSize) = 32#64 := rfl
    have hs : asm% (speSize - (decResultVecOff + vecSize)) = 16 := rfl
    rw [h8, h32, hs, memRegion_16_cells (ret + 32#64)]
    dsimp only [vecU8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun g5 => Entails.sepExists_elim fun g4 =>
      Entails.sepExists_elim fun g1 => Entails.sepExists_elim fun g2 => ?_
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right okTagVec (Entails.sepExists_right g1
      (Entails.sepExists_right g2 (Entails.sepExists_right (BitVec.ofNat 64 bs.length)
      (Entails.sepExists_right g4 (Entails.sepExists_right g5 ?_)))))
    rw [show (okTagVec = okTagVec ∧ BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length) = True from
      eq_true ⟨rfl, rfl⟩, pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)

abbrev DirGetCellsGhost :=
  BitVec 64 × BitVec 64 × DirGhost × BitVec 64 × BitVec 64 × BitVec 32 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def dirGetCellsSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (F0 : FsFiles) (calleeStk : Nat) : Spec DirGetCellsGhost where
  pre := fun (ret, self, dir, nCap, nPtr, id, o0, o1, o2, o3, o4, o5, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 (keyName id).length ∧
      s.sp = fsp ∧ s.fs.files = F0 ∧ PkNameOk pathOk dir id⌝ ∗
    dirAt A self dir ∗ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName id) ∗
    words6At ret o0 o1 o2 o3 o4 o5 ∗ stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, self, dir, nCap, nPtr, id, _o0, _o1, _o2, _o3, _o4, _o5, fsp) s0 sf =>
    ∃∗ gr : Except Unit (List (BitVec 8)),
    ∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64,
    ∃∗ g3 : BitVec 64, ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64,
      ⌜gr = dir.get rd F0 (keyName id) ∧ sf.trace = s0.trace⌝ ∗
      words6At ret g0 g1 g2 g3 g4 g5 ∗
      dirGetDetached A gr g0 g1 g2 g3 g4 g5 ∗
      dirAt A self dir ∗ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName id) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem dirGet_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk calleeStk : Nat} {F0 : FsFiles}
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName + dirGetRelOff)
      ((dirGetCellsSpec rd pathOk A F0 calleeStk).inImage img) := by
  rw [← dirGet_fnAddr_eq]
  refine subroutine_ok_outcome_intro
    fun ⟨ret, self, dir, nCap, nPtr, id, o0, o1, o2, o3, o4, o5, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (dirGetCellsSpec rd pathOk A F0 calleeStk).pre
      (ret, self, dir, nCap, nPtr, id, o0, o1, o2, o3, o4, o5, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [dirGetCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hfiles, hnameOk⟩, hmem⟩
  subst hfsp
  rcases hnameOk with ⟨hnlen, hdlen, hpOk⟩
  have hx3_nat : (s0.readReg64 .x3).toNat = (keyName id).length := by
    rw [hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [stackAt_sub_split s0.sp hle hhi, vecU8Buf_eq_bytes_sep_rest A nCap nPtr (keyName id)] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let nameRem := vecU8BufRest A nCap nPtr (keyName id)
  let callG : DirGetGhost := ⟨ret, self, dir, nPtr, keyName id, false⟩
  have hpre0 : s0.mem ⊨ (dirGetSpec rd pathOk A img getStk).pre callG s0 ∗
      (nameRem ∗ stkRem ∗ R) := by
    dsimp only [dirGetSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    simp only [memRegion_48_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3_nat, hnlen, hdlen, hpOk⟩, ?_⟩
    dsimp only [stkRem, nameRem]
    convert hmem using 1; ac_rfl
  refine hGet.mono_outcome callG (nameRem ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, dirGetSpec, dirGetCellsSpec, callG] at hq ⊢
    rw [hfiles] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨gr, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hdisj, hq⟩
    have hq' := Satisfies.mono (sepConj_mono_left (getResultAt_unpack A ret gr)) hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq' ⊢
    rcases hq' with ⟨g0, g1, g2, g3, g4, g5, hq'⟩
    refine ⟨gr, g0, g1, g2, g3, g4, g5, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hdisj, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi, vecU8Buf_eq_bytes_sep_rest A nCap nPtr (keyName id)]
    dsimp only [stkRem, nameRem] at hq'
    convert hq' using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, dirGetSpec, dirGetCellsSpec] at hq ⊢
    exact allowPanic_frame (F := nameRem ∗ stkRem) (fun h => h) (by simpa only [sepConj_assoc] using hq)
  · exact False.elim (allowPanic_not_exited hq)
  · dsimp only [dirGetSpec, Spec.inImage] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

/-! ## 3. Cell-level wrapper for `decode_kyber_pre_key` (`decodeSignedPreKeySpec`) -/

def decodeSpkDetached (A : RustAlloc) :
    Except SignalProtocolError SignedPreKeyRecord →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
    BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → SepProp
  | .error e, w0, w1, w2, w3, w4, w5, w6, _, _, _, _ =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝ ∗ speDetached A [] w1 w2 w3 w4 w5 w6 e
  | .ok r, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10 =>
    ⌜w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
    spkStructDetached A r.signedPreKey w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10

private theorem signedPreKeyResultAt_unpack (A : RustAlloc) (ret : BitVec 64)
    (res : Except SignalProtocolError SignedPreKeyRecord) :
    signedPreKeyResultAt A ret res ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
        words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
        decodeSpkDetached A res w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 := by
  cases res with
  | error e =>
    dsimp only [signedPreKeyResultAt, errResultAt, decodeSpkDetached]
    have htag : errTag = 0xFFFFFFFFFFFFFFFF#64 := rfl
    have hoff8 : asm64% resultErrSpeOff = 8#64 := rfl
    have hoff56 : asm64% (resultErrSpeOff + speSize) = 56#64 := rfl
    have hsz : 88 - asm% (resultErrSpeOff + speSize) = 32 := rfl
    rw [htag, hoff8, hoff56, hsz, memRegion_32_cells (ret + 56#64)]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (speAt_unpack A [] (ret + 8#64) e))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w10 => Entails.sepExists_elim fun w9 =>
      Entails.sepExists_elim fun w8 => Entails.sepExists_elim fun w7 =>
      Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 =>
      Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
      Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 => ?_
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFF#64 (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
      (Entails.sepExists_right u3 (Entails.sepExists_right u4
      (Entails.sepExists_right u5 (Entails.sepExists_right w7
      (Entails.sepExists_right w8 (Entails.sepExists_right w9
      (Entails.sepExists_right w10 ?_))))))))))
    dsimp only [words6At, words11At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  | ok r =>
    dsimp only [signedPreKeyResultAt, decodeSpkDetached]
    refine Entails.trans (spkStruct_unpack A ret r.signedPreKey) ?_
    refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
      Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
      Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 =>
      Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun w7 =>
      Entails.sepExists_elim fun w8 => Entails.sepExists_elim fun w9 =>
      Entails.sepExists_elim fun w10 => ?_
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right w6 (Entails.sepExists_right w7
      (Entails.sepExists_right w8 (Entails.sepExists_right w9
      (Entails.sepExists_right w10 ?_))))))))))
    dsimp only [spkStructDetached]
    have hpull :
        (words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          ⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature) =
        (⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature) := by ac_rfl
    rw [hpull]
    refine Entails.pure_left fun hprops => ?_
    have hgoal :
        words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature ⊢
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          ⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          SpqrV1.Alloc.vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          SpqrV1.Alloc.vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          SpqrV1.Alloc.vecU8Buf A w6 w7 r.signedPreKey.signature :=
      Entails.pure_right hprops.2.2.2.2.2 (Entails.pure_right hprops (Entails.refl _))
    exact Entails.trans hgoal (Entails.of_eq (by ac_rfl))

abbrev DecodeCellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def decodeSpkCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DecodeCellsGhost where
  pre := fun (ret, bCap, bPtr, bytes, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = bPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bytes.length ∧
      s.sp = fsp ∧ 0 < bytes.length ∧ bytes.length < 2 ^ 32⌝ ∗
    SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
    words11At ret c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, bCap, bPtr, bytes, _c0, _c1, _c2, _c3, _c4, _c5, _c6, _c7, _c8, _c9, _c10, fsp)
      s0 sf =>
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
    ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
    ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
      decodeSpkDetached A (SignedPreKeyRecord.deserialize bytes) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem decodeSpk_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeSignedPreKeySpec A img))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName + decodeSpkRelOff)
      ((decodeSpkCellsSpec A calleeStk).inImage img) := by
  rw [← decodeSpk_fnAddr_eq]
  refine subroutine_ok_outcome_intro
    fun ⟨ret, bCap, bPtr, bytes, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, fsp⟩
      R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (decodeSpkCellsSpec A calleeStk).pre
      (ret, bCap, bPtr, bytes, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [decodeSpkCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen_pos, hlen_lt⟩, hmem⟩
  subst hfsp
  have hx2_nat : (s0.readReg64 .x2).toNat = bytes.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [stackAt_sub_split s0.sp hle hhi, vecU8Buf_eq_bytes_sep_rest A bCap bPtr bytes] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  let bytesRem := vecU8BufRest A bCap bPtr bytes
  let callG : DecodeGhost := ⟨bPtr, bytes, ret⟩
  let _ : 0 < callG.bytes.length := hlen_pos
  have hpre0 : s0.mem ⊨ (decodeSignedPreKeySpec A img).pre callG s0 ∗
      (bytesRem ∗ stkRem ∗ R) := by
    dsimp only [decodeSignedPreKeySpec, callG, SpqrV1.ChainProofs.bytesAt] at hmem ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem
    refine satisfies_inImage_pre hinv ?_
    simp only [memRegion_88_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_nat, hlen_pos, hlen_lt⟩, ?_⟩
    dsimp only [stkRem, bytesRem]
    convert hmem using 1; ac_rfl
  refine hDec.mono_outcome callG (bytesRem ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, decodeSignedPreKeySpec, decodeSpkCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    rw [sepConj_assoc] at hq
    have hq' := Satisfies.mono
      (sepConj_mono_left (signedPreKeyResultAt_unpack A ret (SignedPreKeyRecord.deserialize bytes)))
      hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq' ⊢
    rcases hq' with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, hq'⟩
    refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi, vecU8Buf_eq_bytes_sep_rest A bCap bPtr bytes]
    dsimp only [SpqrV1.ChainProofs.bytesAt, stkRem, bytesRem] at hq' ⊢
    simp only [Bool.false_eq_true, ↓reduceIte]
    convert hq' using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, decodeSignedPreKeySpec, decodeSpkCellsSpec] at hq ⊢
    exact allowPanic_frame (F := bytesRem ∗ stkRem) (fun h => h) (by simpa only [sepConj_assoc] using hq)
  · exact False.elim (allowPanic_not_exited hq)
  · dsimp only [decodeSignedPreKeySpec, Spec.inImage] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

/-! ## 4. Cell-level wrappers for `__rust_dealloc` and `dropSpeWordSpec` -/

abbrev DeallocBufGhost := BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64

def deallocBufCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DeallocBufGhost where
  pre := fun (cap, ptr, bytes, fsp) s =>
    ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64⌝ ∗
    SpqrV1.Alloc.vecU8Buf A cap ptr bytes ∗ stackAt fsp calleeStk ∗ A.pool
  post := fun (_cap, _ptr, _bytes, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ stackAt fsp calleeStk ∗ A.pool

theorem deallocBuf_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hC : AllocContractsX img A ext)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName + deallocRelOff)
      ((deallocBufCellsSpec A calleeStk).inImage img) := by
  rw [← dealloc_fnAddr_eq]
  refine subroutine_ok_outcome_intro fun ⟨cap, ptr, bytes, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (deallocBufCellsSpec A calleeStk).pre (cap, ptr, bytes, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [deallocBufCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hcap⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  have hmem' := Satisfies.mono (sepConj_mono_left (vecU8Buf_ne_zero_dealloc A bytes hcap)) hmem
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hmem'
  rcases hmem' with ⟨hlay, hmem'⟩
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hx1_nat : (s0.readReg64 .x1).toNat = cap.toNat := congrArg BitVec.toNat hx1
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  have hpre0 : s0.mem ⊨
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img).pre
        (ptr, cap.toNat, 1) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_nat, hx2_nat, hlay⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem' using 1; ac_rfl
  refine hC.dealloc.mono_outcome (ptr, cap.toNat, 1) (stkRem ∗ R) s0 hpc hrun hpre0 hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, rustDeallocExternSpecWithStack, deallocBufCellsSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [Spec.inImage] at hq
    exact False.elim (not_satisfies_false_sepConj hq)
  · dsimp only [Spec.inImage] at hq
    exact False.elim (not_satisfies_false_sepConj hq)
  · dsimp only [Spec.inImage] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

abbrev DropSpeCellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def dropSpeWordCellsSpec (A : RustAlloc) (calleeStk : Nat) : Spec DropSpeCellsGhost where
  pre := fun (a, d1, d2, d3, d4, d5, fsp) s =>
    ⌜s.readReg64 .x0 = a ∧ s.sp = fsp⌝ ∗
    words6At a (speWord 14) d1 d2 d3 d4 d5 ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (a, _d1, _d2, _d3, _d4, _d5, fsp) s0 sf =>
    ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64,
    ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      words6At a c0 c1 c2 c3 c4 c5 ∗
      stackAt fsp calleeStk ∗ A.pool

theorem dropSpeWord_cells_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {calleeStk : Nat}
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDropSpeName)
      (dropSpeWordSpec A img))
    (hle : dropSpeStackX ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName + dropSpeRelOff)
      ((dropSpeWordCellsSpec A calleeStk).inImage img) := by
  rw [← cliDropSpe_fnAddr_eq]
  refine subroutine_ok_outcome_intro fun ⟨a, d1, d2, d3, d4, d5, fsp⟩ R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (dropSpeWordCellsSpec A calleeStk).pre (a, d1, d2, d3, d4, d5, fsp) s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  simp only [dropSpeWordCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - dropSpeStackX)
  let callG : DropSpeWordGhost := ⟨a, 14⟩
  have hpre0 : s0.mem ⊨ (dropSpeWordSpec A img).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [dropSpeWordSpec, callG]
    refine satisfies_inImage_pre hinv ?_
    simp only [memRegion_40_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨d5, d4, d3, d2, d1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Or.inr trivial⟩, ?_⟩
    dsimp only [words6At, stkRem] at hmem ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    convert hmem using 1; ac_rfl
  refine hDrop.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, dropSpeWordSpec, dropSpeWordCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [memRegion_48_cells, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨c5, c4, c3, c2, c1, c0, hq⟩
    refine ⟨c0, c1, c2, c3, c4, c5, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · dsimp only [dropSpeWordSpec, Spec.inImage] at hq
    exact False.elim (not_satisfies_false_sepConj hq)
  · dsimp only [dropSpeWordSpec, Spec.inImage] at hq
    exact False.elim (not_satisfies_false_sepConj hq)
  · dsimp only [dropSpeWordSpec, Spec.inImage] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

/-! ## 5. Inner poll spec & outer stack/box framing (`spkGetPoll_of_inner`) -/

def spkGetPollInnerSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) : Spec PkPollGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.dir x.id ∧ PkSizeOk rd s.fs.files x.dir x.id⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 0#8) ∗
      dirAt A x.self x.dir ∗ memRegion x.out 88 ∗
      A.pool ∗ stackAt (s.sp - 384#64) calleeStk ∗ cells (s.sp - 384#64) 48
  post := fun x s0 sf =>
    (∃∗ ans : PkAns SignedPreKeyRecord,
      ⌜ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace⌝ ∗
      spkAnsAt A x.out ans) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
      dirAt A x.self x.dir ∗
      A.pool ∗ stackAt (s0.sp - 384#64) calleeStk ∗ cells (s0.sp - 384#64) 48
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem spkGetPoll_of_inner {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName)
        ((spkGetPollInnerSpec rd pathOk A calleeStk).inImage img))
    (hstk : 0x180 + calleeStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetPollName)
      (spkGetPollSpec rd pathOk A img stk) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗
    (⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.dir x.id ∧ PkSizeOk rd s0.fs.files x.dir x.id⌝ ∗
      pkBoxAt x.fut x.self x.id 0#8 ∗ dirAt A x.self x.dir ∗ memRegion x.out 88 ∗
      A.pool ∗ stackAt s0.sp stk)) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hsize⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 0xd#64) 3 ∗
        dirAt A x.self x.dir ∗ memRegion x.out 88 ∗ A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 384 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 384) (by omega) hstk_hi,
    stackAt_spkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 0xd#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 384))
  have hpre_in : s0.mem ⊨ ((spkGetPollInnerSpec rd pathOk A calleeStk).inImage img).pre x s0 ∗
      (F_extra ∗ R) := by
    refine satisfies_inImage_pre hinv ?_
    dsimp only [spkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, hsize⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  refine (hInner hcal_hi).mono_outcome x (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, spkGetPollInnerSpec, spkGetPollSpec, pkGetPollSpecOf, pkBoxAt] at hq ⊢
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 384) (by omega) hstk_hi,
      stackAt_spkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, spkGetPollInnerSpec, spkGetPollSpec, pkGetPollSpecOf] at hq ⊢
    exact allowPanic_frame (F := F_extra) (fun h => h) (by simpa only [sepConj_assoc] using hq)
  · exact False.elim (allowPanic_not_exited hq)
  · dsimp only [Spec.inImage] at hq
    exact False.elim (not_satisfies_false_sepConj hq)

end CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
