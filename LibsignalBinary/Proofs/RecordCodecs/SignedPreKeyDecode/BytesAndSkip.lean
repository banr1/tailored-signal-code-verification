/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `SignedPreKeyRecordStructure::decode` `bytes::merge` and `skip_field` Branches

Unified `bytes::merge` Hoare triples for tags 2 (`public_key`), 3 (`private_key`), and 4
(`signature`), error-push stubs, and unknown-tag `skip_field` (`+300 .. +316`) across fixed-image
and `[LibsignalPlacement]` (Block `562`) programs.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
attribute [local arm64_norm] BitVec.toNat_zero

namespace CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Polymorphic cursor-advance helper across generalized `prog` / `ret` -/

theorem spkAdvanceCursor_prog {subStack : Nat} {prog : Program} {ret : BitVec 64}
    {img : Obj.Image} {A : RustAlloc}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Option SignedPreKeyRecordStructure}
    {Q0 P R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (hperm : Q0 ⊢ sliceCursorAfter sp' ptr bs rest ∗ R)
    (hent : sliceCursorAt sp' (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R ⊢ P)
    (h : Wire.SepWPp prog ret s P
      (spkConvergePostAt subStack img A s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (tryFromQp s0)) :
    Wire.SepWPp prog ret s Q0
      (spkConvergePostAt subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  refine Wire.SepWPp.mono_pre hperm ?_
  rw [sliceCursorAfter_eq_take_cursorAt sp' ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at hent h ⊢
  refine Wire.SepWPp.mono_pre
    (P' := P ∗ (ptr ↦ₛ bs.take k))
    (Entails.trans (by apply entails_of_eq; ac_rfl) (sepConj_mono_left hent)) ?_
  exact Wire.SepWPp.frame_tryFrom h
    (fun sf Pf hqm => spkConvergePostAt_append_prefix subStack img A s0 sp' x19 ptr bs k hkl out sf Pf hqm)

theorem spkAdvanceToLatch_prog {subStack : Nat} {prog : Program} {ret : BitVec 64}
    {img : Obj.Image} {A : RustAlloc}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {m' : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    {Q0 : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp prog ret s
      (spkLoopMemAt subStack A sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest m')
      (spkConvergePostAt subStack img A s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (tryFromQp s0))
    (hperm : Q0 ⊢ sliceCursorAfter sp' ptr bs rest ∗
      (((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion (sp' + 112#64) 48 ∗
        spkStructLoopOf A sp' rest.length m' ∗
        memRegion x19 88 ∗
        A.pool ∗
        stackAt sp' subStack)) :
    Wire.SepWPp prog ret s Q0
      (spkConvergePostAt subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) :=
  spkAdvanceCursor_prog hsuf hperm (Entails.refl _) h

private theorem bytesMerge_ok_peel (trEq : Prop) (a b c : SepProp) (x0Eq capOk : Prop) (rest : SepProp) :
    ⌜trEq⌝ ∗ a ∗ b ∗ c ∗ ⌜x0Eq⌝ ∗ ⌜capOk⌝ ∗ rest =
      ⌜trEq⌝ ∗ ⌜x0Eq⌝ ∗ ⌜capOk⌝ ∗ a ∗ b ∗ c ∗ rest := by
  ac_rfl

/-! ## Error stubs for `bytes` fields (`+424`, `+528`, `+400` → `+648` → `+656`) -/

/-- Tag 2 (`public_key`) error push setup `+424..+456` → `+648` → `+656`. -/
theorem pushTag2_424_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_pushTag2)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = err) (hnz : err ≠ 0#64)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ decodeErrorAtStackLen A err 0 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hpush := @pushCall_648_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 424 36
  dsimp only [tripleRatchetProgAtExt] at hpush hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_pushCall) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hpush (sp' := sp') (x19 := x19) (ptr := ptr) (err := err)
      (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simp [hsp_eq, arm64_norm], by simp [h29, arm64_norm],
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [h29, arm64_norm]) hnz
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simp [htr, arm64_norm]))
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
  apply entails_of_eq
  simp only [hsp_eq, h29, arm64_norm]
  try ac_rfl

/-- Tag 3 (`private_key`) error push setup `+528..+560` → `+648` → `+656`. -/
theorem pushTag3_528_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_pushTag3)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = err) (hnz : err ≠ 0#64)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ decodeErrorAtStackLen A err 0 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hpush := @pushCall_648_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 528 36
  dsimp only [tripleRatchetProgAtExt] at hpush hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_pushCall) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hpush (sp' := sp') (x19 := x19) (ptr := ptr) (err := err)
      (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simp [hsp_eq, arm64_norm], by simp [h29, arm64_norm],
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [h29, arm64_norm]) hnz
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simp [htr, arm64_norm]))
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
  apply entails_of_eq
  simp only [hsp_eq, h29, arm64_norm]
  try ac_rfl

/-- Tag 4 (`signature`) error push setup `+400..+420` + `+636..+644` → `+648` → `+656`. -/
theorem pushTag4_400_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_pushTag4)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = err) (hnz : err ≠ 0#64)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ decodeErrorAtStackLen A err 0 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hpush := @pushCall_648_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 400 24
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 636 12
  dsimp only [tripleRatchetProgAtExt] at hpush hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_pushCall) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hpush (sp' := sp') (x19 := x19) (ptr := ptr) (err := err)
      (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simp [hsp_eq, arm64_norm], by simp [h29, arm64_norm],
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [h29, arm64_norm]) hnz
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simp [htr, arm64_norm]))
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
  apply entails_of_eq
  simp only [hsp_eq, h29, arm64_norm]
  try ac_rfl

/-! ## Unified `bytes::merge` verification for Tags 2, 3, and 4 -/

def spkBytesEntryOff : SpkBytesField → BitVec 64
  | .pub => spkOff_tag2
  | .priv => spkOff_tag3
  | .sig => spkOff_tag4

/-- Unified Hoare triple for `bytes::merge` on `f : SpkBytesField` (Tag 2 `+236`, Tag 3 `+76`, Tag 4 `+256`). -/
theorem bytesField_merge_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    (f : SpkBytesField)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (hlen : bs.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkBytesEntryOff f)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlatch : ∀ (v : List (BitVec 8)) (rest2 : List (BitVec 8)) (s3 : State),
      mergeBytes wt rest = some (v, rest2) →
      s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_latch →
      s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s3
        (spkLoopMemAt cfg.subStack A sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 (f.setBytes m v))
        (spkConvergePostAt cfg.subStack img A s0 sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 out)
        (tryFromQp s0))
    (hnone : mergeBytes wt rest = none → out = none) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (spkAfterVarintMemAt cfg.subStack A sp' x19 ptr bs rest bs.length m)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by
    rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintMemAt
  refine spkAdvanceCursorAt hsuf ?_
  let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (spkStructLoopOf_mono A sp' m hle_bs))))) ?_
  unfold spkStructLoopOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
  rw [f.split_field A g sp' m]
  simp only [sepConj_assoc]
  have hcall := B.bytesMerge7
  have hstack := stackAt_sub_split sp' cfg.mergeStk cfg.subStack
    (spkCfg_split_merge cfg) (spkCfg_subStack_le cfg)
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h24 : s.readReg64 (Reg.gpr 24#5) = sp' + 16#64 := hregs.x24
  have h0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0
  have hwt8 : (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat := by
    cases wt <;> decide
  have hcap_in : BytesMergeCapOk (f.pin g).cap rest.length := f.capOk_pin hg
  cases f with
  | pub =>
    have herr := @pushTag2_424_wp cfg img A ext B s0
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 236 20
    dsimp only [spkBytesEntryOff, SpkBytesField.slotOff, tripleRatchetProgAtExt] at hcall herr hlatch hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    refine Wire.SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]") -
        ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_tryFrom
      ⟨wt, sp' + 16#64, (SpkBytesField.pub.pin g).cap, (SpkBytesField.pub.pin g).ptr,
        SpkBytesField.pub.getBytes m, sp' + 104#64, sp', ptr1, rest⟩
      hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
      (ret_pc := entry + spkOff_tag2Ret) (by simp [arm64_norm])
      (by simpa [arm64_norm] using htr)
      (T := vecU8At A (sp' + 16#64) (SpkBytesField.pub.pin g).cap (SpkBytesField.pub.pin g).ptr
          (SpkBytesField.pub.getBytes m) ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗
        A.pool ∗ stackAt sp' cfg.mergeStk)
      (φ := rest.length < 2 ^ 63 ∧ BytesMergeCapOk (SpkBytesField.pub.pin g).cap rest.length)
      (by simp [spkBytesMergeRawSpecAt, hsp_eq, h29, h0, hwt8, arm64_norm])
      ⟨hlen_rest, hcap_in⟩
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hregs2 : SpkLoopRegs s0 sp' x19 s2 :=
      ⟨hsp2_eq,
       by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1,
       by simpa [h24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hregs.x19_eq, arm64_norm] using hcs2.1,
       ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩⟩
    dsimp only [spkBytesMergeRawSpecAt]
    cases hm : mergeBytes wt rest with
    | some p =>
      rcases p with ⟨v, rest2⟩
      obtain ⟨k2, hkl2, hr2, _⟩ := mergeBytes_suffix hm
      have hle2 : rest2.length ≤ rest.length := by rw [hr2]; simp
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => ?_
      rw [bytesMerge_ok_peel]
      refine Wire.SepWPp.pure_pre fun htr2 => ?_
      refine Wire.SepWPp.pure_pre fun hx0_2 => ?_
      refine Wire.SepWPp.pure_pre fun hcap' => ?_
      have hx0_z : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_latch) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine spkAdvanceToLatch_prog ⟨k2, hkl2, hr2⟩
        (hlatch v rest2 _ hm (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simp [htr2, htr, arm64_norm])) ?_
      have hupd := SpkBytesField.pub.capOk_update hg hle2 hcap' (p := ⟨cap', ptr'⟩)
      have hpack : vecU8At A (sp' + 16#64) cap' ptr' v ∗ SpkBytesField.pub.rest A g sp' m ⊢
          spkStructLoopOf A sp' rest2.length (SpkBytesField.pub.setBytes m v) := by
        have hu := SpkBytesField.pub.unsplit_field A g sp' m ⟨cap', ptr'⟩ v
        dsimp only [SpkBytesField.slotOff] at hu
        rw [hu]
        exact spkStructAt_entails_loopOf A _ sp' rest2.length _ hupd
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpack))))
      apply entails_of_eq
      dsimp only [ptr1]
      rw [hstack]
      simp only [hsp_eq, hsp2_eq, arm64_norm]
      ac_rfl
    | none =>
      simp only [sepConj_assoc]
      refine Wire.SepWPp.pure_pre fun htr2 => ?_
      simp only [sepConj_assoc, sepConj_pure_left_comm]
      refine Wire.SepWPp.pure_pre fun hx0_nz => ?_
      have hbeq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_nz
      refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_pushTag2) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine Wire.SepWPp.mono_pre ?_
        (herr (sp' := sp') (x19 := x19) (ptr := ptr1) (err := s2.readReg64 .x0)
          (mErr := m) (bs := rest) (out := out) (hnone hm)
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) hx0_nz
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
      have hof : vecU8At A (sp' + 16#64) (SpkBytesField.pub.pin g).cap (SpkBytesField.pub.pin g).ptr
          (SpkBytesField.pub.getBytes m) ∗ SpkBytesField.pub.rest A g sp' m ⊢ spkStructOf A sp' m := by
        have hs := SpkBytesField.pub.split_field A g sp' m
        dsimp only [SpkBytesField.slotOff] at hs
        rw [← hs]
        exact spkStructAt_entails_of A g sp' m
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))
      apply entails_of_eq
      rw [hstack]
      simp only [hsp_eq, hsp2_eq, arm64_norm]
      ac_rfl
  | priv =>
    have herr := @pushTag3_528_wp cfg img A ext B s0
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 76 16
    dsimp only [spkBytesEntryOff, SpkBytesField.slotOff, tripleRatchetProgAtExt] at hcall herr hlatch hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    refine Wire.SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]") -
        ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_tryFrom
      ⟨wt, sp' + 40#64, (SpkBytesField.priv.pin g).cap, (SpkBytesField.priv.pin g).ptr,
        SpkBytesField.priv.getBytes m, sp' + 104#64, sp', ptr1, rest⟩
      hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
      (ret_pc := entry + spkOff_tag3Ret) (by simp [arm64_norm])
      (by simpa [arm64_norm] using htr)
      (T := vecU8At A (sp' + 40#64) (SpkBytesField.priv.pin g).cap (SpkBytesField.priv.pin g).ptr
          (SpkBytesField.priv.getBytes m) ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗
        A.pool ∗ stackAt sp' cfg.mergeStk)
      (φ := rest.length < 2 ^ 63 ∧ BytesMergeCapOk (SpkBytesField.priv.pin g).cap rest.length)
      (by simp [spkBytesMergeRawSpecAt, hsp_eq, h24, h29, h0, hwt8, arm64_norm])
      ⟨hlen_rest, hcap_in⟩
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hregs2 : SpkLoopRegs s0 sp' x19 s2 :=
      ⟨hsp2_eq,
       by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1,
       by simpa [h24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hregs.x19_eq, arm64_norm] using hcs2.1,
       ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩⟩
    dsimp only [spkBytesMergeRawSpecAt]
    cases hm : mergeBytes wt rest with
    | some p =>
      rcases p with ⟨v, rest2⟩
      obtain ⟨k2, hkl2, hr2, _⟩ := mergeBytes_suffix hm
      have hle2 : rest2.length ≤ rest.length := by rw [hr2]; simp
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => ?_
      rw [bytesMerge_ok_peel]
      refine Wire.SepWPp.pure_pre fun htr2 => ?_
      refine Wire.SepWPp.pure_pre fun hx0_2 => ?_
      refine Wire.SepWPp.pure_pre fun hcap' => ?_
      have hx0_z : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_latch) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine spkAdvanceToLatch_prog ⟨k2, hkl2, hr2⟩
        (hlatch v rest2 _ hm (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simp [htr2, htr, arm64_norm])) ?_
      have hupd := SpkBytesField.priv.capOk_update hg hle2 hcap' (p := ⟨cap', ptr'⟩)
      have hpack : vecU8At A (sp' + 40#64) cap' ptr' v ∗ SpkBytesField.priv.rest A g sp' m ⊢
          spkStructLoopOf A sp' rest2.length (SpkBytesField.priv.setBytes m v) := by
        have hu := SpkBytesField.priv.unsplit_field A g sp' m ⟨cap', ptr'⟩ v
        dsimp only [SpkBytesField.slotOff] at hu
        rw [hu]
        exact spkStructAt_entails_loopOf A _ sp' rest2.length _ hupd
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpack))))
      apply entails_of_eq
      dsimp only [ptr1]
      rw [hstack]
      simp only [hsp_eq, hsp2_eq, arm64_norm]
      ac_rfl
    | none =>
      simp only [sepConj_assoc]
      refine Wire.SepWPp.pure_pre fun htr2 => ?_
      simp only [sepConj_assoc, sepConj_pure_left_comm]
      refine Wire.SepWPp.pure_pre fun hx0_nz => ?_
      have hbeq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_nz
      refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_pushTag3) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine Wire.SepWPp.mono_pre ?_
        (herr (sp' := sp') (x19 := x19) (ptr := ptr1) (err := s2.readReg64 .x0)
          (mErr := m) (bs := rest) (out := out) (hnone hm)
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) hx0_nz
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
      have hof : vecU8At A (sp' + 40#64) (SpkBytesField.priv.pin g).cap (SpkBytesField.priv.pin g).ptr
          (SpkBytesField.priv.getBytes m) ∗ SpkBytesField.priv.rest A g sp' m ⊢ spkStructOf A sp' m := by
        have hs := SpkBytesField.priv.split_field A g sp' m
        dsimp only [SpkBytesField.slotOff] at hs
        rw [← hs]
        exact spkStructAt_entails_of A g sp' m
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))
      apply entails_of_eq
      rw [hstack]
      simp only [hsp_eq, hsp2_eq, arm64_norm]
      ac_rfl
  | sig =>
    have herr := @pushTag4_400_wp cfg img A ext B s0
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 256 20
    dsimp only [spkBytesEntryOff, SpkBytesField.slotOff, tripleRatchetProgAtExt] at hcall herr hlatch hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    refine Wire.SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]") -
        ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_tryFrom
      ⟨wt, sp' + 64#64, (SpkBytesField.sig.pin g).cap, (SpkBytesField.sig.pin g).ptr,
        SpkBytesField.sig.getBytes m, sp' + 104#64, sp', ptr1, rest⟩
      hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
      (ret_pc := entry + spkOff_tag4Ret) (by simp [arm64_norm])
      (by simpa [arm64_norm] using htr)
      (T := vecU8At A (sp' + 64#64) (SpkBytesField.sig.pin g).cap (SpkBytesField.sig.pin g).ptr
          (SpkBytesField.sig.getBytes m) ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗
        A.pool ∗ stackAt sp' cfg.mergeStk)
      (φ := rest.length < 2 ^ 63 ∧ BytesMergeCapOk (SpkBytesField.sig.pin g).cap rest.length)
      (by simp [spkBytesMergeRawSpecAt, hsp_eq, h24, h29, h0, hwt8, arm64_norm])
      ⟨hlen_rest, hcap_in⟩
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hregs2 : SpkLoopRegs s0 sp' x19 s2 :=
      ⟨hsp2_eq,
       by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1,
       by simpa [h24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hregs.x19_eq, arm64_norm] using hcs2.1,
       ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩⟩
    dsimp only [spkBytesMergeRawSpecAt]
    cases hm : mergeBytes wt rest with
    | some p =>
      rcases p with ⟨v, rest2⟩
      obtain ⟨k2, hkl2, hr2, _⟩ := mergeBytes_suffix hm
      have hle2 : rest2.length ≤ rest.length := by rw [hr2]; simp
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => ?_
      rw [bytesMerge_ok_peel]
      refine Wire.SepWPp.pure_pre fun htr2 => ?_
      refine Wire.SepWPp.pure_pre fun hx0_2 => ?_
      refine Wire.SepWPp.pure_pre fun hcap' => ?_
      have hx0_z : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
      refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_latch) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine spkAdvanceToLatch_prog ⟨k2, hkl2, hr2⟩
        (hlatch v rest2 _ hm (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simp [htr2, htr, arm64_norm])) ?_
      have hupd := SpkBytesField.sig.capOk_update hg hle2 hcap' (p := ⟨cap', ptr'⟩)
      have hpack : vecU8At A (sp' + 64#64) cap' ptr' v ∗ SpkBytesField.sig.rest A g sp' m ⊢
          spkStructLoopOf A sp' rest2.length (SpkBytesField.sig.setBytes m v) := by
        have hu := SpkBytesField.sig.unsplit_field A g sp' m ⟨cap', ptr'⟩ v
        dsimp only [SpkBytesField.slotOff] at hu
        rw [hu]
        exact spkStructAt_entails_loopOf A _ sp' rest2.length _ hupd
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpack))))
      apply entails_of_eq
      dsimp only [ptr1]
      rw [hstack]
      simp only [hsp_eq, hsp2_eq, arm64_norm]
      ac_rfl
    | none =>
      simp only [sepConj_assoc]
      refine Wire.SepWPp.pure_pre fun htr2 => ?_
      simp only [sepConj_assoc, sepConj_pure_left_comm]
      refine Wire.SepWPp.pure_pre fun hx0_nz => ?_
      have hbeq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_nz
      refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_pushTag4) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine Wire.SepWPp.mono_pre ?_
        (herr (sp' := sp') (x19 := x19) (ptr := ptr1) (err := s2.readReg64 .x0)
          (mErr := m) (bs := rest) (out := out) (hnone hm)
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) hx0_nz
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
      have hof : vecU8At A (sp' + 64#64) (SpkBytesField.sig.pin g).cap (SpkBytesField.sig.pin g).ptr
          (SpkBytesField.sig.getBytes m) ∗ SpkBytesField.sig.rest A g sp' m ⊢ spkStructOf A sp' m := by
        have hs := SpkBytesField.sig.split_field A g sp' m
        dsimp only [SpkBytesField.slotOff] at hs
        rw [← hs]
        exact spkStructAt_entails_of A g sp' m
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))
      apply entails_of_eq
      rw [hstack]
      simp only [hsp_eq, hsp2_eq, arm64_norm]
      ac_rfl

/-! ## Unknown field `skip_field [local#7]` (`+300..+316` & `+592..+596`) -/

/-- Unknown tag skip (`+300..+316` → `+92` on `Ok`, `+592..+596` → `+656` on `Err`). -/
theorem skip_300_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {tag : ℕ} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (hlen : bs.length < 2 ^ 63)
    (htag : tag < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_skip)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlatch : ∀ (rest2 : List (BitVec 8)) (s3 : State),
      skipUnknown m tag wt rest = some (m, rest2) →
      s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_latch →
      s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s3
        (spkLoopMemAt cfg.subStack A sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 m)
        (spkConvergePostAt cfg.subStack img A s0 sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 out)
        (tryFromQp s0))
    (hnone : skipUnknown m tag wt rest = none → out = none) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (spkAfterVarintMemAt cfg.subStack A sp' x19 ptr bs rest bs.length m)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by
    rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintMemAt
  refine spkAdvanceCursorAt hsuf ?_
  let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  have hcall := B.skipField7
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 300 20
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 592 8
  dsimp only [tripleRatchetProgAtExt] at hcall hlatch hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0w : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  have hwt8 : (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat := by
    cases wt <;> decide
  have htag32 : (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt (by omega : tag < 2 ^ 64)]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#6]") -
      ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom
    ⟨wt, tag, 100, sp' + 104#64, sp', ptr1, rest⟩
    hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + spkOff_skipRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗
      A.pool ∗ stackAt sp' cfg.subStack)
    (φ := tag < 2 ^ 32 ∧ (100 : ℕ) < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by simp [spkSkipFieldSpecAt, SpkCfg.subStack, hsp_eq, h29, h0w, h1, hwt8, htag32, arm64_norm])
    ⟨htag, by decide, hlen_rest⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hregs2 : SpkLoopRegs s0 sp' x19 s2 :=
    ⟨hsp2_eq,
     by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1,
     by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
     by simpa [hregs.x19_eq, arm64_norm] using hcs2.1,
     ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
      by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
      by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
      by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩⟩
  dsimp only [spkSkipFieldSpecAt]
  cases hs : skipField (2 * rest.length + 2) 100 tag wt rest with
  | some rest2 =>
    have hsu : skipUnknown m tag wt rest = some (m, rest2) := by
      unfold skipUnknown recursionLimit; rw [hs]; rfl
    obtain ⟨k2, hkl2, hr2⟩ := skipField_suffix hs
    have hle2 : rest2.length ≤ bs.length := by rw [hr2, List.length_drop]; omega
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_2 => ?_
    have hx0_z : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_latch) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine spkAdvanceToLatch_prog ⟨k2, hkl2, hr2⟩
      (hlatch rest2 _ hsu (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3 (by simp [htr2, htr, arm64_norm])) ?_
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (spkStructLoopOf_mono A sp' m hle2)))))
    apply entails_of_eq
    dsimp only [ptr1, SpkCfg.subStack]
    simp only [hsp_eq, hsp2_eq, arm64_norm]
    ac_rfl
  | none =>
    have hsu : skipUnknown m tag wt rest = none := by
      unfold skipUnknown recursionLimit; rw [hs]; rfl
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_nz => ?_
    have hbeq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_nz
    refine Wire.SepWPp.of_sepWP_end hF2 hsym2 ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine ⟨⟨by simpa [arm64_norm] using hregs2.sp,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hF3, hsym3, by simp [htr2, htr, arm64_norm],
      by simpa [arm64_norm] using hregs2.x24,
      by simpa [arm64_norm] using hregs2.x19_eq,
      ⟨by simpa [arm64_norm] using hregs2.saved.x25,
       by simpa [arm64_norm] using hregs2.saved.x26,
       by simpa [arm64_norm] using hregs2.saved.x27,
       by simpa [arm64_norm] using hregs2.saved.x28⟩⟩, ?_⟩
    simp only [arm64_norm]
    refine Entails.trans ?_
      (spkConvergeMem_none_intro cfg.subStack A sp' x19 ptr1 (s2.readReg64 (Reg.gpr 0#5)) 0 m rest (hnone hsu) hx0_nz)
    refine Entails.trans ?_
      (sepConj_mono_left (spkStructLoopOf_entails_of A sp' bs.length m))
    apply entails_of_eq
    dsimp only [SpkCfg.subStack]
    simp only [hsp_eq, hsp2_eq, arm64_norm]
    try ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Bytes & Skip Field Proofs (Block `562`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

attribute [local irreducible] Program.fetch Program.externAt?

theorem spkAdvanceCursor_placed_prog [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {A : RustAlloc} {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Option SignedPreKeyRecordStructure} {Q0 P R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (hperm : Q0 ⊢ sliceCursorAfter sp' ptr bs rest ∗ R)
    (hent : sliceCursorAt sp' (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R ⊢ P)
    (h : Wire.SepWPp prog ret s P (spkConvergePostPlaced A s0 sp' x19
      (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out) (tryFromQp s0)) :
    Wire.SepWPp prog ret s Q0 (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  refine Wire.SepWPp.mono_pre hperm ?_
  rw [sliceCursorAfter_eq_take_cursorAt sp' ptr bs rest hsuf]; rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at hent h ⊢
  refine Wire.SepWPp.mono_pre (P' := P ∗ (ptr ↦ₛ bs.take k))
    (Entails.trans (by apply entails_of_eq; ac_rfl) (sepConj_mono_left hent)) ?_
  exact Wire.SepWPp.frame_tryFrom h
    (fun sf Pf hqm => spkConvergePostPlaced_append_prefix A s0 sp' x19 ptr bs k hkl out sf Pf hqm)

theorem spkAdvanceToLatch_placed_prog [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {A : RustAlloc} {s0 s : State} {sp' x19 ptr : BitVec 64} {bs rest : List (BitVec 8)}
    {m' : SignedPreKeyRecordStructure} {out : Option SignedPreKeyRecordStructure} {Q0 : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp prog ret s
      (spkLoopMem A sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest m')
      (spkConvergePostPlaced A s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (tryFromQp s0))
    (hperm : Q0 ⊢ sliceCursorAfter sp' ptr bs rest ∗ (((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion (sp' + 112#64) 48 ∗ spkStructLoopOf A sp' rest.length m' ∗ memRegion x19 88 ∗
      A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100))) :
    Wire.SepWPp prog ret s Q0 (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) :=
  spkAdvanceCursor_placed_prog hsuf hperm (Entails.refl _) h

theorem SpkLoopRegs.of_calleeSaved {s0 s s2 : State} {sp' x19 : BitVec 64}
    (hsp2 : s2.sp = s.sp) (hcs2 : CalleeSavedPreserved s s2)
    (hregs : SpkLoopRegs s0 sp' x19 s) : SpkLoopRegs s0 sp' x19 s2 :=
  ⟨hsp2.trans hregs.sp, hcs2.2.2.2.2.2.2.2.2.2.2.1.trans hregs.x29,
   hcs2.2.2.2.2.2.1.trans hregs.x24, hcs2.1.trans hregs.x19_eq,
   ⟨hcs2.2.2.2.2.2.2.1.trans hregs.saved.x25, hcs2.2.2.2.2.2.2.2.1.trans hregs.saved.x26,
    hcs2.2.2.2.2.2.2.2.2.1.trans hregs.saved.x27, hcs2.2.2.2.2.2.2.2.2.2.1.trans hregs.saved.x28⟩⟩

private theorem bytesField_ok_pack (f : SpkBytesField) (A : RustAlloc) (g : SpkGhost)
    (sp' x19 : BitVec 64) (rest rest2 v : List (BitVec 8)) (ptr1 : BitVec 64)
    (m : SignedPreKeyRecordStructure) (cap' ptr' : BitVec 64)
    (hg : SpkGhostCapOk g rest.length) (hle2 : rest2.length ≤ rest.length)
    (hcap' : BytesMergeCapOk cap' rest2.length) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗ stackAt sp' SpqrV1.Prost.BytesMerge.bytesMerge3Stack ∗
      vecU8At A (sp' + f.slotOff) cap' ptr' v ∗ sliceCursorAfter sp' ptr1 rest rest2 ∗
      memRegion (sp' + 112#64) 48 ∗ f.rest A g sp' m ∗ memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 (SpqrV1.Varint.skipField3Stack 100))
        (SpqrV1.Varint.skipField3Stack 100 - SpqrV1.Prost.BytesMerge.bytesMerge3Stack) ⊢
    sliceCursorAfter sp' ptr1 rest rest2 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion (sp' + 112#64) 48 ∗ spkStructLoopOf A sp' rest2.length (f.setBytes m v) ∗
      memRegion x19 88 ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100) := by
  have hstack := stackAt_sub_split sp' SpqrV1.Prost.BytesMerge.bytesMerge3Stack
    (SpqrV1.Varint.skipField3Stack 100)
  have hpack : vecU8At A (sp' + f.slotOff) cap' ptr' v ∗ f.rest A g sp' m ⊢
      spkStructLoopOf A sp' rest2.length (f.setBytes m v) := by
    rw [f.unsplit_field A g sp' m ⟨cap', ptr'⟩ v]
    exact spkStructAt_entails_loopOf A _ sp' rest2.length _ (f.capOk_update hg hle2 hcap' (p := ⟨cap', ptr'⟩))
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpack))))
  apply entails_of_eq; rw [hstack]; ac_rfl

private theorem bytesField_err_pack (f : SpkBytesField) (A : RustAlloc) (g : SpkGhost)
    (sp' x19 ptr1 err : BitVec 64) (rest : List (BitVec 8)) (m : SignedPreKeyRecordStructure) :
    ((sp' + 104#64) ↦₆₄ sp') ∗ A.pool ∗ stackAt sp' SpqrV1.Prost.BytesMerge.bytesMerge3Stack ∗
      decodeErrorAtStackLen A err 0 ∗ vecU8At A (sp' + f.slotOff) (f.pin g).cap (f.pin g).ptr (f.getBytes m) ∗
      memRegion sp' 16 ∗ (ptr1 ↦ₛ rest) ∗
      memRegion (sp' + 112#64) 48 ∗ f.rest A g sp' m ∗ memRegion x19 88 ∗
      memRegion (sp' - BitVec.ofNat 64 (SpqrV1.Varint.skipField3Stack 100))
        (SpqrV1.Varint.skipField3Stack 100 - SpqrV1.Prost.BytesMerge.bytesMerge3Stack) ⊢
    memRegion (sp' + 112#64) 48 ∗ decodeErrorAtStackLen A err 0 ∗
      spkStructOf A sp' m ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
      memRegion x19 88 ∗ (ptr1 ↦ₛ rest) ∗ A.pool ∗
      stackAt sp' (SpqrV1.Varint.skipField3Stack 100) := by
  have hstack := stackAt_sub_split sp' SpqrV1.Prost.BytesMerge.bytesMerge3Stack
    (SpqrV1.Varint.skipField3Stack 100)
  have hof : vecU8At A (sp' + f.slotOff) (f.pin g).cap (f.pin g).ptr (f.getBytes m) ∗
      f.rest A g sp' m ⊢ spkStructOf A sp' m := by
    rw [← f.split_field A g sp' m]; exact spkStructAt_entails_of A g sp' m
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))
  apply entails_of_eq; rw [hstack]; ac_rfl

private def spkBytesRetOff : SpkBytesField → BitVec 64
  | .pub => spkOff_tag2Ret | .priv => spkOff_tag3Ret | .sig => spkOff_tag4Ret

private theorem bytesField_ret_ok_step [LibsignalPlacement] {H : LibsignalHooks}
    (f : SpkBytesField) {s0 s2 : State} {sp' x19 : BitVec 64}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc2 : s2.pc = (blkPl_562).base + spkBytesRetOff f) (hrun2 : s2.status = .Running)
    (hregs2 : SpkLoopRegs s0 sp' x19 s2) (hx0_z : s2.readReg64 (Reg.gpr 0#5) = 0#64)
    (hsp2_align : s2.spAligned = true) (hcrl2 : LibsignalCodeRoLoaded lsmpl s2.mem)
    (htr2 : s2.trace = s0.trace)
    (hcont : ∀ s3, s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 → s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem →
      s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3 P Q Qp) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s2 P Q Qp := by
  cases f <;> (
    dsimp only [spkBytesRetOff] at hpc2
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_latch) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 =>
      hcont _ (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simp [htr2, arm64_norm]))

private theorem bytesField_ret_err_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (f : SpkBytesField)
    {s0 s2 : State} {sp' x19 ptr1 err : BitVec 64} {mErr : SignedPreKeyRecordStructure}
    {rest : List (BitVec 8)} {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc2 : s2.pc = (blkPl_562).base + spkBytesRetOff f) (hrun2 : s2.status = .Running)
    (hregs2 : SpkLoopRegs s0 sp' x19 s2) (hx0 : s2.readReg64 (Reg.gpr 0#5) = err) (hnz : err ≠ 0#64)
    (hsp2_align : s2.spAligned = true) (hcrl2 : LibsignalCodeRoLoaded lsmpl s2.mem)
    (htr2 : s2.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s2
      (memRegion (sp' + 112#64) 48 ∗ decodeErrorAtStackLen A err 0 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr1 ↦ₛ rest) ∗ A.pool ∗
        stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr1 rest out) (tryFromQp s0) := by
  have hpush := @pushCall_648_placed_wp _ A H hH s0
  have hsp2_eq : s2.sp = sp' := hregs2.sp
  have h29 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  have hbeq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr (hx0 ▸ hnz)
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
  cases f <;> (
    dsimp only [spkBytesRetOff] at hpc2
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_pushCall) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
    refine Wire.SepWPp.mono_pre ?_
      (hpush (sp' := sp') (x19 := x19) (ptr := ptr1) (err := err) (mErr := mErr) (bs := rest)
        (out := out) herr (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simp [hsp2_eq, arm64_norm], by simp [h29, arm64_norm],
         by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp [h29, arm64_norm]) hnz
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simp [htr2, arm64_norm]))
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
    apply entails_of_eq; simp only [hsp2_eq, h29, hx0, arm64_norm]; try ac_rfl)

private theorem bytesField_entry_step [LibsignalPlacement]
    {H : LibsignalHooks} (f : SpkBytesField) {s0 s : State}
    {sp' x19 : BitVec 64} {wt : WireType} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_562).base + spkBytesEntryOff f) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hcont : ∀ s1, s1.pc = lsmpl.base 558 → s1.status = .Running →
      SpkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → (s1.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat →
      s1.readReg64 .x1 = sp' + f.slotOff →
      s1.readReg64 .x2 = sp' + 104#64 →
      s1.readReg64 .x30 = (blkPl_562).base + spkBytesRetOff f →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s1 P Q Qp) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s P Q Qp := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h24 : s.readReg64 (Reg.gpr 24#5) = sp' + 16#64 := hregs.x24
  have hwt8 : (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat := by
    cases wt <;> decide
  cases f <;> (
    dsimp only [spkBytesEntryOff, SpkBytesField.slotOff, spkBytesRetOff] at hpc hcont
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 558) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 =>
      hcont _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simp [hsp_eq, arm64_norm], by simp [h29, arm64_norm],
         by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
          by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcrl1 (by simpa [arm64_norm] using htr)
        (by simp [hx0, hwt8, arm64_norm]) (by simp [hsp_eq, h24, arm64_norm])
        (by simp [h29, arm64_norm]) (by simp [arm64_norm]))

theorem bytesField_merge_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H)
    (f : SpkBytesField) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k) (hlen : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_562).base + spkBytesEntryOff f) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlatch : ∀ (v rest2 : List (BitVec 8)) (s3 : State), mergeBytes wt rest = some (v, rest2) →
      s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 → s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem →
      s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkLoopMem A sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) +
          BitVec.ofNat 64 (rest.length - rest2.length)) rest2 (f.setBytes m v))
        (spkConvergePostPlaced A s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) +
          BitVec.ofNat 64 (rest.length - rest2.length)) rest2 out) (tryFromQp s0))
    (hnone : mergeBytes wt rest = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintMem; refine spkAdvanceCursor_placed hsuf ?_
  let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (spkStructLoopOf_mono A sp' m hle_bs))))) ?_
  unfold spkStructLoopOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
  refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
  rw [f.split_field A g sp' m]; simp only [sepConj_assoc]
  have hstack := stackAt_sub_split sp' SpqrV1.Prost.BytesMerge.bytesMerge3Stack
    (SpqrV1.Varint.skipField3Stack 100)
  refine bytesField_entry_step f hpc hrun hregs hx0 hsp hcrl htr
    fun s1 hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 hx0_1 hx1_1 hx2_1 hx30_1 => ?_
  have hsp1_eq : s1.sp = sp' := hregs1.sp
  refine sepWPp_call_lscro
    ⟨wt, sp' + f.slotOff, (f.pin g).cap, (f.pin g).ptr, f.getBytes m, sp' + 104#64, sp', ptr1, rest⟩
    (spk_bytesMerge7_placed_ok d) hpc1 hrun1 hsp1 hcrl1
    (ret_pc := (blkPl_562).base + spkBytesRetOff f) hx30_1 htr1
    (T := vecU8At A (sp' + f.slotOff) (f.pin g).cap (f.pin g).ptr (f.getBytes m) ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗ A.pool ∗
      stackAt sp' SpqrV1.Prost.BytesMerge.bytesMerge3Stack)
    (φ := rest.length < 2 ^ 63 ∧ BytesMergeCapOk (f.pin g).cap rest.length)
    (by simp [SpqrV1.Prost.BytesMerge.bytesMerge3RawSpec, hsp1_eq, hx0_1, hx1_1, hx2_1])
    ⟨hlen_rest, f.capOk_pin hg⟩ (by rw [hstack]; sep_focus)
    fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
  have hregs2 := SpkLoopRegs.of_calleeSaved hsp2 hcs2 hregs1
  have hsp2_eq : s2.sp = sp' := hregs2.sp; dsimp only [SpqrV1.Prost.BytesMerge.bytesMerge3RawSpec]
  cases hm : mergeBytes wt rest with
  | some p =>
    rcases p with ⟨v, rest2⟩; obtain ⟨k2, hkl2, hr2, _⟩ := mergeBytes_suffix hm
    have hle2 : rest2.length ≤ rest.length := by rw [hr2]; simp
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => ?_
    rw [bytesMerge_ok_peel]
    refine Wire.SepWPp.pure_pre fun htr2 => Wire.SepWPp.pure_pre fun hx0_2 =>
      Wire.SepWPp.pure_pre fun hcap' => bytesField_ret_ok_step f hpc2 hrun2 hregs2 hx0_2
        hsp2_align hcrl2 (htr2.trans htr1) fun s3 hpc3 hrun3 hregs3 hsp3 hcrl3 htr3 =>
        spkAdvanceToLatch_placed_prog ⟨k2, hkl2, hr2⟩
          (hlatch v rest2 s3 hm hpc3 hrun3 hregs3 hsp3 hcrl3 htr3)
          (by simpa only [ptr1, hsp1_eq, hsp2_eq, sepConj_assoc] using
            bytesField_ok_pack f A g sp' x19 rest rest2 v ptr1 m cap' ptr' hg hle2 hcap')
  | none =>
    simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_nz => Wire.SepWPp.mono_pre
      (by simpa only [hsp1_eq, hsp2_eq, sepConj_assoc] using
        bytesField_err_pack f A g sp' x19 ptr1 (s2.readReg64 (Reg.gpr 0#5)) rest m)
      (bytesField_ret_err_placed_wp hH f (mErr := m) (hnone hm) hpc2 hrun2 hregs2 rfl hx0_nz
        hsp2_align hcrl2 (htr2.trans htr1))

theorem skip_300_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (d : SignedPortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {tag : ℕ} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k) (hlen : bs.length < 2 ^ 63) (htag : tag < 2 ^ 32)
    (hpc : s.pc = (blkPl_562).base + spkOff_skip) (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s) (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlatch : ∀ (rest2 : List (BitVec 8)) (s3 : State), skipUnknown m tag wt rest = some (m, rest2) →
      s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 → s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem →
      s3.trace = s0.trace → Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkLoopMem A sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) +
          BitVec.ofNat 64 (rest.length - rest2.length)) rest2 m)
        (spkConvergePostPlaced A s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) +
          BitVec.ofNat 64 (rest.length - rest2.length)) rest2 out) (tryFromQp s0))
    (hnone : skipUnknown m tag wt rest = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintMem; refine spkAdvanceCursor_placed hsuf ?_
  let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  have hsp_eq : s.sp = sp' := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0w : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  have hwt8 : (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat := by cases wt <;> decide
  have htag32 : (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : tag < 2 ^ 64)]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 546) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine sepWPp_call_lscro ⟨wt, tag, 100, sp' + 104#64, sp', ptr1, rest⟩ (spk_skipField7_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_skipRet) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗
      A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
    (φ := tag < 2 ^ 32 ∧ (100 : ℕ) < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by simp [SpqrV1.Varint.skipField3Spec, hsp_eq, h29, h0w, h1, hwt8, htag32, arm64_norm])
    ⟨htag, by decide, hlen_rest⟩ (by sep_focus) fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
  have hregs2 : SpkLoopRegs s0 sp' x19 s2 := SpkLoopRegs.of_calleeSaved hsp2 hcs2
    ⟨by simp [hsp_eq, arm64_norm], by simp [h29, arm64_norm],
     by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
     ⟨by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
      by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
  have hsp2_eq : s2.sp = sp' := hregs2.sp; dsimp only [SpqrV1.Varint.skipField3Spec]
  cases hs : skipField (2 * rest.length + 2) 100 tag wt rest with
  | some rest2 =>
    have hsu : skipUnknown m tag wt rest = some (m, rest2) := by unfold skipUnknown recursionLimit; rw [hs]; rfl
    obtain ⟨k2, hkl2, hr2⟩ := skipField_suffix hs
    have hle2 : rest2.length ≤ bs.length := by rw [hr2, List.length_drop]; omega
    simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine Wire.SepWPp.pure_pre fun hx0_2 => ?_
    have hx0_z : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_latch) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
    refine spkAdvanceToLatch_placed_prog ⟨k2, hkl2, hr2⟩
      (hlatch rest2 _ hsu (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simp [htr2, htr, arm64_norm])) ?_
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (spkStructLoopOf_mono A sp' m hle2)))))
    apply entails_of_eq; dsimp only [ptr1]; simp only [hsp_eq, hsp2_eq, arm64_norm]; ac_rfl
  | none =>
    have hsu : skipUnknown m tag wt rest = none := by unfold skipUnknown recursionLimit; rw [hs]; rfl
    simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine Wire.SepWPp.pure_pre fun hx0_nz => ?_
    have hbeq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_nz
    refine sepWPp_of_sepWP_end_lscro hcrl2 ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
    refine ⟨⟨by simpa [arm64_norm] using hregs2.sp,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hcrl3, by simp [htr2, htr, arm64_norm],
      by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
      ⟨by simpa [arm64_norm] using hregs2.saved.x25, by simpa [arm64_norm] using hregs2.saved.x26,
       by simpa [arm64_norm] using hregs2.saved.x27, by simpa [arm64_norm] using hregs2.saved.x28⟩⟩, ?_⟩
    simp only [arm64_norm]; refine Entails.trans ?_
      (spkConvergeMem_none_intro (SpqrV1.Varint.skipField3Stack 100) A sp' x19 ptr1 (s2.readReg64 (Reg.gpr 0#5)) 0 m rest (hnone hsu) hx0_nz)
    refine Entails.trans ?_ (sepConj_mono_left (spkStructLoopOf_entails_of A sp' bs.length m))
    apply entails_of_eq; simp only [hsp_eq, hsp2_eq, arm64_norm]; try ac_rfl

end Placed

end CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers
