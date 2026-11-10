/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.BytesAndSkip
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.DecodeKey
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `SignedPreKeyRecordStructure::decode` Scalar Field Branches (`id` and `timestamp`)

Hoare triples for tag 1 (`id : uint32`, `+276 .. +296`) and tag 5 (`timestamp : fixed64`,
`+176 .. +216`), together with wire-type and short-buffer error stubs (Block `562`).
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

/-! ## Local separation-logic packing helpers -/

private theorem sliceCursorAt_entails_memRegion (sp' ptr : BitVec 64) (bs : List (BitVec 8)) :
    sliceCursorAt sp' ptr bs ⊢ memRegion sp' 16 ∗ (ptr ↦ₛ bs) := by
  unfold sliceCursorAt
  rw [← sepConj_assoc]
  exact sepConj_mono_left (Wire.pointsTo64_pair_entails_memRegion16 sp' ptr (BitVec.ofNat 64 bs.length))

private theorem spkErrBytes_pack_pre (sp' k : BitVec 64) (b0 b1 : BitVec 8) (rest : SepProp) :
    ((sp' + 112#64) ↦₆₄ k) ∗ ((sp' + 120#64) ↦₈ b0) ∗ ((sp' + 121#64) ↦₈ b1) ∗
      memRegion (sp' + 122#64) 6 ∗ memRegion (sp' + 128#64) 32 ∗ rest ⊢
    ((sp' + 112#64) ↦₆₄ k) ∗ memRegion (sp' + 120#64) 40 ∗ rest := by
  have hp :
      ((sp' + 112#64) ↦₆₄ k) ∗ ((sp' + 120#64) ↦₈ b0) ∗ ((sp' + 121#64) ↦₈ b1) ∗
        memRegion (sp' + 122#64) 6 ∗ memRegion (sp' + 128#64) 32 ∗ rest =
      (((sp' + 120#64) ↦₈ b0) ∗ ((sp' + 121#64) ↦₈ b1) ∗
        memRegion (sp' + 122#64) 6 ∗ memRegion (sp' + 128#64) 32) ∗
        ((sp' + 112#64) ↦₆₄ k) ∗ rest := by
    ac_rfl
  rw [hp]
  refine Entails.trans (sepConj_mono_left (spkErrBytes_pack40 sp' b0 b1)) ?_
  apply entails_of_eq; ac_rfl

private theorem tag5Short_pack (subStack : Nat) (A : RustAlloc) (sp' x19 ptr1 : BitVec 64)
    (short : List (BitVec 8)) (n : ℕ) (m : SignedPreKeyRecordStructure) :
    (sp' ↦₆₄ ptr1) ∗ ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 short.length) ∗ (ptr1 ↦ₛ short) ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion (sp' + 112#64) 48 ∗
      spkStructLoopOf A sp' n m ∗ memRegion x19 88 ∗ A.pool ∗
      stackAt sp' subStack ⊢
    memRegion (sp' + 112#64) 48 ∗ spkStructOf A sp' m ∗ memRegion sp' 16 ∗
      ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion x19 88 ∗ (ptr1 ↦ₛ short) ∗ A.pool ∗
      stackAt sp' subStack := by
  have hp :
      (sp' ↦₆₄ ptr1) ∗ ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 short.length) ∗ (ptr1 ↦ₛ short) ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion (sp' + 112#64) 48 ∗
        spkStructLoopOf A sp' n m ∗ memRegion x19 88 ∗ A.pool ∗
        stackAt sp' subStack =
      ((sp' ↦₆₄ ptr1) ∗ ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 short.length)) ∗
        spkStructLoopOf A sp' n m ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr1 ↦ₛ short) ∗ A.pool ∗
        stackAt sp' subStack := by
    ac_rfl
  rw [hp]
  refine Entails.trans
    (sepConj_mono (Wire.pointsTo64_pair_entails_memRegion16 sp' ptr1 (BitVec.ofNat 64 short.length))
      (sepConj_mono_left (spkStructLoopOf_entails_of A sp' n m))) ?_
  apply entails_of_eq; ac_rfl

private theorem tag5_cap_peel (a1 a2 a3 a4 a5 a6 : SepProp) (p : Prop) (rest : SepProp) :
    a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ ⌜p⌝ ∗ rest =
      ⌜p⌝ ∗ a1 ∗ a2 ∗ a3 ∗ a4 ∗ a5 ∗ a6 ∗ rest := by
  ac_rfl

/-! ## Tag 1 (`id : uint32`, `+276..+296`, `+320..+324`, `+460..+524`) -/

/-- Tag 1 (`id`) error push setup `+492..+524` → `+648` → `+656` (`err` in `X1`). -/
theorem pushTag1_492_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_pushTag1)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx1 : s.readReg64 .x1 = err) (hnz : err ≠ 0#64)
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
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 492 36
  dsimp only [tripleRatchetProgAtExt] at hpush hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h1 : s.readReg64 (Reg.gpr 1#5) = err := hx1
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

/-- Tag 1 bad wire-type error construction `+460..+488` → `+492` → `+648` → `+656`. -/
theorem tag1BadWt_460_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr w0 : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag1BadWt)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = w0)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := B.decodeErrorFrom
  have hpush := @pushTag1_492_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 460 32
  dsimp only [tripleRatchetProgAtExt] at hcall hpush hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = w0 := hx0
  have hstack := stackAt_sub_split sp' cfg.errStk cfg.subStack
    (spkCfg_split_err cfg) (spkCfg_subStack_le cfg)
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpackBytes sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun b0 =>
    Wire.SepWPp.exists_pre fun b1 => ?_
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
      ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre
    (by
      exact spkErrBytes_pack_pre sp' (BitVec.ofNat 64 (2 ^ 63 + 6)) (w0.setWidth 8) 0#8 _) ?_
  refine Wire.SepWPp.call_tryFrom (sp' + 112#64, BitVec.ofNat 64 (2 ^ 63 + 6)) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + spkOff_tag1FromRet) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ BitVec.ofNat 64 (2 ^ 63 + 6)) ∗
      memRegion (sp' + 112#64 + 8#64) 40 ∗
      A.pool ∗ stackAt sp' cfg.errStk)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap (BitVec.ofNat 64 (2 ^ 63 + 6)))
    (by simp [decodeErrorFromSpecWithStack, hsp_eq, h29, arm64_norm])
    ⟨rfl, by simp [KindNoHeap]⟩
    (by
      have ha : sp' + 112#64 + 8#64 = sp' + 120#64 := by bv_omega
      rw [ha, hstack]; sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  dsimp only [decodeErrorFromSpecWithStack]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨herr_nz, htr2⟩ => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 :=
    by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1
  have hregs2 : SpkLoopRegs s0 sp' x19 s2 :=
    ⟨hsp2_eq, hx29_2,
     by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
     by simpa [hregs.x19_eq, arm64_norm] using hcs2.1,
     ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
      by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
      by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
      by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩⟩
  refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_pushTag1) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine Wire.SepWPp.mono_pre ?_
    (hpush (sp' := sp') (x19 := x19) (ptr := ptr) (err := s2.readReg64 .x0)
      (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
       by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
       ⟨by simpa [arm64_norm] using hregs2.saved.x25,
        by simpa [arm64_norm] using hregs2.saved.x26,
        by simpa [arm64_norm] using hregs2.saved.x27,
        by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
      (by simp [arm64_norm]) herr_nz
      (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
      hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
  apply entails_of_eq
  rw [hstack]
  simp only [hsp_eq, hsp2_eq, arm64_norm]
  try ac_rfl

/-- Tag 1 (`id : uint32`) Hoare triple (`+276..+296` & `+320..+324`). -/
theorem tag1_276_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (hlen : bs.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag1)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlatch : ∀ (v : BitVec 32) (rest2 : List (BitVec 8)) (s3 : State),
      mergeUint32 wt rest = some (v, rest2) →
      s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_latch →
      s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s3
        (spkLoopMemAt cfg.subStack A sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 { m with id := v })
        (spkConvergePostAt cfg.subStack img A s0 sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 out)
        (tryFromQp s0))
    (hnone : mergeUint32 wt rest = none → out = none) :
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
  have hcall := B.decodeVarint6
  have hbad := @tag1BadWt_460_wp cfg img A ext B s0
  have hpush := @pushTag1_492_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 276 24
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 320 8
  dsimp only [tripleRatchetProgAtExt] at hcall hbad hpush hlatch hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  cases wt with
  | varint =>
    dsimp only [WireType.toNat] at hx0
    have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
    have hstack := stackAt_sub_split sp' cfg.varintStk cfg.subStack
      (spkCfg_split_varint cfg) (spkCfg_subStack_le cfg)
    refine Wire.SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]") -
        ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_tryFrom
      ⟨sp' + 104#64, sp', ptr1, rest⟩
      hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
      (ret_pc := entry + spkOff_tag1Ret) (by simp [arm64_norm])
      (by simpa [arm64_norm] using htr)
      (T := ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗
        A.pool ∗ stackAt sp' cfg.varintStk)
      (φ := sp' + 104#64 = sp' + 104#64 ∧ rest.length < 2 ^ 63)
      (by simp [spkDecodeVarintSpecAt, hsp_eq, h29, arm64_norm])
      ⟨rfl, hlen_rest⟩
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 :=
      by simpa [h29, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.2.1
    have hregs2 : SpkLoopRegs s0 sp' x19 s2 :=
      ⟨hsp2_eq, hx29_2,
       by simpa [hregs.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hregs.x19_eq, arm64_norm] using hcs2.1,
       ⟨by simpa [hregs.saved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
        by simpa [hregs.saved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩⟩
    dsimp only [spkDecodeVarintSpecAt]
    cases hdv : decodeVarint rest with
    | some p =>
      rcases p with ⟨v64, rest2⟩
      have hm : mergeUint32 .varint rest = some (v64.setWidth 32, rest2) := by
        unfold mergeUint32; simp [hdv]
      obtain ⟨k2, hkl2, hr2⟩ := mergeUint32_suffix hm
      have hle2 : rest2.length ≤ bs.length := by rw [hr2, List.length_drop]; omega
      simp only [sepConj_assoc]
      refine Wire.SepWPp.pure_pre fun ⟨hx0_0, hx1_v⟩ => ?_
      refine Wire.SepWPp.pure_pre fun htr2 => ?_
      have hw0_0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
      have hw1_v : s2.readReg64 (Reg.gpr 1#5) = v64 := hx1_v
      refine Wire.SepWPp.mono_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (spkStructLoopOf_mono A sp' m hle2))))))) ?_
      unfold spkStructLoopOf
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        sepConj_pure_left_comm]
      refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
      rw [spkStructAt_split_id A g sp' m]
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_latch) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      have hid : ((sp' + 96#64) ↦₃₂ v64.setWidth 32) ∗
          (vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗
            vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
            vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗
            ((sp' + 88#64) ↦₆₄ m.timestamp) ∗
            memRegion (sp' + 100#64) 4) ⊢
          spkStructLoopOf A sp' rest2.length { m with id := v64.setWidth 32 } := by
        rw [← spkStructAt_split_id A g sp' { m with id := v64.setWidth 32 }]
        exact spkStructAt_entails_loopOf A g sp' rest2.length _ hg
      refine spkAdvanceToLatch_prog ⟨k2, hkl2, hr2⟩
        (hlatch (v64.setWidth 32) rest2 _ hm (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
        (by
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hid))))
          apply entails_of_eq
          rw [hstack]
          simp only [hsp_eq, hsp2_eq, hw1_v, arm64_norm]
          ac_rfl)
    | none =>
      have hm : mergeUint32 .varint rest = none := by
        unfold mergeUint32; simp [hdv]
      simp only [sepConj_assoc]
      refine Wire.SepWPp.pure_pre fun hx0_1 => ?_
      refine Wire.SepWPp.pure_pre fun htr2 => ?_
      simp only [sepConj_assoc, sepConj_pure_left_comm]
      refine Wire.SepWPp.pure_pre fun hx1_nz => ?_
      have hw0_1 : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
      have hbeq : (s2.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx1_nz
      refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + spkOff_pushTag1) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine Wire.SepWPp.mono_pre ?_
        (hpush (sp' := sp') (x19 := x19) (ptr := ptr1) (err := s2.readReg64 .x1)
          (mErr := m) (bs := rest) (out := out) (hnone hm)
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [arm64_norm] using hregs2.x24, by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp [arm64_norm]) hx1_nz
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simp [htr2, htr, arm64_norm]))
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (spkStructLoopOf_entails_of A sp' bs.length m))))))))) ?_
      apply entails_of_eq
      rw [hstack]
      simp only [hsp_eq, hsp2_eq, arm64_norm]
      ac_rfl
  | sixtyFourBit | lengthDelimited | startGroup | endGroup | thirtyTwoBit =>
    have hm : out = none := hnone (by unfold mergeUint32; simp)
    have hcur := sliceCursorAt_entails_memRegion sp' ptr1 rest
    have hof := spkStructLoopOf_entails_of A sp' bs.length m
    dsimp only [WireType.toNat] at hx0
    have h0 : s.readReg64 (Reg.gpr 0#5) = _ := hx0
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag1BadWt) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.mono_pre ?_
      (hbad (sp' := sp') (x19 := x19) (ptr := ptr1) (w0 := s.readReg64 (Reg.gpr 0#5))
        (mErr := m) (bs := rest) (out := out) hm
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26,
          by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simp [htr, arm64_norm]))
    refine Entails.trans
      (sepConj_mono hcur
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))) ?_
    apply entails_of_eq; ac_rfl

/-! ## Tag 5 (`timestamp : fixed64`, `+176..+216`, `+564..+588`, `+600..+604`) -/

/-- Tag 5 bad wire-type setup `+564..+588` → `+608` (`tag5FromPush_608_wp`). -/
theorem tag5BadWt_564_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr w0 : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag5BadWt)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = w0)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hnext := @tag5FromPush_608_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 564 28
  dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = w0 := hx0
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpackBytes sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun b0 =>
    Wire.SepWPp.exists_pre fun b1 => ?_
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5FromCommon) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hnext (sp' := sp') (x19 := x19) (ptr := ptr)
      (kind := BitVec.ofNat 64 (2 ^ 63 + 6)) (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [KindNoHeap])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simp [htr, arm64_norm]))
  simp only [h29, arm64_norm]
  exact spkErrBytes_pack_pre sp' (BitVec.ofNat 64 (2 ^ 63 + 6)) (w0.setWidth 8) 1#8 _

/-- Tag 5 short-buffer (`< 8` bytes) setup `+600..+604` → `+608` (`tag5FromPush_608_wp`). -/
theorem tag5Eof_600_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag5Eof)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗
        spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗
        stackAt sp' cfg.subStack)
      (spkConvergePostAt cfg.subStack img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hnext := @tag5FromPush_608_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 600 8
  dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => ?_
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5FromCommon) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hnext (sp' := sp') (x19 := x19) (ptr := ptr)
      (kind := BitVec.ofNat 64 (2 ^ 63 + 7)) (mErr := mErr) (bs := bs) (out := out) herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [KindNoHeap])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simp [htr, arm64_norm]))
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
  apply entails_of_eq
  simp only [hsp_eq, h29, arm64_norm]
  try ac_rfl

/-- Tag 5 (`timestamp : fixed64`) Hoare triple (`+176..+216`). -/
theorem tag5_176_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (hlen : bs.length < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_tag5)
    (hrun : s.status = .Running)
    (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlatch : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (s3 : State),
      mergeFixed64 wt rest = some (v, rest2) →
      s3.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_latch →
      s3.status = .Running →
      SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge) s3
        (spkLoopMemAt cfg.subStack A sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 { m with timestamp := v })
        (spkConvergePostAt cfg.subStack img A s0 sp' x19
          (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length))
          rest2 out)
        (tryFromQp s0))
    (hnone : mergeFixed64 wt rest = none → out = none) :
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
  have hbad := @tag5BadWt_564_wp cfg img A ext B s0
  have heof := @tag5Eof_600_wp cfg img A ext B s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 176 44
  dsimp only [tripleRatchetProgAtExt] at hbad heof hlatch hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  cases wt with
  | sixtyFourBit =>
    dsimp only [WireType.toNat] at hx0
    have h0 : s.readReg64 (Reg.gpr 0#5) = 1#64 := hx0
    rcases rest with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest2⟩⟩⟩⟩⟩⟩⟩⟩
    · have hm : out = none := hnone (by unfold mergeFixed64; simp)
      unfold sliceCursorAt
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5Eof) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre (tag5Short_pack cfg.subStack A sp' x19 ptr1 [] bs.length m)
        (heof (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := []) (out := out) hm
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simp [htr, arm64_norm]))
    · have hm : out = none := hnone (by unfold mergeFixed64; simp)
      unfold sliceCursorAt
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5Eof) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre (tag5Short_pack cfg.subStack A sp' x19 ptr1 [b0] bs.length m)
        (heof (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := [b0]) (out := out) hm
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simp [htr, arm64_norm]))
    · have hm : out = none := hnone (by unfold mergeFixed64; simp)
      unfold sliceCursorAt
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5Eof) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre (tag5Short_pack cfg.subStack A sp' x19 ptr1 [b0, b1] bs.length m)
        (heof (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := [b0, b1]) (out := out) hm
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simp [htr, arm64_norm]))
    · have hm : out = none := hnone (by unfold mergeFixed64; simp)
      unfold sliceCursorAt
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5Eof) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre (tag5Short_pack cfg.subStack A sp' x19 ptr1 [b0, b1, b2] bs.length m)
        (heof (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := [b0, b1, b2]) (out := out) hm
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simp [htr, arm64_norm]))
    · have hm : out = none := hnone (by unfold mergeFixed64; simp)
      unfold sliceCursorAt
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5Eof) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre (tag5Short_pack cfg.subStack A sp' x19 ptr1 [b0, b1, b2, b3] bs.length m)
        (heof (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := [b0, b1, b2, b3]) (out := out) hm
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simp [htr, arm64_norm]))
    · have hm : out = none := hnone (by unfold mergeFixed64; simp)
      unfold sliceCursorAt
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5Eof) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre (tag5Short_pack cfg.subStack A sp' x19 ptr1 [b0, b1, b2, b3, b4] bs.length m)
        (heof (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := [b0, b1, b2, b3, b4]) (out := out) hm
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simp [htr, arm64_norm]))
    · have hm : out = none := hnone (by unfold mergeFixed64; simp)
      unfold sliceCursorAt
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5Eof) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre (tag5Short_pack cfg.subStack A sp' x19 ptr1 [b0, b1, b2, b3, b4, b5] bs.length m)
        (heof (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := [b0, b1, b2, b3, b4, b5]) (out := out) hm
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simp [htr, arm64_norm]))
    · have hm : out = none := hnone (by unfold mergeFixed64; simp)
      unfold sliceCursorAt
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5Eof) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre (tag5Short_pack cfg.subStack A sp' x19 ptr1 [b0, b1, b2, b3, b4, b5, b6] bs.length m)
        (heof (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := [b0, b1, b2, b3, b4, b5, b6]) (out := out) hm
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simp [htr, arm64_norm]))
    ·
      let restFull := b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest2
      have hm : mergeFixed64 .sixtyFourBit restFull =
          some (le64 b0 b1 b2 b3 b4 b5 b6 b7, rest2) := rfl
      have hge8 : 8 ≤ restFull.length := by simp [restFull]
      have hle2 : rest2.length ≤ bs.length := by
        simp only [List.length_cons] at hle_bs
        omega
      have ⟨hcc_ok, hsub8⟩ := spk_sub8_ge8 hge8 hlen_rest
      have hult_false : (BitVec.ofNat 64 restFull.length).ult 8#64 = false := by
        simpa using hcc_ok
      have hult_false' : (BitVec.ofNat 64 (rest2.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)).ult 8#64 = false := by
        simpa only [restFull, List.length_cons] using hult_false
      have hsub8' : BitVec.ofNat 64 restFull.length - 8#64 = BitVec.ofNat 64 rest2.length := by
        rw [hsub8]
        congr 1
      have hsub8'' : BitVec.ofNat 64 (rest2.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) - 8#64 =
          BitVec.ofNat 64 rest2.length := by
        simpa only [restFull, List.length_cons] using hsub8'
      refine Wire.SepWPp.mono_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (spkStructLoopOf_mono A sp' m hle2))))) ?_
      unfold spkStructLoopOf sliceCursorAt
      rw [spk_pointsToBytes8_cons ptr1 b0 b1 b2 b3 b4 b5 b6 b7 rest2,
        spk_le64_eq_pair32 b0 b1 b2 b3 b4 b5 b6 b7]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun g => ?_
      rw [tag5_cap_peel]
      refine Wire.SepWPp.pure_pre fun hg => ?_
      rw [spkStructAt_split_timestamp A g sp' m]
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_latch) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      have h8take : (ptr1 ↦₆₄ le64 b0 b1 b2 b3 b4 b5 b6 b7) = (ptr1 ↦ₛ restFull.take 8) := by
        have hnil := (spk_pointsToBytes8_cons ptr1 b0 b1 b2 b3 b4 b5 b6 b7 []).symm
        rw [pointsToBytes_nil, sepConj_emp, spk_le64_eq_pair32] at hnil
        exact hnil
      have hl_app := hlatch (le64 b0 b1 b2 b3 b4 b5 b6 b7) rest2 _ hm
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26,
          by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simp [htr, arm64_norm])
      have hlen_sub : restFull.length - rest2.length = 8 := by
        simp only [restFull, List.length_cons]
        omega
      rw [hlen_sub, show rest2 = restFull.drop 8 from rfl] at hl_app
      have hframed := Wire.SepWPp.frame_tryFrom hl_app
        (fun sf Pf hqm =>
          spkConvergePostAt_append_prefix cfg.subStack img A s0 sp' x19 ptr1 restFull 8 hge8 out sf Pf hqm)
      refine Wire.SepWPp.mono_pre ?_ hframed
      unfold spkLoopMemAt sliceCursorAt
      have hts : ((sp' + 88#64) ↦₆₄ le64 b0 b1 b2 b3 b4 b5 b6 b7) ∗
          (vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗
            vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
            vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗
            ((sp' + 96#64) ↦₃₂ m.id) ∗
            memRegion (sp' + 100#64) 4) ⊢
          spkStructLoopOf A sp' rest2.length
            { m with timestamp := le64 b0 b1 b2 b3 b4 b5 b6 b7 } := by
        rw [← spkStructAt_split_timestamp A g sp'
          { m with timestamp := le64 b0 b1 b2 b3 b4 b5 b6 b7 }]
        exact spkStructAt_entails_loopOf A g sp' rest2.length _ hg
      rw [h8take]
      dsimp only [ptr1, restFull, List.drop, List.take]
      simp only [hsp_eq, h29, List.length_cons, arm64_norm]
      try rw [hsub8']
      try rw [hsub8'']
      set p1 := ptr + BitVec.ofNat 64 (bs.length - (rest2.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
      refine Entails.trans
        (Q := (((sp' + 88#64) ↦₆₄ le64 b0 b1 b2 b3 b4 b5 b6 b7) ∗
            (vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗
              vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
              vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗
              ((sp' + 96#64) ↦₃₂ m.id) ∗
              memRegion (sp' + 100#64) 4)) ∗
          ((sp' ↦₆₄ (p1 + 8#64)) ∗
            ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 rest2.length) ∗
            ((p1 + 8#64) ↦ₛ rest2) ∗
            ((sp' + 104#64) ↦₆₄ sp') ∗
            memRegion (sp' + 112#64) 48 ∗
            memRegion x19 88 ∗
            A.pool ∗
            stackAt sp' cfg.subStack ∗
            (p1 ↦ₛ ([b0, b1, b2, b3, b4, b5, b6, b7] : List (BitVec 8)))))
        (by
          apply entails_of_eq
          simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
            BitVec.add_assoc, BitVec.reduceAdd]
          ac_rfl)
        (Entails.trans (sepConj_mono_left hts)
          (by
            apply entails_of_eq
            simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
              BitVec.add_assoc, BitVec.reduceAdd]
            ac_rfl))
  | varint | lengthDelimited | startGroup | endGroup | thirtyTwoBit =>
    have hm : out = none := hnone (by unfold mergeFixed64; simp)
    have hcur := sliceCursorAt_entails_memRegion sp' ptr1 rest
    have hof := spkStructLoopOf_entails_of A sp' bs.length m
    dsimp only [WireType.toNat] at hx0
    have h0 : s.readReg64 (Reg.gpr 0#5) = _ := hx0
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_tag5BadWt) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.mono_pre ?_
      (hbad (sp' := sp') (x19 := x19) (ptr := ptr1) (w0 := s.readReg64 (Reg.gpr 0#5))
        (mErr := m) (bs := rest) (out := out) hm
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [arm64_norm] using hregs.x24, by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26,
          by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp [arm64_norm])
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simp [htr, arm64_norm]))
    refine Entails.trans
      (sepConj_mono hcur
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))) ?_
    apply entails_of_eq; ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Tag 1 & Tag 5 Proofs (Block `562`) -/

section Placed
open CryptoVerification.RecordCodecs.Placed

theorem SpkLoopRegs.of_unchanged {s0 s s1 : State} {sp' x19 : BitVec 64} (h : SpkLoopRegs s0 sp' x19 s)
    (hu : s1.sp = s.sp ∧ s1.readReg64 (Reg.gpr 29#5) = s.readReg64 (Reg.gpr 29#5) ∧
      s1.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) ∧ s1.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) ∧
      s1.readReg64 (Reg.gpr 25#5) = s.readReg64 (Reg.gpr 25#5) ∧ s1.readReg64 (Reg.gpr 26#5) = s.readReg64 (Reg.gpr 26#5) ∧
      s1.readReg64 (Reg.gpr 27#5) = s.readReg64 (Reg.gpr 27#5) ∧ s1.readReg64 (Reg.gpr 28#5) = s.readReg64 (Reg.gpr 28#5)) :
    SpkLoopRegs s0 sp' x19 s1 :=
  ⟨hu.1.trans h.sp, hu.2.1.trans h.x29, hu.2.2.1.trans h.x24, hu.2.2.2.1.trans h.x19_eq,
   ⟨hu.2.2.2.2.1.trans h.saved.x25, hu.2.2.2.2.2.1.trans h.saved.x26,
    hu.2.2.2.2.2.2.1.trans h.saved.x27, hu.2.2.2.2.2.2.2.trans h.saved.x28⟩⟩

theorem pushTag1_492_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {s0 s : State} {sp' x19 ptr err : BitVec 64} {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_pushTag1) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx1 : s.readReg64 .x1 = err) (hnz : err ≠ 0#64) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ decodeErrorAtStackLen A err 0 ∗ spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hpush := @pushCall_648_placed_wp _ A H hH s0; have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29; have h1 : s.readReg64 (Reg.gpr 1#5) = err := hx1
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 => sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_pushCall) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre ?_ (hpush (sp' := sp') (x19 := x19) (ptr := ptr) (err := err) (mErr := mErr) (bs := bs)
    (out := out) herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
    (by simp [h29, arm64_norm]) hnz (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]))
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
  apply entails_of_eq; simp only [hsp_eq, h29, arm64_norm]; try ac_rfl

theorem tag1BadWt_460_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {s0 s : State} {sp' x19 ptr w0 : BitVec 64} {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag1BadWt) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = w0) (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hcall := spk_decodeErrorFrom_placed_ok hH; have hpush := @pushTag1_492_placed_wp _ A H hH s0; have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29; have h0 : s.readReg64 (Reg.gpr 0#5) = w0 := hx0
  have hstack := stackAt_sub_split sp' decodeErrorHookStack (SpqrV1.Varint.skipField3Stack 100)
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpackBytes sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun b0 => Wire.SepWPp.exists_pre fun b1 => sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 261) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre (spkErrBytes_pack_pre sp' (BitVec.ofNat 64 (2 ^ 63 + 6)) (w0.setWidth 8) 0#8 _) ?_
  refine sepWPp_call_lscro (sp' + 112#64, BitVec.ofNat 64 (2 ^ 63 + 6)) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (ret_pc := (blkPl_562).base + spkOff_tag1FromRet) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ BitVec.ofNat 64 (2 ^ 63 + 6)) ∗ memRegion (sp' + 112#64 + 8#64) 40 ∗ A.pool ∗ stackAt sp' decodeErrorHookStack)
    (φ := sp' + 112#64 = sp' + 112#64 ∧ KindNoHeap (BitVec.ofNat 64 (2 ^ 63 + 6)))
    (by simp [decodeErrorFromSpec, hsp_eq, h29, arm64_norm]) ⟨rfl, by simp [KindNoHeap]⟩
    (by rw [show sp' + 112#64 + 8#64 = sp' + 120#64 by bv_omega, hstack]; sep_focus) fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
  have hregs2 : SpkLoopRegs s0 sp' x19 s2 := SpkLoopRegs.of_calleeSaved hsp2 hcs2 (hregs.of_unchanged (by simp [arm64_norm]))
  have hsp2_eq := hregs2.sp; dsimp only [decodeErrorFromSpec]; simp only [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨herr_nz, htr2⟩ => sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_pushTag1) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
  refine Wire.SepWPp.mono_pre ?_ (hpush (sp' := sp') (x19 := x19) (ptr := ptr) (err := s2.readReg64 .x0) (mErr := mErr) (bs := bs) (out := out) herr
    (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (hregs2.of_unchanged (by simp [arm64_norm])) (by simp [arm64_norm]) herr_nz
    (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align) hcrl3 (by simp [htr2, htr, arm64_norm]))
  apply entails_of_eq; rw [hstack]; simp only [hsp_eq, hsp2_eq, arm64_norm]; try ac_rfl

theorem tag1_276_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : SignedHooksPlaced A H) (d : SignedPortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {wt : WireType} {m : SignedPreKeyRecordStructure} {out : Option SignedPreKeyRecordStructure}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k) (hlen : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag1) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlatch : ∀ (v : BitVec 32) (rest2 : List (BitVec 8)) (s3 : State), mergeUint32 wt rest = some (v, rest2) →
      s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running → SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem → s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkLoopMem A sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) rest2 { m with id := v })
        (spkConvergePostPlaced A s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) rest2 out) (tryFromQp s0))
    (hnone : mergeUint32 wt rest = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkAfterVarintMem A sp' x19 ptr bs rest bs.length m) (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintMem; refine spkAdvanceCursor_placed hsuf ?_; let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  have hcall := spk_decodeVarint6_placed_ok d; have hbad := @tag1BadWt_460_placed_wp _ A H hH s0; have hpush := @pushTag1_492_placed_wp _ A H hH s0
  have hsp_eq := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  cases wt with
  | varint =>
    dsimp only [WireType.toNat] at hx0; have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
    have hstack := stackAt_sub_split sp' SpqrV1.Varint.decodeVarint2Stack (SpqrV1.Varint.skipField3Stack 100)
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 559) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
    refine sepWPp_call_lscro ⟨sp' + 104#64, sp', ptr1, rest⟩ hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (ret_pc := (blkPl_562).base + spkOff_tag1Ret) (by simp [arm64_norm]) (by simpa [arm64_norm] using htr)
      (T := ((sp' + 104#64) ↦₆₄ sp') ∗ sliceCursorAt sp' ptr1 rest ∗ A.pool ∗ stackAt sp' SpqrV1.Varint.decodeVarint2Stack)
      (φ := sp' + 104#64 = sp' + 104#64 ∧ rest.length < 2 ^ 63)
      (by simp [SpqrV1.Varint.decodeVarint2Spec, hsp_eq, h29, arm64_norm]) ⟨rfl, hlen_rest⟩
      (by rw [hstack]; sep_focus) fun s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2 => ?_
    have hregs2 : SpkLoopRegs s0 sp' x19 s2 := SpkLoopRegs.of_calleeSaved hsp2 hcs2 (hregs.of_unchanged (by simp [arm64_norm]))
    clear hsp2 hcs2; have hsp2_eq := hregs2.sp
    have hsp'_align : (sp' &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp_eq] using hsp
    dsimp only [SpqrV1.Varint.decodeVarint2Spec]
    cases hdv : decodeVarint rest with
    | some p =>
      rcases p with ⟨v64, rest2⟩
      have hm : mergeUint32 .varint rest = some (v64.setWidth 32, rest2) := by unfold mergeUint32; simp [hdv]
      obtain ⟨k2, hkl2, hr2⟩ := mergeUint32_suffix hm; have hle2 : rest2.length ≤ bs.length := by rw [hr2, List.length_drop]; omega
      simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun ⟨hx0_0, hx1_v⟩ => Wire.SepWPp.pure_pre fun htr2 => ?_
      have hw0_0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0; have hw1_v : s2.readReg64 (Reg.gpr 1#5) = v64 := hx1_v
      refine Wire.SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (spkStructLoopOf_mono A sp' m hle2))))))) ?_
      unfold spkStructLoopOf; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
      refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
      rw [spkStructAt_split_id A g sp' m]; simp only [sepConj_assoc]; refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_latch) ?_
      wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
      have hid : ((sp' + 96#64) ↦₃₂ v64.setWidth 32) ∗
          (vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗ vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
            vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗ ((sp' + 88#64) ↦₆₄ m.timestamp) ∗ memRegion (sp' + 100#64) 4) ⊢
          spkStructLoopOf A sp' rest2.length { m with id := v64.setWidth 32 } := by
        rw [← spkStructAt_split_id A g sp' { m with id := v64.setWidth 32 }]; exact spkStructAt_entails_loopOf A g sp' rest2.length _ hg
      refine spkAdvanceToLatch_placed_prog ⟨k2, hkl2, hr2⟩
        (hlatch (v64.setWidth 32) rest2 _ hm (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (hregs2.of_unchanged (by simp [arm64_norm]))
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align) hcrl3 (by simp [htr2, htr, arm64_norm])) ?_
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hid))))
      apply entails_of_eq; dsimp only [ptr1]; rw [hstack]; simp only [hsp_eq, hsp2_eq, hw1_v, arm64_norm]; ac_rfl
    | none =>
      have hm : mergeUint32 .varint rest = none := by unfold mergeUint32; simp [hdv]
      simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun hx0_1 => Wire.SepWPp.pure_pre fun htr2 => ?_
      simp only [sepConj_assoc, sepConj_pure_left_comm]; refine Wire.SepWPp.pure_pre fun hx1_nz => ?_
      have hw0_1 : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1; have hbeq : (s2.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx1_nz
      refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_562).base + spkOff_pushTag1) ?_
      wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) fun hcrl3 => ?_
      refine Wire.SepWPp.mono_pre ?_ (hpush (sp' := sp') (x19 := x19) (ptr := ptr1) (err := s2.readReg64 .x1) (mErr := m) (bs := rest)
        (out := out) (hnone hm) (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (hregs2.of_unchanged (by simp [arm64_norm]))
        (by simp [arm64_norm]) hx1_nz (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align) hcrl3 (by simp [htr2, htr, arm64_norm]))
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (spkStructLoopOf_entails_of A sp' bs.length m))))))))) ?_
      apply entails_of_eq; rw [hstack]; simp only [hsp_eq, hsp2_eq, arm64_norm]; ac_rfl
  | sixtyFourBit | lengthDelimited | startGroup | endGroup | thirtyTwoBit =>
    have hm : out = none := hnone (by unfold mergeUint32; simp)
    have hcur := sliceCursorAt_entails_memRegion sp' ptr1 rest; have hof := spkStructLoopOf_entails_of A sp' bs.length m
    dsimp only [WireType.toNat] at hx0; have h0 : s.readReg64 (Reg.gpr 0#5) = _ := hx0
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag1BadWt) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
    refine Wire.SepWPp.mono_pre ?_ (hbad (sp' := sp') (x19 := x19) (ptr := ptr1) (w0 := s.readReg64 (Reg.gpr 0#5)) (mErr := m)
      (bs := rest) (out := out) hm (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]))
    refine Entails.trans (sepConj_mono hcur (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))) ?_; apply entails_of_eq; ac_rfl

theorem tag5BadWt_564_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {s0 s : State} {sp' x19 ptr w0 : BitVec 64} {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5BadWt) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = w0) (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hnext := @tag5FromPush_608_placed_wp _ A H hH s0
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29; have h0 : s.readReg64 (Reg.gpr 0#5) = w0 := hx0
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpackBytes sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun b0 =>
    Wire.SepWPp.exists_pre fun b1 => sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag5FromCommon) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre ?_ (hnext (sp' := sp') (x19 := x19) (ptr := ptr) (kind := BitVec.ofNat 64 (2 ^ 63 + 6))
    (mErr := mErr) (bs := bs) (out := out) herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (hregs.of_unchanged (by simp [arm64_norm])) (by simp [KindNoHeap])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]))
  simp only [h29, arm64_norm]; exact spkErrBytes_pack_pre sp' (BitVec.ofNat 64 (2 ^ 63 + 6)) (w0.setWidth 8) 1#8 _

theorem tag5Eof_600_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {mErr : SignedPreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure} (herr : out = none)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5Eof) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (memRegion (sp' + 112#64) 48 ∗ spkStructOf A sp' mErr ∗ memRegion sp' 16 ∗ ((sp' + 104#64) ↦₆₄ sp') ∗
        memRegion x19 88 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hnext := @tag5FromPush_608_placed_wp _ A H hH s0; have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  refine Wire.SepWPp.mono_pre (sepConj_mono_left (spkMemRegion48_unpack16 sp')) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun e0 => Wire.SepWPp.exists_pre fun e1 =>
    sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag5FromCommon) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
  refine Wire.SepWPp.mono_pre ?_ (hnext (sp' := sp') (x19 := x19) (ptr := ptr) (kind := BitVec.ofNat 64 (2 ^ 63 + 7))
    (mErr := mErr) (bs := bs) (out := out) herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (hregs.of_unchanged (by simp [arm64_norm])) (by simp [KindNoHeap])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]))
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left (spkErr16_pack40 sp' e1)))
  apply entails_of_eq; simp only [hsp_eq, h29, arm64_norm]; try ac_rfl

private theorem tag5_short_step [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {s0 s : State} {sp' x19 ptr1 : BitVec 64} {n : ℕ} {short : List (BitVec 8)} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure} (hm : out = none) (hlt : short.length < 8)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (h0 : s.readReg64 (Reg.gpr 0#5) = 1#64) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (sliceCursorAt sp' ptr1 short ∗ ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion (sp' + 112#64) 48 ∗
        spkStructLoopOf A sp' n m ∗ memRegion x19 88 ∗ A.pool ∗ stackAt sp' (SpqrV1.Varint.skipField3Stack 100))
      (spkConvergePostPlaced A s0 sp' x19 ptr1 short out) (tryFromQp s0) := by
  have heof := @tag5Eof_600_placed_wp _ A H hH s0; have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hult : (BitVec.ofNat 64 short.length).ult 8#64 = true := by
    simp [BitVec.ult, Nat.mod_eq_of_lt (by omega : short.length < 2 ^ 64)]; omega
  unfold sliceCursorAt; simp only [sepConj_assoc]; refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag5Eof) ?_
  wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 =>
    Wire.SepWPp.mono_pre (tag5Short_pack (SpqrV1.Varint.skipField3Stack 100) A sp' x19 ptr1 short n m)
      (heof (sp' := sp') (x19 := x19) (ptr := ptr1) (mErr := m) (bs := short) (out := out) hm
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]))

theorem tag5_176_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {s0 s : State} {sp' x19 ptr : BitVec 64} {bs rest : List (BitVec 8)} {wt : WireType} {m : SignedPreKeyRecordStructure}
    {out : Option SignedPreKeyRecordStructure} (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k) (hlen : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_562).base + spkOff_tag5) (hrun : s.status = .Running) (hregs : SpkLoopRegs s0 sp' x19 s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlatch : ∀ (v : BitVec 64) (rest2 : List (BitVec 8)) (s3 : State), mergeFixed64 wt rest = some (v, rest2) →
      s3.pc = (blkPl_562).base + spkOff_latch → s3.status = .Running → SpkLoopRegs s0 sp' x19 s3 →
      s3.spAligned = true → LibsignalCodeRoLoaded lsmpl s3.mem → s3.trace = s0.trace →
      Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s3
        (spkLoopMem A sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) rest2 { m with timestamp := v })
        (spkConvergePostPlaced A s0 sp' x19 (ptr + BitVec.ofNat 64 (bs.length - rest.length) + BitVec.ofNat 64 (rest.length - rest2.length)) rest2 out) (tryFromQp s0))
    (hnone : mergeFixed64 wt rest = none → out = none) :
    Wire.SepWPp (lsProg_562 H) ((blkPl_562).base + spkOff_converge) s
      (spkAfterVarintMem A sp' x19 ptr bs rest bs.length m) (spkConvergePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hle_bs : rest.length ≤ bs.length := by rcases hsuf with ⟨k, _, rfl⟩; simp
  have hlen_rest : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hle_bs hlen
  unfold spkAfterVarintMem; refine spkAdvanceCursor_placed hsuf ?_; let ptr1 := ptr + BitVec.ofNat 64 (bs.length - rest.length)
  have hbad := @tag5BadWt_564_placed_wp _ A H hH s0; have hsp_eq := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  cases wt with
  | sixtyFourBit =>
    dsimp only [WireType.toNat] at hx0; have h0 : s.readReg64 (Reg.gpr 0#5) = 1#64 := hx0
    by_cases hlt8 : rest.length < 8
    · exact tag5_short_step hH (hnone (by
        rcases rest with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
          (simp [mergeFixed64] at hlt8 ⊢; try omega))) hlt8 hpc hrun hregs h0 hsp hcrl htr
    rcases rest with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest2⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      try (simp at hlt8; done)
    let restFull := b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest2
    have hm : mergeFixed64 .sixtyFourBit restFull = some (le64 b0 b1 b2 b3 b4 b5 b6 b7, rest2) := rfl
    have hge8 : 8 ≤ restFull.length := by simp [restFull]
    have hle2 : rest2.length ≤ bs.length := by simp only [List.length_cons] at hle_bs; omega
    have ⟨hcc_ok, hsub8⟩ := spk_sub8_ge8 hge8 hlen_rest
    have hult_false : (BitVec.ofNat 64 restFull.length).ult 8#64 = false := by simpa using hcc_ok
    have hult_false' : (BitVec.ofNat 64 (rest2.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)).ult 8#64 = false := by
      simpa only [restFull, List.length_cons] using hult_false
    have hsub8' : BitVec.ofNat 64 restFull.length - 8#64 = BitVec.ofNat 64 rest2.length := by rw [hsub8]; congr 1
    refine Wire.SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (spkStructLoopOf_mono A sp' m hle2))))) ?_
    unfold spkStructLoopOf sliceCursorAt; rw [spk_pointsToBytes8_cons ptr1 b0 b1 b2 b3 b4 b5 b6 b7 rest2, spk_le64_eq_pair32 b0 b1 b2 b3 b4 b5 b6 b7]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun g => ?_; rw [tag5_cap_peel]; refine Wire.SepWPp.pure_pre fun hg => ?_
    rw [spkStructAt_split_timestamp A g sp' m]; simp only [sepConj_assoc]; refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_latch) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
    have h8take : (ptr1 ↦₆₄ le64 b0 b1 b2 b3 b4 b5 b6 b7) = (ptr1 ↦ₛ restFull.take 8) := by
      have hnil := (spk_pointsToBytes8_cons ptr1 b0 b1 b2 b3 b4 b5 b6 b7 []).symm; rw [pointsToBytes_nil, sepConj_emp, spk_le64_eq_pair32] at hnil; exact hnil
    have hl_app := hlatch (le64 b0 b1 b2 b3 b4 b5 b6 b7) rest2 _ hm (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (hregs.of_unchanged (by simp [arm64_norm])) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm])
    have hlen_sub : restFull.length - rest2.length = 8 := by simp only [restFull, List.length_cons]; omega
    rw [hlen_sub, show rest2 = restFull.drop 8 from rfl] at hl_app
    refine Wire.SepWPp.mono_pre ?_ (Wire.SepWPp.frame_tryFrom hl_app
      (fun sf Pf hqm => spkConvergePostPlaced_append_prefix A s0 sp' x19 ptr1 restFull 8 hge8 out sf Pf hqm))
    unfold spkLoopMem sliceCursorAt
    have hts : ((sp' + 88#64) ↦₆₄ le64 b0 b1 b2 b3 b4 b5 b6 b7) ∗
        (vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗ vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
          vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗ ((sp' + 96#64) ↦₃₂ m.id) ∗ memRegion (sp' + 100#64) 4) ⊢
        spkStructLoopOf A sp' rest2.length { m with timestamp := le64 b0 b1 b2 b3 b4 b5 b6 b7 } := by
      rw [← spkStructAt_split_timestamp A g sp' { m with timestamp := le64 b0 b1 b2 b3 b4 b5 b6 b7 }]; exact spkStructAt_entails_loopOf A g sp' rest2.length _ hg
    rw [h8take]; dsimp only [ptr1, restFull, List.drop, List.take]; simp only [hsp_eq, h29, List.length_cons, arm64_norm]
    erw [hsub8']
    set p1 := ptr + BitVec.ofNat 64 (bs.length - (rest2.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1))
    refine Entails.trans (Q := (((sp' + 88#64) ↦₆₄ le64 b0 b1 b2 b3 b4 b5 b6 b7) ∗
        (vecU8At A (sp' + 16#64) g.pub.cap g.pub.ptr m.publicKey ∗ vecU8At A (sp' + 40#64) g.priv.cap g.priv.ptr m.privateKey ∗
          vecU8At A (sp' + 64#64) g.sig.cap g.sig.ptr m.signature ∗ ((sp' + 96#64) ↦₃₂ m.id) ∗ memRegion (sp' + 100#64) 4)) ∗
      ((sp' ↦₆₄ (p1 + 8#64)) ∗ ((sp' + 8#64) ↦₆₄ BitVec.ofNat 64 rest2.length) ∗ ((p1 + 8#64) ↦ₛ rest2) ∗
        ((sp' + 104#64) ↦₆₄ sp') ∗ memRegion (sp' + 112#64) 48 ∗ memRegion x19 88 ∗ A.pool ∗
        stackAt sp' (SpqrV1.Varint.skipField3Stack 100) ∗ (p1 ↦ₛ ([b0, b1, b2, b3, b4, b5, b6, b7] : List (BitVec 8)))))
      (by apply entails_of_eq; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)
      (Entails.trans (sepConj_mono_left hts)
        (by apply entails_of_eq; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl))
  | varint | lengthDelimited | startGroup | endGroup | thirtyTwoBit =>
    have hm : out = none := hnone (by unfold mergeFixed64; simp)
    have hcur := sliceCursorAt_entails_memRegion sp' ptr1 rest; have hof := spkStructLoopOf_entails_of A sp' bs.length m
    dsimp only [WireType.toNat] at hx0; have h0 : s.readReg64 (Reg.gpr 0#5) = _ := hx0
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_tag5BadWt) ?_
    wp_steps; refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcrl1 => ?_
    refine Wire.SepWPp.mono_pre ?_ (hbad (sp' := sp') (x19 := x19) (ptr := ptr1) (w0 := s.readReg64 (Reg.gpr 0#5)) (mErr := m)
      (bs := rest) (out := out) hm (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (hregs.of_unchanged (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simp [htr, arm64_norm]))
    refine Entails.trans (sepConj_mono hcur (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof)))) ?_; apply entails_of_eq; ac_rfl

end Placed

end CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers
