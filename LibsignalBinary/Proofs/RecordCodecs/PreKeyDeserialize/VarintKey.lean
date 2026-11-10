/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Post
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# `PreKeyRecord::deserialize` Tag Varint Decode

Verifies the inline fast-path and `decode_varint` slow-path key decode steps in
`PreKeyRecord::deserialize`.
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

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

/-! ## Loop memory bundles & error-cleanup bridge entailments -/

def pkLoopMem (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs : List (BitVec 8)) (m : PreKeyRecordStructure) : SepProp :=
  sliceCursorAt (sp' + 40#64) ptr bs ∗
    ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
    memRegion (sp' + 112#64) 48 ∗
    preKeyStructLoopOf A (sp' + 56#64) bs.length m ∗
    memRegion sp' 40 ∗
    memRegion x19 56 ∗
    A.pool ∗
    stackAt sp' (skipFieldStackX 100)
def pkAfterVarintMem (A : RustAlloc) (sp' x19 ptr : BitVec 64)
    (bs rest : List (BitVec 8)) (n : ℕ) (m : PreKeyRecordStructure) : SepProp :=
  sliceCursorAfter (sp' + 40#64) ptr bs rest ∗
    ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
    memRegion (sp' + 112#64) 48 ∗
    preKeyStructLoopOf A (sp' + 56#64) n m ∗
    memRegion sp' 40 ∗
    memRegion x19 56 ∗
    A.pool ∗
    stackAt sp' (skipFieldStackX 100)
theorem pkPointsTo112_memRegion40_entails_memRegion48 (sp' v : BitVec 64) :
    ((sp' + 112#64) ↦₆₄ v) ∗ memRegion (sp' + 120#64) 40 ⊢ memRegion (sp' + 112#64) 48 := by
  rw [pkMemRegion48_split8 sp']
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 112#64) v)
theorem pkPointsTo120_memRegion32_entails_memRegion40 (sp' v : BitVec 64) :
    ((sp' + 120#64) ↦₆₄ v) ∗ memRegion (sp' + 128#64) 32 ⊢ memRegion (sp' + 120#64) 40 := by
  rw [ProofLib.memRegion_split (sp' + 120#64) 8 32 (by decide)]
  have ha : sp' + 120#64 + 8#64 = sp' + 128#64 := by bv_omega
  rw [ha]
  exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 120#64) v)
theorem pkErrMem_of_structOf (A : RustAlloc) (sp' x19 ptr err : BitVec 64)
    (n : ℕ) (mErr : PreKeyRecordStructure) (bs : List (BitVec 8)) :
    memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      memRegion (sp' + 112#64) 48 ∗
      decodeErrorAtStackLen A err n ∗
      preKeyStructOf A (sp' + 56#64) mErr ∗
      memRegion sp' 40 ∗ memRegion x19 56 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
    preKeyStructOf A (sp' + 56#64) mErr ∗
      memRegion sp' 40 ∗
      memRegion (sp' + 40#64) 16 ∗
      memRegion (sp' + 112#64) 48 ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      decodeErrorAt A err ∗
      memRegion x19 56 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
  have hdec := decodeErrorWith_entails_at A err n
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hdec))))) ?_
  apply entails_of_eq
  ac_rfl
theorem pkErrMem_of_loopOf (A : RustAlloc) (sp' x19 ptr err : BitVec 64)
    (n k : ℕ) (mErr : PreKeyRecordStructure) (bs : List (BitVec 8)) :
    memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      memRegion (sp' + 112#64) 48 ∗
      decodeErrorAtStackLen A err n ∗
      preKeyStructLoopOf A (sp' + 56#64) k mErr ∗
      memRegion sp' 40 ∗ memRegion x19 56 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
    preKeyStructOf A (sp' + 56#64) mErr ∗
      memRegion sp' 40 ∗
      memRegion (sp' + 40#64) 16 ∗
      memRegion (sp' + 112#64) 48 ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      decodeErrorAt A err ∗
      memRegion x19 56 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (preKeyStructLoopOf_entails_of A (sp' + 56#64) k mErr)))))))
    (pkErrMem_of_structOf A sp' x19 ptr err n mErr bs)
/-! ## `DecodeError::from` & `DecodeError::push` tails (`+0x1c4..+0x1cc`, `+0x2cc..+0x2d4`) -/
theorem decodeErrorFrom_1c8_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr kind : BitVec 64}
    {bs : List (BitVec 8)} {mErr : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x1c8#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hkind : KindNoHeap kind) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 120#64) 40 ∗
        preKeyStructOf A (sp' + 56#64) mErr ∗
        memRegion sp' 40 ∗ memRegion x19 56 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := decodeErrorFrom_ok_sub hC
  have hpost := @post_err_1d0_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 456 8
  dsimp only [tripleRatchetProgAtExt] at hcall hpost hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom (sp' + 112#64, kind) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (464)) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 120#64) 40 ∗
      A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := KindNoHeap kind)
    (by simp [decodeErrorFromSpecWithStack, hsp_eq, arm64_norm])
    hkind
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      hsp2 hcs2
  dsimp only [decodeErrorFromSpecWithStack]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨_hx0_ne, htr2⟩ => ?_
  refine Wire.SepWPp.mono_pre ?_
    (hpost (err := s2.readReg64 .x0) (mErr := mErr) herr
      ⟨hregs2.sp, hsp2_align, hF2, hsym2, (by simp [htr2, htr, arm64_norm]), hregs2.saved⟩
      hpc2 hrun2 rfl hregs2.x19_eq hregs2.x22)
  refine Entails.trans ?_
    (pkErrMem_of_structOf A sp' x19 ptr (s2.readReg64 .x0) 0 mErr bs)
  apply entails_of_eq
  simp only [hstack, hsp_eq, arm64_norm]
  ac_rfl
theorem decodeErrorFrom_1c4_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x1c4#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hkind : KindNoHeap (s.readReg64 .x8)) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        ((sp' + 112#64) ↦₆₄ w0) ∗ memRegion (sp' + 120#64) 40 ∗
        preKeyStructOf A (sp' + 56#64) mErr ∗
        memRegion sp' 40 ∗ memRegion x19 56 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hnext := @decodeErrorFrom_1c8_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 452 4
  dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (456)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hnext (kind := s.readReg64 .x8) (mErr := mErr) herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simpa [arm64_norm] using htr) hkind)
  apply entails_of_eq
  simp only [arm64_norm]
theorem decodeErrorPush_2cc_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr err : BitVec 64} {n : ℕ}
    {bs : List (BitVec 8)} {mErr : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x2cc#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = sp' + 112#64)
    (herr_ne : err ≠ 0#64)
    (hn : n < 2 ^ 32) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        ((sp' + 112#64) ↦₆₄ err) ∗ memRegion (sp' + 120#64) 40 ∗
        decodeErrorAtStackLen A err n ∗
        preKeyStructOf A (sp' + 56#64) mErr ∗
        memRegion sp' 40 ∗ memRegion x19 56 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := decodeErrorPush_ok_sub hC
  have hpost := @post_err_1d0_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 716 12
  dsimp only [tripleRatchetProgAtExt] at hcall hpost hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = sp' + 112#64 := hx0
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "<prost::error::DecodeError>::push" -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom (sp' + 112#64, err, n) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (720)) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗
      A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ n < 4294967296)
    (by simp [decodeErrorPushExternSpecWithStack, hsp_eq, h0, arm64_norm])
    ⟨herr_ne, hn⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  dsimp only [decodeErrorPushExternSpecWithStack]
  rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun err' => ?_
  refine Wire.SepWPp.pure_pre fun _herr' => ?_
  refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (464)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
  intro hF3 hsym3
  refine Wire.SepWPp.mono_pre ?_
    (hpost (err := err') (mErr := mErr) herr
      ⟨by simpa [arm64_norm] using hregs2.sp,
       by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
       hF3, hsym3,
       by simpa [arm64_norm] using htr2.trans htr,
       ⟨by simpa [arm64_norm] using hregs2.saved.x24,
        by simpa [arm64_norm] using hregs2.saved.x25,
        by simpa [arm64_norm] using hregs2.saved.x26,
        by simpa [arm64_norm] using hregs2.saved.x27,
        by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
      (by simp [arm64_norm])
      (by simpa [arm64_norm] using hregs2.x19_eq)
      (by simpa [speWord, arm64_norm] using hregs2.x22))
  have hscr := pkPointsTo112_memRegion40_entails_memRegion48 sp' err'
  refine Entails.trans ?_
    (pkErrMem_of_structOf A sp' x19 ptr err' (n + 1) mErr bs)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
  apply entails_of_eq
  simp only [hstack, hsp_eq, arm64_norm]
  ac_rfl
/-! ## `decode_varint` fast, slice, slow, and dispatch paths (`+0x080..+0x0dc`, `+0x15c..+0x170`) -/
theorem decodeVarintSlow_15c_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x15c#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0e0#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = key →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePost img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : decodeVarint bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := varintSlow_ok_sub hC
  have hpost := @post_err_1d0_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 348 24
  dsimp only [tripleRatchetProgAtExt] at hcall hpost hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (64 + 2 * extHookStack) (skipFieldStackX 100)
  unfold pkLoopMem sliceCursorAt
  simp only [hstack]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom (sp' + 184#64, sp' + 40#64, ptr, bs) hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (356)) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ ((sp' + 40#64) ↦₆₄ ptr) ∗
      ((sp' + 40#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      A.pool ∗ stackAt sp' (64 + 2 * extHookStack))
    (φ := bs.length < 18446744073709551616)
    (by simp [decodeVarintSlowSpecWithStack, hsp_eq, arm64_norm])
    (by omega)
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      hsp2 hcs2
  dsimp only [decodeVarintSlowSpecWithStack]
  rw [VarintBridge.decodeVarint_eq_varintSlow bs]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [Option.map]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hlen_sub : bs.length - (bs.length - rest.length) = rest.length := by
      rw [hrest, List.length_drop]; omega
    rw [hlen_sub, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hx0_2, hx1_2⟩ => ?_
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have hx1_2' : s2.readReg64 (Reg.gpr 1#5) = key := hx1_2
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (224)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hcont key rest _ hd
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3
        (by simpa [arm64_norm] using htr2.trans htr)
        (by simp [arm64_norm]))
    apply entails_of_eq
    unfold pkAfterVarintMem sliceCursorAfter
    simp only [hstack, hsp_eq, arm64_norm]
    ac_rfl
  | none =>
    dsimp only [Option.map]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hx0_1, _hx1_ne⟩ => ?_
    have hx0_1' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (464)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hpost (err := s2.readReg64 (Reg.gpr 1#5)) (mErr := m) (hnone hd)
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hF3, hsym3,
         by simpa [arm64_norm] using htr2.trans htr,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [arm64_norm])
        (by simpa [arm64_norm] using hregs2.x19_eq)
        (by simpa [speWord, arm64_norm] using hregs2.x22))
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 40#64)
      (ptr + BitVec.ofNat 64 (min 10 bs.length))
      (BitVec.ofNat 64 (bs.length - min 10 bs.length))
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_
      (pkErrMem_of_loopOf A sp' x19 ptr (s2.readReg64 (Reg.gpr 1#5)) 0 bs.length m bs)
    refine Entails.trans ?_ (sepConj_mono_left hpair)
    apply entails_of_eq
    simp only [hstack, hsp_eq, arm64_norm]
    ac_rfl
theorem decodeVarintSlice_0ac_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0ac#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64)
    (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx1 : s.readReg64 .x1 = ptr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hpre_slice : VarintSlicePre bs)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0e0#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = key →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePost img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : decodeVarint bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hcall := varintSlice_ok_sub d
  have hpost := @post_err_1d0_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 172 52
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 604 8
  dsimp only [tripleRatchetProgAtExt] at hcall hpost hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h23 : s.readReg64 (Reg.gpr 23#5) = sp' + 40#64 := hx23
  have h21 : s.readReg64 (Reg.gpr 21#5) = sp' + 48#64 := hx21
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split sp' decodeVarintSliceStackX (skipFieldStackX 100)
  unfold pkLoopMem sliceCursorAt
  simp only [hstack, pkMemRegion48_split24 sp', sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom ⟨sp' + 112#64, ptr, bs⟩ hcall
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (180)) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 112#64) 24 ∗ (ptr ↦ₛ bs) ∗
      A.pool ∗ stackAt sp' decodeVarintSliceStackX)
    (φ := bs.length < 9223372036854775808 ∧ VarintSlicePre bs)
    (by simp [decodeVarintSliceSpecX, hsp_eq, h1, h2, hx2_nat, arm64_norm])
    ⟨hlen, hpre_slice⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  have h23_2 : s2.readReg64 (Reg.gpr 23#5) = sp' + 40#64 := by
    simpa [arm64_norm, h23] using hcs2.2.2.2.2.1
  have h21_2 : s2.readReg64 (Reg.gpr 21#5) = sp' + 48#64 := by
    simpa [arm64_norm, h21] using hcs2.2.2.1
  dsimp only [decodeVarintSliceSpecX]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [varintSliceResultAt]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hlen64 : bs.length < 2 ^ 64 := by omega
    have hrest64 : rest.length < 2 ^ 64 := by omega
    have hsub64 : bs.length - rest.length < 2 ^ 64 := by omega
    have hsub_bv :
        BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) =
          BitVec.ofNat 64 rest.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hrest64]
      omega
    have hult_false :
        (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64,
        decide_eq_false_iff_not]
      omega
    rw [pointsTo64_zero_split32 (sp' + 112#64)]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (224)) ?_
    wp_steps
    wp_if hcc
    · exfalso
      rw [← hrest] at hcc
      exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
      intro hF3 hsym3
      refine Wire.SepWPp.mono_pre ?_
        (hcont key rest _ hd
          (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
           by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x24,
            by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26,
            by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3
          (by simpa [arm64_norm] using htr2.trans htr)
          (by simp [arm64_norm]))
      have hscr := pkScratch24_ok_entails_memRegion48 sp' key
        (BitVec.ofNat 64 (bs.length - rest.length))
      unfold pkAfterVarintMem sliceCursorAfter
      simp only [← hrest, hsub_bv]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr)))
      apply entails_of_eq
      simp only [hstack, hsp_eq, arm64_norm]
      ac_rfl
  | none =>
    dsimp only [varintSliceResultAt]
    rw [pointsTo64_one_split32 (sp' + 112#64), sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm]
    refine Wire.SepWPp.exists_pre fun e => Wire.SepWPp.pure_pre fun _he_ne => ?_
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (464)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hpost (err := e) (mErr := m) (hnone hd)
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hF3, hsym3,
         by simpa [arm64_norm] using htr2.trans htr,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [arm64_norm])
        (by simpa [arm64_norm] using hregs2.x19_eq)
        (by simpa [speWord, arm64_norm] using hregs2.x22))
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 40#64) ptr
      (BitVec.ofNat 64 bs.length)
    have hscr := pkScratch24_err_entails_memRegion48 sp' e
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_
      (pkErrMem_of_loopOf A sp' x19 ptr e 0 bs.length m bs)
    refine Entails.trans ?_
      (sepConj_mono hpair
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
    apply entails_of_eq
    simp only [hstack, hsp_eq, arm64_norm]
    ac_rfl
theorem decodeVarintMulti_098_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x098#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64)
    (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx1 : s.readReg64 .x1 = ptr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hne : bs ≠ [])
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0e0#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = key →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePost img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : decodeVarint bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have hslice := @decodeVarintSlice_0ac_cps img A ext hC d s0
  have hslow := @decodeVarintSlow_15c_cps img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 152 20
  dsimp only [tripleRatchetProgAtExt] at hslice hslow hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hlen_pos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hlen64 : bs.length < 2 ^ 64 := by omega
  by_cases hlen11 : 11 ≤ bs.length
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_true_eq]
      omega
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (172)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact hslice
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simpa [arm64_norm] using hx23)
      (by simpa [arm64_norm] using hx21)
      (by simpa [arm64_norm] using hx1)
      (by simpa [arm64_norm] using hx2)
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simpa [arm64_norm] using htr)
      hlen (Or.inl hlen11) hcont hnone
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_false_iff_not]
      omega
    have hlast_addr :
        ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) =
          ptr + BitVec.ofNat 64 (bs.length - 1) := by
      have heq : bs.length = (bs.length - 1) + 1 := by omega
      have h1_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (bs.length - 1) + 1#64 := by
        conv_lhs => rw [heq]
        exact BitVec.ofNat_add (bs.length - 1) 1
      rw [h1_eq]
      bv_omega
    by_cases hlast : (bs.getLast hne).toNat ≤ 0x7F
    · have hbit31 := (signExtend32_bit31_eq_false_iff (bs.getLast hne)).mpr hlast
      unfold pkLoopMem sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (172)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre ?_
        (hslice
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24,
            by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simpa [arm64_norm] using hx23)
          (by simpa [arm64_norm] using hx21)
          (by simpa [arm64_norm] using hx1)
          (by simpa [arm64_norm] using hx2)
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simpa [arm64_norm] using htr)
          hlen (Or.inr ⟨hne, hlast⟩) hcont hnone)
      apply entails_of_eq
      unfold pkLoopMem sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [arm64_norm, sepConj_assoc]
    · have hbit31 := (signExtend32_bit31_eq_true_iff (bs.getLast hne)).mpr (by omega)
      unfold pkLoopMem sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [sepConj_assoc]
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (348)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre ?_
        (hslow
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24,
            by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simpa [arm64_norm] using htr)
          hlen hcont hnone)
      apply entails_of_eq
      unfold pkLoopMem sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]
      simp only [arm64_norm, sepConj_assoc]
theorem decodeVarint_080_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x080#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64)
    (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint (b0 :: bs1) = some (key, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0e0#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = key →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr (b0 :: bs1) rest (b0 :: bs1).length m)
        (pkEpiloguePost img A s0 sp' x19 ptr (b0 :: bs1) out)
        (tryFromQp s0))
    (hnone : decodeVarint (b0 :: bs1) = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr (b0 :: bs1) m)
      (pkEpiloguePost img A s0 sp' x19 ptr (b0 :: bs1) out)
      (tryFromQp s0) := by
  have hmulti := @decodeVarintMulti_098_cps img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 128 24
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 216 8
  dsimp only [tripleRatchetProgAtExt] at hmulti hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have h23 : s.readReg64 (Reg.gpr 23#5) = sp' + 40#64 := hx23
  have h21 : s.readReg64 (Reg.gpr 21#5) = sp' + 48#64 := hx21
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (b0 :: bs1).length := hx2
  by_cases hb0 : b0.toNat ≤ 0x7F
  · have hbit63 := (signExtend64_bit63_eq_false_iff b0).mpr hb0
    have hd := decodeVarint_cons_of_le b0 bs1 hb0
    have hsub1 :
        BitVec.ofNat 64 (bs1.length + 1) - 1#64 =
          BitVec.ofNat 64 bs1.length := by
      have h1_eq : BitVec.ofNat 64 (bs1.length + 1) = BitVec.ofNat 64 bs1.length + 1#64 :=
        BitVec.ofNat_add bs1.length 1
      rw [h1_eq]
      bv_omega
    unfold pkLoopMem sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (224)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    have hse := signExtend64_eq_zeroExtend64_of_le b0 hb0
    refine Wire.SepWPp.mono_pre ?_
      (hcont (b0.zeroExtend 64) bs1 _ hd
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x24,
          by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26,
          by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr)
        (by simp [hse, arm64_norm]))
    apply entails_of_eq
    unfold pkAfterVarintMem sliceCursorAfter
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [List.length_cons, Nat.add_sub_cancel_left, hsub1, arm64_norm, sepConj_assoc]
  · have hbit63 := (signExtend64_bit63_eq_true_iff b0).mpr (by omega)
    unfold pkLoopMem sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (152)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.mono_pre ?_
      (hmulti
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x24,
          by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26,
          by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simpa [arm64_norm] using hx23)
        (by simpa [arm64_norm] using hx21)
        (by simp [arm64_norm])
        (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr)
        (List.cons_ne_nil b0 bs1) hlen hcont hnone)
    apply entails_of_eq
    unfold pkLoopMem sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [arm64_norm, sepConj_assoc]
/-! ## `decode_key` validation tail (`+0x0e0..+0x0f8` and error stubs `+0x1a8..+0x1c0`) -/
theorem pkDecodeKey_err_entails (A : RustAlloc) (sp' x19 ptr w0 v : BitVec 64)
    (bs rest : List (BitVec 8)) (len : ℕ) (m : PreKeyRecordStructure) :
    sliceCursorAfter (sp' + 40#64) ptr bs rest ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      ((sp' + 112#64) ↦₆₄ w0) ∗
      ((sp' + 120#64) ↦₆₄ v) ∗
      memRegion (sp' + 128#64) 32 ∗
      preKeyStructLoopOf A (sp' + 56#64) len m ∗
      memRegion sp' 40 ∗ memRegion x19 56 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) ⊢
    memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      ((sp' + 112#64) ↦₆₄ w0) ∗ memRegion (sp' + 120#64) 40 ∗
      preKeyStructOf A (sp' + 56#64) m ∗
      memRegion sp' 40 ∗ memRegion x19 56 ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100) := by
  refine Entails.trans
    (sepConj_mono_left (sliceCursorAfter_entails_memRegion (sp' + 40#64) ptr bs rest)) ?_
  rw [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  rw [← sepConj_assoc]
  exact sepConj_mono (pkPointsTo120_memRegion32_entails_memRegion40 sp' v)
    (sepConj_mono_left (preKeyStructLoopOf_entails_of A (sp' + 56#64) len m))
theorem decodeKey_tail_0e0_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr key : BitVec 64}
    {bs rest : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0e0#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = key)
    (hcont : ∀ (tag : ℕ) (wt : WireType) (s1 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0fc#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePost img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : decodeKey bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  have herr1c4 := @decodeErrorFrom_1c4_wp img A ext hC d s0
  have herr1c8 := @decodeErrorFrom_1c8_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 224 28
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 424 28
  dsimp only [tripleRatchetProgAtExt] at herr1c4 herr1c8 hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have h0 : s.readReg64 (Reg.gpr 0#5) = key := hx0
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h22 : s.readReg64 (Reg.gpr 22#5) = 0x8000000000000002#64 := hregs.x22
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by
      unfold decodeKey
      rw [hdv]
      simp only [hkey32, ↓reduceIte]
    have hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    unfold pkAfterVarintMem
    rw [pkMemRegion48_split_112_120_128 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w0 => ?_
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (452)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.mono_pre ?_
      (herr1c4 (w0 := w0) (mErr := m) (hnone hdk)
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x24,
          by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26,
          by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr)
        (by simp [KindNoHeap, arm64_norm]))
    refine Entails.trans ?_
      (pkDecodeKey_err_entails A sp' x19 ptr w0 key bs rest bs.length m)
    apply entails_of_eq
    ac_rfl
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by
        unfold decodeKey
        rw [hdv]
        simp only [hkey32, ↓reduceIte, hwt]
      have hge6 : 6 ≤ key.toNat % 8 :=
        (WireType.ofNat?_eq_none_iff (key.toNat % 8) (by omega)).mp hwt
      have hbcs := key_and7_ule6_of_ge key hge6
      unfold pkAfterVarintMem
      rw [pkMemRegion48_split_112_120_128 sp']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w0 => ?_
      refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (456)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
      intro hF1 hsym1
      refine Wire.SepWPp.mono_pre ?_
        (herr1c8 (kind := 0x8000000000000003#64) (mErr := m) (hnone hdk)
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24,
            by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simpa [arm64_norm] using htr)
          (by simp [KindNoHeap]))
      refine Entails.trans ?_
        (pkDecodeKey_err_entails A sp' x19 ptr 0x8000000000000003#64 (key &&& 7#64) bs rest bs.length m)
      apply entails_of_eq
      simp only [arm64_norm]
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := WireType.lt_six_of_ofNat?_eq_some hwt
      have hbcs := key_and7_ule6_of_lt key hlt6
      by_cases htag0 : key.toNat / 8 < 1
      · have hdk : decodeKey bs = none := by
          unfold decodeKey
          rw [hdv]
          simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
        unfold pkAfterVarintMem
        rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine Wire.SepWPp.exists_pre fun w0 => ?_
        refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (452)) ?_
        wp_steps
        refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
        intro hF1 hsym1
        refine Wire.SepWPp.mono_pre ?_
          (herr1c4 (w0 := w0) (mErr := m) (hnone hdk)
            (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
             by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
             by simpa [arm64_norm] using hregs.x19_eq,
             ⟨by simpa [arm64_norm] using hregs.saved.x24,
              by simpa [arm64_norm] using hregs.saved.x25,
              by simpa [arm64_norm] using hregs.saved.x26,
              by simpa [arm64_norm] using hregs.saved.x27,
              by simpa [arm64_norm] using hregs.saved.x28⟩⟩
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
            hF1 hsym1 (by simpa [arm64_norm] using htr)
            (by simp [KindNoHeap, arm64_norm]))
        refine Entails.trans
          (sepConj_mono (sliceCursorAfter_entails_memRegion (sp' + 40#64) ptr bs rest)
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (preKeyStructLoopOf_entails_of A (sp' + 56#64) bs.length m)))))) ?_
        apply entails_of_eq
        simp only [arm64_norm, sepConj_assoc]
      · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
          unfold decodeKey
          rw [hdv]
          simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
        refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (252)) ?_
        wp_steps
        refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
        intro hF1 hsym1
        have htag_eq := key_tag32_zeroExtend64_eq key hkey_lt
        have hand7_eq := key_and7_eq_wt key hwt
        exact hcont (key.toNat / 8) wt _ hdk
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24,
            by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26,
            by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hF1 hsym1 (by simpa [arm64_norm] using htr)
          (by simp [arm64_norm]; exact hand7_eq)
          (by simp [arm64_norm]; exact htag_eq)
theorem decodeKey_080_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x080#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64)
    (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (tag : ℕ) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0fc#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr (b0 :: bs1) rest (b0 :: bs1).length m)
        (pkEpiloguePost img A s0 sp' x19 ptr (b0 :: bs1) out)
        (tryFromQp s0))
    (hnone : decodeKey (b0 :: bs1) = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr (b0 :: bs1) m)
      (pkEpiloguePost img A s0 sp' x19 ptr (b0 :: bs1) out)
      (tryFromQp s0) :=
  decodeVarint_080_cps hC d hpc hrun hregs hx23 hx21 hx2 hsp hF hsym htr hlen
    (fun key rest s1 hdv hpc1 hrun1 hregs1 hsp1 hF1 hsym1 htr1 hx0_1 =>
      decodeKey_tail_0e0_cps hC d hdv hpc1 hrun1 hregs1 hsp1 hF1 hsym1 htr1 hx0_1
        (fun tag wt s2 hdk => hcont tag wt rest s2 hdk)
        hnone)
    (fun hdv_none => hnone (by simp [decodeKey, hdv_none]))

/-! ## Relocatable `[LibsignalPlacement]` Cursor Advance Combinator -/
section Placed
open CryptoVerification.RecordCodecs.Placed
theorem pkAdvanceCursor_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (sliceCursorAt (sp' + 40#64) (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (pkEpiloguePostPlaced A s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (tryFromQp s0)) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (sliceCursorAfter (sp' + 40#64) ptr bs rest ∗ R)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt (sp' + 40#64) ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine Wire.SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 40#64) (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗
      (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; ac_rfl) ?_
  exact Wire.SepWPp.frame_tryFrom h
    (fun sf Pf hqm => pkEpiloguePostPlaced_append_prefix A s0 sp' x19 ptr bs k hkl out sf Pf hqm)
end Placed
end CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
