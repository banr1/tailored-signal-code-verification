/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.VarintKey
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Post
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# `PreKeyRecord::deserialize` Field Merge Branches and Tag Dispatch

CPS proofs for tag 1 (`id : u32`), tag 2 (`public_key`), tag 3 (`private_key`), unknown-tag
`skip_field`, tag dispatch (`+0x0fc .. +0x110`), and relocatable error-cleanup helpers on
Block `65`.
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

/-! ## Cursor advance combinator and tag-dispatch arithmetic -/

theorem pkAdvanceCursor {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (sliceCursorAt (sp' + 40#64) (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (pkEpiloguePost img A s0 sp' x19
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest out)
      (tryFromQp s0)) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (sliceCursorAfter (sp' + 40#64) ptr bs rest ∗ R)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
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
    (fun sf Pf hqm => pkEpiloguePost_append_prefix img A s0 sp' x19 ptr bs k hkl out sf Pf hqm)

theorem pk_tag_ge4_conds (tag : ℕ) (hge : 4 ≤ tag) (hlt : tag < 2 ^ 32) :
    (((BitVec.ofNat 64 tag).setWidth 32 - 3#32 == 0#32) = false) ∧
    (((BitVec.ofNat 64 tag).setWidth 32 - 3#32 != 0#32) = true) ∧
    (((BitVec.ofNat 64 tag).setWidth 32 - 2#32 == 0#32) = false) ∧
    (((BitVec.ofNat 64 tag).setWidth 32 - 2#32 != 0#32) = true) ∧
    (((BitVec.ofNat 64 tag).setWidth 32 - 1#32 == 0#32) = false) ∧
    (((BitVec.ofNat 64 tag).setWidth 32 - 1#32 != 0#32) = true) := by
  have h3 : (BitVec.ofNat 64 tag).setWidth 32 - 3#32 ≠ 0#32 := by bv_omega
  have h2 : (BitVec.ofNat 64 tag).setWidth 32 - 2#32 ≠ 0#32 := by bv_omega
  have h1 : (BitVec.ofNat 64 tag).setWidth 32 - 1#32 ≠ 0#32 := by bv_omega
  exact ⟨beq_eq_false_iff_ne.mpr h3, bne_iff_ne.mpr h3,
    beq_eq_false_iff_ne.mpr h2, bne_iff_ne.mpr h2,
    beq_eq_false_iff_ne.mpr h1, bne_iff_ne.mpr h1⟩

/-! ## Field merge branches: tag 1 (`id`), tag 2 (`public_key`), tag 3 (`private_key`), unknown (`≥ 4`) -/

theorem mergeId_114_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x114#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x070#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length { m with id := v })
        (pkEpiloguePost img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  unfold pkLoopMem preKeyStructLoopOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
  rw [preKeyStructAt_split_id A g sp' m]
  simp only [sepConj_assoc]
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 104#64) m.id))))) ?_
  have hcall := int32Merge_ok_sub d
  have herr := @decodeErrorPush_2cc_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 276 24
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 648 36
  dsimp only [tripleRatchetProgAtExt] at hcall herr hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hregs.x20
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have hstack := stackAt_sub_split sp' int32MergeStackX (skipFieldStackX 100)
  simp only [hstack]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom ⟨wt, sp' + 104#64, sp' + 184#64, sp' + 40#64, ptr, bs⟩ hcall
    (by simp [arm64_norm])
    (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (292)) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 104#64) 4 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      sliceCursorAt (sp' + 40#64) ptr bs ∗ A.pool ∗ stackAt sp' int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 56#64 + 48#64 = sp' + 104#64 ∧
      sp' + 160#64 + 24#64 = sp' + 184#64 ∧ bs.length < 9223372036854775808)
    (by cases wt <;> simp [int32MergeSpecX, hsp_eq, WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved hregs hsp2 hcs2
  dsimp only [int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest⟩ := mergeUint32_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (112)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hcont v rest _ hm
        (by simp [arm64_norm])
        (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3
        (by simpa [arm64_norm] using htr2.trans htr))
    have hstruct : (((sp' + 104#64) ↦₃₂ v) ∗ memRegion (sp' + 108#64) 4) ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey) ⊢
        preKeyStructLoopOf A (sp' + 56#64) rest.length { m with id := v } := by
      refine Entails.trans ?_
        (preKeyStructAt_entails_loopOf A g (sp' + 56#64) rest.length { m with id := v }
          (hg.mono hrest_le))
      rw [preKeyStructAt_split_id A g sp' { m with id := v }]
      exact Entails.refl _
    unfold pkAfterVarintMem
    have hsp2_eq : s2.sp = sp' := hregs2.sp
    simp only [hstack, hsp_eq, arm64_norm]
    simp only [sepConj_assoc] at hstruct
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hstruct))))
    apply entails_of_eq; ac_rfl
  | none =>
    dsimp only
    have hout := hnone hm
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
    have hsp2_eq : s2.sp = sp' := hregs2.sp
    rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64),
      ProofLib.memRegion_four (sp' + 104#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => Wire.SepWPp.exists_pre fun vErr => ?_
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (716)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := { m with id := vErr }) hout
        (by simp [arm64_norm])
        (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3
        (by simpa [arm64_norm] using htr2.trans htr)
        (by simp [arm64_norm])
        hx0_ne (by decide))
    have hstruct : (((sp' + 104#64) ↦₃₂ vErr) ∗ memRegion (sp' + 108#64) 4) ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey) ⊢
        preKeyStructOf A (sp' + 56#64) { m with id := vErr } := by
      refine Entails.trans ?_ (preKeyStructAt_entails_of A g (sp' + 56#64) { m with id := vErr })
      rw [preKeyStructAt_split_id A g sp' { m with id := vErr }]
      exact Entails.refl _
    simp only [hstack, hsp_eq, arm64_norm]
    simp only [sepConj_assoc] at hstruct
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hstruct)))))))
    apply entails_of_eq; ac_rfl

theorem mergePublicKey_05c_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x05c#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x070#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length { m with publicKey := v })
        (pkEpiloguePost img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  unfold pkLoopMem preKeyStructLoopOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
  rw [preKeyStructAt_split_pub A g sp' m]
  have hcall := bytesMerge_ok_sub d
  have herr := @decodeErrorPush_2cc_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 92 20
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 684 32
  dsimp only [tripleRatchetProgAtExt] at hcall herr hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom
    ⟨wt, sp' + 56#64, g.pub.cap, g.pub.ptr, m.publicKey, sp' + 184#64, sp' + 40#64, ptr, bs⟩ hcall
    (by simp [arm64_norm])
    (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (108)) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      sliceCursorAt (sp' + 40#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 56#64 = sp' + 56#64 ∧
      sp' + 160#64 + 24#64 = sp' + 184#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk g.pub.cap bs.length)
    (by cases wt <;> simp [bytesMergeRawSpecX, hsp_eq, WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, by bv_omega, hlen, hg.pub⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved hregs hsp2 hcs2
  have hsp2_eq : s2.sp = sp' := hregs2.sp
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => Wire.SepWPp.pure_pre fun hcap' => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (112)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hcont v rest _ hm
        (by simp [arm64_norm])
        (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3
        (by simpa [arm64_norm] using htr2.trans htr))
    have hstruct : vecU8At A (sp' + 56#64) cap' ptr' v ∗
        (vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructLoopOf A (sp' + 56#64) rest.length { m with publicKey := v } := by
      refine Entails.trans ?_
        (preKeyStructAt_entails_loopOf A { g with pub := ⟨cap', ptr'⟩ } (sp' + 56#64) rest.length
          { m with publicKey := v } ⟨hcap', bytesMergeCapOk_mono hg.priv hrest_le⟩)
      rw [preKeyStructAt_split_pub A { g with pub := ⟨cap', ptr'⟩ } sp' { m with publicKey := v }]
      exact Entails.refl _
    unfold pkAfterVarintMem
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hstruct))))
    apply entails_of_eq; ac_rfl
  | none =>
    dsimp only
    have hout := hnone hm
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
    rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => ?_
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (716)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := m) hout
        (by simp [arm64_norm])
        (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3
        (by simpa [arm64_norm] using htr2.trans htr)
        (by simp [arm64_norm])
        hx0_ne (by decide))
    have hstruct : vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
        (vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructOf A (sp' + 56#64) m := by
      rw [← preKeyStructAt_split_pub A g sp' m]
      exact preKeyStructAt_entails_of A g (sp' + 56#64) m
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hstruct)))))))
    apply entails_of_eq; ac_rfl

theorem mergePrivateKey_12c_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x12c#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x070#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length { m with privateKey := v })
        (pkEpiloguePost img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  unfold pkLoopMem preKeyStructLoopOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
  rw [preKeyStructAt_split_priv A g sp' m]
  have hcall := bytesMerge_ok_sub d
  have herr := @decodeErrorPush_2cc_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 300 24
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 612 36
  dsimp only [tripleRatchetProgAtExt] at hcall herr hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hregs.x20
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom
    ⟨wt, sp' + 80#64, g.priv.cap, g.priv.ptr, m.privateKey, sp' + 184#64, sp' + 40#64, ptr, bs⟩ hcall
    (by simp [arm64_norm])
    (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (316)) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      sliceCursorAt (sp' + 40#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 56#64 + 24#64 = sp' + 80#64 ∧
      sp' + 160#64 + 24#64 = sp' + 184#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk g.priv.cap bs.length)
    (by cases wt <;> simp [bytesMergeRawSpecX, hsp_eq, WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen, hg.priv⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved hregs hsp2 hcs2
  have hsp2_eq : s2.sp = sp' := hregs2.sp
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => Wire.SepWPp.pure_pre fun hcap' => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (112)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hcont v rest _ hm
        (by simp [arm64_norm])
        (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3
        (by simpa [arm64_norm] using htr2.trans htr))
    have hstruct : vecU8At A (sp' + 80#64) cap' ptr' v ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructLoopOf A (sp' + 56#64) rest.length { m with privateKey := v } := by
      refine Entails.trans ?_
        (preKeyStructAt_entails_loopOf A { g with priv := ⟨cap', ptr'⟩ } (sp' + 56#64) rest.length
          { m with privateKey := v } ⟨bytesMergeCapOk_mono hg.pub hrest_le, hcap'⟩)
      rw [preKeyStructAt_split_priv A { g with priv := ⟨cap', ptr'⟩ } sp' { m with privateKey := v }]
      exact Entails.refl _
    unfold pkAfterVarintMem
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hstruct))))
    apply entails_of_eq; ac_rfl
  | none =>
    dsimp only
    have hout := hnone hm
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
    rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => ?_
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (716)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := m) hout
        (by simp [arm64_norm])
        (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3
        (by simpa [arm64_norm] using htr2.trans htr)
        (by simp [arm64_norm])
        hx0_ne (by decide))
    have hstruct : vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructOf A (sp' + 56#64) m := by
      rw [← preKeyStructAt_split_priv A g sp' m]
      exact preKeyStructAt_entails_of A g (sp' + 56#64) m
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hstruct)))))))
    apply entails_of_eq; ac_rfl

theorem mergeSkipField_144_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x144#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (rest : List (BitVec 8)) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x070#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length m)
        (pkEpiloguePost img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  unfold pkLoopMem
  have hcall := skipField_ok_sub d
  have hpost := @post_err_1d0_wp img A ext hC d s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 324 24
  dsimp only [tripleRatchetProgAtExt] at hcall hpost hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  refine Wire.SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]") -
      ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize")) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.call_tryFrom ⟨wt, tag, 100, sp' + 184#64, sp' + 40#64, ptr, bs⟩ hcall
    (by simp [arm64_norm])
    (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (340)) (by simp [arm64_norm])
    (by simpa [arm64_norm] using htr)
    (T := ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ sliceCursorAt (sp' + 40#64) ptr bs ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 4294967296 ∧
      sp' + 160#64 + 24#64 = sp' + 184#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 4294967296 ∧ bs.length < 9223372036854775808)
    (by cases wt <;> simp [skipFieldSpecX, hsp_eq, h1, WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, by bv_omega, rfl, by decide, hlen⟩
    (by sep_focus)
    ?_
  clear hcall
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved hregs hsp2 hcs2
  have hsp2_eq : s2.sp = sp' := hregs2.sp
  dsimp only [skipFieldSpecX]
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only
    obtain ⟨k, hkl, hrest⟩ := skipField_suffix hs
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (112)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hcont rest _ hs
        (by simp [arm64_norm])
        (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3
        (by simpa [arm64_norm] using htr2.trans htr))
    unfold pkAfterVarintMem
    simp only [hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (preKeyStructLoopOf_mono A (sp' + 56#64) m hrest_le)))))
    apply entails_of_eq; ac_rfl
  | none =>
    dsimp only
    have hout := hnone hs
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    refine Wire.SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (464)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    refine Wire.SepWPp.mono_pre ?_
      (hpost (err := s2.readReg64 (Reg.gpr 0#5)) (mErr := m) hout
        ⟨by simp [hsp2_eq, arm64_norm],
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hF3, hsym3, by simp [htr2, htr, arm64_norm],
         ⟨by simpa [arm64_norm] using hregs2.saved.x24,
          by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26,
          by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp [arm64_norm])
        (by simp [hrun2, arm64_norm])
        (by simp [arm64_norm])
        (by simpa [arm64_norm] using hregs2.x19_eq)
        (by simpa [speWord, arm64_norm] using hregs2.x22))
    simp only [hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (pkErrMem_of_loopOf A sp' x19 ptr (s2.readReg64 (Reg.gpr 0#5)) 0 bs.length m bs)
    apply entails_of_eq; ac_rfl

/-! ## Tag dispatch `+0x0fc..+0x110` and unified `mergeField_0fc_cps` -/

theorem dispatch_tag_0fc_cps {img : Obj.Image}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 : BitVec 64} {tag : ℕ}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0fc#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x114#64 →
      s1.status = .Running → PkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1 P Q Qp)
    (h2 : tag = 2 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x05c#64 →
      s1.status = .Running → PkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1 P Q Qp)
    (h3 : tag = 3 → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x12c#64 →
      s1.status = .Running → PkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1 P Q Qp)
    (h4 : 4 ≤ tag → ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x144#64 →
      s1.status = .Running → PkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1 P Q Qp) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s P Q Qp := by
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 252 24
  dsimp only [tripleRatchetProgAtExt] at h1 h2 h3 h4 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  rcases tag with _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (276)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h1 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (92)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h2 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (300)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h3 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 4) := hx1
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := pk_tag_ge4_conds (n + 4) (by omega) htag_lt
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (324)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact h4 (by omega) _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simpa [arm64_norm] using hx1')
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr

theorem mergeField_0fc_cps {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x0fc#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (m' : PreKeyRecordStructure) (rest : List (BitVec 8)) (s1 : State),
      PreKeyRecordStructure.mergeField m tag wt bs = some (m', rest) →
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x070#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length m')
        (pkEpiloguePost img A s0 sp' x19 ptr bs out)
        (tryFromQp s0))
    (hnone : PreKeyRecordStructure.mergeField m tag wt bs = none →
      out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePost img A s0 sp' x19 ptr bs out)
      (tryFromQp s0) := by
  refine dispatch_tag_0fc_cps hpc hrun hregs hx1 htag_ge htag_lt hsp hF hsym htr
    (fun htag s1 hpc1 hrun1 hregs1 hx8_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx8_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx8_1 hsp1 hF1 hsym1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx8_1 hx1_1 hsp1 hF1 hsym1 htr1 => ?_)
  · subst htag
    exact mergeId_114_cps hC d hpc1 hrun1 hregs1 (hx8_1.trans hx8) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with id := v } rest s2
        (by simp [PreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [PreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact mergePublicKey_05c_cps hC d hpc1 hrun1 hregs1 (hx8_1.trans hx8) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with publicKey := v } rest s2
        (by simp [PreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [PreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact mergePrivateKey_12c_cps hC d hpc1 hrun1 hregs1 (hx8_1.trans hx8) hsp1 hF1 hsym1 htr1 hlen
      (fun v rest s2 hm => hcont { m with privateKey := v } rest s2
        (by simp [PreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [PreKeyRecordStructure.mergeField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact mergeSkipField_144_cps hC d hpc1 hrun1 hregs1 (hx8_1.trans hx8) hx1_1 htag_lt
      hsp1 hF1 hsym1 htr1 hlen
      (fun rest s2 hs => hcont m rest s2
        (by simp [PreKeyRecordStructure.mergeField, skipUnknown, recursionLimit, hs]))
      (fun hs => hnone
        (by simp [PreKeyRecordStructure.mergeField, skipUnknown, recursionLimit, hs]))

/-! ## Relocatable `[LibsignalPlacement]` Error-Cleanup & `DecodeError` Helpers (Block `65`) -/

section Placed
open CryptoVerification.RecordCodecs.Placed

theorem cleanup_err_210_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {bs : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (528)) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err) (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ memRegion (sp' + 56#64) 56 ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  have hstack := stackAt_sub_split sp' dropDecodeErrorStackX (skipFieldStackX 100)
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pkMemRegion56_err_unpack x19)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun w0 => Wire.SepWPp.exists_pre fun w1 =>
    Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w3 =>
    Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
    Wire.SepWPp.exists_pre fun r5 => Wire.SepWPp.exists_pre fun r6 => ?_
  have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 4) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_noPanic_lscro err (pk_dropDecodeError_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (532)) (by simpa [arm64_norm] using htr)
    (T := decodeErrorAt A err ∗ A.pool ∗ stackAt sp' dropDecodeErrorStackX)
    (φ := err = err) (by simp [dropDecodeErrorSpecX, hsp_eq, h0, arm64_norm]) rfl
    (by rw [hstack]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  dsimp only [dropDecodeErrorSpecX]; rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
  have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x19 := by simpa [hx19, arm64_norm] using hcs2.1
  have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = speWord 2 := by simpa [hx22, arm64_norm] using hcs2.2.2.2.1
  have hsaved2 : PkSavedRegs s0 s2 :=
    ⟨by simpa [hsaved.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
     by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
     by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
     by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
     by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
  refine sepWPp_of_sepWP_end_lscro hcrl2 ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
  refine ⟨⟨by simp [hsp2_eq, arm64_norm],
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hcrl3, by simp [htr2, htr, arm64_norm],
    ⟨by simpa [arm64_norm] using hsaved2.x24, by simpa [arm64_norm] using hsaved2.x25,
     by simpa [arm64_norm] using hsaved2.x26, by simpa [arm64_norm] using hsaved2.x27,
     by simpa [arm64_norm] using hsaved2.x28⟩⟩, ?_⟩
  simp only [arm64_norm]; unfold pkEpilogueMem
  refine Entails.trans ?_
    (sepConj_mono (pkMemRegion160_pack sp') (sepConj_mono_right (sepConj_mono_left (pkSpeInvalidProto56_intro A x19 r0 r1 herr))))
  refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left (pkMemRegion40_pack sp' r0 r1 r5 r6)))
  apply entails_of_eq; rw [hstack, hsp_eq]; dsimp only [errTag, skipFieldStackX, dropDecodeErrorStackX, extHookStack]; ac_rfl

theorem cleanup_priv_1f4_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr err privCap privPtr : BitVec 64}
    {privBs bs : List (BitVec 8)} {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (500)) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err) (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2)
    (hx20 : s.readReg64 .x20 = privCap) (hx21 : s.readReg64 .x21 = privPtr) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (vecU8Buf A privCap privPtr privBs ∗ memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  by_cases hcap : privCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_zero_elim A privPtr privBs)) ?_
    rw [emp_sepConj]; have h20 : s.readReg64 (Reg.gpr 20#5) = 0#64 := hx20
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (528)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    exact cleanup_err_210_placed_wp d (err := err) herr
      ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hcrl1, by simp [htr, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27,
        by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm]) (by simp [hx22, arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A privCap privPtr privBs hcap)) ?_
    simp only [sepConj_assoc]; refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
    have h20 : s.readReg64 (Reg.gpr 20#5) = privCap := hx20
    have h21 : s.readReg64 (Reg.gpr 21#5) = privPtr := hx21
    have hbeq : (privCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (privPtr, privCap.toNat, 1) (pk_dealloc_placed_ok d)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (524)) (by simpa [arm64_norm] using htr)
      (T := A.pool ∗ A.live privPtr privCap.toNat 1 ∗ memRegion privPtr privCap.toNat ∗ stackAt sp' extHookStack)
      (φ := privPtr = privPtr ∧ privCap.toNat = privCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk privCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, hsp_eq, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩ (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hx19, arm64_norm] using hcs2.1
    have hx22_2 : s2.readReg64 .x22 = speWord 2 := by simpa [hx22, arm64_norm] using hcs2.2.2.2.1
    have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = err := by simpa [h0, arm64_norm] using hcs2.2.2.2.2.1
    have hsaved2 : PkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (528)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (cleanup_err_210_placed_wp d (err := err) herr
        ⟨by simp [hsp2_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hcrl3, by simp [htr2, htr, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved2.x24, by simpa [arm64_norm] using hsaved2.x25,
          by simpa [arm64_norm] using hsaved2.x26, by simpa [arm64_norm] using hsaved2.x27,
          by simpa [arm64_norm] using hsaved2.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [arm64_norm]) (by simp [hx19_2, arm64_norm]) (by simp [hx22_2, arm64_norm]))
    simp only [hsp_eq, arm64_norm]; apply entails_of_eq; rw [hstack]; ac_rfl

theorem post_err_1d0_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr err : BitVec 64}
    {mErr : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord}
    (herr : out = .error .invalidProtobufEncoding) (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (464)) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = err) (hx19 : s.readReg64 .x19 = x19)
    (hx22 : s.readReg64 .x22 = speWord 2) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (preKeyStructOf A (sp' + 56#64) mErr ∗ memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        decodeErrorAt A err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  unfold preKeyStructOf; simp only [sepExists_sepConj_left]
  refine Wire.SepWPp.exists_pre fun ⟨⟨pubCap, pubPtr⟩, ⟨privCap, privPtr⟩⟩ => ?_
  rw [preKeyStructAt_split_pub A ⟨⟨pubCap, pubPtr⟩, ⟨privCap, privPtr⟩⟩ sp' mErr,
    vecU8At_eq_header_buf A (sp' + 56#64) pubCap pubPtr mErr.publicKey,
    vecU8At_eq_header_buf A (sp' + 80#64) privCap privPtr mErr.privateKey]; simp only [sepConj_assoc]
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun pad32 => ?_
  have h56_pack := pkStruct56_pack sp' pubCap pubPtr (BitVec.ofNat 64 mErr.publicKey.length)
    privCap privPtr (BitVec.ofNat 64 mErr.privateKey.length) mErr.id pad32
  by_cases hcap : pubCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_left (vecU8Buf_zero_elim A pubPtr mErr.publicKey))) ?_
    simp only [emp_sepConj]
    refine Wire.SepWPp.mono_pre
      (P' := ((sp' + 56#64) ↦₆₄ 0#64) ∗ ((sp' + 64#64) ↦₆₄ pubPtr) ∗
        ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 mErr.publicKey.length) ∗
        ((sp' + 80#64) ↦₆₄ privCap) ∗ ((sp' + 88#64) ↦₆₄ privPtr) ∗
        ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 mErr.privateKey.length) ∗
        vecU8Buf A privCap privPtr mErr.privateKey ∗ ((sp' + 104#64) ↦₃₂ mErr.id) ∗ ((sp' + 108#64) ↦₃₂ pad32) ∗
        memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ decodeErrorAt A err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (by dsimp only [vecHeader]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _) ?_
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (500)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (cleanup_priv_1f4_placed_wp d (err := err) (privCap := privCap) (privPtr := privPtr) (privBs := mErr.privateKey) herr
        ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hcrl1, by simp [htr, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
          by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27,
          by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm]) (by simp [hx22, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]))
    dsimp only [vecHeader] at h56_pack; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h56_pack
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56_pack))))
    apply entails_of_eq; ac_rfl
  · refine Wire.SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_left (vecU8Buf_dealloc A pubCap pubPtr mErr.publicKey hcap))) ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have hbeq : (pubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have h0 : s.readReg64 (Reg.gpr 0#5) = err := hx0
    refine Wire.SepWPp.mono_pre
      (P' := ((sp' + 56#64) ↦₆₄ pubCap) ∗ ((sp' + 64#64) ↦₆₄ pubPtr) ∗
        ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 mErr.publicKey.length) ∗
        A.live pubPtr pubCap.toNat 1 ∗ memRegion pubPtr pubCap.toNat ∗
        ((sp' + 80#64) ↦₆₄ privCap) ∗ ((sp' + 88#64) ↦₆₄ privPtr) ∗
        ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 mErr.privateKey.length) ∗
        vecU8Buf A privCap privPtr mErr.privateKey ∗ ((sp' + 104#64) ↦₃₂ mErr.id) ∗ ((sp' + 108#64) ↦₃₂ pad32) ∗
        memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ decodeErrorAt A err ∗ memRegion x19 56 ∗
        (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (by dsimp only [vecHeader]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _) ?_
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine sepWPp_call_noPanic_lscro (pubPtr, pubCap.toNat, 1) (pk_dealloc_placed_ok d)
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (496)) (by simpa [arm64_norm] using htr)
      (T := A.pool ∗ A.live pubPtr pubCap.toNat 1 ∗ memRegion pubPtr pubCap.toNat ∗ stackAt sp' extHookStack)
      (φ := pubPtr = pubPtr ∧ pubCap.toNat = pubCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk pubCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, hsp_eq, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩ (by rw [hstack]; sep_focus) ?_
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = sp' := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x19 := by simpa [hx19, arm64_norm] using hcs2.1
    have hx20_2 : s2.readReg64 .x20 = privCap := by simpa [hsp_eq, arm64_norm] using hcs2.2.1
    have hx21_2 : s2.readReg64 .x21 = privPtr := by simpa [hsp_eq, arm64_norm] using hcs2.2.2.1
    have hx22_2 : s2.readReg64 .x22 = speWord 2 := by simpa [hx22, arm64_norm] using hcs2.2.2.2.1
    have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = err := by simpa [h0, arm64_norm] using hcs2.2.2.2.2.1
    have hsaved2 : PkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x24, arm64_norm] using hcs2.2.2.2.2.2.1,
       by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (500)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (cleanup_priv_1f4_placed_wp d (err := err) (privCap := privCap) (privPtr := privPtr) (privBs := mErr.privateKey) herr
        ⟨by simp [hsp2_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hcrl3, by simp [htr2, htr, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved2.x24, by simpa [arm64_norm] using hsaved2.x25,
          by simpa [arm64_norm] using hsaved2.x26, by simpa [arm64_norm] using hsaved2.x27,
          by simpa [arm64_norm] using hsaved2.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        (by simp [arm64_norm]) (by simp [hx19_2, arm64_norm]) (by simp [hx22_2, arm64_norm])
        (by simp [hx20_2, arm64_norm]) (by simp [hx21_2, arm64_norm]))
    rw [hstack]; simp only [hsp_eq, arm64_norm]
    dsimp only [vecHeader] at h56_pack; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h56_pack
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56_pack))))
    apply entails_of_eq; ac_rfl

end Placed
end CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
