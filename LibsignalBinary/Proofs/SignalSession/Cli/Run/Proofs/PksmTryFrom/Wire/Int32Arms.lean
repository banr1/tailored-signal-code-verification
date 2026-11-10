/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArms
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

/-!
# `PreKeySignalMessage::try_from`: `int32::merge` Field Arms

Symbolic execution of the four `prost::encoding::int32::merge` field arms (`pre_key_id`,
`registration_id`, `signed_pre_key_id`, `kyber_pre_key_id`) and their unified CPS wrapper
`int32ArmPK_cps`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_104 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 104) = sp' + 408#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_100 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 100) = sp' + 412#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_96 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 96) = sp' + 416#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_92 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 92) = sp' + 420#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_88 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 88) = sp' + 424#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_84 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 84) = sp' + 428#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_80 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 80) = sp' + 432#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_76 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 76) = sp' + 436#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_72 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 72) = sp' + 440#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_64 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 64) = sp' + 448#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ia_bv_add_neg_56 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 56) = sp' + 456#64 := by bv_omega

theorem L1_IS5Wire_Int32Arms : True := trivial

/-! ## 1. Shared Callee, Decomposition & Error-Tail Helpers -/

theorem int32Merge_ok_subPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Prost.Int32MergeOkExtX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")))
      ((Prost.int32MergeSpecX A).inImage img) := by
  have heq : (contractProg img.base ext).fnAddr preKeyTryFromName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) =
      (contractProg img.base ext).fnAddr int32MergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"),
      (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact h

def wirePreKeyVecsOf (A : RustAlloc) (a : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  ∃∗ g : WirePreKeyGhost,
    optVecU8At A g.kyberCt a m.kyberCiphertext ∗
    optVecU8At A g.baseKey (a + 0x18#64) m.baseKey ∗
    optVecU8At A g.identityKey (a + 0x30#64) m.identityKey ∗
    optVecU8At A g.message (a + 0x48#64) m.message

theorem wirePreKeyOf_eq_vecs_u32s (A : RustAlloc) (a : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A a m =
      wirePreKeyVecsOf A a m ∗ optU32At (a + 0x60#64) m.registrationId ∗
      optU32At (a + 0x68#64) m.preKeyId ∗ optU32At (a + 0x70#64) m.signedPreKeyId ∗
      optU32At (a + 0x78#64) m.kyberPreKeyId := by
  unfold wirePreKeyOf wirePreKeyAt wirePreKeyVecsOf
  simp only [sepExists_sepConj_left, sepConj_assoc]

def wirePreKeyRest1 (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsOf A (sp' + 312#64) m ∗ optU32At (sp' + 408#64) m.registrationId ∗
  optU32At (sp' + 424#64) m.signedPreKeyId ∗ optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyOf_eq_preKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A (sp' + 312#64) m =
      optU32At (sp' + 416#64) m.preKeyId ∗ wirePreKeyRest1 A sp' m := by
  rw [wirePreKeyOf_eq_vecs_u32s]; unfold wirePreKeyRest1
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyOf_update_preKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage)
    (o : Option (BitVec 32)) :
    optU32At (sp' + 416#64) o ∗ wirePreKeyRest1 A sp' m =
      wirePreKeyOf A (sp' + 312#64) { m with preKeyId := o } := by
  rw [wirePreKeyOf_eq_preKeyId A sp' { m with preKeyId := o }]; rfl

/-! ## 2. Tag 1 (`pre_key_id`, `+0x260..+0x27c` / `+0x3f0..+0x410`, `off = 0x68`) -/

set_option maxHeartbeats 800000 in
/-- `Option<u32>` flag init for `pre_key_id` (tag 1) at `+0x260..+0x268` → `+0x26c`.-/
theorem initOptU32_preKeyId_cpsX {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {o : Option (BitVec 32)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x260#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (v0 : BitVec 32) (s1 : State),
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x26c#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (optU32At (sp' + 416#64) (some v0) ∗ F) Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (optU32At (sp' + 416#64) o ∗ F) Q Qp := by
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 608 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 608#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases o with
  | some v =>
    unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (620)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr))
    unfold optU32At; simp only [arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    have ha : sp' + 416#64 + 4#64 = sp' + 420#64 := by bv_omega
    unfold optU32At; rw [ha, sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (616)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 416#64) 0#32
    rw [ha] at hent1
    refine SepWPp.mono_pre (by rw [← sepConj_assoc]; exact sepConj_mono_left hent1) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w => SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + bv% (620)) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF2 hsym2 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont 0#32 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF2 hsym2 (by simpa [arm64_norm] using htr))
    have hsplit1 : ((sp' + 416#64) ↦₆₄ 1#64) = ((sp' + 416#64) ↦₃₂ 1#32) ∗ ((sp' + 420#64) ↦₃₂ 0#32) := by
      have hs := pointsTo64_one_split32 (sp' + 416#64)
      rw [ha] at hs; exact hs
    unfold optU32At; simp only [hsplit1, arm64_norm]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
/-- Tag 1 (`pre_key_id`) merge arm `+0x260..+0x27c` / `+0x3f0..+0x410` → `+0x0e4` (Ok) or `+0x460` (Err).-/
theorem mergePreKeyId_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext) (hint32 : Prost.Int32MergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x260#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with preKeyId := some v })
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  rw [wirePreKeyOf_eq_preKeyId A sp' m]
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 416#64) m.preKeyId ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyRest1 A sp' m)) (by apply entails_of_eq; ac_rfl) ?_
  refine initOptU32_preKeyId_cpsX (s0 := s0) hpc hrun hregs hsp hF hsym htr ?_
  intro v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1
  have hx0' : s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hcall := int32Merge_ok_subPK hint32; have hpush := @decodeErrorPushPK_tail_wpX img A ext hPush s0
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 620 20
  preKeyTryFrom_fetches img.base H 1008 36
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hpush hcont hpc1 ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 620#64 at hpc1
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq : s1.sp = sp' := hregs1.sp; have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23; have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0'
  have hstack := stackAt_sub_split sp' Prost.int32MergeStackX (Prost.skipFieldStackX 100)
  unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, hstack, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 420#64) v0))) ?_
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) (fun hF2 hsym2 => ?_)
  refine SepWPp.call_tryFromX
    ⟨wt, sp' + 420#64, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hF2 hsym2
    (ret_pc := entry + bv% (632)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 420#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 420#64 = sp' + 420#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 9223372036854775808)
    (by dsimp only [Prost.int32MergeSpecX]; simp only [hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs1.x27,
       by simpa [arm64_norm] using hregs1.x25, by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [Prost.int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_2 => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (228)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1))
    rw [← wirePreKeyOf_update_preKeyId A sp' m (some v)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    dsimp only; rw [hnone hm, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64), ProofLib.memRegion_four (sp' + 420#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr => SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (1112)) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hpush (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := { m with preKeyId := some vErr })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm]) hx0_ne (by decide))
    rw [← wirePreKeyOf_update_preKeyId A sp' m (some vErr)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-! ## 3. Tag 5 (`registration_id`, `+0x280..+0x29c` / `+0x414..+0x434`, `off = 0x60`) -/

def wirePreKeyRest5 (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsOf A (sp' + 312#64) m ∗ optU32At (sp' + 416#64) m.preKeyId ∗
  optU32At (sp' + 424#64) m.signedPreKeyId ∗ optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyOf_eq_regId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A (sp' + 312#64) m =
      optU32At (sp' + 408#64) m.registrationId ∗ wirePreKeyRest5 A sp' m := by
  rw [wirePreKeyOf_eq_vecs_u32s]; unfold wirePreKeyRest5
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyOf_update_regId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage)
    (o : Option (BitVec 32)) :
    optU32At (sp' + 408#64) o ∗ wirePreKeyRest5 A sp' m =
      wirePreKeyOf A (sp' + 312#64) { m with registrationId := o } := by
  rw [wirePreKeyOf_eq_regId A sp' { m with registrationId := o }]; rfl

set_option maxHeartbeats 800000 in
/-- `Option<u32>` flag init for `registration_id` (tag 5) at `+0x280..+0x288` → `+0x28c`.-/
theorem initOptU32_regId_cpsX {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {o : Option (BitVec 32)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x280#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (v0 : BitVec 32) (s1 : State),
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x28c#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (optU32At (sp' + 408#64) (some v0) ∗ F) Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (optU32At (sp' + 408#64) o ∗ F) Q Qp := by
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 640 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 640#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases o with
  | some v =>
    unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (652)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr))
    unfold optU32At; simp only [arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    have ha : sp' + 408#64 + 4#64 = sp' + 412#64 := by bv_omega
    unfold optU32At; rw [ha, sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (648)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 408#64) 0#32
    rw [ha] at hent1
    refine SepWPp.mono_pre (by rw [← sepConj_assoc]; exact sepConj_mono_left hent1) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w => SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + bv% (652)) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF2 hsym2 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont 0#32 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF2 hsym2 (by simpa [arm64_norm] using htr))
    have hsplit1 : ((sp' + 408#64) ↦₆₄ 1#64) = ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ 0#32) := by
      have hs := pointsTo64_one_split32 (sp' + 408#64)
      rw [ha] at hs; exact hs
    unfold optU32At; simp only [hsplit1, arm64_norm]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
/-- Tag 5 (`registration_id`) merge arm `+0x280..+0x29c` / `+0x414..+0x434` → `+0x0e4` (Ok) or `+0x460` (Err).-/
theorem mergeRegId_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext) (hint32 : Prost.Int32MergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x280#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with registrationId := some v })
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  rw [wirePreKeyOf_eq_regId A sp' m]
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 408#64) m.registrationId ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyRest5 A sp' m)) (by apply entails_of_eq; ac_rfl) ?_
  refine initOptU32_regId_cpsX (s0 := s0) hpc hrun hregs hsp hF hsym htr ?_
  intro v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1
  have hx0' : s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hcall := int32Merge_ok_subPK hint32; have hpush := @decodeErrorPushPK_tail_wpX img A ext hPush s0
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 652 20
  preKeyTryFrom_fetches img.base H 1044 36
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hpush hcont hpc1 ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 652#64 at hpc1
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq : s1.sp = sp' := hregs1.sp; have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23; have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0'
  have hstack := stackAt_sub_split sp' Prost.int32MergeStackX (Prost.skipFieldStackX 100)
  unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, hstack, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 412#64) v0))) ?_
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) (fun hF2 hsym2 => ?_)
  refine SepWPp.call_tryFromX
    ⟨wt, sp' + 412#64, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hF2 hsym2
    (ret_pc := entry + bv% (664)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 412#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 412#64 = sp' + 412#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 9223372036854775808)
    (by dsimp only [Prost.int32MergeSpecX]; simp only [hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs1.x27,
       by simpa [arm64_norm] using hregs1.x25, by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [Prost.int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_2 => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (228)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1))
    rw [← wirePreKeyOf_update_regId A sp' m (some v)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    dsimp only; rw [hnone hm, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64), ProofLib.memRegion_four (sp' + 412#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr => SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (1112)) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hpush (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := { m with registrationId := some vErr })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm]) hx0_ne (by decide))
    rw [← wirePreKeyOf_update_regId A sp' m (some vErr)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-! ## 4. Tag 6 (`signed_pre_key_id`, `+0x1d0..+0x1ec` / `+0x384..+0x3a4`, `off = 0x70`) -/

def wirePreKeyRest6 (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsOf A (sp' + 312#64) m ∗ optU32At (sp' + 408#64) m.registrationId ∗
  optU32At (sp' + 416#64) m.preKeyId ∗ optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyOf_eq_signedPreKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A (sp' + 312#64) m =
      optU32At (sp' + 424#64) m.signedPreKeyId ∗ wirePreKeyRest6 A sp' m := by
  rw [wirePreKeyOf_eq_vecs_u32s]; unfold wirePreKeyRest6
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyOf_update_signedPreKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage)
    (o : Option (BitVec 32)) :
    optU32At (sp' + 424#64) o ∗ wirePreKeyRest6 A sp' m =
      wirePreKeyOf A (sp' + 312#64) { m with signedPreKeyId := o } := by
  rw [wirePreKeyOf_eq_signedPreKeyId A sp' { m with signedPreKeyId := o }]; rfl

set_option maxHeartbeats 800000 in
/-- `Option<u32>` flag init for `signed_pre_key_id` (tag 6) at `+0x1d0..+0x1d8` → `+0x1dc`.-/
theorem initOptU32_signedPreKeyId_cpsX {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {o : Option (BitVec 32)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x1d0#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (v0 : BitVec 32) (s1 : State),
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x1dc#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (optU32At (sp' + 424#64) (some v0) ∗ F) Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (optU32At (sp' + 424#64) o ∗ F) Q Qp := by
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 464 12
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 464#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases o with
  | some v =>
    unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (476)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr))
    unfold optU32At; simp only [arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    have ha : sp' + 424#64 + 4#64 = sp' + 428#64 := by bv_omega
    unfold optU32At; rw [ha, sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (472)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 424#64) 0#32
    rw [ha] at hent1
    refine SepWPp.mono_pre (by rw [← sepConj_assoc]; exact sepConj_mono_left hent1) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w => SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + bv% (476)) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF2 hsym2 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont 0#32 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF2 hsym2 (by simpa [arm64_norm] using htr))
    have hsplit1 : ((sp' + 424#64) ↦₆₄ 1#64) = ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ 0#32) := by
      have hs := pointsTo64_one_split32 (sp' + 424#64)
      rw [ha] at hs; exact hs
    unfold optU32At; simp only [hsplit1, arm64_norm]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
/-- Tag 6 (`signed_pre_key_id`) merge arm `+0x1d0..+0x1ec` / `+0x384..+0x3a4` → `+0x0e4` (Ok) or `+0x460` (Err).-/
theorem mergeSignedPreKeyId_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext) (hint32 : Prost.Int32MergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x1d0#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with signedPreKeyId := some v })
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  rw [wirePreKeyOf_eq_signedPreKeyId A sp' m]
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 424#64) m.signedPreKeyId ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyRest6 A sp' m)) (by apply entails_of_eq; ac_rfl) ?_
  refine initOptU32_signedPreKeyId_cpsX (s0 := s0) hpc hrun hregs hsp hF hsym htr ?_
  intro v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1
  have hx0' : s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hcall := int32Merge_ok_subPK hint32; have hpush := @decodeErrorPushPK_tail_wpX img A ext hPush s0
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 476 20
  preKeyTryFrom_fetches img.base H 900 36
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hpush hcont hpc1 ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 476#64 at hpc1
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq : s1.sp = sp' := hregs1.sp; have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23; have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0'
  have hstack := stackAt_sub_split sp' Prost.int32MergeStackX (Prost.skipFieldStackX 100)
  unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, hstack, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 428#64) v0))) ?_
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) (fun hF2 hsym2 => ?_)
  refine SepWPp.call_tryFromX
    ⟨wt, sp' + 428#64, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hF2 hsym2
    (ret_pc := entry + bv% (488)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 428#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 428#64 = sp' + 428#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 9223372036854775808)
    (by dsimp only [Prost.int32MergeSpecX]; simp only [hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs1.x27,
       by simpa [arm64_norm] using hregs1.x25, by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [Prost.int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_2 => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (228)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1))
    rw [← wirePreKeyOf_update_signedPreKeyId A sp' m (some v)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    dsimp only; rw [hnone hm, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64), ProofLib.memRegion_four (sp' + 428#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr => SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (1112)) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hpush (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := { m with signedPreKeyId := some vErr })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm]) hx0_ne (by decide))
    rw [← wirePreKeyOf_update_signedPreKeyId A sp' m (some vErr)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-! ## 5. Tag 7 (`kyber_pre_key_id`, `+0x2c8..+0x2d4` / `+0x0d4..+0x0e0` / `+0x3cc..+0x3ec`, `off = 0x78`) -/

def wirePreKeyRest7 (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  wirePreKeyVecsOf A (sp' + 312#64) m ∗ optU32At (sp' + 408#64) m.registrationId ∗
  optU32At (sp' + 416#64) m.preKeyId ∗ optU32At (sp' + 424#64) m.signedPreKeyId

theorem wirePreKeyOf_eq_kyberPreKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A (sp' + 312#64) m =
      optU32At (sp' + 432#64) m.kyberPreKeyId ∗ wirePreKeyRest7 A sp' m := by
  rw [wirePreKeyOf_eq_vecs_u32s]; unfold wirePreKeyRest7
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem wirePreKeyOf_update_kyberPreKeyId (A : RustAlloc) (sp' : BitVec 64) (m : ProtoPreKeySignalMessage)
    (o : Option (BitVec 32)) :
    optU32At (sp' + 432#64) o ∗ wirePreKeyRest7 A sp' m =
      wirePreKeyOf A (sp' + 312#64) { m with kyberPreKeyId := o } := by
  rw [wirePreKeyOf_eq_kyberPreKeyId A sp' { m with kyberPreKeyId := o }]; rfl

set_option maxHeartbeats 800000 in
/-- `Option<u32>` flag init for `kyber_pre_key_id` (tag 7) at `+0x2c8..+0x2d4` → `+0x0d4`.-/
theorem initOptU32_kyberPreKeyId_cpsX {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {o : Option (BitVec 32)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2c8#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (v0 : BitVec 32) (s1 : State),
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0d4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (optU32At (sp' + 432#64) (some v0) ∗ F) Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (optU32At (sp' + 432#64) o ∗ F) Q Qp := by
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 712 16
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 712#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases o with
  | some v =>
    unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (212)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF1 hsym1 (by simpa [arm64_norm] using htr))
    unfold optU32At; simp only [arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    have ha : sp' + 432#64 + 4#64 = sp' + 436#64 := by bv_omega
    unfold optU32At; rw [ha, sepConj_assoc]
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (720)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    have hent1 := pointsTo32_memRegion4_entails_exists_pointsTo64 (sp' + 432#64) 0#32
    rw [ha] at hent1
    refine SepWPp.mono_pre (by rw [← sepConj_assoc]; exact sepConj_mono_left hent1) ?_
    rw [sepExists_sepConj_left]
    refine SepWPp.exists_pre (fun w => SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + bv% (212)) ?_)
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF2 hsym2 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont 0#32 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hF2 hsym2 (by simpa [arm64_norm] using htr))
    have hsplit1 : ((sp' + 432#64) ↦₆₄ 1#64) = ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ 0#32) := by
      have hs := pointsTo64_one_split32 (sp' + 432#64)
      rw [ha] at hs; exact hs
    unfold optU32At; simp only [hsplit1, arm64_norm]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
/-- Tag 7 (`kyber_pre_key_id`) merge arm `+0x2c8..+0x2d4` / `+0x0d4..+0x0e0` / `+0x3cc..+0x3ec` → `+0x0e4` (Ok) or `+0x460` (Err).-/
theorem mergeKyberPreKeyId_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext) (hint32 : Prost.Int32MergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2c8#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with kyberPreKeyId := some v })
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  rw [wirePreKeyOf_eq_kyberPreKeyId A sp' m]
  refine SepWPp.mono_pre
    (P' := optU32At (sp' + 432#64) m.kyberPreKeyId ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyRest7 A sp' m)) (by apply entails_of_eq; ac_rfl) ?_
  refine initOptU32_kyberPreKeyId_cpsX (s0 := s0) hpc hrun hregs hsp hF hsym htr ?_
  intro v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1
  have hx0' : s1.readReg64 .x0 = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hcall := int32Merge_ok_subPK hint32; have hpush := @decodeErrorPushPK_tail_wpX img A ext hPush s0
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 212 16
  preKeyTryFrom_fetches img.base H 972 36
  dsimp only [contractProg, tripleRatchetProgAtExt] at hcall hpush hcont hpc1 ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 212#64 at hpc1
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq : s1.sp = sp' := hregs1.sp; have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23; have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0'
  have hstack := stackAt_sub_split sp' Prost.int32MergeStackX (Prost.skipFieldStackX 100)
  unfold optU32At; simp only [BitVec.add_assoc, BitVec.reduceAdd, hstack, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 436#64) v0))) ?_
  refine SepWPp.of_sepWP_frozen hF1 hsym1 (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) (fun hF2 hsym2 => ?_)
  refine SepWPp.call_tryFromX
    ⟨wt, sp' + 436#64, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hF2 hsym2
    (ret_pc := entry + bv% (224)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr1)
    (T := memRegion (sp' + 436#64) 4 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 436#64 = sp' + 436#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 9223372036854775808)
    (by dsimp only [Prost.int32MergeSpecX]; simp only [hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs1.x27,
       by simpa [arm64_norm] using hregs1.x25, by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [Prost.int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩; dsimp only; rw [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_2 => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (228)) ?_
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1))
    rw [← wirePreKeyOf_update_kyberPreKeyId A sp' m (some v)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl
  | none =>
    dsimp only; rw [hnone hm, sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64), ProofLib.memRegion_four (sp' + 436#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.exists_pre (fun vErr => SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (1112)) ?_))
    wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hpush (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := { m with kyberPreKeyId := some vErr })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm]) hx0_ne (by decide))
    rw [← wirePreKeyOf_update_kyberPreKeyId A sp' m (some vErr)]
    unfold optU32At; simp only [hstack, hsp_eq, arm64_norm]; apply entails_of_eq; ac_rfl

/-- Descriptor for the 4 `int32` arms of `PreKeySignalMessage::try_from`. -/
inductive Int32FieldPK where
  | preKeyId | registrationId | signedPreKeyId | kyberPreKeyId

/-- Entry offset of each `int32` arm in `PreKeySignalMessage::try_from`. -/
def Int32FieldPK.entryOff : Int32FieldPK → BitVec 64
  | .preKeyId => 0x260#64 | .registrationId => 0x280#64
  | .signedPreKeyId => 0x1d0#64 | .kyberPreKeyId => 0x2c8#64

/-- Field update for each `int32` arm of `ProtoPreKeySignalMessage`. -/
def Int32FieldPK.set (f : Int32FieldPK) (m : ProtoPreKeySignalMessage) (v : BitVec 32) :
    ProtoPreKeySignalMessage :=
  match f with
  | .preKeyId => { m with preKeyId := some v }
  | .registrationId => { m with registrationId := some v }
  | .signedPreKeyId => { m with signedPreKeyId := some v }
  | .kyberPreKeyId => { m with kyberPreKeyId := some v }

/-- Unified `int32` arm CPS theorem parametrized over `f : Int32FieldPK`.-/
theorem int32ArmPK_cps (f : Int32FieldPK) {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext) (hint32 : Prost.Int32MergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + f.entryOff)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) (f.set m v))
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  cases f with
  | preKeyId => exact mergePreKeyId_cpsX hPush hint32 hpc hrun hregs hx0 hsp hF hsym htr hlen hcont hnone
  | registrationId => exact mergeRegId_cpsX hPush hint32 hpc hrun hregs hx0 hsp hF hsym htr hlen hcont hnone
  | signedPreKeyId => exact mergeSignedPreKeyId_cpsX hPush hint32 hpc hrun hregs hx0 hsp hF hsym htr hlen hcont hnone
  | kyberPreKeyId => exact mergeKyberPreKeyId_cpsX hPush hint32 hpc hrun hregs hx0 hsp hF hsym htr hlen hcont hnone

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
