/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyB
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 400000

/-!
# `PreKeySignalMessage::try_from`: `bytes::merge` Arms and `DecodeError::push` Tails

Symbolic execution of the four `prost::encoding::bytes::merge` field arms (`kyber_ciphertext`,
`base_key`, `identity_key`, `message`) and their `DecodeError::push` error tails
(`+0x340..+0x45c → +0x460`).
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

theorem L1_BytesArms : True := trivial

@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_216 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 216) = sp' + 296#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_200 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 200) = sp' + 312#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_176 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 176) = sp' + 336#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_152 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 152) = sp' + 360#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_128 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 128) = sp' + 384#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_72 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 72) = sp' + 440#64 := by bv_omega
@[local simp, local arm64_norm, local wp_norm]
private theorem ba_bv_add_neg_64 (sp' : BitVec 64) : sp' + 512#64 + bv% (2 ^ 64 - 64) = sp' + 448#64 := by bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Basic register / memory helpers -/

theorem wirePreKeyAt_entails_of (A : RustAlloc) (g : WirePreKeyGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g a m ⊢ wirePreKeyOf A a m := by
  unfold wirePreKeyOf; exact Entails.sepExists_intro (P := fun g => wirePreKeyAt A g a m) g

/-! ## Caller-relative `bytes::merge` & `DecodeError::push` wrappers and shared tail (`+0x458..+0x460`) -/

abbrev PksmDecodeErrorPushOk (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
    ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img)

theorem decodeErrorPush_ok_subPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : PksmDecodeErrorPushOk img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "<prost::error::DecodeError>::push" -
          ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img) := by
  have heq :
      (contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "<prost::error::DecodeError>::push" -
          ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") =
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"),
      (ls_lemma% fnOff "<prost::error::DecodeError>::push")]
    bv_omega
  rw [heq]; exact h

theorem bytesMerge_ok_subPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Prost.BytesMergeOkExtX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
          (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")))
      (Prost.bytesMergeSpecX A img) := by
  have heq : (contractProg img.base ext).fnAddr preKeyTryFromName +
      bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
        (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) =
      (contractProg img.base ext).fnAddr bytesMergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"),
      (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact h

set_option maxHeartbeats 800000 in
/-- Shared `DecodeError::push` tail at `+0x458..+0x45c` → `+0x460` on `contractProg img.base ext`.-/
theorem decodeErrorPushPK_tail_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {ptr err : BitVec 64} {n : Nat}
    {bs : List (BitVec 8)} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x458#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = sp' + 448#64)
    (herr : err ≠ 0#64)
    (hn : n < 2 ^ 32) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 448#64) ↦₆₄ err) ∗ memRegion (sp' + 456#64) 56 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        decodeErrorAtStackLen A err n ∗
        wirePreKeyOf A (sp' + 312#64) mErr)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs none)
      (tryFromQp s0) := by
  have hcall := decodeErrorPush_ok_subPK hPush
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 1112 8
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1112#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName +
      bv% (ls_off% "<prost::error::DecodeError>::push" - ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry; examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (Prost.skipFieldStackX 100); simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym
    (mid := entry + bv% (ls_off% "<prost::error::DecodeError>::push" - ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) ?_
  wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
  refine SepWPp.call_tryFromX (sp' + 448#64, err, n) hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (1116)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 448#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ n < 2 ^ 32)
    (by simp only [decodeErrorPushExternSpecWithStack, hsp_eq, hx0, arm64_norm])
    ⟨herr, hn⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  dsimp only [decodeErrorPushExternSpecWithStack]; rw [sepConj_assoc]
  refine SepWPp.pure_pre (fun htr2 => ?_)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre (fun err' => SepWPp.pure_pre (fun herr' => SepWPp.of_sepWP_end hF2 hsym2 ?_))
  wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF3 hsym3 => ?_)
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
    by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
    hF3, hsym3, by simpa [arm64_norm] using htr2.trans htr⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 448#64) err')) ?_
  refine Entails.trans ?_ (preKeyLoopExitMem_err_intro A sp' ptr bs err' herr' (n + 1) mErr)
  apply entails_of_eq; simp only [hstack, hsp_eq, memRegion64_split8_448 sp', arm64_norm]; ac_rfl

/-! ## `wirePreKeyAt` field-splitting helpers for the 4 `Vec<u8>` fields -/

def wirePreKeyU32s (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) : SepProp :=
  optU32At (sp' + 408#64) m.registrationId ∗
    optU32At (sp' + 416#64) m.preKeyId ∗
    optU32At (sp' + 424#64) m.signedPreKeyId ∗
    optU32At (sp' + 432#64) m.kyberPreKeyId

theorem wirePreKeyAt_split_kyberCt (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g (sp' + 312#64) m =
      optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
      (optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) := by
  unfold wirePreKeyAt wirePreKeyU32s; simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem vecU8At_kyberCt_entails_wirePreKeyOf (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoPreKeySignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 312#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyOf A (sp' + 312#64) { m with kyberCiphertext := some v0 } := by
  refine Entails.trans ?_ (wirePreKeyAt_entails_of A { g with kyberCt := ⟨cap0, ptr0⟩ } (sp' + 312#64) { m with kyberCiphertext := some v0 })
  rw [wirePreKeyAt_split_kyberCt A { g with kyberCt := ⟨cap0, ptr0⟩ } sp' { m with kyberCiphertext := some v0 }]
  exact Entails.refl _

theorem wirePreKeyAt_split_baseKey (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g (sp' + 312#64) m =
      optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) := by
  unfold wirePreKeyAt wirePreKeyU32s; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem vecU8At_baseKey_entails_wirePreKeyOf (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoPreKeySignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 336#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyOf A (sp' + 312#64) { m with baseKey := some v0 } := by
  refine Entails.trans ?_ (wirePreKeyAt_entails_of A { g with baseKey := ⟨cap0, ptr0⟩ } (sp' + 312#64) { m with baseKey := some v0 })
  rw [wirePreKeyAt_split_baseKey A { g with baseKey := ⟨cap0, ptr0⟩ } sp' { m with baseKey := some v0 }]
  exact Entails.refl _

theorem wirePreKeyAt_split_identityKey (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g (sp' + 312#64) m =
      optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) := by
  unfold wirePreKeyAt wirePreKeyU32s; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem vecU8At_identityKey_entails_wirePreKeyOf (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoPreKeySignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 360#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.message (sp' + 384#64) m.message ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyOf A (sp' + 312#64) { m with identityKey := some v0 } := by
  refine Entails.trans ?_ (wirePreKeyAt_entails_of A { g with identityKey := ⟨cap0, ptr0⟩ } (sp' + 312#64) { m with identityKey := some v0 })
  rw [wirePreKeyAt_split_identityKey A { g with identityKey := ⟨cap0, ptr0⟩ } sp' { m with identityKey := some v0 }]
  exact Entails.refl _

theorem wirePreKeyAt_split_message (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeyAt A g (sp' + 312#64) m =
      optVecU8At A g.message (sp' + 384#64) m.message ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       wirePreKeyU32s sp' m) := by
  unfold wirePreKeyAt wirePreKeyU32s; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

theorem vecU8At_message_entails_wirePreKeyOf (A : RustAlloc) (g : WirePreKeyGhost)
    (sp' cap0 ptr0 : BitVec 64) (m : ProtoPreKeySignalMessage) (v0 : List (BitVec 8)) :
    vecU8At A (sp' + 384#64) cap0 ptr0 v0 ∗
      (optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
       optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
       optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
       wirePreKeyU32s sp' m) ⊢
      wirePreKeyOf A (sp' + 312#64) { m with message := some v0 } := by
  refine Entails.trans ?_ (wirePreKeyAt_entails_of A { g with message := ⟨cap0, ptr0⟩ } (sp' + 312#64) { m with message := some v0 })
  rw [wirePreKeyAt_split_message A { g with message := ⟨cap0, ptr0⟩ } sp' { m with message := some v0 }]
  exact Entails.refl _

/-! ## Tag 8 (`kyber_ciphertext`, `+0x238..+0x25c` / `+0x36c..+0x380` → `+0x3e0..+0x3ec`, `off = 0x00`) -/

set_option maxHeartbeats 800000 in
/-- Initialize `m.kyberCiphertext` (`Option<Vec<u8>>` at `sp' + 312`) to `Some` at `+0x238..+0x24c`.-/
theorem initOptVecU8_kyberCt_cpsPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x238#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 vecPtr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x24c#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (vecU8At A (sp' + 312#64) cap0 vecPtr0 v0 ∗ F) Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (optVecU8At A pin (sp' + 312#64) u ∗ F) Q Qp := by
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 568 20
  dsimp only [contractProg] at hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 568#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry; examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 312#64 320#64 328#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 => SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (588)) ?_))
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 312#64 320#64 328#64]; apply entails_of_eq; ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 312#64) v0, sepConj_assoc]; refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (588)) ?_
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 312#64) v0 hp]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
/-- Tag 8 (`kyber_ciphertext`) merge arm `+0x238..+0x25c` and error stub `+0x36c..+0x380` → `+0x3e0..+0x3ec` → `+0x458`.-/
theorem mergeKyberCiphertext_cpsPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x238#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with kyberCiphertext := some v })
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  unfold wirePreKeyOf; simp only [sepExists_sepConj_right]; refine SepWPp.exists_pre (fun g => ?_)
  rw [wirePreKeyAt_split_kyberCt A g sp' m]
  let F_msg := optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
    optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
    optVecU8At A g.message (sp' + 384#64) m.message ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; ac_rfl) ?_
  refine initOptVecU8_kyberCt_cpsPK hpc hrun hregs hsp hF hsym htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1
  have hcall := bytesMerge_ok_subPK hbytes; have herr := @decodeErrorPushPK_tail_wpX img A ext hPush s0
  let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 588 20; preKeyTryFrom_fetches img.base H 876 24; preKeyTryFrom_fetches img.base H 992 16
  dsimp only [contractProg] at hcall herr hcont hpc1 ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 588#64 at hpc1
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName +
      bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
        (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry; examples_hide_fetches
  have hsp_eq : s1.sp = sp' := hregs1.sp; have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.bytesMergeStackX (Prost.skipFieldStackX 100); simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF1 hsym1
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) (fun hF2 hsym2 => ?_)
  refine SepWPp.call_tryFromX ⟨wt, sp' + 312#64, cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hF2 hsym2
    (ret_pc := entry + bv% (600)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 312#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 312#64 = sp' + 312#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      Prost.BytesMergeCapOk cap0 bs.length)
    (by simp only [Prost.bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, Prost.bytesMergeCapOk_of_len_lt32 hlen⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs1.x27,
       by simpa [arm64_norm] using hregs1.x25, by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩
      hsp2 hcs2
  dsimp only [Prost.bytesMergeSpecX, Spec.inImage, Prost.bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun _ => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (228)) ?_
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_kyberCt_entails_wirePreKeyOf A g sp' cap' ptr' m v
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl
  | none =>
    dsimp only; have hres := hnone hm; subst hres; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (1112)) ?_)
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := { m with kyberCiphertext := some v0 })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm]) hx0_ne (by decide))
    have hmsg := vecU8At_kyberCt_entails_wirePreKeyOf A g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl

/-! ## Tag 2 (`base_key`, `+0x190..+0x1b4` / `+0x3a8..+0x3c8`, `off = 0x18`) -/

set_option maxHeartbeats 800000 in
/-- Initialize `m.baseKey` (`Option<Vec<u8>>` at `sp' + 336`) to `Some` at `+0x190..+0x1a4`.-/
theorem initOptVecU8_baseKey_cpsPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x190#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 vecPtr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x1a4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (vecU8At A (sp' + 336#64) cap0 vecPtr0 v0 ∗ F) Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (optVecU8At A pin (sp' + 336#64) u ∗ F) Q Qp := by
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 400 20
  dsimp only [contractProg] at hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 400#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry; examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 336#64 344#64 352#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 => SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (420)) ?_))
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 336#64 344#64 352#64]; apply entails_of_eq; ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 336#64) v0, sepConj_assoc]; refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (420)) ?_
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 336#64) v0 hp]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
/-- Tag 2 (`base_key`) merge arm `+0x190..+0x1b4` and error stub `+0x3a8..+0x3c8` → `+0x458`.-/
theorem mergeBaseKey_cpsPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x190#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with baseKey := some v })
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  unfold wirePreKeyOf; simp only [sepExists_sepConj_right]; refine SepWPp.exists_pre (fun g => ?_)
  rw [wirePreKeyAt_split_baseKey A g sp' m]
  let F_msg := optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
    optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
    optVecU8At A g.message (sp' + 384#64) m.message ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; ac_rfl) ?_
  refine initOptVecU8_baseKey_cpsPK hpc hrun hregs hsp hF hsym htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1
  have hcall := bytesMerge_ok_subPK hbytes; have herr := @decodeErrorPushPK_tail_wpX img A ext hPush s0
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 420 20; preKeyTryFrom_fetches img.base H 936 36
  dsimp only [contractProg] at hcall herr hcont hpc1 ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 420#64 at hpc1
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName +
      bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
        (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry; examples_hide_fetches
  have hsp_eq : s1.sp = sp' := hregs1.sp; have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.bytesMergeStackX (Prost.skipFieldStackX 100); simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF1 hsym1
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) (fun hF2 hsym2 => ?_)
  refine SepWPp.call_tryFromX ⟨wt, sp' + 336#64, cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hF2 hsym2
    (ret_pc := entry + bv% (432)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 336#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 336#64 = sp' + 336#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      Prost.BytesMergeCapOk cap0 bs.length)
    (by simp only [Prost.bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, Prost.bytesMergeCapOk_of_len_lt32 hlen⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs1.x27,
       by simpa [arm64_norm] using hregs1.x25, by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩
      hsp2 hcs2
  dsimp only [Prost.bytesMergeSpecX, Spec.inImage, Prost.bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun _ => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (228)) ?_
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_baseKey_entails_wirePreKeyOf A g sp' cap' ptr' m v
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl
  | none =>
    dsimp only; have hres := hnone hm; subst hres; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (1112)) ?_)
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := { m with baseKey := some v0 })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm]) hx0_ne (by decide))
    have hmsg := vecU8At_baseKey_entails_wirePreKeyOf A g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl

/-! ## Tag 3 (`identity_key`, `+0x2a0..+0x2c4` / `+0x340..+0x360`, `off = 0x30`) -/

set_option maxHeartbeats 800000 in
/-- Initialize `m.identityKey` (`Option<Vec<u8>>` at `sp' + 360`) to `Some` at `+0x2a0..+0x2b4`.-/
theorem initOptVecU8_identityKey_cpsPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2a0#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 vecPtr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2b4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (vecU8At A (sp' + 360#64) cap0 vecPtr0 v0 ∗ F) Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (optVecU8At A pin (sp' + 360#64) u ∗ F) Q Qp := by
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 672 20
  dsimp only [contractProg] at hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 672#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry; examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 360#64 368#64 376#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 => SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (692)) ?_))
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 360#64 368#64 376#64]; apply entails_of_eq; ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 360#64) v0, sepConj_assoc]; refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (692)) ?_
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 360#64) v0 hp]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
/-- Tag 3 (`identity_key`) merge arm `+0x2a0..+0x2c4` and error stub `+0x340..+0x360` → `+0x458`.-/
theorem mergeIdentityKey_cpsPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2a0#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with identityKey := some v })
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  unfold wirePreKeyOf; simp only [sepExists_sepConj_right]; refine SepWPp.exists_pre (fun g => ?_)
  rw [wirePreKeyAt_split_identityKey A g sp' m]
  let F_msg := optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
    optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
    optVecU8At A g.message (sp' + 384#64) m.message ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; ac_rfl) ?_
  refine initOptVecU8_identityKey_cpsPK hpc hrun hregs hsp hF hsym htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1
  have hcall := bytesMerge_ok_subPK hbytes; have herr := @decodeErrorPushPK_tail_wpX img A ext hPush s0
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 692 20; preKeyTryFrom_fetches img.base H 832 36
  dsimp only [contractProg] at hcall herr hcont hpc1 ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 692#64 at hpc1
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName +
      bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
        (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry; examples_hide_fetches
  have hsp_eq : s1.sp = sp' := hregs1.sp; have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.bytesMergeStackX (Prost.skipFieldStackX 100); simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF1 hsym1
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) (fun hF2 hsym2 => ?_)
  refine SepWPp.call_tryFromX ⟨wt, sp' + 360#64, cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hF2 hsym2
    (ret_pc := entry + bv% (704)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 360#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 360#64 = sp' + 360#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      Prost.BytesMergeCapOk cap0 bs.length)
    (by simp only [Prost.bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, Prost.bytesMergeCapOk_of_len_lt32 hlen⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs1.x27,
       by simpa [arm64_norm] using hregs1.x25, by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩
      hsp2 hcs2
  dsimp only [Prost.bytesMergeSpecX, Spec.inImage, Prost.bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun _ => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (228)) ?_
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_identityKey_entails_wirePreKeyOf A g sp' cap' ptr' m v
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl
  | none =>
    dsimp only; have hres := hnone hm; subst hres; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (1112)) ?_)
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := { m with identityKey := some v0 })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm]) hx0_ne (by decide))
    have hmsg := vecU8At_identityKey_entails_wirePreKeyOf A g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl

/-! ## Tag 4 (`message`, `+0x200..+0x224` / `+0x438..+0x454`, `off = 0x48`) -/

set_option maxHeartbeats 800000 in
/-- Initialize `m.message` (`Option<Vec<u8>>` at `sp' + 384`) to `Some` at `+0x200..+0x214`.-/
theorem initOptVecU8_message_cpsPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {pin : VecPin} {u : Option (List (BitVec 8))} {F : SepProp}
    {Q : State → SepProp → Prop} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x200#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hcont : ∀ (cap0 vecPtr0 : BitVec 64) (v0 : List (BitVec 8)) (s1 : State),
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x214#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (vecU8At A (sp' + 384#64) cap0 vecPtr0 v0 ∗ F) Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (optVecU8At A pin (sp' + 384#64) u ∗ F) Q Qp := by
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 512 20
  dsimp only [contractProg] at hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 512#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry; examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h25 : s.readReg64 (Reg.gpr 25#5) = 1#64 := hregs.x25
  cases u with
  | none =>
    rw [optVecU8At_none_split A pin sp' 384#64 392#64 400#64]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w2 => SepWPp.exists_pre (fun w1 => SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (532)) ?_))
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont 0#64 1#64 [] _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr)
    rw [← pointsTo64_emptyVec_eq_vecU8At A sp' 384#64 392#64 400#64]; apply entails_of_eq; ac_rfl
  | some v0 =>
    rw [optVecU8At_some_unfold A pin (sp' + 384#64) v0, sepConj_assoc]; refine SepWPp.pure_pre (fun hp => ?_)
    have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt pin.cap hp.2.1
    refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (532)) ?_
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) (fun hF1 hsym1 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont pin.cap pin.ptr v0 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
         by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
         by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
        (by simp only [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr)
    rw [← vecU8At_fold_of_pure A pin (sp' + 384#64) v0 hp]; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
/-- Tag 4 (`message`) merge arm `+0x200..+0x224` and error stub `+0x438..+0x454` → `+0x458`.-/
theorem mergeMessage_cpsPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x200#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) { m with message := some v })
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  unfold wirePreKeyOf; simp only [sepExists_sepConj_right]; refine SepWPp.exists_pre (fun g => ?_)
  rw [wirePreKeyAt_split_message A g sp' m]
  let F_msg := optVecU8At A g.kyberCt (sp' + 312#64) m.kyberCiphertext ∗
    optVecU8At A g.baseKey (sp' + 336#64) m.baseKey ∗
    optVecU8At A g.identityKey (sp' + 360#64) m.identityKey ∗ wirePreKeyU32s sp' m
  refine SepWPp.mono_pre
    (P' := optVecU8At A g.message (sp' + 384#64) m.message ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ F_msg))
    (by apply entails_of_eq; dsimp only [F_msg]; ac_rfl) ?_
  refine initOptVecU8_message_cpsPK hpc hrun hregs hsp hF hsym htr ?_
  intro cap0 vecPtr0 v0 s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hF1 hsym1 htr1
  have hcall := bytesMerge_ok_subPK hbytes; have herr := @decodeErrorPushPK_tail_wpX img A ext hPush s0
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 532 20; preKeyTryFrom_fetches img.base H 1080 32
  dsimp only [contractProg] at hcall herr hcont hpc1 ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s1.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 532#64 at hpc1
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName +
      bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
        (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry; examples_hide_fetches
  have hsp_eq : s1.sp = sp' := hregs1.sp; have h29 : s1.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs1.x29
  have h23 : s1.readReg64 (Reg.gpr 23#5) = sp' + 312#64 := hregs1.x23
  have h0 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 wt.toNat := hx0_1.trans hx0
  have hstack := stackAt_sub_split sp' Prost.bytesMergeStackX (Prost.skipFieldStackX 100); simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF1 hsym1
    (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
  wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm]) (fun hF2 hsym2 => ?_)
  refine SepWPp.call_tryFromX ⟨wt, sp' + 384#64, cap0, vecPtr0, v0, sp' + 440#64, sp' + 296#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun1, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp1 ⊢; exact hsp1) hF2 hsym2
    (ret_pc := entry + bv% (544)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr1)
    (T := vecU8At A (sp' + 384#64) cap0 vecPtr0 v0 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      sliceCursorAt (sp' + 296#64) ptr bs ∗ A.pool ∗ stackAt sp' Prost.bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 384#64 = sp' + 384#64 ∧ sp' + 440#64 = sp' + 440#64 ∧ bs.length < 2 ^ 63 ∧
      Prost.BytesMergeCapOk cap0 bs.length)
    (by simp only [Prost.bytesMergeRawSpecX, hsp_eq, h0, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, rfl, by omega, Prost.bytesMergeCapOk_of_len_lt32 hlen⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF3 hsym3 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs1.x27,
       by simpa [arm64_norm] using hregs1.x25, by simpa [arm64_norm] using h23, by simpa [arm64_norm] using hregs1.x22,
       by simpa [arm64_norm] using hregs1.x21, by simpa [arm64_norm] using hregs1.x20, by simpa [arm64_norm] using hregs1.x19⟩
      hsp2 hcs2
  dsimp only [Prost.bytesMergeSpecX, Spec.inImage, Prost.bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_0 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun cap' => SepWPp.exists_pre (fun ptr' => SepWPp.pure_pre (fun _ => ?_)))
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (228)) ?_
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1))
    have hmsg := vecU8At_message_entails_wirePreKeyOf A g sp' cap' ptr' m v
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hmsg)))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl
  | none =>
    dsimp only; have hres := hnone hm; subst hres; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun hx0_ne => ?_)
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
    rw [memRegion64_split8_448 sp', ProofLib.memRegion_eight (sp' + 448#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_pre (fun w0 => SepWPp.of_sepWP_frozen hF3 hsym3 (mid := entry + bv% (1112)) ?_)
    wp_steps; refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) (fun hF4 hsym4 => ?_)
    refine SepWPp.mono_pre ?_
      (herr (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := { m with message := some v0 })
        (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF4 hsym4 (by simpa [arm64_norm] using htr2.trans htr1) (by simp only [arm64_norm]) hx0_ne (by decide))
    have hmsg := vecU8At_message_entails_wirePreKeyOf A g sp' cap0 vecPtr0 m v0
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hmsg))))))))
    apply entails_of_eq; simp only [hstack, hsp_eq, F_msg, arm64_norm]; ac_rfl

/-! ## Parametric `bytesArmPK_cps` template (`off ∈ {0x00, 0x18, 0x30, 0x48}`) -/

inductive BytesArmFieldPK where
  | kyberCt
  | baseKey
  | identityKey
  | message
  deriving DecidableEq

@[simp]
def BytesArmFieldPK.off : BytesArmFieldPK → BitVec 64
  | .kyberCt => 0x00#64
  | .baseKey => 0x18#64
  | .identityKey => 0x30#64
  | .message => 0x48#64

@[simp]
def BytesArmFieldPK.entryOff : BytesArmFieldPK → BitVec 64
  | .kyberCt => 0x238#64
  | .baseKey => 0x190#64
  | .identityKey => 0x2a0#64
  | .message => 0x200#64

@[simp]
def BytesArmFieldPK.set : BytesArmFieldPK → ProtoPreKeySignalMessage → List (BitVec 8) → ProtoPreKeySignalMessage
  | .kyberCt, m, v => { m with kyberCiphertext := some v }
  | .baseKey, m, v => { m with baseKey := some v }
  | .identityKey, m, v => { m with identityKey := some v }
  | .message, m, v => { m with message := some v }

/-- Parametric `bytes::merge` arm specification for all 4 `Option<Vec<u8>>` fields of
`PreKeySignalMessage::try_from` (`off ∈ {0x00, 0x18, 0x30, 0x48}`). -/
theorem bytesArmPK_cps (f : BytesArmFieldPK) {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hPush : PksmDecodeErrorPushOk img A ext)
    (hbytes : Prost.BytesMergeOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + f.entryOff)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64 →
      s1.status = .Running →
      PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗
          A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) (f.set m v))
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
        (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res)
      (tryFromQp s0) := by
  cases f
  · exact mergeKyberCiphertext_cpsPK hPush hbytes hpc hrun hregs hx0 hsp hF hsym htr hlen hcont hnone
  · exact mergeBaseKey_cpsPK hPush hbytes hpc hrun hregs hx0 hsp hF hsym htr hlen hcont hnone
  · exact mergeIdentityKey_cpsPK hPush hbytes hpc hrun hregs hx0 hsp hF hsym htr hlen hcont hnone
  · exact mergeMessage_cpsPK hPush hbytes hpc hrun hregs hx0 hsp hF hsym htr hlen hcont hnone

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
