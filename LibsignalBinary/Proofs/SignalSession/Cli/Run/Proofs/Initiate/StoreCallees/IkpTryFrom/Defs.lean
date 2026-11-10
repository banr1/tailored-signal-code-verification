/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyPairTryFrom.Decode
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# `IdentityKeyPair::try_from` Stack Layout, Invariants, and Cleanup Tails

Callee wrappers, `224`-byte stack frame layout (`ikpCalleeSavedAt`), protobuf decode invariants,
return-buffer decompositions (`identityKeyPairResultAt`), and shared epilogue/deallocation tails.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom

open CryptoVerification.RecordCodecsBinary.IdentityKeyPairTryFrom.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Relative-offset callee `subroutine_ok` wrappers -/

theorem ikp_bytesMerge_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
          (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))
      ((bytesMergeRawSpecX A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")
    (by decide)]
  exact d.bytesMerge

theorem ikp_varintSlice_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") -
          (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))
      ((decodeVarintSliceSpecX A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")
    (by decide)]
  exact d.varintSlice

theorem ikp_skipField_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]") -
          (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))
      ((skipFieldSpecX A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]")
    (by decide)]
  exact d.skipField

theorem ikp_dropDecodeError_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") -
          (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))
      ((dropDecodeErrorSpecX A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")
    (by decide)]
  exact d.dropDecodeError

theorem ikp_pkTryFrom_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (d : DecodeDeps img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName +
        bv% ((ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") -
          (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))
      ((pkTryFromCodeSpec img).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img
    (sub_ok_at_of_fnAddr d.pkTryFrom identityKeyPairTryFromName
      (num% ((ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") -
        (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))))

theorem ikp_varintSlow_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName +
        bv% ((ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>") -
          (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))
      ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img) :=
  sub_ok_at_of_fnAddr hC.decodeVarintSlow identityKeyPairTryFromName
    (num% ((ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))

theorem ikp_decodeErrorFrom_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName +
        bv% ((ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
          (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img) :=
  sub_ok_at_of_fnAddr hC.decodeErrorFrom identityKeyPairTryFromName
    (num% ((ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))

theorem ikp_decodeErrorPush_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName +
        bv% ((ls_off% "<prost::error::DecodeError>::push") -
          (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img) :=
  sub_ok_at_of_fnAddr hC.decodeErrorPush identityKeyPairTryFromName
    (num% ((ls_off% "<prost::error::DecodeError>::push") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))

theorem ikp_dealloc_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName +
        bv% ((ls_off% "__rustc::__rust_dealloc") -
          (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hC.alloc.dealloc identityKeyPairTryFromName
    (num% ((ls_off% "__rustc::__rust_dealloc") -
      (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")))

/-! ## Stack layout (`sp' = sp - 224#64`) inside `smallRootStack` -/

abbrev ikpSubStack : Nat := smallRootStack - 224

theorem spAligned_sub224 {s0 : State} (hsp0 : s0.spAligned = true) :
    ((s0.sp - 224#64) &&& 15#64 == 0#64) = true := by
  rw [State.spAligned] at hsp0
  revert hsp0
  generalize s0.sp = sp
  intro hsp0
  bv_kernel

/-- Saved callee-saved registers and FP/LR in `[sp' + 144 .. sp' + 168)` and `[sp' + 176 .. sp' + 224)`. -/
def ikpCalleeSavedAt (sp' : BitVec 64) (s0 : State) : SepProp :=
  ((sp' + 144#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp' + 152#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp' + 160#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp' + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp' + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp' + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp' + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp' + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp' + 216#64) ↦₆₄ s0.readReg64 .x19)

theorem ikpRootStack_split (sp : BitVec 64) :
    stackAt sp smallRootStack =
      memRegion (sp - 224#64 - BitVec.ofNat 64 ikpSubStack) (ikpSubStack - skipFieldStackX 100) ∗
      stackAt (sp - 224#64) (skipFieldStackX 100) ∗
      memRegion (sp - 224#64) 144 ∗
      memRegion (sp - 224#64 + 144#64) 80 := by
  have h1 := stackAt_sub_split sp 224 smallRootStack (by decide) (by decide)
  have h2 : memRegion (sp - BitVec.ofNat 64 smallRootStack) ikpSubStack =
      stackAt (sp - 224#64) ikpSubStack := by
    unfold stackAt
    have ha : sp - BitVec.ofNat 64 smallRootStack =
        sp - 224#64 - BitVec.ofNat 64 ikpSubStack := by
      change sp - 65536#64 = sp - 224#64 - 65312#64
      bv_omega
    rw [ha]
  have h2b := stackAt_sub_split (sp - 224#64) (skipFieldStackX 100) ikpSubStack
    (by decide) (by decide)
  have h3 : stackAt sp 224 =
      memRegion (sp - 224#64) 144 ∗ memRegion (sp - 224#64 + 144#64) 80 := by
    unfold stackAt
    exact Prost.memRegion_split (sp - 224#64) 144 80 (by decide)
  rw [h1, h2, h2b, h3]
  ac_rfl

theorem ikpMem80_cells (sp' : BitVec 64) :
    memRegion (sp' + 144#64) 80 ⊢
      ∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
      ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ wbuf : BitVec 64,
      ∃∗ w25 : BitVec 64, ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
        ((sp' + 144#64) ↦₆₄ w29) ∗ ((sp' + 152#64) ↦₆₄ w30) ∗
        ((sp' + 160#64) ↦₆₄ w25) ∗ ((sp' + 168#64) ↦₆₄ wbuf) ∗
        ((sp' + 176#64) ↦₆₄ w24) ∗ ((sp' + 184#64) ↦₆₄ w23) ∗
        ((sp' + 192#64) ↦₆₄ w22) ∗ ((sp' + 200#64) ↦₆₄ w21) ∗
        ((sp' + 208#64) ↦₆₄ w20) ∗ ((sp' + 216#64) ↦₆₄ w19) := by
  rw [show (80 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))) by decide,
    Prost.memRegion_split (sp' + 144#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64) 8 56 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem ikpCalleeSaved_unsplit (sp : BitVec 64) (s0 : State) (wbuf : BitVec 64) :
    memRegion (sp - 224#64 - BitVec.ofNat 64 ikpSubStack) (ikpSubStack - skipFieldStackX 100) ∗
      stackAt (sp - 224#64) (skipFieldStackX 100) ∗
      memRegion (sp - 224#64) 144 ∗
      (((sp - 224#64 + 168#64) ↦₆₄ wbuf) ∗ ikpCalleeSavedAt (sp - 224#64) s0) ⊢
      stackAt sp smallRootStack := by
  rw [ikpRootStack_split sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  set sp' := sp - 224#64
  unfold ikpCalleeSavedAt
  rw [show (80 : Nat) = 8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 8)))))))) by decide,
    Prost.memRegion_split (sp' + 144#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64) 8 56 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64) 8 48 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 144#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans ?_
    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 144#64) (s0.readReg64 .x29))
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 152#64) (s0.readReg64 .x30))
        (sepConj_mono (pointsTo64_entails_memRegion (sp' + 160#64) (s0.readReg64 .x25))
          (sepConj_mono (pointsTo64_entails_memRegion (sp' + 168#64) wbuf)
            (sepConj_mono (pointsTo64_entails_memRegion (sp' + 176#64) (s0.readReg64 .x24))
              (sepConj_mono (pointsTo64_entails_memRegion (sp' + 184#64) (s0.readReg64 .x23))
                (sepConj_mono (pointsTo64_entails_memRegion (sp' + 192#64) (s0.readReg64 .x22))
                  (sepConj_mono (pointsTo64_entails_memRegion (sp' + 200#64) (s0.readReg64 .x21))
                    (sepConj_mono (pointsTo64_entails_memRegion (sp' + 208#64) (s0.readReg64 .x20))
                      (pointsTo64_entails_memRegion (sp' + 216#64) (s0.readReg64 .x19)))))))))))
  apply entails_of_eq; ac_rfl

/-! ## State & memory invariants for `IdentityKeyPair::try_from` -/

structure IkpBaseState (img : Obj.Image) (s0 : State) (sp' : BitVec 64) (s : State) : Prop where
  sp : s.sp = sp'
  spAligned : s.spAligned = true
  frozen : img.FrozenLoaded s
  symtab : s.symtab = img.symtab
  trace : s.trace = s0.trace
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28

theorem IkpBaseState.of_steps {img : Obj.Image} {s0 s1 s2 : State} {sp' : BitVec 64}
    (hb : IkpBaseState img s0 sp' s1)
    (hF : img.FrozenLoaded s2) (hsym : s2.symtab = img.symtab)
    (hsp : s2.sp = sp') (htr : s2.trace = s0.trace)
    (h26 : s2.readReg64 .x26 = s0.readReg64 .x26)
    (h27 : s2.readReg64 .x27 = s0.readReg64 .x27)
    (h28 : s2.readReg64 .x28 = s0.readReg64 .x28) :
    IkpBaseState img s0 sp' s2 where
  sp := hsp
  spAligned := by rw [State.spAligned, hsp, ← hb.sp, ← State.spAligned]; exact hb.spAligned
  frozen := hF
  symtab := hsym
  trace := htr
  x26 := h26
  x27 := h27
  x28 := h28

theorem IkpBaseState.of_calleeSaved {img : Obj.Image} {s0 s1 s2 : State} {sp' : BitVec 64}
    (hb : IkpBaseState img s0 sp' s1)
    (hsp2 : s2.sp = s1.sp) (hal2 : s2.spAligned = true)
    (hF2 : img.FrozenLoaded s2) (hsym2 : s2.symtab = img.symtab)
    (htr2 : s2.trace = s0.trace) (hcs : CalleeSavedPreserved s1 s2) :
    IkpBaseState img s0 sp' s2 where
  sp := hsp2.trans hb.sp
  spAligned := hal2
  frozen := hF2
  symtab := hsym2
  trace := htr2
  x26 := hcs.2.2.2.2.2.2.2.1.trans hb.x26
  x27 := hcs.2.2.2.2.2.2.2.2.1.trans hb.x27
  x28 := hcs.2.2.2.2.2.2.2.2.2.1.trans hb.x28

structure IkpLoopRegs (img : Obj.Image) (s0 : State) (sp' ret : BitVec 64) (s : State) : Prop where
  base : IkpBaseState img s0 sp' s
  x29 : s.readReg64 .x29 = sp' + 144#64
  x19 : s.readReg64 .x19 = ret
  x21 : s.readReg64 .x21 = sp' + 48#64
  x24 : s.readReg64 .x24 = speWord 9

theorem IkpLoopRegs.of_calleeSaved {img : Obj.Image} {s0 s1 s2 : State} {sp' ret : BitVec 64}
    (hr : IkpLoopRegs img s0 sp' ret s1)
    (hsp2 : s2.sp = s1.sp) (hal2 : s2.spAligned = true)
    (hF2 : img.FrozenLoaded s2) (hsym2 : s2.symtab = img.symtab)
    (htr2 : s2.trace = s0.trace) (hcs : CalleeSavedPreserved s1 s2) :
    IkpLoopRegs img s0 sp' ret s2 where
  base := hr.base.of_calleeSaved hsp2 hal2 hF2 hsym2 htr2 hcs
  x29 := hcs.2.2.2.2.2.2.2.2.2.2.1.trans hr.x29
  x19 := hcs.1.trans hr.x19
  x21 := hcs.2.2.1.trans hr.x21
  x24 := hcs.2.2.2.2.2.1.trans hr.x24

def ikpStructAt (A : RustAlloc) (pk sk : VecPin) (a : BitVec 64)
    (m : IdentityKeyPairStructure) : SepProp :=
  vecU8At A a pk.cap pk.ptr m.publicKey ∗
  vecU8At A (a + 24#64) sk.cap sk.ptr m.privateKey

def ikpStructOf (A : RustAlloc) (a : BitVec 64) (m : IdentityKeyPairStructure) : SepProp :=
  ∃∗ pk : VecPin, ∃∗ sk : VecPin, ikpStructAt A pk sk a m

def ikpStructLoopOf (A : RustAlloc) (a : BitVec 64) (n : Nat)
    (m : IdentityKeyPairStructure) : SepProp :=
  ∃∗ pk : VecPin, ∃∗ sk : VecPin,
    ⌜BytesMergeCapOk pk.cap n ∧ BytesMergeCapOk sk.cap n⌝ ∗ ikpStructAt A pk sk a m

theorem ikpStructAt_entails_loopOf (A : RustAlloc) (pk sk : VecPin) (a : BitVec 64)
    (n : Nat) (m : IdentityKeyPairStructure)
    (hpk : BytesMergeCapOk pk.cap n) (hsk : BytesMergeCapOk sk.cap n) :
    ikpStructAt A pk sk a m ⊢ ikpStructLoopOf A a n m := by
  unfold ikpStructLoopOf
  refine Entails.trans ?_ (sepExists_intro _ pk)
  refine Entails.trans ?_ (sepExists_intro _ sk)
  rw [pure_true_emp ⟨hpk, hsk⟩, emp_sepConj]
  exact Entails.refl _

theorem ikpStructLoopOf_mono (A : RustAlloc) (a : BitVec 64) {m n : Nat}
    (msg : IdentityKeyPairStructure) (hle : m ≤ n) :
    ikpStructLoopOf A a n msg ⊢ ikpStructLoopOf A a m msg :=
  Entails.sepExists_elim fun pk => Entails.sepExists_elim fun sk =>
    Entails.pure_left fun ⟨hpk, hsk⟩ =>
      ikpStructAt_entails_loopOf A pk sk a m msg
        (bytesMergeCapOk_mono hpk hle) (bytesMergeCapOk_mono hsk hle)

theorem ikpStructLoopOf_entails_of (A : RustAlloc) (a : BitVec 64) (n : Nat)
    (m : IdentityKeyPairStructure) :
    ikpStructLoopOf A a n m ⊢ ikpStructOf A a m :=
  Entails.sepExists_elim fun pk => Entails.sepExists_elim fun sk =>
    Entails.pure_left fun _ =>
      Entails.trans (sepExists_intro (fun sk' => ikpStructAt A pk sk' a m) sk)
        (sepExists_intro (fun pk' => ∃∗ sk', ikpStructAt A pk' sk' a m) pk)

/-! ## Pure field-length and suffix lemmas for `IdentityKeyPairStructure` -/

theorem ikp_mergeField_suffix {m m' : IdentityKeyPairStructure} {tag : Nat} {wt : WireType}
    {bs rest : List (BitVec 8)}
    (h : IdentityKeyPairStructure.mergeField m tag wt bs = some (m', rest)) :
    ∃ k, k ≤ bs.length ∧ rest = bs.drop k := by
  unfold IdentityKeyPairStructure.mergeField at h
  rcases tag with _ | _ | _ | tag3 <;>
    simp only [skipUnknown, Option.map_eq_some_iff] at h
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩
    obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨⟨v, r⟩, hm, _, rfl⟩
    obtain ⟨k, hkl, hr, _⟩ := mergeBytes_suffix hm; exact ⟨k, hkl, hr⟩
  · rcases h with ⟨r, hs, _, rfl⟩; exact skipField_suffix hs

def IkpFieldsLe (N : Nat) (m : IdentityKeyPairStructure) : Prop :=
  m.publicKey.length ≤ N ∧ m.privateKey.length ≤ N

theorem ikp_mergeField_fields_le {N : Nat} {m m' : IdentityKeyPairStructure} {tag : Nat}
    {wt : WireType} {bs rest : List (BitVec 8)}
    (hm : IkpFieldsLe N m) (hbs : bs.length ≤ N)
    (h : IdentityKeyPairStructure.mergeField m tag wt bs = some (m', rest)) :
    IkpFieldsLe N m' := by
  rcases hm with ⟨h1, h2⟩
  unfold IdentityKeyPairStructure.mergeField at h
  split at h <;> simp only [skipUnknown, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
  · rcases h with ⟨v, r, hv, ⟨rfl, rfl⟩⟩
    exact ⟨Nat.le_trans (mergeBytes_len_le hv) hbs, h2⟩
  · rcases h with ⟨v, r, hv, ⟨rfl, rfl⟩⟩
    exact ⟨h1, Nat.le_trans (mergeBytes_len_le hv) hbs⟩
  · rcases h with ⟨r, _, ⟨rfl, rfl⟩⟩
    exact ⟨h1, h2⟩

theorem ikp_decodeLoop_fields_le :
    ∀ (fuel N : Nat) (m m' : IdentityKeyPairStructure) (bs : List (BitVec 8)),
      IkpFieldsLe N m → bs.length ≤ N →
      decodeFieldsLoop IdentityKeyPairStructure.mergeField fuel m bs = some m' →
      IkpFieldsLe N m'
  | 0, _, _, _, [], hm, _, h => by
    simp only [decodeFieldsLoop, Option.some.injEq] at h; subst h; exact hm
  | 0, _, _, _, _ :: _, _, _, h => by simp [decodeFieldsLoop] at h
  | fuel + 1, _, m, m', [], hm, _, h => by
    simp only [decodeFieldsLoop, Option.some.injEq] at h; subst h; exact hm
  | fuel + 1, N, m, m', b :: rest, hm, hbs, h => by
    simp only [decodeFieldsLoop] at h
    split at h
    · contradiction
    · rename_i tag wt rest1 hk
      split at h
      · contradiction
      · rename_i m1 rest2 hmr
        rcases decodeKey_suffix hk with ⟨k1, _, hk1_le, rfl, _, _⟩
        have hbs1 : ((b :: rest).drop k1).length ≤ N := by
          simp only [List.length_drop]; omega
        have hm1 := ikp_mergeField_fields_le hm hbs1 hmr
        rcases ikp_mergeField_suffix hmr with ⟨k2, hk2_le, rfl⟩
        have hbs2 : (((b :: rest).drop k1).drop k2).length ≤ N := by
          simp only [List.length_drop] at hbs1 ⊢; omega
        exact ikp_decodeLoop_fields_le fuel N m1 m' (((b :: rest).drop k1).drop k2) hm1 hbs2 h

theorem ikp_decode_field_lengths {bs : List (BitVec 8)} {m' : IdentityKeyPairStructure}
    (h : IdentityKeyPairStructure.decode bs = some m') :
    IkpFieldsLe bs.length m' :=
  ikp_decodeLoop_fields_le bs.length bs.length IdentityKeyPairStructure.empty m' bs
    ⟨Nat.zero_le _, Nat.zero_le _⟩ (Nat.le_refl _) h

/-! ## Return buffer splitting and `identityKeyPairResultAt` intro lemmas -/

theorem memRegion72_split_err (r : BitVec 64) :
    memRegion r 72 ⊢
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ b0 : BitVec 8,
        (r ↦₈ b0) ∗ memRegion (r + 1#64) 7 ∗
        ((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗
        memRegion (r + 24#64) 48 := by
  rw [show (72 : Nat) = 1 + (7 + (8 + (8 + 48))) by decide,
    Prost.memRegion_split r 1 71 (by decide),
    Prost.memRegion_split (r + 1#64) 7 64 (by decide),
    Prost.memRegion_split (r + 1#64 + 7#64) 8 56 (by decide),
    Prost.memRegion_split (r + 1#64 + 7#64 + 8#64) 8 48 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem ikpResult_err_spe2 (A : RustAlloc) (r w2 : BitVec 64)
    {out : Except SignalProtocolError IdentityKeyPair}
    (hout : out = .error .invalidProtobufEncoding) :
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
      ((r + 8#64) ↦₆₄ speWord 2) ∗ ((r + 16#64) ↦₆₄ w2) ∗
      memRegion (r + 24#64) 48 ⊢
      identityKeyPairResultAt A r out := by
  rw [hout]
  dsimp only [identityKeyPairResultAt, speAt]
  have ha16 : r + 8#64 + 8#64 = r + 16#64 := by bv_omega
  have h48 : memRegion (r + 24#64) 48 =
      memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16 := by
    have hs := Prost.memRegion_split (r + 24#64) 32 16 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  have h40 : ((r + 16#64) ↦₆₄ w2) ∗ memRegion (r + 24#64) 32 ⊢
      memRegion (r + 16#64) 40 := by
    rw [Prost.memRegion_split (r + 16#64) 8 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (r + 16#64) w2)
  rw [ha16, h48]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right h40))))
  apply entails_of_eq; ac_rfl

theorem ikpResult_err_spe7 (A : RustAlloc) (r w2 : BitVec 64)
    {out : Except SignalProtocolError IdentityKeyPair}
    (hout : out = .error .noKeyTypeIdentifier) :
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
      ((r + 8#64) ↦₆₄ speWord 7) ∗ ((r + 16#64) ↦₆₄ w2) ∗
      memRegion (r + 24#64) 48 ⊢
      identityKeyPairResultAt A r out := by
  rw [hout]
  dsimp only [identityKeyPairResultAt, speAt]
  have ha16 : r + 8#64 + 8#64 = r + 16#64 := by bv_omega
  have h48 : memRegion (r + 24#64) 48 =
      memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16 := by
    have hs := Prost.memRegion_split (r + 24#64) 32 16 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  have h40 : ((r + 16#64) ↦₆₄ w2) ∗ memRegion (r + 24#64) 32 ⊢
      memRegion (r + 16#64) 40 := by
    rw [Prost.memRegion_split (r + 16#64) 8 32 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (pointsTo64_entails_memRegion (r + 16#64) w2)
  rw [ha16, h48]
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right h40))))
  apply entails_of_eq; ac_rfl

theorem ikpResult_err_spe8 (A : RustAlloc) (r : BitVec 64) (t : BitVec 8)
    {out : Except SignalProtocolError IdentityKeyPair}
    (hout : out = .error (.badKeyType t)) :
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
      ((r + 8#64) ↦₆₄ speWord 8) ∗ ((r + 16#64) ↦₆₄ t.zeroExtend 64) ∗
      memRegion (r + 24#64) 48 ⊢
      identityKeyPairResultAt A r out := by
  rw [hout]
  dsimp only [identityKeyPairResultAt, speAt]
  have ha16 : r + 8#64 + 8#64 = r + 16#64 := by bv_omega
  have ha17 : r + 8#64 + 9#64 = r + 17#64 := by bv_omega
  have h48 : memRegion (r + 24#64) 48 =
      memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16 := by
    have hs := Prost.memRegion_split (r + 24#64) 32 16 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  have hw8 : ((r + 16#64) ↦₆₄ t.zeroExtend 64) ⊢
      ((r + 16#64) ↦₈ t) ∗ memRegion (r + 17#64) 7 := by
    have hz : ∀ u : BitVec 8, u.zeroExtend 64 =
        0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ u := by decide
    rw [hz t, ← pointsToBytes8_eq_pointsTo64, pointsToBytes_cons]
    have hm7 : ((r + 16#64 + 1#64) ↦ₛ [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]) ⊢
        memRegion (r + 17#64) 7 := by
      simpa [BitVec.add_assoc] using
        pointsToBytes_entails_memRegion (r + 16#64 + 1#64) [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]
    exact sepConj_mono_right hm7
  have h39 : memRegion (r + 17#64) 7 ∗ memRegion (r + 24#64) 32 =
      memRegion (r + 17#64) 39 := by
    have hs := (Prost.memRegion_split (r + 17#64) 7 32 (by decide)).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  rw [ha16, ha17, h48]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hw8)))) ?_
  have hrew :
      (r ↦₈ 1#8) ∗ (memRegion (r + 1#64) 7 ∗
        (((r + 8#64) ↦₆₄ speWord 8) ∗
          ((((r + 16#64) ↦₈ t) ∗ memRegion (r + 17#64) 7) ∗
            (memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16)))) =
      (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
        (((r + 8#64) ↦₆₄ speWord 8) ∗ ((r + 16#64) ↦₈ t) ∗
          (memRegion (r + 17#64) 7 ∗ memRegion (r + 24#64) 32)) ∗
        memRegion (r + 0x38#64) 16 := by ac_rfl
  rw [hrew, h39]
  exact Entails.refl _

theorem ikpResult_err_spe9 (A : RustAlloc) (r : BitVec 64) (n : Nat)
    {out : Except SignalProtocolError IdentityKeyPair}
    (hout : out = .error (.badKeyLength n)) :
    (r ↦₈ 1#8) ∗ memRegion (r + 1#64) 7 ∗
      ((r + 8#64) ↦₆₄ speWord 9) ∗ ((r + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion (r + 24#64) 48 ⊢
      identityKeyPairResultAt A r out := by
  rw [hout]
  dsimp only [identityKeyPairResultAt, speAt]
  have ha16 : r + 8#64 + 8#64 = r + 16#64 := by bv_omega
  have ha24 : r + 8#64 + 16#64 = r + 24#64 := by bv_omega
  have h48 : memRegion (r + 24#64) 48 =
      memRegion (r + 24#64) 32 ∗ memRegion (r + 0x38#64) 16 := by
    have hs := Prost.memRegion_split (r + 24#64) 32 16 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hs
    exact hs
  rw [ha16, ha24, h48]
  apply entails_of_eq; ac_rfl

/-! ## Shared epilogue (`+812 .. +836`) and Vec dealloc tails (`+772 .. +808`) -/

theorem epilogue_812_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : DecodeGhost} {s0 s : State} {wbuf : BitVec 64}
    (hst : IkpBaseState img s0 (s0.sp - 224#64) s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64)
    (hrun : s.status = .Running) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (memRegion (s0.sp - 224#64 - BitVec.ofNat 64 ikpSubStack) (ikpSubStack - skipFieldStackX 100) ∗
        stackAt (s0.sp - 224#64) (skipFieldStackX 100) ∗
        memRegion (s0.sp - 224#64) 144 ∗
        ((s0.sp - 224#64 + 168#64) ↦₆₄ wbuf) ∗
        ikpCalleeSavedAt (s0.sp - 224#64) s0 ∗
        identityKeyPairResultAt A x.ret (IdentityKeyPair.tryFrom x.bytes) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ logOff img ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (identityKeyPairTryFromSpec A img).post x s0 sf))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hx26, hx27, hx28⟩
  unfold ikpCalleeSavedAt
  simp only [sepConj_assoc]
  let H := Rust.withPanics ext
  code_fetches_from CryptoVerification.libsignalSessionCode
    ikpTryFromBin img.base H
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
    812 28
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
  examples_hide_fetches
  refine Wire.SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hF1 hsym1
  refine ⟨by simp_all [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], hv⟩
  · dsimp only [identityKeyPairTryFromSpec, Spec.inImage]
    rw [pure_true_emp (by simp_all [arm64_norm]), emp_sepConj]
    have hstk := ikpCalleeSaved_unsplit s0.sp s0 wbuf
    unfold ikpCalleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))
    apply entails_of_eq
    ac_rfl

theorem cleanup_sk_792_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    {s0 s : State} {sp' skCap skPtr : BitVec 64} {skBs : List (BitVec 8)}
    (hst : IkpBaseState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 792#64)
    (hrun : s.status = .Running)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (vecU8Buf A skCap skPtr skBs ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseState img s0 sp' sf ∧
        (Pf ⊢ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  by_cases hcap : skCap = 0#64
  · subst hcap
    rw [vecU8Buf_zero]
    refine Wire.SepWPp.pure_pre fun _ => ?_
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      792 4
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    have _hsp_eq := hst.sp
    refine Wire.SepWPp.of_sepWP_end hst.frozen hst.symtab ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hF1 hsym1
    exact ⟨hst.of_steps hF1 hsym1 (by simp_all [arm64_norm])
      (by simp_all [hst.trace, arm64_norm]) (by simp_all [hst.x26, arm64_norm])
      (by simp_all [hst.x27, arm64_norm]) (by simp_all [hst.x28, arm64_norm]),
      Entails.refl _⟩
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A skCap skPtr skBs hcap)) ?_
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_ok hC
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      792 20
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    have hsp_eq := hst.sp
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have _hne : (skCap == 0#64) = false := beq_false_of_ne hcap
    refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab
      (mid := entry + bv% ((ls_off% "__rustc::__rust_dealloc") -
        (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_noPanic_tryFrom (skPtr, skCap.toNat, 1) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hF1 hsym1
      (ret_pc := entry + bv% (812)) (by simp_all [arm64_norm])
      (T := A.pool ∗ A.live skPtr skCap.toNat 1 ∗ memRegion skPtr skCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := skPtr = skPtr ∧ skCap.toNat = skCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk skCap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    refine Wire.SepWPp.of_sepWP_end hF2 hsym2 ?_
    refine Wire.SepWP.done hpc2 hrun2 ?_
    intro hF3 hsym3
    refine ⟨{
      sp := hsp2.trans (by tryFromPost_sp [hsp_eq])
      spAligned := hsp2_align
      frozen := hF3
      symtab := hsym3
      trace := htr2.trans (by simp_all [hst.trace, arm64_norm])
      x26 := hcs2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x26, arm64_norm])
      x27 := hcs2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x27, arm64_norm])
      x28 := hcs2.2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x28, arm64_norm])
    }, ?_⟩
    apply entails_of_eq
    try rw [hsp_eq]
    rw [hstack]
    simp only [arm64_norm]
    try rw [hsp_eq]
    ac_rfl

theorem cleanup_pk_sk_772_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : TripleRatchetHooksW img C A S ext)
    {s0 s : State} {sp' pkCap pkPtr skCap skPtr : BitVec 64}
    {pkBs skBs : List (BitVec 8)}
    (hst : IkpBaseState img s0 sp' s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 772#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = pkCap) (hx20 : s.readReg64 .x20 = pkPtr)
    (hx21 : s.readReg64 .x21 = skCap) (hx23 : s.readReg64 .x23 = skPtr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyPairTryFromName + 812#64) s
      (vecU8Buf A pkCap pkPtr pkBs ∗ vecU8Buf A skCap skPtr skBs ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (fun sf Pf => IkpBaseState img s0 sp' sf ∧
        (Pf ⊢ A.pool ∗ stackAt sp' (skipFieldStackX 100)))
      (tryFromQp s0) := by
  let H := Rust.withPanics ext
  have hnext := @cleanup_sk_792_wp img C A S ext hC s0
  by_cases hcap : pkCap = 0#64
  · subst hcap
    rw [vecU8Buf_zero]
    refine Wire.SepWPp.pure_pre fun _ => ?_
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      772 4
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    have _hsp_eq := hst.sp
    refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab (mid := entry + bv% (792)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hF1 hsym1
    exact hnext
      (hst.of_steps hF1 hsym1 (by simp_all [arm64_norm])
        (by simp_all [hst.trace, arm64_norm]) (by simp_all [hst.x26, arm64_norm])
        (by simp_all [hst.x27, arm64_norm]) (by simp_all [hst.x28, arm64_norm]))
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A pkCap pkPtr pkBs hcap)) ?_
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := ikp_dealloc_ok hC
    code_fetches_from CryptoVerification.libsignalSessionCode
      ikpTryFromBin img.base H
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from")
      (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))
      772 20
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr identityKeyPairTryFromName = entry
    examples_hide_fetches
    have hsp_eq := hst.sp
    have hstack := stackAt_sub_split sp' extHookStack (skipFieldStackX 100)
    have _hne : (pkCap == 0#64) = false := beq_false_of_ne hcap
    refine Wire.SepWPp.of_sepWP_frozen hst.frozen hst.symtab
      (mid := entry + bv% ((ls_off% "__rustc::__rust_dealloc") -
        (ls_off% "<libsignal_protocol::identity_key::IdentityKeyPair as core::convert::TryFrom<&[u8]>>::try_from"))) ?_
    wp_steps
    refine Wire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_noPanic_tryFrom (pkPtr, pkCap.toNat, 1) hcall
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by tryFromPost_sp_align hst.spAligned) hF1 hsym1
      (ret_pc := entry + bv% (792)) (by simp_all [arm64_norm])
      (T := A.pool ∗ A.live pkPtr pkCap.toNat 1 ∗ memRegion pkPtr pkCap.toNat ∗ stackAt s.sp extHookStack)
      (φ := pkPtr = pkPtr ∧ pkCap.toNat = pkCap.toNat ∧ (1#64 : BitVec 64).toNat = 1 ∧ LayoutOk pkCap.toNat 1)
      (by simp_all [rustDeallocExternSpecWithStack, arm64_norm])
      ⟨rfl, rfl, rfl, layoutOk_align1 hpos hlt⟩
      (by rw [hstack, hsp_eq]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hst2 : IkpBaseState img s0 sp' s2 := {
      sp := hsp2.trans (by tryFromPost_sp [hsp_eq])
      spAligned := hsp2_align
      frozen := hF2
      symtab := hsym2
      trace := htr2.trans (by simp_all [hst.trace, arm64_norm])
      x26 := hcs2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x26, arm64_norm])
      x27 := hcs2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x27, arm64_norm])
      x28 := hcs2.2.2.2.2.2.2.2.2.2.1.trans (by simp_all [hst.x28, arm64_norm])
    }
    have hx21_2 : s2.readReg64 .x21 = skCap :=
      hcs2.2.2.1.trans (by simp_all [arm64_norm])
    have hx23_2 : s2.readReg64 .x23 = skPtr :=
      hcs2.2.2.2.2.1.trans (by simp_all [arm64_norm])
    refine Wire.SepWPp.mono_pre
      (P' := vecU8Buf A skCap skPtr skBs ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (by
        apply entails_of_eq
        simp only [arm64_norm]
        try rw [hsp_eq]
        rw [hstack]
        ac_rfl) ?_
    exact hnext hst2 hpc2 hrun2 hx21_2 hx23_2

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IkpTryFrom
