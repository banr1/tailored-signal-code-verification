/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W0Spec
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas -- shake: keep

/-!
# `PreKeySignalMessage::try_from`: Decode-Loop Head, Scratch Helpers, and Varint/Error Tails

Instruction decode lemmas (`+0x000..+0x464`), decode-loop register/memory invariants,
64-byte scratch helpers, loop-head checks (`+0x0e4..+0x0f0`, `+0x300..+0x304`), and slow-varint /
`DecodeError` tail blocks (`+0x120`, `+0x2ec`, `+0x324`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  memRegion_split decodeVarint_suffix pointsTo64_pair_entails_memRegion16
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_IS5Wire_DecodeKeyB : True := trivial

abbrev SepWPp := Wire.SepWPp
abbrev SepWP.done := @Wire.SepWP.done
abbrev SepWPp.of_sepWP := @Wire.SepWPp.of_sepWP
abbrev SepWPp.of_sepWP_frozen := @Wire.SepWPp.of_sepWP_frozen
abbrev SepWPp.of_sepWP_end := @Wire.SepWPp.of_sepWP_end
abbrev SepWPp.panic := @Wire.SepWPp.panic
abbrev SepWPp.frame_tryFrom := @Wire.SepWPp.frame_tryFrom
abbrev SepWPp.bind := @Wire.SepWPp.bind
abbrev SepWPp.bind_entails := @Wire.SepWPp.bind_entails
abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
abbrev SepWPp.call_tryFromX := @Wire.SepWPp.call_tryFrom

gen_decodes libsignalSessionCode_tree pksmLoopDec [
  (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 0) →
    (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from" + 1124)]

/-- Fetch hypotheses for `PreKeySignalMessage::try_from`, from fn-relative offset `k0`, `len` bytes. -/
macro "preKeyTryFrom_fetches " b:term:max H:term:max k0:term:max len:term:max : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.pksmLoopDec $b $H
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
      $k0 $len)

/-- Native stack budget of `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` (`32,832` B). -/
abbrev dk_varintSlowStackX : Nat := 64 + 2 * extHookStack

abbrev PksmDecodeErrorFromOk (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
    ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img)

abbrev PksmDecodeVarintSlowOk (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName)
    ((decodeVarintSlowSpecWithStack A dk_varintSlowStackX).inImage img)

theorem decodeErrorFrom_ok_subPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : PksmDecodeErrorFromOk img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
          ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img) := by
  have heq :
      (contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" -
          ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") =
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"),
      (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")]
    bv_omega
  rw [heq]; exact h

theorem decodeVarintSlow_ok_subPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : PksmDecodeVarintSlowOk img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" -
          ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))
      ((decodeVarintSlowSpecWithStack A dk_varintSlowStackX).inImage img) := by
  have heq :
      (contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" -
          ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from") =
      (tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"),
      (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact h

theorem decodeVarintSlice_ok_subPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Prost.DecodeVarintSliceOkExtX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") -
          (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")))
      ((Prost.decodeVarintSliceSpecX A).inImage img) := by
  have heq :
      (contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") -
          (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) =
      (contractProg img.base ext).fnAddr decodeVarintSliceName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"),
      (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]
    bv_omega
  rw [heq]; exact h

/-! ## 1. Loop-Invariant Helpers (`PreKeyLoopRegs`, `preKeyLoopExitMem`, `preKeyLoopExitPost`) -/

theorem PreKeyLoopRegs.of_calleeSaved {sp' sret len ptr : BitVec 64} {vb : BitVec 8}
    {s1 s2 : State} (h1 : PreKeyLoopRegs sp' sret len ptr vb s1)
    (hsp : s2.sp = s1.sp) (hcs : CalleeSavedPreserved s1 s2) :
    PreKeyLoopRegs sp' sret len ptr vb s2 := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, _, h25, _, h27, _, h29, _⟩
  exact ⟨hsp.trans h1.sp, h29.trans h1.x29, h27.trans h1.x27, h25.trans h1.x25,
    h23.trans h1.x23, h22.trans h1.x22, h21.trans h1.x21, h20.trans h1.x20, h19.trans h1.x19⟩

theorem wirePreKeyOf_entails_exists_of (A : RustAlloc) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) :
    wirePreKeyOf A a m ⊢ ∃∗ mErr : ProtoPreKeySignalMessage, wirePreKeyOf A a mErr :=
  Entails.sepExists_intro m

theorem preKeyLoopExitMem_append_prefix (A : RustAlloc) (sp' ptr : BitVec 64)
    (bs : List (BitVec 8)) (k : Nat) (hk : k ≤ bs.length)
    (x24 : BitVec 64) (res : Option ProtoPreKeySignalMessage) :
    preKeyLoopExitMem A sp' (ptr + BitVec.ofNat 64 k) (bs.drop k) x24 res ∗ (ptr ↦ₛ bs.take k) =
      preKeyLoopExitMem A sp' ptr bs x24 res := by
  unfold preKeyLoopExitMem; rw [← pointsToBytes_take_drop ptr bs k hk]; ac_nf

theorem preKeyLoopExitPost_append_prefix {img : Obj.Image} {A : RustAlloc} {s0 sf : State}
    {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {k : Nat} (hk : k ≤ bs.length)
    {res : Option ProtoPreKeySignalMessage} {Pm : SepProp}
    (h : preKeyLoopExitPost img A s0 sp' sret len ptr0 vb
      (ptr + BitVec.ofNat 64 k) (bs.drop k) res sf Pm) :
    preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res sf (Pm ∗ (ptr ↦ₛ bs.take k)) := by
  rcases h with ⟨hst, hent⟩; refine ⟨hst, ?_⟩
  rw [← preKeyLoopExitMem_append_prefix A sp' ptr bs k hk (sf.readReg64 .x24) res]
  exact sepConj_mono_left hent

theorem preKeyLoopExitMem_err_intro (A : RustAlloc) (sp' ptr : BitVec 64) (bs : List (BitVec 8))
    (x24 : BitVec 64) (hx24 : x24 ≠ 0#64) (n : Nat) (mErr : ProtoPreKeySignalMessage) :
    memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      decodeErrorAtStackLen A x24 n ∗ wirePreKeyOf A (sp' + 312#64) mErr ⊢
      preKeyLoopExitMem A sp' ptr bs x24 none := by
  unfold preKeyLoopExitMem; dsimp only; rw [pure_true_emp hx24, emp_sepConj]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
  exact sepConj_mono (decodeErrorWith_entails_at A x24 n)
    (wirePreKeyOf_entails_exists_of A (sp' + 312#64) mErr)

theorem preKeyLoopExitMem_ok_intro (A : RustAlloc) (sp' ptr : BitVec 64) (bs : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) :
    sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      wirePreKeyOf A (sp' + 312#64) m ⊢
      preKeyLoopExitMem A sp' ptr bs 0#64 (some m) := by
  unfold preKeyLoopExitMem sliceCursorAt; dsimp only
  rw [pure_true_emp rfl, emp_sepConj,
    ← sepConj_assoc ((sp' + 296#64) ↦₆₄ ptr) ((sp' + 296#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) (ptr ↦ₛ bs),
    sepConj_assoc (((sp' + 296#64) ↦₆₄ ptr) ∗ ((sp' + 296#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length))]
  exact sepConj_mono_left (pointsTo64_pair_entails_memRegion16 (sp' + 296#64) ptr (BitVec.ofNat 64 bs.length))

theorem SepWPp.advance_cursorPK {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs rest : List (BitVec 8)} {res : Option ProtoPreKeySignalMessage} {R : SepProp}
    (hsuf : ∃ k, k ≤ bs.length ∧ rest = bs.drop k)
    (h : SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest ∗ R)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) rest res) (tryFromQp s0)) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ R)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  rw [sliceCursorAfter_eq_take_cursorAt (sp' + 296#64) ptr bs rest hsuf]
  rcases hsuf with ⟨k, hkl, rfl⟩
  have hk : bs.length - (bs.drop k).length = k := by simp; omega
  rw [hk] at h ⊢
  refine SepWPp.mono_pre
    (P' := (sliceCursorAt (sp' + 296#64) (ptr + BitVec.ofNat 64 k) (bs.drop k) ∗ R) ∗ (ptr ↦ₛ bs.take k))
    (by apply entails_of_eq; ac_rfl) ?_
  exact SepWPp.frame_tryFrom h (fun _ _ hqm => preKeyLoopExitPost_append_prefix hkl hqm)

/-! ### 64-byte scratch memory helpers at `sp' + 448#64` -/

theorem memRegion64_split24 (sp' : BitVec 64) :
    memRegion (sp' + 448#64) 64 = memRegion (sp' + 448#64) 24 ∗ memRegion (sp' + 472#64) 40 := by
  have hs := memRegion_split (sp' + 448#64) 24 40 (by decide)
  have ha : sp' + 448#64 + 24#64 = sp' + 472#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem memRegion56_split40 (sp' : BitVec 64) :
    memRegion (sp' + 456#64) 56 = memRegion (sp' + 456#64) 40 ∗ memRegion (sp' + 496#64) 16 := by
  have hs := memRegion_split (sp' + 456#64) 40 16 (by decide)
  have ha : sp' + 456#64 + 40#64 = sp' + 496#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem memRegion48_16_eq_64 (sp' : BitVec 64) :
    memRegion (sp' + 448#64) 48 ∗ memRegion (sp' + 496#64) 16 = memRegion (sp' + 448#64) 64 := by
  have hs := (memRegion_split (sp' + 448#64) 48 16 (by decide)).symm
  have ha : sp' + 448#64 + 48#64 = sp' + 496#64 := by bv_omega
  rw [ha] at hs; exact hs

theorem scratch24_ok_entails_memRegion64 (sp' v w : BitVec 64) :
    ((sp' + 448#64) ↦₃₂ 0#32) ∗ ((sp' + 452#64) ↦₃₂ 0#32) ∗ ((sp' + 456#64) ↦₆₄ v) ∗
      ((sp' + 464#64) ↦₆₄ w) ∗ memRegion (sp' + 472#64) 40 ⊢ memRegion (sp' + 448#64) 64 := by
  have h0 : ((sp' + 448#64) ↦₃₂ 0#32) ∗ ((sp' + 452#64) ↦₃₂ 0#32) = ((sp' + 448#64) ↦₆₄ 0#64) := by
    have hs := (pointsTo64_zero_split32 (sp' + 448#64)).symm
    have ha : sp' + 448#64 + 4#64 = sp' + 452#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h0, memRegion64_split24 sp', memRegion_split (sp' + 448#64) 8 16 (by decide),
    memRegion_split (sp' + 448#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 448#64 + 8#64 = sp' + 456#64 := by bv_omega
  have ha2 : sp' + 456#64 + 8#64 = sp' + 464#64 := by bv_omega
  rw [ha1, ha2]; refine Entails.trans ?_
    (sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion (sp' + 448#64) 0#64)
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 456#64) v)
        (pointsTo64_entails_memRegion (sp' + 464#64) w))) (Entails.refl _))
  apply entails_of_eq; ac_rfl

theorem scratch24_err_entails_memRegion64 (sp' e : BitVec 64) :
    ((sp' + 448#64) ↦₃₂ 1#32) ∗ ((sp' + 452#64) ↦₃₂ 0#32) ∗ ((sp' + 456#64) ↦₆₄ e) ∗
      memRegion (sp' + 464#64) 8 ∗ memRegion (sp' + 472#64) 40 ⊢ memRegion (sp' + 448#64) 64 := by
  have h1 : ((sp' + 448#64) ↦₃₂ 1#32) ∗ ((sp' + 452#64) ↦₃₂ 0#32) = ((sp' + 448#64) ↦₆₄ 1#64) := by
    have hs := (pointsTo64_one_split32 (sp' + 448#64)).symm
    have ha : sp' + 448#64 + 4#64 = sp' + 452#64 := by bv_omega
    rw [ha] at hs; exact hs
  rw [← sepConj_assoc, h1, memRegion64_split24 sp', memRegion_split (sp' + 448#64) 8 16 (by decide),
    memRegion_split (sp' + 448#64 + 8#64) 8 8 (by decide)]
  have ha1 : sp' + 448#64 + 8#64 = sp' + 456#64 := by bv_omega
  have ha2 : sp' + 456#64 + 8#64 = sp' + 464#64 := by bv_omega
  rw [ha1, ha2]; refine Entails.trans ?_
    (sepConj_mono (sepConj_mono (pointsTo64_entails_memRegion (sp' + 448#64) 1#64)
      (sepConj_mono (pointsTo64_entails_memRegion (sp' + 456#64) e) (Entails.refl _))) (Entails.refl _))
  apply entails_of_eq; ac_rfl

theorem memRegion64_split_448_456_464 (sp' : BitVec 64) :
    memRegion (sp' + 448#64) 64 =
      (∃∗ w0 : BitVec 64, (sp' + 448#64) ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (sp' + 456#64) ↦₆₄ w1) ∗
      memRegion (sp' + 464#64) 48 := by
  rw [memRegion_split (sp' + 448#64) 8 56 (by decide), memRegion_split (sp' + 448#64 + 8#64) 8 48 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  have ha1 : sp' + 448#64 + 8#64 = sp' + 456#64 := by bv_omega
  have ha2 : sp' + 456#64 + 8#64 = sp' + 464#64 := by bv_omega
  rw [ha1, ha2]

theorem pointsTo64_456_memRegion48_entails_memRegion56 (sp' v : BitVec 64) :
    ((sp' + 456#64) ↦₆₄ v) ∗ memRegion (sp' + 464#64) 48 ⊢ memRegion (sp' + 456#64) 56 := by
  rw [memRegion_split (sp' + 456#64) 8 48 (by decide)]
  have ha : sp' + 456#64 + 8#64 = sp' + 464#64 := by bv_omega
  rw [ha]; exact sepConj_mono_left (pointsTo64_entails_memRegion (sp' + 456#64) v)

theorem decodeKeyPK_err_entailsX (A : RustAlloc) (sp' ptr w0 v : BitVec 64)
    (bs rest : List (BitVec 8)) (m : ProtoPreKeySignalMessage) :
    sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      ((sp' + 448#64) ↦₆₄ w0) ∗ ((sp' + 456#64) ↦₆₄ v) ∗ memRegion (sp' + 464#64) 48 ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ wirePreKeyOf A (sp' + 312#64) m ⊢
    memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
      ((sp' + 448#64) ↦₆₄ w0) ∗ memRegion (sp' + 456#64) 56 ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ wirePreKeyOf A (sp' + 312#64) m := by
  refine Entails.trans (sepConj_mono_left (sliceCursorAfter_entails_memRegion (sp' + 296#64) ptr bs rest)) ?_
  rw [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
  rw [← sepConj_assoc]; exact sepConj_mono_left (pointsTo64_456_memRegion48_entails_memRegion56 sp' v)

theorem memRegion64_split8 (sp' : BitVec 64) :
    memRegion (sp' + 448#64) 64 = memRegion (sp' + 448#64) 8 ∗ memRegion (sp' + 456#64) 56 := by
  have hs := memRegion_split (sp' + 448#64) 8 56 (by decide)
  have ha : sp' + 448#64 + 8#64 = sp' + 456#64 := by bv_omega
  rw [ha] at hs; exact hs

abbrev memRegion64_split8_448 := memRegion64_split8

/-! ## 2. Loop Head (`+0x0e4..+0x0f0`, `+0x300..+0x304`) -/

theorem loopExitEmptyPK_300_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x300#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hres : res = some m) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  subst hres; let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 768 8
  dsimp only [contractProg] at hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 768#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches; refine SepWPp.of_sepWP_end hF hsym ?_; wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine ⟨⟨⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
    by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
    by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩,
    by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp, hF1, hsym1, by simpa [arm64_norm] using htr⟩, ?_⟩
  simp only [arm64_norm]; exact preKeyLoopExitMem_ok_intro A sp' ptr bs m

set_option maxHeartbeats 800000 in
theorem loopCheckPK_e4_empty_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hres : res = some m) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr [] ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr [] res) (tryFromQp s0) := by
  have hexit := @loopExitEmptyPK_300_wpX img A ext s0
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 228 16
  dsimp only [contractProg] at hexit hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 228#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  unfold sliceCursorAt; simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (768)) ?_; wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.mono_pre ?_
    (hexit (sp' := sp') (sret := sret) (len := len) (ptr0 := ptr0) (vb := vb)
      (ptr := ptr) (bs := []) (m := m) (res := res)
      (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr hres)
  unfold sliceCursorAt; apply entails_of_eq; ac_rfl

set_option maxHeartbeats 800000 in
theorem loopCheckPK_e4_cons_cpsX {img : Obj.Image}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0e4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : (b0 :: bs1).length < 2 ^ 32)
    (hcont : ∀ s1 : State,
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x0f4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x28 = sp' + 296#64 → s1.readReg64 .x26 = sp' + 304#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab → s1.trace = s0.trace →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ F) Q Qp) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ F) Q Qp := by
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 228 16
  dsimp only [contractProg] at hcont hpc ⊢
  change SepWPp (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 228#64 at hpc
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches; have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := Wire.cons_len_bv64_ne_zero b0 bs1 (by omega)
  unfold sliceCursorAt; simp only [sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (244)) ?_; wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.mono_pre ?_
    (hcont _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1 htr)
  unfold sliceCursorAt; apply entails_of_eq; ac_rfl

/-! ## 3. Tail Callee Blocks (`+0x120`, `+0x2ec`, `+0x324`) -/

set_option maxHeartbeats 800000 in
theorem decodeErrorFromPK_tail_wpX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hFrom : PksmDecodeErrorFromOk img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x324#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hkind : KindNoHeap (s.readReg64 .x8)) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (memRegion (sp' + 296#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        ((sp' + 448#64) ↦₆₄ w0) ∗ memRegion (sp' + 456#64) 56 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗ wirePreKeyOf A (sp' + 312#64) mErr)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs none) (tryFromQp s0) := by
  have hcall := decodeErrorFrom_ok_subPK hFrom
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 804 20
  change SepWPp (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 804#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) _ at hcall
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches; have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have hstack := stackAt_sub_split sp' Prost.decodeErrorHookStackX (Prost.skipFieldStackX 100)
  simp only [hstack, memRegion56_split40 sp', sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from" - ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) ?_; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_tryFromX (sp' + 448#64, s.readReg64 (Reg.gpr 8#5)) hcall
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [State.spAligned, arm64_norm]) hF1 hsym1
    (ret_pc := entry + bv% (816)) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (T := ((sp' + 448#64) ↦₆₄ s.readReg64 (Reg.gpr 8#5)) ∗ memRegion (sp' + 456#64) 40 ∗
      A.pool ∗ stackAt sp' Prost.decodeErrorHookStackX)
    (φ := KindNoHeap (s.readReg64 (Reg.gpr 8#5)))
    (by simp_all [decodeErrorFromSpecWithStack, Prost.decodeErrorHookStackX, arm64_norm]) hkind (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  dsimp only [decodeErrorFromSpecWithStack]; rw [sepConj_assoc]; refine SepWPp.pure_pre (fun ⟨hx0_ne, htr2⟩ => ?_)
  refine SepWPp.of_sepWP_end hF2 hsym2 ?_; wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hF3 hsym3 => ?_
  refine ⟨⟨⟨by simp_all [arm64_norm, hregs2.sp], by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
    by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
    by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩,
    by simp_all [State.spAligned, arm64_norm], hF3, hsym3, by simp_all [arm64_norm]⟩, ?_⟩
  simp only [arm64_norm]
  refine Entails.trans ?_
    (preKeyLoopExitMem_err_intro A sp' ptr bs (s2.readReg64 (Reg.gpr 0#5)) hx0_ne 0 mErr)
  rw [← memRegion48_16_eq_64 sp']
  apply entails_of_eq; simp only [hstack, Prost.decodeErrorHookStackX, hsp_eq, arm64_norm]; ac_rfl

set_option maxHeartbeats 800000 in
theorem decodeVarintSlowPK_tail_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hSlow : PksmDecodeVarintSlowOk img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x2ec#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x154#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace → s1.readReg64 .x24 = key →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  have hcall := decodeVarintSlow_ok_subPK hSlow
  let H := Rust.withPanics ext; preKeyTryFrom_fetches img.base H 748 20
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 748#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) _ at hcall
  dsimp only [contractProg] at hcont
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have hstack := stackAt_sub_split sp' dk_varintSlowStackX (Prost.skipFieldStackX 100)
  unfold sliceCursorAt; simp only [hstack, sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" - ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")) ?_; wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_tryFromX (sp' + 440#64, sp' + 296#64, ptr, bs) hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (756)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ ((sp' + 296#64) ↦₆₄ ptr) ∗
      ((sp' + 296#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      A.pool ∗ stackAt sp' dk_varintSlowStackX)
    (φ := bs.length < 18446744073709551616)
    (by simp only [decodeVarintSlowSpecWithStack, dk_varintSlowStackX, hsp_eq, arm64_norm]) (by omega) (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  dsimp only [decodeVarintSlowSpecWithStack]; rw [VarintBridge.decodeVarint_eq_varintSlow bs]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩; dsimp only [Option.map]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hlen_sub : bs.length - (bs.length - rest.length) = rest.length := by rw [hrest, List.length_drop]; omega
    rw [hlen_sub, sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun ⟨hx0_2, hx1_2⟩ => ?_)
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have hx1_2' : s2.readReg64 (Reg.gpr 1#5) = key := hx1_2
    refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (340)) ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
    refine SepWPp.mono_pre ?_
      (hcont key rest _ hd (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
         by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
         by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hF3 hsym3 (by simpa [arm64_norm] using htr2.trans htr) (by simp only [arm64_norm]))
    apply entails_of_eq; unfold sliceCursorAfter; simp only [hstack, dk_varintSlowStackX, hsp_eq, arm64_norm]; ac_rfl
  | none =>
    dsimp only [Option.map]; rw [hnone hd, sepConj_assoc]; refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepConj_assoc, sepConj_pure_left_comm]; refine SepWPp.pure_pre (fun ⟨hx0_1, hx1_ne⟩ => ?_)
    have hx0_1' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine SepWPp.of_sepWP_end hF2 hsym2 ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
      by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hF3, hsym3, by simpa [arm64_norm] using htr2.trans htr⟩, ?_⟩
    simp only [arm64_norm]
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 296#64)
      (ptr + BitVec.ofNat 64 (min 10 bs.length)) (BitVec.ofNat 64 (bs.length - min 10 bs.length))
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left hpair)
        (preKeyLoopExitMem_err_intro A sp' ptr bs (s2.readReg64 (Reg.gpr 1#5)) hx1_ne 0 m))
    apply entails_of_eq; simp only [hstack, dk_varintSlowStackX, hsp_eq, arm64_norm]; ac_rfl

set_option maxHeartbeats 800000 in
theorem decodeVarintSlicePK_tail_cpsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hvarint : Prost.DecodeVarintSliceOkExtX img A ext)
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x120#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32) (hpre_slice : VarintSlicePre bs)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (contractProg img.base ext).fnAddr preKeyTryFromName + 0x154#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace → s1.readReg64 .x24 = key →
      SepWPp (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : decodeVarint bs = none → res = none) :
    SepWPp (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPost img A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  have hcall := decodeVarintSlice_ok_subPK hvarint; let H := Rust.withPanics ext
  preKeyTryFrom_fetches img.base H 288 52; preKeyTryFrom_fetches img.base H 824 8
  change SepWPp (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 1120#64) _ _ _ _
  change s.pc = (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + 288#64 at hpc
  change subroutine_ok (libsignalSessionCode.rebase img.base H)
    ((libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) _ at hcall
  dsimp only [contractProg] at hcont
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr preKeyTryFromName = entry
  examples_hide_fetches
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  have h28 : s.readReg64 (Reg.gpr 28#5) = sp' + 296#64 := hx28
  have h26 : s.readReg64 (Reg.gpr 26#5) = sp' + 304#64 := hx26
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split sp' Prost.decodeVarintSliceStackX (Prost.skipFieldStackX 100)
  unfold sliceCursorAt; simp only [hstack, memRegion64_split24 sp', sepConj_assoc]
  refine SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") - (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from"))) ?_; wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) fun hF1 hsym1 => ?_
  refine SepWPp.call_tryFromX ⟨sp' + 448#64, ptr, bs⟩ hcall
    (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
    (ret_pc := entry + bv% (296)) (by simp only [arm64_norm]) (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 448#64) 24 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' Prost.decodeVarintSliceStackX)
    (φ := bs.length < 9223372036854775808 ∧ VarintSlicePre bs)
    (by simp only [Prost.decodeVarintSliceSpecX, Prost.decodeVarintSliceStackX, hsp_eq, h1, h2, hx2_nat, arm64_norm])
    ⟨by omega, hpre_slice⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
  have hregs2 : PreKeyLoopRegs sp' sret len ptr0 vb s2 :=
    PreKeyLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29, by simpa [arm64_norm] using hregs.x27,
       by simpa [arm64_norm] using hregs.x25, by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20, by simpa [arm64_norm] using hregs.x19⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs2.x29
  have h28_2 : s2.readReg64 (Reg.gpr 28#5) = sp' + 296#64 := by simpa [arm64_norm, h28] using hcs2.2.2.2.2.2.2.2.2.2.1
  have h26_2 : s2.readReg64 (Reg.gpr 26#5) = sp' + 304#64 := by simpa [arm64_norm, h26] using hcs2.2.2.2.2.2.2.2.1
  dsimp only [Prost.decodeVarintSliceSpecX]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩; dsimp only [varintSliceResultAt]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hlen64 : bs.length < 2 ^ 64 := by omega
    have hrest64 : rest.length < 2 ^ 64 := by omega
    have hsub64 : bs.length - rest.length < 2 ^ 64 := by omega
    have hsub_bv : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) = BitVec.ofNat 64 rest.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hrest64]; omega
    have hult_false : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, decide_eq_false_iff_not]; omega
    rw [pointsTo64_zero_split32 (sp' + 448#64)]; simp only [sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    refine SepWPp.of_sepWP_frozen hF2 hsym2 (mid := entry + bv% (340)) ?_; wp_steps; wp_if hcc
    · exfalso; rw [← hrest] at hcc; exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · wp_steps
      refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
      refine SepWPp.mono_pre ?_
        (hcont key rest _ hd (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
           by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
           by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hF3 hsym3 (by simpa [arm64_norm] using htr2.trans htr) (by simp only [arm64_norm]))
      have hscr := scratch24_ok_entails_memRegion64 sp' key (BitVec.ofNat 64 (bs.length - rest.length))
      unfold sliceCursorAfter; simp only [← hrest, hsub_bv]
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr)))
      apply entails_of_eq; simp only [hstack, Prost.decodeVarintSliceStackX, hsp_eq, arm64_norm]; ac_rfl
  | none =>
    dsimp only [varintSliceResultAt]
    rw [hnone hd, pointsTo64_one_split32 (sp' + 448#64), sepConj_assoc]
    refine SepWPp.pure_pre (fun htr2 => ?_)
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_pre (fun e => SepWPp.pure_pre (fun he_ne => ?_))
    refine SepWPp.of_sepWP_end hF2 hsym2 ?_; wp_steps
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) fun hF3 hsym3 => ?_
    refine ⟨⟨⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29, by simpa [arm64_norm] using hregs2.x27,
      by simpa [arm64_norm] using hregs2.x25, by simpa [arm64_norm] using hregs2.x23, by simpa [arm64_norm] using hregs2.x22,
      by simpa [arm64_norm] using hregs2.x21, by simpa [arm64_norm] using hregs2.x20, by simpa [arm64_norm] using hregs2.x19⟩,
      by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
      hF3, hsym3, by simpa [arm64_norm] using htr2.trans htr⟩, ?_⟩
    simp only [arm64_norm]
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 296#64) ptr (BitVec.ofNat 64 bs.length)
    have hscr := scratch24_err_entails_memRegion64 sp' e
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono hpair (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
        (preKeyLoopExitMem_err_intro A sp' ptr bs e he_ne 0 m))
    apply entails_of_eq; simp only [hstack, Prost.decodeVarintSliceStackX, hsp_eq, arm64_norm]; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
