/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.BodyDefs
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsW
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneX
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SP2Ext` and `[LibsignalPlacement]` Definitions for `SessionRecord::deserialize`

Defines loop invariants, segment steps, PC helpers, and callee bundles (`DeserializeCalleesAtX`,
X-stack `DeserializeCalleesAtW` / `DeserializeCalleesAtWA`, and relocatable
`DeserializeCalleesPlacedW`), together with `bytes::merge` and `int32::merge` call-stepping lemmas
for `message::merge<Chain>` and `SessionRecord::deserialize`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

theorem DDX1 : True := trivial

/-! ## 1. `OkAtX` and Prost Callee Contracts on `SP2Ext` -/

/-- `subroutine_ok` on `SP2Ext b ext` (`contractProg b ext`) at `fnAddr name`. -/
def OkAtX {α : Type} (b : BitVec 64) (ext : String → Option (State → State))
    (name : String) (spec : Spec α) : Prop :=
  subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr name) spec

/-- `prost::encoding::varint::decode_varint_slice` on `SP2Ext b ext`. -/
def DecodeVarintSliceOkX (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  OkAtX b ext Prost.decodeVarintSliceName (Prost.decodeVarintSliceSpec A)

/-- `prost::encoding::int32::merge` on `SP2Ext b ext`. -/
def Int32MergeOkX (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  OkAtX b ext Prost.int32MergeName (Prost.int32MergeSpec A)

/-- `prost::encoding::bytes::merge` on `SP2Ext img.base ext`. -/
def BytesMergeOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  OkAtX img.base ext Prost.bytesMergeName (Prost.bytesMergeSpec A img)

/-- Symbol name for `RawVec<Chain>::grow_one`. -/
abbrev growOneChainNameX : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"

/-- The callee contracts needed by `deserialize` and `merge_field` on `SP2Ext img.base ext`. -/
def DeserializeCalleesAtX (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  DecodeVarintSliceOkX img.base A0 ext ∧
    Int32MergeOkX img.base A0 ext ∧
    BytesMergeOkX img A0 ext ∧
    OkAtX img.base ext growOneChainNameX
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage img)

/-- General `merge_field` contract restricted by `P`, on `SP2Ext img.base ext`. -/
def MergeFieldGenOkAtX (img : Obj.Image)
    (ext : String → Option (State → State)) (P : GenField → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeFieldGenSpecAt img P)

/-- General `message::merge<Chain>` contract on `SP2Ext img.base ext`. -/
def ChainMergeGenOkAtX (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  OkAtX img.base ext chainMergeName (chainMergeGenSpecAt img)

/-! ## 2. `ChainDefs` Predicates on `SP2Ext img.base ext` -/

/-- `message::merge<Chain> + off` in `SP2Ext img.base ext`. -/
noncomputable abbrev chainPCAtX (img : Obj.Image)
    (ext : String → Option (State → State)) (off : BitVec 64) : BitVec 64 :=
  (SP2Ext img.base ext).fnAddr chainMergeName + off

/-- One segment step of the general chain merge on `SP2Ext img.base ext`. -/
abbrev ChainStepGAtX (img : Obj.Image)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (chainMergeGenSpecAt img) x R s0 s Q

/-- The field-loop head `+0x120` after `k` of the chain's fields on `SP2Ext img.base ext`. -/
def ChainLoopGAtX (img : Obj.Image)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chainPCAtX img ext 0x120#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = s0.sp - 0x100#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x24 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x21 = 98#64 ∧ s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x25 = s0.sp - 0xf8#64 ∧ s.readReg64 .x26 = 1#64 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 32 ∧
    (s.mem ⊨ prostChainGAt A0 x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      stackAt (s0.sp - 0x100#64) chainMergeSubStack ∗ chainMergeSavedRegs s0.sp s0 ∗ R)

/-! ## 3. `BodyDefs` Predicates on `SP2Ext img.base ext` -/

/-- `SessionRecord::deserialize + off` in `SP2Ext img.base ext`. -/
noncomputable abbrev deserPCAtX (img : Obj.Image)
    (ext : String → Option (State → State)) (off : BitVec 64) : BitVec 64 :=
  (SP2Ext img.base ext).fnAddr recDeserializeName + off

/-- One segment step of the general deserialize on `SP2Ext img.base ext`. -/
abbrev DeserStepGAtX (img : Obj.Image)
    (ext : String → Option (State → State)) (x : DeserializeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (deserializeGenSpecAt img) x R s0 s Q

/-- The field-loop head `+0x254` after `k` of the record's fields on `SP2Ext img.base ext`. -/
def DeserLoopGAtX (img : Obj.Image)
    (ext : String → Option (State → State)) (x : DeserializeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = deserPCAtX img ext 0x254#64 ∧ s.status = .Running ∧
    (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = deserSpL s0.sp ∧ s.spAligned = true ∧ s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
    s.readReg64 .x19 = x.out ∧ s.readReg64 .x20 = 0#64 ∧
    s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
    (s.mem ⊨ deserLocalsG (deserSpL s0.sp) x.p (encodeRecord x.r)
        (((recFields x.r).drop k).flatMap GenField.enc) (ssgAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)

/-! ## 4. Callee Offset Resolution on `SP2Ext` from `chainMergeName` (`0x3974`) -/

theorem bytesMerge_ok_sub_seedChain_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : BytesMergeOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
      (Prost.bytesMergeSpec A img) := by
  have heq : (SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) =
      (SP2Ext img.base ext).fnAddr Prost.bytesMergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact h

theorem int32Merge_ok_sub_seedChain_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : Int32MergeOkX b A ext) :
    subroutine_ok (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
      (Prost.int32MergeSpec A) := by
  have heq : (SP2Ext b ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) =
      (SP2Ext b ext).fnAddr Prost.int32MergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact h

theorem decodeVarintSlice_ok_sub_cme_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DecodeVarintSliceOkX b A ext) :
    subroutine_ok (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))
      (Prost.decodeVarintSliceSpec A) := by
  have heq : (SP2Ext b ext).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") =
      (SP2Ext b ext).fnAddr Prost.decodeVarintSliceName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]
    bv_omega
  rw [heq]; exact h

theorem growOneChain_ok_sub_seedChain_ext {img : Obj.Image}
    {ext : String → Option (State → State)}
    (h : OkAtX img.base ext growOneChainNameX
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage img)) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))
      ((CryptoVerification.LibsignalSession.growOneSpec A0).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr chainMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") =
      (SP2Ext img.base ext).fnAddr growOneChainNameX := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")]
    bv_omega
  rw [heq]; exact h

/-! ## 5. `step_chainMerge_bytesMerge_at_ext` & `step_chainMerge_int32Merge_at_ext` on `SP2Ext` -/

/-- Step a `bl bytes::merge` (`entry + 18446744073709547028#64`) call inside `message::merge<Chain>`
on a `< 128`-byte field `[BitVec.ofNat 8 b.length] ++ b`, on `SP2Ext img.base ext`. -/
theorem step_chainMerge_bytesMerge_at_ext (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hBM : BytesMergeOkX img A0 ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (bs0 b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 32)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = (vecU8 A0 v bs0 ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
      stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        ((vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R)) := by
  have hcall := bytesMerge_ok_sub_seedChain_ext hBM
  rw [hP]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun cap0 => SepWPp.exists_elim fun ptr0 => ?_
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_frozen_seedChain
    (x := BytesMergeGhost.mk .lengthDelimited v cap0 ptr0 bs0 bufRef slot curPtr
      ([BitVec.ofNat 8 b.length] ++ b ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
      (chainMergeSubStack - bytesMergeStack) ∗ F)
    hcall hpc hrun hsp_aligned hF hsym hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_sub_to_bytesMerge_seedChain (sp0 - 256#64)] at hm
    dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2, by omega, bytesMergeCapOk_of_len_lt32 hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec, chainMergeSeedSpec,
      Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hFm hsymm hcsm
    rw [hsp] at hspm
    have hmB := mergeBytes_lt128_seedChain b rest hb
    dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec]
    rw [hmB, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun _ => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    have hlen1 : ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 := by simp
    rw [hlen1] at hcur
    have hv : vecU8At A0 v cap' ptr' b ⊢ vecU8 A0 v b :=
      Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.mono_pre_seedChain ?_ (hnext sm hpcm hrunm hspm hFm hsymm (htrm.trans htr) hcsm hx0m)
    rw [hcur, stackAt_sub_to_bytesMerge_seedChain (sp0 - 256#64)]
    have hEq1 :
        (bufRef ↦₆₄ slot) ∗ emp ∗ stackAt (sp0 - 256#64) bytesMergeStack ∗
          vecU8At A0 v cap' ptr' b ∗
          ((curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest) ∗
          memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
            (chainMergeSubStack - bytesMergeStack) ∗ F =
        vecU8At A0 v cap' ptr' b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
              (chainMergeSubStack - bytesMergeStack) ∗
              stackAt (sp0 - 256#64) bytesMergeStack) ∗ F) := by ac_rfl
    have hEq2 :
        vecU8 A0 v b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
              (chainMergeSubStack - bytesMergeStack) ∗
              stackAt (sp0 - 256#64) bytesMergeStack) ∗ F) =
        (vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
            (chainMergeSubStack - bytesMergeStack) ∗
            stackAt (sp0 - 256#64) bytesMergeStack)) ∗ F := by ac_rfl
    rw [hEq1, ← hEq2]
    exact sepConj_mono_left hv

/-- Step a `bl int32::merge` (`entry + 18446744073709548112#64`) call inside `message::merge<Chain>`
on `pbVarintBody 5 i.toNat ++ rest`, on `SP2Ext img.base ext`. -/
theorem step_chainMerge_int32Merge_at_ext (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hIM : Int32MergeOkX img.base A0 ext)
    (dst bufRef slot curPtr sp0 ret_pc : BitVec 64) (w0 : BitVec 32)
    (i : BitVec 32) (rest : List (BitVec 8))
    (hlen_lt : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 32)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 0#8)
    (hx1 : s.readReg64 .x1 = dst)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = ((dst ↦₃₂ w0) ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr (pbVarintBody 5 i.toNat ++ rest) ∗
      stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R)) := by
  have hcall := int32Merge_ok_sub_seedChain_ext hIM
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_frozen_seedChain
    (x := Int32MergeGhost.mk .varint dst bufRef slot curPtr (pbVarintBody 5 i.toNat ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
      (chainMergeSubStack - int32MergeStack) ∗ F)
    hcall hpc hrun hsp_aligned hF hsym hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_int32Merge_seedChain (sp0 - 256#64)] at hm
    simp only [sepConj_assoc] at hm
    have hcell : (dst ↦₃₂ w0) ⊢ memRegion dst 4 := by
      rw [ProofLib.memRegion_four]
      exact Entails.sepExists_right w0 (Entails.refl _)
    have hm1 := Satisfies.mono (sepConj_mono_left hcell) hm
    dsimp only [int32MergeSpec]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, by omega⟩, ?_⟩
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [int32MergeSpec, chainMergeSeedSpec, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hFm hsymm hcsm
    rw [hsp] at hspm
    have hmI := mergeUint32_pbVarintBody_seedChain i rest
    dsimp only [int32MergeSpec]
    rw [hmI, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr (pbVarintBody 5 i.toNat) rest
    have hGoalEq :
        ((bufRef ↦₆₄ slot) ∗ emp ∗ stackAt (sp0 - 256#64) int32MergeStack ∗
          (dst ↦₃₂ i) ∗
          sliceCursorAfter slot curPtr (pbVarintBody 5 i.toNat ++ rest) rest ∗
          memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
            (chainMergeSubStack - int32MergeStack) ∗ F) =
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F) := by
      rw [hcur, stackAt_sub_to_int32Merge_seedChain (sp0 - 256#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm hFm hsymm (htrm.trans htr) hcsm hx0m

/-! ## 6. X-Stack (`W`-Suffixed) Specifications, Bundles & Helpers on `SP2Ext` -/

/-- Anchor declaration for incremental close checking of the X-stack (`W`) section. -/
theorem DDX_W1 : True := trivial

/-- X-stack budget for `message::merge<Chain>` (`0x3974`): `12288 + 16384 = 28672` (`0x7000`). -/
abbrev chainMergeStackX : Nat := chainMergeStack + 16384

/-- X-stack sub-budget below `chainMerge`'s 256-byte frame: `12032 + 16384 = 28416`. -/
abbrev chainMergeSubStackX : Nat := chainMergeSubStack + 16384

/-- X-stack budget for `SessionStructure::merge_field` (`0x581c`): `16384 + 16384 = 32768` (`0x8000`). -/
abbrev mergeFieldStackX : Nat := mergeFieldStack + 16384

/-- X-stack sub-budget below `merge_field`'s 240-byte frame: `16144 + 16384 = 32528`. -/
abbrev mergeFieldSubStackX : Nat := 32528

/-- `merge_field` (`0x581c`) on one in-scope field, restricted by `P`, at `mergeFieldStackX`,
parameterized by `img`. -/
def mergeFieldGenSpecAtW (img : Obj.Image) (P : GenField → Prop) : Spec MergeFieldGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSGAt A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := Serialization.allocPanic

/-- `message::merge<Chain>` (`0x3974`) on one in-scope chain, into a default chain, at
`chainMergeStackX`, parameterized by `img`. -/
def chainMergeGenSpecAtW (img : Obj.Image) : Spec ChainMergeGenGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = 99#32 ∧ x.c.Ok ∧
      (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostChainGAt A0 x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      stackAt s.sp chainMergeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainGAt A0 x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      stackAt s0.sp chainMergeStackX
  onPanic := Serialization.allocPanic

/-- The X-stack callee contracts needed by `deserialize` and `merge_field` on `SP2Ext img.base ext`,
using the X-stack `*OkW` specs and `Stage1X.GrowOneChainOkX`. -/
def DeserializeCalleesAtW (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Prost.X.DecodeVarintSliceOkW img A0 ext ∧
    CryptoVerification.LibsignalTripleRatchet.Prost.X.Int32MergeOkW img A0 ext ∧
    CryptoVerification.LibsignalTripleRatchet.Prost.X.BytesMergeOkW img A0 ext ∧
    Stage1X.GrowOneChainOkX img A0 ext

/-- General `merge_field` contract restricted by `P` at `mergeFieldStackX`, on `SP2Ext img.base ext`. -/
def MergeFieldGenOkAtW (img : Obj.Image)
    (ext : String → Option (State → State)) (P : GenField → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeFieldGenSpecAtW img P)

/-- General `message::merge<Chain>` contract at `chainMergeStackX`, on `SP2Ext img.base ext`. -/
def ChainMergeGenOkAtW (img : Obj.Image)
    (ext : String → Option (State → State)) : Prop :=
  OkAtX img.base ext chainMergeName (chainMergeGenSpecAtW img)

/-- One segment step of the general chain merge at `chainMergeStackX` on `SP2Ext img.base ext`. -/
abbrev ChainStepGAtW (img : Obj.Image)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (chainMergeGenSpecAtW img) x R s0 s Q

/-- The field-loop head `+0x120` after `k` of the chain's fields at `chainMergeSubStackX` on `SP2Ext img.base ext`. -/
def ChainLoopGAtW (img : Obj.Image)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chainPCAtX img ext 0x120#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = s0.sp - 0x100#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x24 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x21 = 98#64 ∧ s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x25 = s0.sp - 0xf8#64 ∧ s.readReg64 .x26 = 1#64 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
    (s.mem ⊨ prostChainGAt A0 x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0 ∗ R)

/-- One segment step of the general deserialize on `SP2Ext img.base ext` (`recDeserializeStack = 65536` unchanged). -/
abbrev DeserStepGAtW (img : Obj.Image)
    (ext : String → Option (State → State)) (x : DeserializeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (deserializeGenSpecAt img) x R s0 s Q

/-- The field-loop head `+0x254` after `k` of the record's fields on `SP2Ext img.base ext` (`deserCalleeStack = 63632` unchanged). -/
abbrev DeserLoopGAtW (img : Obj.Image)
    (ext : String → Option (State → State)) (x : DeserializeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  DeserLoopGAtX img ext x R s0 k s

/-! ### 6.0b Arbitrary-Allocator (`A : RustAlloc`) `*WA` Specifications & Predicates -/

/-- General `SessionRecord::deserialize` contract carrying `A.pool` and `sessionRecordAt A` (`= sessDeserializeExtSpec DeserializeScope A img` by `rfl`). -/
noncomputable def deserializeGenSpecAtA (A : RustAlloc) (img : Obj.Image) : Spec DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧ s.readReg64 .x1 = BitVec.ofNat 64 (encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScope x.r ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      (x.p ↦ₛ encodeRecord x.r) ∗ memRegion x.out 368 ∗ A.pool ∗ stackAt s.sp recDeserializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗
      (∃∗ g : RecordGhost, ⌜Serialization.CanonRecord g x.r⌝ ∗ sessionRecordAt A x.out g x.r) ∗
      A.pool ∗ stackAt s0.sp recDeserializeStack
  onPanic := Serialization.allocPanic

def deserLocalsGA (A : RustAlloc) (L p : BitVec 64) (bs rest : List (BitVec 8)) (v : SSG) : SepProp :=
  memRegion L 0x3f8 ∗ Prost.sliceCursorAfter (L + 0x3f8#64) p bs rest ∗
    ((L + 0x408#64) ↦₆₄ 0#64) ∗ ((L + 0x410#64) ↦₆₄ 8#64) ∗ ((L + 0x418#64) ↦₆₄ 0#64) ∗
    prostSSGAt A (L + 0x420#64) v ∗ memRegion (L + 0x578#64) 0x170 ∗
    ((L + 0x6e8#64) ↦₆₄ (L + 0x3f8#64)) ∗ memRegion (L + 0x6f0#64) 0x20

@[simp] theorem deserLocalsGA_A0 : deserLocalsGA A0 = deserLocalsG := rfl

def deserOutRecordGA (A : RustAlloc) (out : BitVec 64) (r : SessionRecord (List (BitVec 8))) : SepProp :=
  (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) ∗
    prostSSGAt A (out + 0x18#64) (ssgAfter r (recFields r).length)

@[simp] theorem deserOutRecordGA_A0 : deserOutRecordGA A0 = deserOutRecordG := rfl

def deserOutRawGA (A : RustAlloc) (x : DeserializeGenGhost) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ encodeRecord x.r) ∗ deserOutRecordGA A x.out x.r ∗
    A.pool ∗ stackAt s0.sp recDeserializeStack

def DeserRetGAtA (_img : Obj.Image) (A : RustAlloc) (x : DeserializeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧ (sf.mem ⊨ deserOutRawGA A x s0 sf ∗ R)

def mergeFieldGenSpecAtWA (A : RustAlloc) (img : Obj.Image) (P : GenField → Prop) : Spec MergeFieldGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGAt A x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ A.pool ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSGAt A x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      A.pool ∗ stackAt s0.sp mergeFieldStackX
  onPanic := Serialization.allocPanic

def chainMergeGenSpecAtWA (A : RustAlloc) (img : Obj.Image) : Spec ChainMergeGenGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = 99#32 ∧ x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostChainGAt A x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗ A.pool ∗ stackAt s.sp chainMergeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainGAt A x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      A.pool ∗ stackAt s0.sp chainMergeStackX
  onPanic := Serialization.allocPanic

def DeserializeCalleesAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Prost.X.DecodeVarintSliceOkW img A ext ∧
    CryptoVerification.LibsignalTripleRatchet.Prost.X.Int32MergeOkW img A ext ∧
    CryptoVerification.LibsignalTripleRatchet.Prost.X.BytesMergeOkW img A ext ∧
    Stage1X.GrowOneChainOkX img A ext

@[simp] theorem DeserializeCalleesAtWA_A0 (img : Obj.Image) (ext : String → Option (State → State)) :
    DeserializeCalleesAtWA img A0 ext = DeserializeCalleesAtW img ext := rfl

def MergeFieldGenOkAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (P : GenField → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeFieldGenSpecAtWA A img P)

def ChainMergeGenOkAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  OkAtX img.base ext chainMergeName (chainMergeGenSpecAtWA A img)

abbrev ChainStepGAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (chainMergeGenSpecAtWA A img) x R s0 s Q

def ChainRetGAtWA (img : Obj.Image) (A : RustAlloc) (x : ChainMergeGenGhost) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ (chainMergeGenSpecAtWA A img).post x s0 sf ∗ R)

def ChainLoopGAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chainPCAtX img ext 0x120#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = s0.sp - 0x100#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x24 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x21 = 98#64 ∧ s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x25 = s0.sp - 0xf8#64 ∧ s.readReg64 .x26 = 1#64 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
    (s.mem ⊨ prostChainGAt A x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      A.pool ∗ stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0 ∗ R)

abbrev DeserStepGAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (x : DeserializeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (SP2Ext img.base ext) (deserializeGenSpecAtA A img) x R s0 s Q

def DeserLoopGAtWA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (x : DeserializeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = deserPCAtX img ext 0x254#64 ∧ s.status = .Running ∧
    (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) ∧
    s.symtab = img.symtab ∧ img.FrozenLoaded s ∧
    s.sp = deserSpL s0.sp ∧ s.spAligned = true ∧ s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
    s.readReg64 .x19 = x.out ∧ s.readReg64 .x20 = 0#64 ∧
    s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
    (s.mem ⊨ deserLocalsGA A (deserSpL s0.sp) x.p (encodeRecord x.r)
        (((recFields x.r).drop k).flatMap GenField.enc) (ssgAfter x.r k) ∗
      memRegion x.out 368 ∗ A.pool ∗ stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)

/-- `<alloc::raw_vec::RawVec<Chain>>::grow_one` (`0x15cac`, stride = 104, also used by `Vec<MessageKey>`)
meets `(Stage1X.growOne104SpecX A).inImage img` on `SP2Ext img.base ext` under `Stage1X.AllocContractsX`. -/
theorem grow_one_72_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Stage1X.AllocContractsX img A ext) :
    Stage1X.GrowOneChainOkX img A ext :=
  Stage1X.grow_one_104_ok_ext_x hA

/-! ### 6.1 X-Stack Offset Resolution on `SP2Ext` from `chainMergeName` (`0x3974`) -/

theorem bytesMerge_ok_sub_seedChain_extW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : Prost.X.BytesMergeOkW img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
      (Prost.X.bytesMergeSpecW A img) := by
  have heq : (SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) =
      (SP2Ext img.base ext).fnAddr Prost.bytesMergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact h

theorem int32Merge_ok_sub_seedChain_extW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : Prost.X.Int32MergeOkW img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
      ((Prost.X.int32MergeSpecW A).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) =
      (SP2Ext img.base ext).fnAddr Prost.int32MergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact h

theorem decodeVarintSlice_ok_sub_cme_extW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : Prost.X.DecodeVarintSliceOkW img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))
      ((Prost.X.decodeVarintSliceSpecW A).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr chainMergeName + bv% (ls_off% "prost::encoding::varint::decode_varint_slice" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") =
      (SP2Ext img.base ext).fnAddr Prost.decodeVarintSliceName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]
    bv_omega
  rw [heq]; exact h

theorem growOneChain_ok_sub_seedChain_extW {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : Stage1X.GrowOneChainOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr chainMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))
      ((Stage1X.growOneChainSpecX A).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr chainMergeName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") =
      (SP2Ext img.base ext).fnAddr Stage1X.growOneChainName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"), (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")]
    bv_omega
  rw [heq]; exact h

/-! ### 6.2 X-Stack Split Helpers for `chainMergeStackX` and `chainMergeSubStackX` -/

theorem stackAt_sub_to_bytesMerge_seedChainW (sp : BitVec 64) :
    stackAt sp chainMergeSubStackX =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗
        stackAt sp Prost.X.bytesMergeStackW :=
  stackAt_sub_split_seedChain sp Prost.X.bytesMergeStackW chainMergeSubStackX

theorem stackAt_sub_to_int32Merge_seedChainW (sp : BitVec 64) :
    stackAt sp chainMergeSubStackX =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.int32MergeStackW) ∗
        stackAt sp Prost.X.int32MergeStackW :=
  stackAt_sub_split_seedChain sp Prost.X.int32MergeStackW chainMergeSubStackX

theorem stackAt_sub_to_varintSlice_cmeW (sp : BitVec 64) :
    stackAt sp chainMergeSubStackX =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.decodeVarintSliceStackW) ∗
        stackAt sp Prost.X.decodeVarintSliceStackW :=
  stackAt_sub_split_seedChain sp Prost.X.decodeVarintSliceStackW chainMergeSubStackX

theorem stackAt_sub_to_growOne_seedChainW (sp : BitVec 64) :
    stackAt sp chainMergeSubStackX =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Stage1X.growOneChainStackX) ∗
        stackAt sp Stage1X.growOneChainStackX :=
  stackAt_sub_split_seedChain sp Stage1X.growOneChainStackX chainMergeSubStackX

theorem stackAt_chainMergeStackX_split_seedChain (sp0 : BitVec 64) :
    stackAt sp0 chainMergeStackX =
      stackAt (sp0 - 256#64) chainMergeSubStackX ∗
        memRegion (sp0 - 256#64) 160 ∗
        (∃∗ w96 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64,
         ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64,
         ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
  have heq : chainMergeStackX = 28576 + 8 * 12 := rfl
  have hsub : stackAt (sp0 - 96#64) 28576 =
      stackAt (sp0 - 256#64) chainMergeSubStackX ∗ memRegion (sp0 - 256#64) 160 := by
    dsimp only [stackAt, chainMergeSubStackX, chainMergeSubStack]
    have hsplit := memRegion_split (sp0 - 96#64 - 28576#64) 28416 160 (by decide)
    have h1 : sp0 - 96#64 - BitVec.ofNat 64 28576 = sp0 - 256#64 - 28416#64 := by
      bv_omega
    have h2 : sp0 - 256#64 - 28416#64 + BitVec.ofNat 64 28416 = sp0 - 256#64 := by
      bv_omega
    rw [h1] at hsplit
    rw [show BitVec.ofNat 64 28416 = 28416#64 from rfl, h2] at hsplit
    rw [h1, hsplit]
  have h12 : stackAt sp0 chainMergeStackX =
      stackAt (sp0 - 96#64) 28576 ∗
        (∃∗ w96 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64,
         ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64,
         ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
    rw [heq, LibsignalTripleRatchet.stackAt_split_cells sp0 28576 12 (by decide)]
    have h96 : sp0 - BitVec.ofNat 64 (8 * 12) = sp0 - 96#64 := rfl
    rw [h96]
    congr 1
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit,
      sepExists_sepConj_right]
  rw [h12, hsub, sepConj_assoc]

theorem growOne_inImage_pre_eq_extWA (img : Obj.Image) (A : RustAlloc) (v cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = sp) :
    ((Stage1X.growOneChainSpecX A).inImage img).pre (v, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = v ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool ∗ stackAt sp Stage1X.growOneChainStackX) := by
  unfold Spec.inImage Stage1X.growOneChainSpecX Stage1X.growOne104SpecX; dsimp only
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  have hpure :
      (s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
        max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63) =
      (bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = v ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) :=
    propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩,
             fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩⟩
  rw [hpure, hsp, h0]
  change _ = _ ∗ (_ ∗ _ ∗ _ ∗ _ ∗ stackAt sp (464 + Stage1X.finishGrowStackX))
  simp only [← sepConj_assoc, pure_sepConj_pure]; ac_rfl

theorem growOne_inImage_pre_eq_extW (img : Obj.Image) (v cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = sp) (hbs : bs.length = cap.toNat * 104) :
    ((Stage1X.growOneChainSpecX A0).inImage img).pre (v, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = v ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧ img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ (ptr ↦ₛ bs) ∗ stackAt sp Stage1X.growOneChainStackX) := by
  rw [growOne_inImage_pre_eq_extWA img A0 v cap ptr sp bs s hsp]
  have hpool : A0.pool = emp := rfl; have hlive : A0.live ptr bs.length 8 = emp := rfl
  have hif : (if cap = 0#64 then emp else A0.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) = (ptr ↦ₛ bs) := by
    rw [hlive]; by_cases h0 : cap = 0#64
    · subst h0; simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul] at hbs
      rw [List.eq_nil_of_length_eq_zero hbs, pointsToBytes_nil]; simp
    · simp [h0]
  rw [hif, hpool]; simp only [emp_sepConj]

theorem growOne_post_elim_sp_extWA (img : Obj.Image) (A : RustAlloc) (v cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat) (s_pre sf : State) (hsp : s_pre.sp = sp)
    (hfull : n = cap.toNat) (hbs : bs.length = n * 104)
    (hmax_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63) :
    ((Stage1X.growOneChainSpecX A).inImage img).post (v, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗ ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜n + 1 ≤ cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        (v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ p') ∗ A.live p' (cap'.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗
        A.pool ∗ stackAt sp Stage1X.growOneChainStackX := by
  unfold Spec.inImage Stage1X.growOneChainSpecX Stage1X.growOne104SpecX; dsimp only; rw [hsp]
  apply Entails.pure_left; intro htr; refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  let cap' : BitVec 64 := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  refine Entails.sepExists_right cap' (Entails.sepExists_right p' ?_)
  have hmax_lt64 : max (2 * cap.toNat) 4 < 2 ^ 64 := by omega
  have hcap'_toNat : cap'.toNat = max (2 * cap.toNat) 4 := by
    change (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax_lt64]
  have hcap'_le : n + 1 ≤ cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by omega
  have hlive_eq : A.live p' (max (2 * cap.toNat) 4 * 104) 8 = A.live p' (cap'.toNat * 104) 8 := by
    rw [hcap'_toNat]
  have hmul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = 104 + (cap'.toNat - (n + 1)) * 104 := by omega
  have hsplit := memRegion_split (p' + BitVec.ofNat 64 (n * 104)) 104 ((cap'.toNat - (n + 1)) * 104) (by omega)
  have haddr : p' + BitVec.ofNat 64 (n * 104) + BitVec.ofNat 64 104 = p' + BitVec.ofNat 64 ((n + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [haddr] at hsplit; rw [hlive_eq, hbs, hmul, hsplit]
  apply Entails.pure_left; intro hp'
  refine Entails.pure_right ⟨hcap'_le, hcap'_lt, hp'⟩ (Entails.of_eq (by dsimp only [cap', Stage1X.growOneChainStackX]; ac_rfl))

theorem growOne_post_elim_sp_extW (img : Obj.Image) (v cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat) (s_pre sf : State) (hsp : s_pre.sp = sp)
    (hfull : n = cap.toNat) (hbs : bs.length = n * 104)
    (hmax_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63) :
    ((Stage1X.growOneChainSpecX A0).inImage img).post (v, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗ ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜n + 1 ≤ cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        (v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ p') ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗
        stackAt sp Stage1X.growOneChainStackX := by
  refine Entails.trans (growOne_post_elim_sp_extWA img A0 v cap ptr sp bs n s_pre sf hsp hfull hbs hmax_lt) ?_
  apply Entails.pure_left; intro htr; refine Entails.pure_right htr ?_
  refine Entails.sepExists_elim fun cap' => Entails.sepExists_right cap' (Entails.sepExists_elim fun p' => Entails.sepExists_right p' ?_)
  have hl : A0.live p' (cap'.toNat * 104) 8 = emp := rfl; have hp : A0.pool = emp := rfl
  rw [hl, hp]; simp only [emp_sepConj]; exact Entails.refl _

/-! ### 6.3 `step_chainMerge_bytesMerge_atW[A]` & `step_chainMerge_int32Merge_atW[A]` on `SP2Ext` -/

/-- Step a `bl bytes::merge` call inside `message::merge<Chain>` for arbitrary `(A : RustAlloc)`. -/
theorem step_chainMerge_bytesMerge_atWA (img : Obj.Image) {A : RustAlloc}
    {ext : String → Option (State → State)} (hBM : Prost.X.BytesMergeOkW img A ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (bs0 b rest : List (BitVec 8))
    (hb : b.length < 128) (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = (vecU8 A v bs0 ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
      A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 256#64 → img.FrozenLoaded sm →
      sm.symtab = img.symtab → sm.trace = s0.trace → CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        ((vecU8 A v b ∗ (bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R)) := by
  have hcall := bytesMerge_ok_sub_seedChain_extW hBM
  rw [hP]; unfold vecU8; simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun cap0 => SepWPp.exists_elim fun ptr0 => ?_
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_frozen_seedChain
    (x := BytesMergeGhost.mk .lengthDelimited v cap0 ptr0 bs0 bufRef slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗ F)
    hcall hpc hrun hsp_aligned hF hsym hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_sub_to_bytesMerge_seedChainW (sp0 - 256#64)] at hm
    dsimp only [Prost.X.bytesMergeSpecW, Spec.inImage, Prost.X.bytesMergeRawSpecW]
    rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2, hlen_lt⟩, ?_⟩; convert hm using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [Prost.X.bytesMergeSpecW, Spec.inImage, Prost.X.bytesMergeRawSpecW, chainMergeSeedSpec, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hFm hsymm hcsm
    rw [hsp] at hspm
    dsimp only [Prost.X.bytesMergeSpecW, Spec.inImage, Prost.X.bytesMergeRawSpecW]
    rw [mergeBytes_lt128_seedChain b rest hb, hsp]; dsimp only; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_; simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    rw [show ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 by simp] at hcur
    have hv : vecU8At A v cap' ptr' b ⊢ vecU8 A v b :=
      Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.mono_pre_seedChain ?_ (hnext sm hpcm hrunm hspm hFm hsymm (htrm.trans htr) hcsm hx0m)
    rw [hcur, stackAt_sub_to_bytesMerge_seedChainW (sp0 - 256#64)]
    set tailAtoms : SepProp := (bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
      sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗ A.pool ∗
      (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗
        stackAt (sp0 - 256#64) Prost.X.bytesMergeStackW) ∗ F
    have hEq1 : (bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (sp0 - 256#64) Prost.X.bytesMergeStackW ∗
        vecU8At A v cap' ptr' b ∗ ((curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest) ∗
        memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗ F =
        vecU8At A v cap' ptr' b ∗ tailAtoms := by dsimp only [tailAtoms]; ac_rfl
    have hEq2 : vecU8 A v b ∗ tailAtoms =
        (vecU8 A v b ∗ (bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗ A.pool ∗
          (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗
            stackAt (sp0 - 256#64) Prost.X.bytesMergeStackW)) ∗ F := by dsimp only [tailAtoms]; ac_rfl
    rw [hEq1, ← hEq2]; exact sepConj_mono_left hv

theorem step_chainMerge_bytesMerge_atW (img : Obj.Image) {ext : String → Option (State → State)}
    (hBM : Prost.X.BytesMergeOkW img A0 ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (bs0 b rest : List (BitVec 8))
    (hb : b.length < 128) (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = (vecU8 A0 v bs0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
    (hnext : ∀ (sm : State), sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 256#64 →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s0.trace → CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        ((vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R)) := by
  have hp : A0.pool = emp := rfl
  exact step_chainMerge_bytesMerge_atWA img hBM v bufRef slot curPtr sp0 ret_pc bs0 b rest hb hlen_lt
    hpc hrun hsp halign hF hsym htr hlr hx0 hx1 hx2 (by rw [hp, emp_sepConj]; exact hP)
    (fun sm h1 h2 h3 h4 h5 h6 h7 h8 => by rw [hp, emp_sepConj]; exact hnext sm h1 h2 h3 h4 h5 h6 h7 h8)

/-- Step a `bl int32::merge` call inside `message::merge<Chain>` for arbitrary `(A : RustAlloc)`. -/
theorem step_chainMerge_int32Merge_atWA (img : Obj.Image) {A : RustAlloc}
    {ext : String → Option (State → State)} (hIM : Prost.X.Int32MergeOkW img A ext)
    (dst bufRef slot curPtr sp0 ret_pc : BitVec 64) (w0 i : BitVec 32) (rest : List (BitVec 8))
    (hlen_lt : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 62)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 0#8)
    (hx1 : s.readReg64 .x1 = dst) (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = ((dst ↦₃₂ w0) ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr (pbVarintBody 5 i.toNat ++ rest) ∗
      A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
    (hnext : ∀ (sm : State), sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 256#64 →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s0.trace → CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R)) := by
  have hcall := int32Merge_ok_sub_seedChain_extW hIM
  have hlen_lt63 : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 63 := Nat.lt_trans hlen_lt (by decide)
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_frozen_seedChain
    (x := Int32MergeGhost.mk .varint dst bufRef slot curPtr (pbVarintBody 5 i.toNat ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.int32MergeStackW) ∗ F)
    hcall hpc hrun hsp_aligned hF hsym hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_int32Merge_seedChainW (sp0 - 256#64)] at hm; simp only [sepConj_assoc] at hm
    have hcell : (dst ↦₃₂ w0) ⊢ memRegion dst 4 := by
      rw [ProofLib.memRegion_four]; exact Entails.sepExists_right w0 (Entails.refl _)
    have hm1 := Satisfies.mono (sepConj_mono_left hcell) hm
    dsimp only [Prost.X.int32MergeSpecW, Spec.inImage]; rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2, hlen_lt63⟩, ?_⟩; convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [Prost.X.int32MergeSpecW, Spec.inImage, chainMergeSeedSpec, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hFm hsymm hcsm
    rw [hsp] at hspm; dsimp only [Prost.X.int32MergeSpecW, Spec.inImage]
    rw [mergeUint32_pbVarintBody_seedChain i rest, hsp]; dsimp only; simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_; simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr (pbVarintBody 5 i.toNat) rest
    have hGoalEq :
        ((bufRef ↦₆₄ slot) ∗ A.pool ∗ stackAt (sp0 - 256#64) Prost.X.int32MergeStackW ∗ (dst ↦₃₂ i) ∗
          sliceCursorAfter slot curPtr (pbVarintBody 5 i.toNat ++ rest) rest ∗
          memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX) (chainMergeSubStackX - Prost.X.int32MergeStackW) ∗ F) =
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          A.pool ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) := by
      rw [hcur, stackAt_sub_to_int32Merge_seedChainW (sp0 - 256#64)]; ac_rfl
    rw [hGoalEq]; exact hnext sm hpcm hrunm hspm hFm hsymm (htrm.trans htr) hcsm hx0m

theorem step_chainMerge_int32Merge_atW (img : Obj.Image) {ext : String → Option (State → State)}
    (hIM : Prost.X.Int32MergeOkW img A0 ext)
    (dst bufRef slot curPtr sp0 ret_pc : BitVec 64) (w0 i : BitVec 32) (rest : List (BitVec 8))
    (hlen_lt : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 62)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr chainMergeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 256#64) (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 0#8)
    (hx1 : s.readReg64 .x1 = dst) (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = ((dst ↦₃₂ w0) ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAt slot curPtr (pbVarintBody 5 i.toNat ++ rest) ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
    (hnext : ∀ (sm : State), sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 256#64 →
      img.FrozenLoaded sm → sm.symtab = img.symtab → sm.trace = s0.trace → CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (SP2Ext img.base ext) ret sm
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗ (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗ stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R)) := by
  have hp : A0.pool = emp := rfl
  exact step_chainMerge_int32Merge_atWA img hIM dst bufRef slot curPtr sp0 ret_pc w0 i rest hlen_lt
    hpc hrun hsp halign hF hsym htr hlr hx0 hx1 hx2 (by rw [hp, emp_sepConj]; exact hP)
    (fun sm h1 h2 h3 h4 h5 h6 h7 h8 => by rw [hp, emp_sepConj]; exact hnext sm h1 h2 h3 h4 h5 h6 h7 h8)

/-! ## 64-bit length comparison helpers at `< 2 ^ 62` -/

theorem cbz_len_cons_false_seedChain62 {b0 : BitVec 8} {bs1 : List (BitVec 8)}
    (hlen : (b0 :: bs1).length < 2 ^ 62) :
    (BitVec.ofNat 64 (b0 :: bs1).length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have h1 := congrArg BitVec.toNat h
  simp only [List.length_cons, BitVec.toNat_ofNat] at hlen h1
  omega

theorem ult_ofNat_add_left_false_seedChain62 {m k : Nat} (hlt : m + k < 2 ^ 62) :
    (BitVec.ofNat 64 (m + k)).ult (BitVec.ofNat 64 m) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem ule_ofNat_add_right_true_seedChain62 {m k : Nat} (hlt : m + k < 2 ^ 62) :
    (BitVec.ofNat 64 m).ule (BitVec.ofNat 64 (m + k)) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : m + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : m < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem ule_ofNat_of_gt_false_seedChain62 {n k : Nat} (hgt : k < n) (hlt : n < 2 ^ 62) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 k) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem ult_ofNat_of_gt_true_seedChain62 {n k : Nat} (hgt : k < n) (hlt : n < 2 ^ 62) :
    (BitVec.ofNat 64 k).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem ult_10_of_gt_cme62 {n : Nat} (hgt : 10 < n) (hlt : n < 2 ^ 62) :
    (10#64).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem ule_10_of_gt_false_cme62 {n : Nat} (hgt : 10 < n) (hlt : n < 2 ^ 62) :
    (BitVec.ofNat 64 n).ule 10#64 = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem encodeVarint_ge128_cons_cme62 {n : Nat} (hge : 128 ≤ n) (hlt : n < 2 ^ 62) :
    ∃ vtail : List (BitVec 8),
      LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 n) =
        BitVec.ofNat 8 (n % 128 + 128) :: vtail := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnlt : ¬ (BitVec.ofNat 64 n).toNat < 0x80 := by omega
  refine ⟨LibsignalProtoCodec.encodeVarintAux 9 (BitVec.ofNat 64 n >>> 7), ?_⟩
  unfold LibsignalProtoCodec.encodeVarint LibsignalProtoCodec.encodeVarintAux
  simp only [hnlt, ↓reduceIte]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := n % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  have hand : (BitVec.ofNat 64 n &&& 0x7F).toNat = n % 128 := by
    rw [BitVec.toNat_and, htoNat, show (0x7F : BitVec 64).toNat = 127 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod n 7
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, hand,
    show (0x80 : BitVec 64).toNat = 128 from rfl, Nat.or_comm, ← hor, BitVec.toNat_ofNat]
  omega

/-! ## 7. Relocatable `[LibsignalPlacement]` Definitions & Helpers -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

/-- Anchor declaration for incremental close checking of the `Placed` section. -/
theorem DDX_Placed : True := trivial

/-- Image-free base contract of `SessionStructure::merge_field` (block `15`) on one in-scope field
restricted by `P`, at `mergeFieldStackX`. -/
def mergeFieldGenRawSpecW (P : GenField → Prop) : Spec MergeFieldGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      prostSSGAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostSSGAt A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := Serialization.allocPanic

/-- Relocatable `[LibsignalPlacement]` contract of `SessionStructure::merge_field` (block `15`) at
`mergeFieldStackX`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
abbrev mergeFieldGenPlacedSpecW [LibsignalPlacement] (P : GenField → Prop) :
    Spec MergeFieldGenGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (mergeFieldGenRawSpecW P)

/-- Image-free base contract of `message::merge<Chain>` (block `11`) on one in-scope chain, into a
default chain, at `chainMergeStackX`. -/
def chainMergeGenRawSpecW : Spec ChainMergeGenGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      (s.readReg64 .x3).setWidth 32 = 99#32 ∧ x.c.Ok ∧
      (x.c.payload ++ x.tail).length < 2 ^ 62⌝ ∗
      prostChainGAt A0 x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      stackAt s.sp chainMergeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗ prostChainGAt A0 x.a x.c ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      stackAt s0.sp chainMergeStackX
  onPanic := Serialization.allocPanic

/-- Relocatable `[LibsignalPlacement]` contract of `message::merge<Chain>` (block `11`) at
`chainMergeStackX`, carrying `LibsignalCodeRoLoaded lsmpl`. -/
abbrev chainMergeGenPlacedSpecW [LibsignalPlacement] : Spec ChainMergeGenGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl chainMergeGenRawSpecW

/-- Image-free base contract of `SessionRecord::deserialize` (block `46`) on a general record
(`DeserializeScope`). -/
noncomputable def deserializeGenRawSpec : Spec DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧
      s.readReg64 .x1 = BitVec.ofNat 64 (CryptoVerification.E2E.Record.encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScope x.r⌝ ∗
      (x.p ↦ₛ CryptoVerification.E2E.Record.encodeRecord x.r) ∗
      memRegion x.out 368 ∗ stackAt s.sp recDeserializeStack
  post := deserializeGenSpec.post
  onPanic := Serialization.allocPanic

/-- Relocatable `[LibsignalPlacement]` contract of `SessionRecord::deserialize` (block `46`) on a
general record (`DeserializeScope`), carrying `LibsignalCodeRoLoaded lsmpl`. -/
noncomputable abbrev deserializeGenPlacedSpec [LibsignalPlacement] : Spec DeserializeGenGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl deserializeGenRawSpec

/-- Relocatable `[LibsignalPlacement]` X-stack callee bundle for `deserialize` and `merge_field`. -/
def DeserializeCalleesPlacedW [LibsignalPlacement] (H : LibsignalHooks) : Prop :=
  Prost.X.DecodeVarintSlicePlacedOkW A0 H ∧
    Prost.X.Int32MergePlacedOkW A0 H ∧
    Prost.X.BytesMergePlacedOkW A0 H ∧
    Stage1X.GrowOneChainPlacedOkX A0 H

/-- Relocatable general `merge_field` (block `15`) contract restricted by `P` at `mergeFieldStackX`. -/
def MergeFieldGenPlacedOkW [LibsignalPlacement] (H : LibsignalHooks) (P : GenField → Prop) : Prop :=
  subroutine_ok (lsProg_15 H) (blkPl_15).base (mergeFieldGenPlacedSpecW P)

/-- Relocatable general `message::merge<Chain>` (block `11`) contract at `chainMergeStackX`. -/
def ChainMergeGenPlacedOkW [LibsignalPlacement] (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_11 H) (blkPl_11).base chainMergeGenPlacedSpecW

/-- `message::merge<Chain> + off` at block `11`'s base address `(blkPl_11).base + off`. -/
abbrev chainPlacedPC [LibsignalPlacement] (off : BitVec 64) : BitVec 64 :=
  (blkPl_11).base + off

/-- One segment step of the relocatable general chain merge at `chainMergeStackX` on `lsProg_11 H`. -/
abbrev ChainStepGPlacedW [LibsignalPlacement] (H : LibsignalHooks) (x : ChainMergeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (lsProg_11 H) chainMergeGenPlacedSpecW x R s0 s Q

/-- The field-loop head `(blkPl_11).base + 0x120` after `k` of the chain's fields at
`chainMergeSubStackX`, carrying `LibsignalCodeRoLoaded lsmpl s.mem`. -/
def ChainLoopGPlacedW [LibsignalPlacement] (x : ChainMergeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chainPlacedPC 0x120#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    LibsignalCodeRoLoaded lsmpl s.mem ∧
    s.sp = s0.sp - 0x100#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x60#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x24 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x21 = 98#64 ∧ s.readReg64 .x22 = 97#64 ∧
    s.readReg64 .x25 = s0.sp - 0xf8#64 ∧ s.readReg64 .x26 = 1#64 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
    (s.mem ⊨ prostChainGAt A0 x.a (chainGAfter x.c k) ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗ chainMergeSavedRegs s0.sp s0 ∗ R)

/-- One segment step of the relocatable general deserialize on `lsProg_46 H`. -/
abbrev DeserStepGPlacedW [LibsignalPlacement] (H : LibsignalHooks) (x : DeserializeGenGhost)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (lsProg_46 H) deserializeGenPlacedSpec x R s0 s Q

/-- The field-loop head `(blkPl_46).base + 0x254` after `k` of the record's fields under
`[LibsignalPlacement]`, carrying `LibsignalCodeRoLoaded lsmpl s.mem`. -/
def DeserLoopGPlacedW [LibsignalPlacement] (x : DeserializeGenGhost)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = deserPlacedPC 0x254#64 ∧ s.status = .Running ∧
    (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) ∧
    LibsignalCodeRoLoaded lsmpl s.mem ∧
    s.sp = deserSpL s0.sp ∧ s.spAligned = true ∧ s.readReg64 .x29 = deserSpL s0.sp + 0x710#64 ∧
    s.readReg64 .x19 = x.out ∧ s.readReg64 .x20 = 0#64 ∧
    s.readReg64 .x23 = deserSpL s0.sp + 0x408#64 ∧
    (s.mem ⊨ deserLocalsG (deserSpL s0.sp) x.p (encodeRecord x.r)
        (((recFields x.r).drop k).flatMap GenField.enc) (ssgAfter x.r k) ∗
      memRegion x.out 368 ∗ stackAt (deserSpL s0.sp) deserCalleeStack ∗ deserSaved s0 ∗ R)

/-! ### 7.1 Cross-Block Callee Transfers into `lsProg_11 H` (`message::merge<Chain>`) -/

theorem bytesMerge_placed_ok_sub_seedChainW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h : Prost.X.BytesMergePlacedOkW A H) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 7) (Prost.X.bytesMergePlacedSpecW A) :=
  ls_call_ro_of_block (callerProg := lsProg_11 H) h

theorem int32Merge_placed_ok_sub_seedChainW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h : Prost.X.Int32MergePlacedOkW A H) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 8)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.int32MergeSpecW A)) :=
  ls_call_ro_of_cl (callerProg := lsProg_11 H) h

theorem decodeVarintSlice_placed_ok_sub_cmeW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h : Prost.X.DecodeVarintSlicePlacedOkW A H) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 76)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.X.decodeVarintSliceSpecW A)) :=
  ls_call_ro_of_cl (callerProg := lsProg_11 H) h

theorem growOneChain_placed_ok_sub_seedChainW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h : Stage1X.GrowOneChainPlacedOkX A H) :
    subroutine_ok (lsProg_11 H) (lsmpl.base 43)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Stage1X.growOneChainSpecX A)) :=
  ls_call_ro_of_cl (callerProg := lsProg_11 H) h

theorem growOne_placed_pre_eq_extW (v cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = sp) (hbs : bs.length = cap.toNat * 104) :
    (Stage1X.growOneChainSpecX A0).pre (v, cap, ptr, bs) s =
    ⌜bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = v ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63⌝ ∗
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ (ptr ↦ₛ bs) ∗ stackAt sp Stage1X.growOneChainStackX) := by
  unfold Stage1X.growOneChainSpecX Stage1X.growOne104SpecX; dsimp only
  have hpool : A0.pool = emp := rfl
  have hlive : A0.live ptr bs.length 8 = emp := rfl
  have hif : (if cap = 0 then emp else A0.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) = (ptr ↦ₛ bs) := by
    rw [hlive]; change (if cap = 0#64 then emp else emp ∗ (ptr ↦ₛ bs)) = (ptr ↦ₛ bs)
    by_cases h0 : cap = 0#64
    · subst h0; simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul] at hbs
      rw [List.eq_nil_of_length_eq_zero hbs, pointsToBytes_nil]; simp
    · simp [h0]
  have hpure :
      (s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
        max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63) =
      (bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = v ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) :=
    propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩,
             fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩⟩
  rw [hpure, hpool, hif, hsp]
  change _ = _ ∗ (_ ∗ _ ∗ _ ∗ stackAt sp (464 + Stage1X.finishGrowStackX))
  simp only [emp_sepConj, ← sepConj_assoc]

theorem growOne_placed_post_elim_sp_extW (v cap ptr sp : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat) (s_pre sf : State) (hsp : s_pre.sp = sp)
    (hfull : n = cap.toNat) (hbs : bs.length = n * 104)
    (hmax_lt : max (2 * cap.toNat) 4 * 104 < 2 ^ 63) :
    (Stage1X.growOneChainSpecX A0).post (v, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗ ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜n + 1 ≤ cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        (v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ p') ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 (n * 104)) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((n + 1) * 104)) ((cap'.toNat - (n + 1)) * 104) ∗
        stackAt sp Stage1X.growOneChainStackX := by
  unfold Stage1X.growOneChainSpecX Stage1X.growOne104SpecX; dsimp only; rw [hsp]
  apply Entails.pure_left; intro htr; refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  let cap' : BitVec 64 := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  refine Entails.sepExists_right cap' (Entails.sepExists_right p' ?_)
  have hmax_lt64 : max (2 * cap.toNat) 4 < 2 ^ 64 := by omega
  have hcap'_toNat : cap'.toNat = max (2 * cap.toNat) 4 := by
    change (BitVec.ofNat 64 (max (2 * cap.toNat) 4)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax_lt64]
  have hcap'_le : n + 1 ≤ cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by omega
  have hlive : A0.live p' (max (2 * cap.toNat) 4 * 104) 8 = emp := rfl
  have hpool : A0.pool = emp := rfl
  have hmul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = 104 + (cap'.toNat - (n + 1)) * 104 := by omega
  have hsplit := memRegion_split (p' + BitVec.ofNat 64 (n * 104)) 104 ((cap'.toNat - (n + 1)) * 104) (by omega)
  have haddr : p' + BitVec.ofNat 64 (n * 104) + BitVec.ofNat 64 104 = p' + BitVec.ofNat 64 ((n + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [haddr] at hsplit; rw [hlive, hpool, hbs, hmul, hsplit]; simp only [emp_sepConj]
  apply Entails.pure_left; intro hp'
  refine Entails.pure_right ⟨hcap'_le, hcap'_lt, hp'⟩ (Entails.of_eq (by dsimp only [cap', Stage1X.growOneChainStackX]; ac_rfl))

/-! ### 7.2 `step_chainMerge_bytesMerge_placedW` & `step_chainMerge_int32Merge_placedW` on `lsProg_11 H` -/

/-- Step a `bl bytes::merge` (`lsmpl.base 7`) call inside `message::merge<Chain>` (`lsProg_11 H`)
on a `< 128`-byte field `[BitVec.ofNat 8 b.length] ++ b`, at `chainMergeSubStackX`. -/
theorem step_chainMerge_bytesMerge_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hBM : Prost.X.BytesMergePlacedOkW A0 H)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (bs0 b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {α : Type} {x : α} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 7)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = (vecU8 A0 v bs0 ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
      stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_11 H) ret sm
        ((vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall := bytesMerge_placed_ok_sub_seedChainW hBM
  rw [hP]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun cap0 => SepWPp.exists_elim fun ptr0 => ?_
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_lscro
    (x := BytesMergeGhost.mk .lengthDelimited v cap0 ptr0 bs0 bufRef slot curPtr
      ([BitVec.ofNat 8 b.length] ++ b ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
      (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗ F)
    hcall hpc hrun hsp_aligned hcrl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_sub_to_bytesMerge_seedChainW (sp0 - 256#64)] at hm
    dsimp only [Prost.X.bytesMergeRawSpecW]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [Prost.X.bytesMergeRawSpecW, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcrlm hcsm
    rw [hsp] at hspm
    have hmB := mergeBytes_lt128_seedChain b rest hb
    dsimp only [Prost.X.bytesMergeRawSpecW]
    rw [hmB, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    have hlen1 : ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 := by simp
    rw [hlen1] at hcur
    have hv : vecU8At A0 v cap' ptr' b ⊢ vecU8 A0 v b :=
      Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.mono_pre_seedChain ?_ (hnext sm hpcm hrunm hspm hcrlm (htrm.trans htr) hcsm hx0m)
    rw [hcur, stackAt_sub_to_bytesMerge_seedChainW (sp0 - 256#64)]
    have hEq1 :
        (bufRef ↦₆₄ slot) ∗ emp ∗ stackAt (sp0 - 256#64) Prost.X.bytesMergeStackW ∗
          vecU8At A0 v cap' ptr' b ∗
          ((curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest) ∗
          memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
            (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗ F =
        vecU8At A0 v cap' ptr' b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
              (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗
              stackAt (sp0 - 256#64) Prost.X.bytesMergeStackW) ∗ F) := by ac_rfl
    have hEq2 :
        vecU8 A0 v b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
              (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗
              stackAt (sp0 - 256#64) Prost.X.bytesMergeStackW) ∗ F) =
        (vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
            (chainMergeSubStackX - Prost.X.bytesMergeStackW) ∗
            stackAt (sp0 - 256#64) Prost.X.bytesMergeStackW)) ∗ F := by ac_rfl
    rw [hEq1, ← hEq2]
    exact sepConj_mono_left hv

/-- Step a `bl int32::merge` (`lsmpl.base 8`) call inside `message::merge<Chain>` (`lsProg_11 H`)
on `pbVarintBody 5 i.toNat ++ rest`, at `chainMergeSubStackX`. -/
theorem step_chainMerge_int32Merge_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hIM : Prost.X.Int32MergePlacedOkW A0 H)
    (dst bufRef slot curPtr sp0 ret_pc : BitVec 64) (w0 : BitVec 32)
    (i : BitVec 32) (rest : List (BitVec 8))
    (hlen_lt : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 62)
    {α : Type} {x : α} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 8)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 0#8)
    (hx1 : s.readReg64 .x1 = dst)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = ((dst ↦₃₂ w0) ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr (pbVarintBody 5 i.toNat ++ rest) ∗
      stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_11 H) ret sm
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall := int32Merge_placed_ok_sub_seedChainW hIM
  have hlen_lt63 : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 63 :=
    Nat.lt_trans hlen_lt (by decide)
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_lscro
    (x := Int32MergeGhost.mk .varint dst bufRef slot curPtr (pbVarintBody 5 i.toNat ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
      (chainMergeSubStackX - Prost.X.int32MergeStackW) ∗ F)
    hcall hpc hrun hsp_aligned hcrl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_int32Merge_seedChainW (sp0 - 256#64)] at hm
    simp only [sepConj_assoc] at hm
    have hcell : (dst ↦₃₂ w0) ⊢ memRegion dst 4 := by
      rw [ProofLib.memRegion_four]
      exact Entails.sepExists_right w0 (Entails.refl _)
    have hm1 := Satisfies.mono (sepConj_mono_left hcell) hm
    dsimp only [Prost.X.int32MergeSpecW]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen_lt63⟩, ?_⟩
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [Prost.X.int32MergeSpecW, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcrlm hcsm
    rw [hsp] at hspm
    have hmI := mergeUint32_pbVarintBody_seedChain i rest
    dsimp only [Prost.X.int32MergeSpecW]
    rw [hmI, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr (pbVarintBody 5 i.toNat) rest
    have hGoalEq :
        ((bufRef ↦₆₄ slot) ∗ emp ∗ stackAt (sp0 - 256#64) Prost.X.int32MergeStackW ∗
          (dst ↦₃₂ i) ∗
          sliceCursorAfter slot curPtr (pbVarintBody 5 i.toNat ++ rest) rest ∗
          memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStackX)
            (chainMergeSubStackX - Prost.X.int32MergeStackW) ∗ F) =
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F) := by
      rw [hcur, stackAt_sub_to_int32Merge_seedChainW (sp0 - 256#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm hcrlm (htrm.trans htr) hcsm hx0m

end Placed

end Proofs.libsignal.Hooks2
