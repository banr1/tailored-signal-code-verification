/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.GrowOneSpecs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefs
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneSysrootExt
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# Helpers for `SessionRecord::archive_current_state_inner`

Callee contracts at `serializeSubStackX`, general byte and heap decompositions of the 336 tail bytes
of `SessionStructure` around `pending_pre_key` (`+0xf8`) and `pending_kyber_pre_key` (`+0x128`), and
stack/`previous_sessions` buffer layouts for both `prevCap = 0` (`grow_one`) and `prevCap ≠ 0`
(in-place slot-`0` store).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
open CryptoVerification.LibsignalSpqrV1 (growOneVecU8Name growOneVecU8Spec GrowOneCall newCapVecU8)
open CryptoVerification.SpqrV1.Prost.MessageMerge (memRegion_split_24_cells)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Callee Offsets and Lifted Contracts -/

theorem libsignalSessionCode_fnOff_archive :
    libsignalSessionCode.fnOff archiveCurrentStateInnerName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner") := by
  exact (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")

theorem libsignalSessionCode_fnOff_promote :
    libsignalSessionCode.fnOff promoteStateName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state") := by
  exact (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_state")

theorem archive_rel_fnAddrX (b : BitVec 64) (ext : String → Option (State → State))
    (name : String) (k : BitVec 64)
    (hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff archiveCurrentStateInnerName) + k =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff name)) :
    (SP2Ext b ext).fnAddr archiveCurrentStateInnerName + k = (SP2Ext b ext).fnAddr name := by
  simp only [SP2Ext, Program.fnAddr_rebase]
  rw [BitVec.add_assoc, hk]

/-- Transfer a contract at `serialize + k` to `archive + k'` when both name the same callee. -/
theorem sub_ok_serialize_to_archiveX {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {spec : Spec α} (k k' : BitVec 64) (name : String)
    (hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff serializeName) + k =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff name))
    (hk' : BitVec.ofNat 64 (libsignalSessionCode.fnOff archiveCurrentStateInnerName) + k' =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff name))
    (h : subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr serializeName + k) spec) :
    subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr archiveCurrentStateInnerName + k') spec := by
  rw [archive_rel_fnAddrX b ext name k' hk']
  rwa [serialize_rel_fnAddrX b ext name k hk] at h

theorem sessionLen_arch_okX (A : RustAlloc) (b : BitVec 64)
    (ext : String → Option (State → State)) :
    subroutine_ok (SP2Ext b ext)
      ((SP2Ext b ext).fnAddr archiveCurrentStateInnerName +
        bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      (sessionLenSubSpecX A) :=
  sub_ok_serialize_to_archiveX _ _ sessionLenName
    (by rw [libsignalSessionCode_fnOff_serialize, libsignalSessionCode_fnOff_sessionLen]; rfl)
    (by rw [libsignalSessionCode_fnOff_archive, libsignalSessionCode_fnOff_sessionLen]; rfl)
    (sessionLen_sub_okX A b ext)

theorem encodeRaw_arch_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hRaw : EncodeRawOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName +
        bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") -
          (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")))
      ((encodeRawSubSpecX A).inImage img) :=
  sub_ok_serialize_to_archiveX _ _ encodeRawName
    (by rw [libsignalSessionCode_fnOff_serialize, libsignalSessionCode_fnOff_encodeRaw]; rfl)
    (by rw [libsignalSessionCode_fnOff_archive, libsignalSessionCode_fnOff_encodeRaw]; rfl)
    (encodeRaw_sub_okX hRaw)

theorem dropLocal1_arch_okX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hDrop : DropSessionStructureLocal1OkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") -
          (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")))
      ((dropLocal1SubSpecX A).inImage img) :=
  sub_ok_serialize_to_archiveX _ _ FromRecordCallees.dropSessionStructureLocal1Name
    (by rw [libsignalSessionCode_fnOff_serialize, libsignalSessionCode_fnOff_dropLocal1]; rfl)
    (by rw [libsignalSessionCode_fnOff_archive, libsignalSessionCode_fnOff_dropLocal1]; rfl)
    (dropLocal1_sub_okX hDrop)

theorem alloc_arch_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName +
        bv% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      ((rustAllocSubSpecX A).inImage img) := by
  have halloc := hC.alloc.alloc_ok_at archiveCurrentStateInnerName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    (by simp only [libsignalSessionCode_fnOff_archive, arm64_norm])
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Proofs.libsignal.Stage1X.extHookStack))
    halloc
    (fun ⟨size, align⟩ s0 => ?_)
    (fun ⟨size, align⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [rustAllocSubSpecX, Proofs.libsignal.Stage1X.rustAllocSpecWithStack,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [rustAllocSubSpecX, Proofs.libsignal.Stage1X.rustAllocSpecWithStack,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

/-- `__rust_dealloc` lifted to the callee stack budget `serializeSubStackX`. -/
def rustDeallocSubSpecX (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧
      (s.readReg64 .x2).toNat = align ∧ LayoutOk size align⌝ ∗
      A.live p size align ∗ memRegion p size ∗ A.pool ∗ stackAt s.sp serializeSubStackX
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp serializeSubStackX

theorem dealloc_arch_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      ((rustDeallocSubSpecX A).inImage img) := by
  have hdealloc := hC.alloc.dealloc_ok_at (name := archiveCurrentStateInnerName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    (by simp only [libsignalSessionCode_fnOff_archive, arm64_norm])
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Proofs.libsignal.Stage1X.extHookStack))
    hdealloc
    (fun ⟨p, size, align⟩ s0 => ?_)
    (fun ⟨p, size, align⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [rustDeallocSubSpecX, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [rustDeallocSubSpecX, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem shim_arch_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      (shimSubSpecX.inImage img) := by
  have hshim := hC.alloc.shim_ok_at archiveCurrentStateInnerName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    (by simp only [libsignalSessionCode_fnOff_archive, arm64_norm])
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Proofs.libsignal.Stage1X.extHookStack))
    hshim
    (fun _ s0 => ?_)
    (fun _ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [shimSubSpecX, Proofs.libsignal.Stage1X.session2ShimSpecX, sessionShimSpec,
      Spec.withHookStack, emp_sepConj,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [shimSubSpecX, Proofs.libsignal.Stage1X.session2ShimSpecX, sessionShimSpec,
      Spec.withHookStack,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem memcpy_arch_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName +
        bv% (ls_off% "memcpy" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      (memcpySubSpecX.inImage img) := by
  have hmemcpy := hC.memcpy_ok_at archiveCurrentStateInnerName
    (num% (ls_off% "memcpy" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    (by simp only [libsignalSessionCode_fnOff_archive, arm64_norm])
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - CryptoVerification.LibsignalTripleRatchet.extHookStack))
    hmemcpy
    (fun ⟨dst, src, bs⟩ s0 => ?_)
    (fun ⟨dst, src, bs⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [memcpySubSpecX, sessionMemcpySpec, libcMemcpySpec,
      stackAt_serializeSub_splitX s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [memcpySubSpecX, sessionMemcpySpec,
      stackAt_serializeSub_splitX s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

/-- `RawVec<Vec<u8>>::grow_one` (`growOneVecU8Spec`) lifted to `serializeSubStackX`. -/
def growOneSubSpecX (A : RustAlloc) : Spec GrowOneCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * 24 ∧ x.ptr ≠ 0 ∧
      max (2 * x.cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 8 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool ∗ stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0 ∧ p'.toNat % 8 = 0⌝ ∗
        (x.v ↦₆₄ newCapVecU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * x.cap.toNat) 4 * 24) 8 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) ((max (2 * x.cap.toNat) 4 - x.cap.toNat) * 24)) ∗
      A.pool ∗ stackAt s0.sp serializeSubStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem growOne_arch_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName +
        bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      ((growOneSubSpecX A).inImage img) := by
  have hfn_fg :
      libsignalSessionCode.fnOff CryptoVerification.SpqrV1.Alloc.finishGrowLibstdName =
        num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")
  have hshim0 := hA.shim_ok_at CryptoVerification.SpqrV1.Alloc.finishGrowLibstdName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]"))
    (by simp only [hfn_fg, arm64_norm])
  have hshim : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.SpqrV1.Alloc.finishGrowLibstdName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")))
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv
        (CryptoVerification.SpqrV1.Alloc.session2ShimSpecWithStack
          CryptoVerification.LibsignalTripleRatchet.extHookStack) (some img)) := by
    refine subroutine_ok_inImage_map' hshim0 fun _ R s0 hpre => ⟨(), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.SpqrV1.Alloc.session2ShimSpecWithStack,
        Proofs.libsignal.Stage1X.session2ShimSpecX, sessionShimSpec, Spec.withHookStack,
        emp_sepConj, CryptoVerification.LibsignalTripleRatchet.extHookStack,
        Proofs.libsignal.Stage1X.extHookStack] at hpre ⊢
      exact hpre
    · simp only [CryptoVerification.SpqrV1.Alloc.session2ShimSpecWithStack,
        Proofs.libsignal.Stage1X.session2ShimSpecX, sessionShimSpec, Spec.withHookStack,
        emp_sepConj, sepConj_assoc,
        CryptoVerification.LibsignalTripleRatchet.extHookStack,
        Proofs.libsignal.Stage1X.extHookStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  have halloc0 := hA.alloc_ok_at CryptoVerification.SpqrV1.Alloc.finishGrowLibstdName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]"))
    (by simp only [hfn_fg, arm64_norm])
  have halloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.SpqrV1.Alloc.finishGrowLibstdName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")))
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv
        (CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack A
          CryptoVerification.LibsignalTripleRatchet.extHookStack) (some img)) := by
    refine subroutine_ok_inImage_map' halloc0 fun ⟨size, align⟩ R s0 hpre =>
      ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.extHookStack,
        Proofs.libsignal.Stage1X.extHookStack] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.extHookStack,
        Proofs.libsignal.Stage1X.extHookStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  have hrealloc0 := hA.realloc_ok_at CryptoVerification.SpqrV1.Alloc.finishGrowLibstdName
    (num% (ls_off% "__rustc::__rust_realloc" -
      ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]"))
    (by simp only [hfn_fg, arm64_norm])
  have hrealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.SpqrV1.Alloc.finishGrowLibstdName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [libstd]")))
      (CryptoVerification.SpqrV1.Alloc.Spec.withOptInv
        (CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack A
          CryptoVerification.LibsignalTripleRatchet.extHookStack) (some img)) := by
    refine subroutine_ok_inImage_map' hrealloc0 fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre =>
      ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.extHookStack,
        Proofs.libsignal.Stage1X.extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2⟩, hmem⟩ := hpre
      exact ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, hlay_old, hlay_new⟩,
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.rustReallocSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.extHookStack,
        Proofs.libsignal.Stage1X.extHookStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  have hbs0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      ((CryptoVerification.SpqrV1.Alloc.growOneVecU8BsSpecWithStack A
        CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
    CryptoVerification.SpqrV1.Alloc.growOneVecU8_bs_opt_ok (A := A) (b := img.base) (ext := ext)
      (hookStack := CryptoVerification.LibsignalTripleRatchet.extHookStack) (img? := some img)
      (by decide)
      (CryptoVerification.SpqrV1.Alloc.finish_grow_libstd_opt_ok (A := A) (b := img.base)
        (ext := ext) (hookStack := CryptoVerification.LibsignalTripleRatchet.extHookStack)
        (img? := some img) (by decide) hshim halloc hrealloc)
  have hg0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      ((CryptoVerification.SpqrV1.Alloc.growOneVecU8Stack32kSpec A).inImage img) := by
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
    let Frame : SepProp := memRegion (s0.sp - 32768#64) 16272
    have hstack : stackAt s0.sp 32768 =
        Frame ∗ stackAt s0.sp ((CryptoVerification.LibsignalTripleRatchet.extHookStack + 48) + 64) :=
      ProofLib.stackAt_split_bottom s0.sp
        ((CryptoVerification.LibsignalTripleRatchet.extHookStack + 48) + 64) 16272 (by decide)
    dsimp only [Spec.inImage] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hinv, hpre0⟩
    simp only [CryptoVerification.SpqrV1.Alloc.growOneVecU8Stack32kSpec, BitVec.ofNat_eq_ofNat,
      sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨⟨hx0, hlen, hptr, hbound⟩, hmem⟩
    have hpre' : s0.mem ⊨
        ((CryptoVerification.SpqrV1.Alloc.growOneVecU8BsSpecWithStack A
          CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img).pre
          (x.v, x.cap, x.ptr, x.bs) s0 ∗ (Frame ∗ R) := by
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hinv, ?_⟩
      simp only [CryptoVerification.SpqrV1.Alloc.growOneVecU8BsSpecWithStack, sepConj_assoc,
        satisfies_pure_sepConj]
      refine ⟨⟨hx0, Nat.le_of_eq hlen, hptr, hbound⟩, ?_⟩
      rw [hstack] at hmem
      by_cases hcap0 : x.cap = 0#64
      · simp only [hcap0, ite_true] at hmem ⊢
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
      · simp only [hcap0, ite_false, ← hlen, Nat.sub_self, memRegion_zero, sepConj_emp,
          sepConj_assoc] at hmem ⊢
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    refine hbs0.mono_outcome (x.v, x.cap, x.ptr, x.bs) (Frame ∗ R) s0 hpc hrun hpre' hsp
      fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      have hsub_mul : (max (2 * x.cap.toNat) 4 - x.cap.toNat) * 24 =
          max (2 * x.cap.toNat) 4 * 24 - x.bs.length := by
        rw [Nat.sub_mul, hlen]
      dsimp only [Spec.inImage, CryptoVerification.SpqrV1.Alloc.growOneVecU8BsSpecWithStack,
        CryptoVerification.SpqrV1.Alloc.growOneVecU8Stack32kSpec, newCapVecU8] at hq ⊢
      rw [hstack, hsub_mul]
      simp only [BitVec.ofNat_eq_ofNat] at hq ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq
    · refine Or.inr (Or.inl ⟨hp_st, ?_⟩)
      dsimp only [Spec.inImage, CryptoVerification.SpqrV1.Alloc.growOneVecU8BsSpecWithStack,
        CryptoVerification.SpqrV1.Alloc.growOneVecU8Stack32kSpec] at hq ⊢
      exact allowPanic_frame id (by rwa [sepConj_assoc])
    · exact False.elim (allowPanic_not_exited hq)
    · exact False.elim (allowPanic_not_exited hq)
  have hg : subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr archiveCurrentStateInnerName +
        bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
      ((CryptoVerification.SpqrV1.Alloc.growOneVecU8Stack32kSpec A).inImage img) := by
    rw [archive_rel_fnAddrX img.base ext growOneVecU8Name _
      (by rw [libsignalSessionCode_fnOff_archive,
        (ls_lemma% fnOff "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")]; rfl)]
    exact hg0
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - 32768))
    hg
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [growOneSubSpecX, CryptoVerification.SpqrV1.Alloc.growOneVecU8Stack32kSpec,
      stackAt_serializeSub_splitX s0.sp 32768 (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [growOneSubSpecX, CryptoVerification.SpqrV1.Alloc.growOneVecU8Stack32kSpec,
      stackAt_serializeSub_splitX s0.sp 32768 (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem archive_panic_at_handle_errorX {b : BitVec 64} {ext : String → Option (State → State)} :
    (SP2Ext b ext).externAt?
      ((SP2Ext b ext).fnAddr archiveCurrentStateInnerName +
        bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")) =
      some Rust.panicked := by
  exact panic_at_panicSymbol_ext (b := b) (ext := ext)
    (name := archiveCurrentStateInnerName) (hname := "alloc::raw_vec::handle_error")
    (k := num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"))
    (stub := num% (ls_off% "alloc::raw_vec::handle_error"))
    libsignalSessionCode_fnOff_archive (by simp only [arm64_norm]) (by decide)
    (ls_hook% "alloc::raw_vec::handle_error")
    (by simp [Rust.isPanicSymbol])

/-! ## General `pending` and `kyber` Byte and Heap Decomposition -/

/-- First 64-bit word (`noneCap` or `g.vec.cap`) of an `OptTailVecInline` representation. -/
def optTailCap : Option TailVecGhost → BitVec 64
  | none => noneCap
  | some g => g.vec.cap

/-- Deallocation obligation for a niche-tagged `Option<TailVecGhost>` whose first two words are
`(cap, ptr)`: when `cap <ₛ 1` (`noneCap = -1` or `cap = 0`), nothing is freed; otherwise
`1 ≤ cap < 2^63` and `__rust_dealloc(ptr, cap, 1)` frees the owned buffer. -/
def tailPinDealloc (A : RustAlloc) (cap ptr : BitVec 64) : SepProp :=
  if cap.slt 1#64 = true then emp
  else ⌜1 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat

theorem noneCap_eq_lit : noneCap = 0xffffffffffffffff#64 := rfl

private theorem cap_pos_of_ne_zero {cap : BitVec 64} (hne : cap ≠ 0#64) : 1 ≤ cap.toNat := by
  by_contra h0
  apply hne
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  omega

private theorem slt_one_eq_false_of_pos_lt {cap : BitVec 64}
    (hne : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    cap.slt 1#64 = false ∧ 1 ≤ cap.toNat := by
  have hpos : 1 ≤ cap.toNat := cap_pos_of_ne_zero hne
  refine ⟨?_, hpos⟩
  rw [Bool.eq_false_iff]
  intro hslt
  rw [BitVec.slt_iff_toInt_lt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at hslt
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hslt
  omega

/-- Decompose `OptTailVecInline size opt bs` (`24 ≤ size`) and `optTailVecHeap A opt` around its
first two 64-bit words `(optTailCap opt, ptr)`, proving that overwriting `cap` with `noneCap`
yields `OptTailVecInline size none` and that `optTailVecHeap A opt` entails
`tailPinDealloc A (optTailCap opt) ptr`. -/
theorem optTailVec_split_inline_heap (A : RustAlloc) (size : Nat) (hsz : 24 ≤ size)
    (opt : Option TailVecGhost) {bs : List (BitVec 8)}
    (hlen : bs.length = size) (hinl : OptTailVecInline size opt bs) :
    ∃ (ptr : BitVec 64) (rest : List (BitVec 8)),
      rest.length = size - 16 ∧
      bs = unpack64 (optTailCap opt) ++ unpack64 ptr ++ rest ∧
      OptTailVecInline size none (unpack64 0xffffffffffffffff#64 ++ unpack64 ptr ++ rest) ∧
      (optTailVecHeap A opt ⊢ tailPinDealloc A (optTailCap opt) ptr) := by
  cases opt with
  | none =>
    rcases hinl with ⟨pad, hpad_len, rfl⟩
    have htake : (pad.take 8).length = 8 := by simp [hpad_len]; omega
    obtain ⟨ptr, hptr_eq⟩ := exists_unpack64_of_length_8 htake
    have hdrop_len : (pad.drop 8).length = size - 16 := by simp [hpad_len]; omega
    have hpad_split : pad = unpack64 ptr ++ pad.drop 8 := by
      rw [← hptr_eq, List.take_append_drop]
    refine ⟨ptr, pad.drop 8, hdrop_len, ?_, ?_, ?_⟩
    · simp only [optTailCap]
      conv => lhs; rw [hpad_split]
      rw [List.append_assoc]
    · refine ⟨unpack64 ptr ++ pad.drop 8, ?_, ?_⟩
      · simp [hdrop_len]; omega
      · simp [noneCap_eq_lit, List.append_assoc]
    · have hslt : noneCap.slt 1#64 = true := by decide
      simp [optTailCap, optTailVecHeap, tailPinDealloc, hslt]
      exact Entails.refl _
  | some g =>
    rcases hinl with ⟨htail_len, rfl⟩
    let rest := unpack64 (BitVec.ofNat 64 g.vec.bytes.length) ++ g.tail
    have hrest_len : rest.length = size - 16 := by
      simp [rest, htail_len]; omega
    refine ⟨g.vec.ptr, rest, hrest_len, ?_, ?_, ?_⟩
    · simp [optTailCap, vecGhostHeaderBytes, vecHeaderBytes, rest, List.append_assoc]
    · refine ⟨unpack64 g.vec.ptr ++ rest, ?_, ?_⟩
      · simp [hrest_len]; omega
      · simp [noneCap_eq_lit, List.append_assoc]
    · unfold optTailCap optTailVecHeap vecGhostHeap RustHeap.vecU8Buf
      apply Entails.pure_left; rintro ⟨hb_le, hcap_lt, hptr_ne⟩
      by_cases hc : g.vec.cap = 0#64
      · have hc0 : g.vec.cap = 0 := hc
        have hslt0 : (0 : BitVec 64).slt 1#64 = true := by decide
        simp only [hc0, tailPinDealloc, hslt0, ↓reduceIte]
        exact Entails.refl _
      · obtain ⟨hslt, hpos⟩ := slt_one_eq_false_of_pos_lt hc hcap_lt
        have hc0 : ¬ (g.vec.cap = 0) := hc
        simp only [hc0, tailPinDealloc, hslt, Bool.false_eq_true, ↓reduceIte]
        refine Entails.pure_right ⟨hpos, hcap_lt⟩ ?_
        refine sepConj_mono_right ?_
        have hcap_split : g.vec.cap.toNat = g.vec.bytes.length + (g.vec.cap.toNat - g.vec.bytes.length) := by
          omega
        conv => rhs; rw [hcap_split]
        rw [memRegion_split g.vec.ptr g.vec.bytes.length (g.vec.cap.toNat - g.vec.bytes.length)
          (by omega)]
        exact sepConj_mono_left (pointsToBytes_entails_memRegion g.vec.ptr g.vec.bytes)

theorem sessionPure_clearPending {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hp : SessionPure G st) :
    SessionPure (clearPendingGhost G) { st with pendingPreKey := false } := by
  rcases hp with ⟨h1, h2, h3, _, h5, h6, h7⟩
  exact ⟨h1, h2, h3, rfl, h5, h6, h7⟩

/-- General decomposition of the 336 tail bytes of `sessionStateReprAt` around both pending pre-key slots
(`+0xf8` and `+0x128`), together with the cleared `SessionInline` and `sessionAtHeap` transition. -/
theorem bs336_split_gen (A : RustAlloc) {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {bs336 : List (BitVec 8)}
    (hinl : SessionInline G sess.state (unpack64 G.localIk.cap ++ bs336)) :
    ∃ (a : List (BitVec 8)) (pPtr : BitVec 64) (pRest : List (BitVec 8))
      (kPtr : BitVec 64) (kTail : List (BitVec 8)),
      a.length = 240 ∧ pRest.length = 32 ∧ kTail.length = 32 ∧
      bs336 = a ++ unpack64 (optTailCap G.pending) ++ unpack64 pPtr ++ pRest ++
        unpack64 (optTailCap G.kyber) ++ unpack64 kPtr ++ kTail ∧
      SessionInline (clearPendingGhost G) (clearPending sess).state
        (unpack64 G.localIk.cap ++
          (a ++ unpack64 0xffffffffffffffff#64 ++ unpack64 pPtr ++ pRest ++
            unpack64 0xffffffffffffffff#64 ++ unpack64 kPtr ++ kTail)) ∧
      (sessionAtHeap A G sess ⊢
        sessionAtHeap A (clearPendingGhost G) (clearPending sess) ∗
          tailPinDealloc A (optTailCap G.pending) pPtr ∗
          tailPinDealloc A (optTailCap G.kyber) kPtr) := by
  obtain ⟨hreg, scBs, pendBs, kybBs, hsc, hsci, hpl, hpi, hkl, hki, hbs⟩ := hinl
  obtain ⟨pPtr, pRest, hpRest, hpend_eq, hpi_none, hp_heap⟩ :=
    optTailVec_split_inline_heap A 48 (by decide) G.pending hpl hpi
  obtain ⟨kPtr, kRest, hkRest, hkyb_eq, hki_none, hk_heap⟩ :=
    optTailVec_split_inline_heap A 32 (by decide) G.kyber hkl hki
  have hP := sessionPrefixBytes_length G sess.state
  have hS : (sessionSuffixBytes G sess.state).length = 16 := by
    simp [sessionSuffixBytes, hreg]
  let a := (sessionPrefixBytes G sess.state).drop 8 ++ scBs
  let kTail := kRest ++ sessionSuffixBytes G sess.state
  have ha_len : a.length = 240 := by simp [a, hP, hsc]
  have hkTail_len : kTail.length = 32 := by simp [kTail, hkRest, hS]
  have hbs336_eq : bs336 = a ++ unpack64 (optTailCap G.pending) ++ unpack64 pPtr ++ pRest ++
      unpack64 (optTailCap G.kyber) ++ unpack64 kPtr ++ kTail := by
    have h8 := congrArg (List.drop 8) hbs
    rw [List.drop_left' (unpack64_length G.localIk.cap)] at h8
    rw [h8, hpend_eq, hkyb_eq]
    simp only [a, kTail, List.append_assoc]
    rw [List.drop_append_of_le_length (by omega)]
  refine ⟨a, pPtr, pRest, kPtr, kTail, ha_len, hpRest, hkTail_len,
    hbs336_eq, ?_, ?_⟩
  · refine ⟨hreg, scBs,
      unpack64 0xffffffffffffffff#64 ++ unpack64 pPtr ++ pRest,
      unpack64 0xffffffffffffffff#64 ++ unpack64 kPtr ++ kRest,
      hsc, hsci,
      by simp [hpRest], hpi_none,
      by simp [hkRest], hki_none, ?_⟩
    have hpref_take : (sessionPrefixBytes G sess.state).take 8 = unpack64 G.localIk.cap := by
      unfold sessionPrefixBytes vecGhostHeaderBytes vecHeaderBytes
      simp only [List.append_assoc]
      exact List.take_left' (unpack64_length G.localIk.cap)
    have hpref_eq : unpack64 G.localIk.cap ++ (sessionPrefixBytes G sess.state).drop 8 =
        sessionPrefixBytes (clearPendingGhost G) (clearPending sess).state := by
      change unpack64 G.localIk.cap ++ (sessionPrefixBytes G sess.state).drop 8 =
        sessionPrefixBytes G sess.state
      rw [← hpref_take, List.take_append_drop]
    have hsuf_eq : sessionSuffixBytes G sess.state =
        sessionSuffixBytes (clearPendingGhost G) (clearPending sess).state := rfl
    simp only [a, kTail, ← List.append_assoc]
    rw [hpref_eq, hsuf_eq]
  · unfold sessionAtHeap sessionHeap
    apply Entails.pure_left; rintro ⟨_, _, halice, hremReg, hlocReg⟩
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpure
    have hpure' : SessionPure (clearPendingGhost G) (clearPending sess).state :=
      sessionPure_clearPending hpure
    have hrel' : PendingRel (clearPendingGhost G).pending (clearPending sess).pendingPreKey ∧
        KyberRel (clearPendingGhost G).kyber (clearPending sess).pendingKyberPreKey ∧
        (clearPendingGhost G).alice.bytes = (clearPending sess).aliceBaseKey ∧
        (clearPendingGhost G).regIds.take 4 = leBytes 4 (clearPending sess).remoteRegistrationId.toNat ∧
        ((clearPendingGhost G).regIds.drop 4).take 4 =
          leBytes 4 (clearPending sess).localRegistrationId.toNat :=
      ⟨trivial, trivial, halice, hremReg, hlocReg⟩
    have hpull1 :
        vecGhostHeap A G.localIk ∗ vecGhostHeap A G.remoteIk ∗
          vecU8Buf A G.root.cap G.root.ptr (keyToBytes32 sess.state.rootKey) ∗
          vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr
            (G.chains.zip sess.state.receiverChains) ∗
          vecGhostHeap A G.alice ∗
          vecU8Buf A G.pq.cap G.pq.ptr sess.state.pqRatchetState ∗
          optSenderChainHeap A G.sender sess.state.senderChain ∗
          optTailVecHeap A G.pending ∗ optTailVecHeap A G.kyber =
        (vecGhostHeap A G.localIk ∗ vecGhostHeap A G.remoteIk ∗
          vecU8Buf A G.root.cap G.root.ptr (keyToBytes32 sess.state.rootKey) ∗
          vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr
            (G.chains.zip sess.state.receiverChains) ∗
          vecGhostHeap A G.alice ∗
          vecU8Buf A G.pq.cap G.pq.ptr sess.state.pqRatchetState ∗
          optSenderChainHeap A G.sender sess.state.senderChain) ∗
          (optTailVecHeap A G.pending ∗ optTailVecHeap A G.kyber) := by
      ac_rfl
    rw [hpull1]
    refine Entails.trans (sepConj_mono_right (sepConj_mono hp_heap hk_heap)) ?_
    simp only [clearPendingGhost, clearPending, optTailVecHeap, sepConj_emp]
    exact sepConj_mono_left
      (Entails.pure_right hpure' (Entails.pure_right hrel' (Entails.of_eq (by ac_rfl))))

/-- Unpack `sessionStateReprAt A (r + 0x18#64) G s` into its head word at `r + 0x18#64`, its 336 tail bytes
at `r + 0x20#64`, and `sessionAtHeap A G s` (with NO pending-none assumption). -/
theorem sessionAt_unpack_rec_genX (A : RustAlloc) (r : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) :
    sessionStateReprAt A (r + 0x18#64) G s ⊢
      ∃∗ bs336 : List (BitVec 8),
        ⌜bs336.length = 336 ∧ G.localIk.cap.toNat < 2 ^ 63 ∧
          SessionInline G s.state (unpack64 G.localIk.cap ++ bs336)⌝ ∗
        ((r + 0x18#64) ↦₆₄ G.localIk.cap) ∗ ((r + 0x20#64) ↦ₛ bs336) ∗ sessionAtHeap A G s := by
  have h := sessionAt_unpack_head_tail A (r + 0x18#64) G s
  have e : r + 0x18#64 + 8#64 = r + 0x20#64 := by rw [BitVec.add_assoc]; rfl
  rwa [e] at h

/-- Split the 336 copied tail bytes at `sp - 448` around the `(cap, ptr)` words of both pending
pre-key slots (`sp - 208`, `sp - 200` and `sp - 160`, `sp - 152`). -/
theorem bytes448_split_genX (sp : BitVec 64) (a pRest kTail : List (BitVec 8))
    (pCap pPtr kCap kPtr : BitVec 64) (ha : a.length = 240) (hpRest : pRest.length = 32) :
    ((sp - 448#64) ↦ₛ (a ++ unpack64 pCap ++ unpack64 pPtr ++ pRest ++
        unpack64 kCap ++ unpack64 kPtr ++ kTail)) =
      (((sp - 448#64) ↦ₛ a) ∗
        ((sp - 208#64) ↦₆₄ pCap) ∗ ((sp - 200#64) ↦₆₄ pPtr) ∗ ((sp - 192#64) ↦ₛ pRest) ∗
        ((sp - 160#64) ↦₆₄ kCap) ∗ ((sp - 152#64) ↦₆₄ kPtr) ∗ ((sp - 144#64) ↦ₛ kTail)) := by
  simp only [List.append_assoc]
  rw [pointsToBytes_append, ha,
    pointsToBytes_append, unpack64_length,
    pointsToBytes_append, unpack64_length,
    pointsToBytes_append, hpRest,
    pointsToBytes_append, unpack64_length,
    pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  have e1 : sp - 448#64 + BitVec.ofNat 64 240 = sp - 208#64 := bv_sub_add_lit sp 448 240
  have e2 : sp - 208#64 + BitVec.ofNat 64 8 = sp - 200#64 := bv_sub_add_lit sp 208 8
  have e3 : sp - 200#64 + BitVec.ofNat 64 8 = sp - 192#64 := bv_sub_add_lit sp 200 8
  have e4 : sp - 192#64 + BitVec.ofNat 64 32 = sp - 160#64 := bv_sub_add_lit sp 192 32
  have e5 : sp - 160#64 + BitVec.ofNat 64 8 = sp - 152#64 := bv_sub_add_lit sp 160 8
  have e6 : sp - 152#64 + BitVec.ofNat 64 8 = sp - 144#64 := bv_sub_add_lit sp 152 8
  rw [e1, e2, e3, e4, e5, e6]

/-- Pack the stack copy at `sp - 456` with cleared niches back into
`sessionStateReprAt A (sp - 456#64) (clearPendingGhost G) (clearPending sess)`. -/
theorem sessionAt_pack_456_clearX (A : RustAlloc) (sp : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    {a pRest kTail : List (BitVec 8)} {pPtr kPtr : BitVec 64}
    (ha : a.length = 240) (hpRest : pRest.length = 32)
    (hinl' : SessionInline (clearPendingGhost G) (clearPending sess).state
      (unpack64 G.localIk.cap ++
        (a ++ unpack64 0xffffffffffffffff#64 ++ unpack64 pPtr ++ pRest ++
          unpack64 0xffffffffffffffff#64 ++ unpack64 kPtr ++ kTail))) :
    (((sp - 456#64) ↦₆₄ G.localIk.cap) ∗
      ((sp - 448#64) ↦ₛ a) ∗
      ((sp - 208#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((sp - 200#64) ↦₆₄ pPtr) ∗
      ((sp - 192#64) ↦ₛ pRest) ∗
      ((sp - 160#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((sp - 152#64) ↦₆₄ kPtr) ∗
      ((sp - 144#64) ↦ₛ kTail) ∗
      sessionAtHeap A (clearPendingGhost G) (clearPending sess)) ⊢
      sessionStateReprAt A (sp - 456#64) (clearPendingGhost G) (clearPending sess) := by
  have hpack := sessionAt_pack_head_tail A (sp - 456#64) (clearPendingGhost G) (clearPending sess) hinl'
  have e : sp - 456#64 + 8#64 = sp - 448#64 := bv_sub_add_lit sp 456 8
  rw [e] at hpack
  refine Entails.trans ?_ hpack
  rw [bytes448_split_genX sp a pRest kTail 0xffffffffffffffff#64 pPtr 0xffffffffffffffff#64 kPtr ha hpRest]
  exact Entails.of_eq (by ac_rfl)

/-! ## Stack Frame and `previous_sessions` Shapes -/

theorem encSessionMem_length_pos (G : SessionGhost) (s : Session (List (BitVec 8))) :
    0 < (encSessionMem G s).length := by
  have hk : (HMAC.keyToBytes32 s.state.rootKey).length = 32 := by simp [HMAC.keyToBytes32]
  have hne : HMAC.keyToBytes32 s.state.rootKey ≠ [] := by
    intro h; rw [h] at hk; simp at hk
  simp only [encSessionMem, bytesField, hne, ↓reduceIte, lenField, List.length_append]
  omega

/-- The archive stack: callee budget `serializeSubStackX`, 8 unused bytes at `sp - 464`, the
`SessionStructure` copy's first word and tail (`sp - 456`, `sp - 448`), 16 bytes at `sp - 112`,
and 12 cells (`sp - 96 .. sp - 8`). -/
theorem stackAt_archive_preX (sp : BitVec 64) :
    stackAt sp archiveStackX =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        stackAt (sp - 464#64) serializeSubStackX ∗
        memRegion (sp - 464#64) 8 ∗
        memRegion (sp - 456#64) 8 ∗
        memRegion (sp - 448#64) 336 ∗
        memRegion (sp - 112#64) 16 ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  have hbase : stackAt sp archiveStackX =
      stackAt (sp - 464#64) serializeSubStackX ∗ memRegion (sp - 464#64) 8 ∗
        memRegion (sp - 456#64) 8 ∗ memRegion (sp - 448#64) 336 ∗
        memRegion (sp - 112#64) 16 ∗ cells (sp - 96#64) 12 := by
    have h1 := LibsignalTripleRatchet.stackAt_split_cells sp (serializeSubStackX + 368) 12
      (by decide)
    rw [show serializeSubStackX + 368 + 8 * 12 = archiveStackX by decide] at h1
    have h2 : stackAt (sp - 96#64) (serializeSubStackX + 368) =
        memRegion (sp - 464#64) 368 ∗ stackAt (sp - 464#64) serializeSubStackX := by
      simp only [stackAt]
      have hsplit := memRegion_split (sp - 96#64 - BitVec.ofNat 64 (serializeSubStackX + 368))
        serializeSubStackX 368 (by decide)
      have e1 : sp - 96#64 - BitVec.ofNat 64 (serializeSubStackX + 368) =
          sp - 464#64 - BitVec.ofNat 64 serializeSubStackX := by
        rw [BitVec.sub_sub, BitVec.ofNat_add, ← BitVec.add_assoc,
          show (96#64 + BitVec.ofNat 64 serializeSubStackX + 368#64 : BitVec 64) =
            464#64 + BitVec.ofNat 64 serializeSubStackX by bv_omega,
          ← BitVec.sub_sub]
      have e2 : sp - 464#64 - BitVec.ofNat 64 serializeSubStackX +
          BitVec.ofNat 64 serializeSubStackX = sp - 464#64 := BitVec.sub_add_cancel _ _
      rw [e1, e2] at hsplit
      rw [e1, hsplit, sepConj_comm]
    have h3 : memRegion (sp - 464#64) 368 =
        memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 8 ∗
          memRegion (sp - 448#64) 336 ∗ memRegion (sp - 112#64) 16 := by
      have s1 := memRegion_split (sp - 464#64) 8 360 (by decide)
      have s2 := memRegion_split (sp - 456#64) 8 352 (by decide)
      have s3 := memRegion_split (sp - 448#64) 336 16 (by decide)
      have e1 : sp - 464#64 + BitVec.ofNat 64 8 = sp - 456#64 := bv_sub_add_lit sp 464 8
      have e2 : sp - 456#64 + BitVec.ofNat 64 8 = sp - 448#64 := bv_sub_add_lit sp 456 8
      have e3 : sp - 448#64 + BitVec.ofNat 64 336 = sp - 112#64 := bv_sub_add_lit sp 448 336
      rw [e1] at s1; rw [e2] at s2; rw [e3] at s3
      rw [s1, s2, s3]
    rw [h1, h2, h3]
    ac_rfl
  rw [hbase, cells_12_eq sp]
  simp only [sepExists_sepConj_right]

/-- The encode buffer `Vec<u8>` at `sp - 88` after `__rust_alloc(n, 1)` returned `p`. -/
theorem vecU8At_nil_88X (A : RustAlloc) (sp p : BitVec 64) (n : Nat)
    (hpos : 0 < n) (hlt : n < 2 ^ 63) (hp : p ≠ 0) :
    (((sp - 88#64) ↦₆₄ BitVec.ofNat 64 n) ∗ ((sp - 80#64) ↦₆₄ p) ∗ ((sp - 72#64) ↦₆₄ 0#64) ∗
      A.live p n 1 ∗ memRegion p n) ⊢
      vecU8At A (sp - 88#64) (BitVec.ofNat 64 n) p [] := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne : BitVec.ofNat 64 n ≠ (0 : BitVec 64) := by
    intro h; have := congrArg BitVec.toNat h; rw [htoNat] at this; simp at this; omega
  have e8 : sp - 88#64 + 8#64 = sp - 80#64 := bv_sub_add_lit sp 88 8
  have e16 : sp - 88#64 + 16#64 = sp - 72#64 := bv_sub_add_lit sp 88 16
  unfold vecU8At vecHeader
  rw [e8, e16]
  simp only [List.length_nil, htoNat, pointsToBytes_nil, BitVec.add_zero,
    Nat.sub_zero, BitVec.ofNat_eq_ofNat, emp_sepConj, sepConj_assoc]
  have hne0 : ¬ (BitVec.ofNat 64 n = 0#64) := hne
  simp only [hne0, ↓reduceIte]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  exact Entails.pure_right ⟨Nat.zero_le _, hlt, hp⟩ (Entails.refl _)

/-- `vecU8At` at `sp - 88` as three cells and its buffer. -/
theorem vecU8At_unpack_88X (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp - 88#64) cap ptr bs =
      (((sp - 88#64) ↦₆₄ cap) ∗ ((sp - 80#64) ↦₆₄ ptr) ∗
        ((sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs) := by
  have e8 : sp - 88#64 + 8#64 = sp - 80#64 := bv_sub_add_lit sp 88 8
  have e16 : sp - 88#64 + 16#64 = sp - 72#64 := bv_sub_add_lit sp 88 16
  unfold vecU8At RustHeap.vecU8Buf vecHeader
  rw [e8, e16]
  ac_rfl

theorem memRegion_344_to_456X (sp : BitVec 64) :
    memRegion (sp - 456#64) 344 ⊢
      ∃∗ v : BitVec 64, ((sp - 456#64) ↦₆₄ v) ∗ memRegion (sp - 448#64) 336 := by
  rw [show (344 : Nat) = 8 + 336 by rfl, memRegion_split _ 8 336 (by decide),
    ProofLib.memRegion_eight]
  have e : sp - 456#64 + BitVec.ofNat 64 8 = sp - 448#64 := bv_sub_add_lit sp 456 8
  rw [e, sepExists_sepConj_left]
  exact Entails.refl _

theorem cell112_splitX (sp : BitVec 64) (v : BitVec 128) :
    ((sp - 112#64) ↦₁₂₈ v) ⊢
      ∃∗ lo : BitVec 64, ∃∗ hi : BitVec 64, ((sp - 112#64) ↦₆₄ lo) ∗ ((sp - 104#64) ↦₆₄ hi) := by
  have h : memRegion (sp - 112#64) 16 =
      ∃∗ lo : BitVec 64, ∃∗ hi : BitVec 64, ((sp - 112#64) ↦₆₄ lo) ∗ ((sp - 104#64) ↦₆₄ hi) := by
    have e : sp - 112#64 + BitVec.ofNat 64 8 = sp - 104#64 := bv_sub_add_lit sp 112 8
    rw [show (16 : Nat) = 8 + 8 by rfl, memRegion_split _ 8 8 (by decide), e,
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, sepExists_sepConj_left]
    simp only [sepExists_sepConj_right]
  rw [← h, ProofLib.memRegion_sixteen]
  exact Entails.sepExists_intro v

theorem cell112_packX (sp lo hi : BitVec 64) :
    (((sp - 112#64) ↦₆₄ lo) ∗ ((sp - 104#64) ↦₆₄ hi)) ⊢ ((sp - 112#64) ↦₁₂₈ (hi ++ lo)) :=
  Entails.of_eq (pointsTo64_pair_sub sp 112 lo hi)

theorem vecU8_from_cellsX (A : RustAlloc) (q cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    ((q ↦₆₄ cap) ∗ ((q + 8#64) ↦₆₄ ptr) ∗ ((q + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      RustHeap.vecU8Buf A cap ptr bs) ⊢ vecU8 A q bs := by
  unfold vecU8 vecU8At RustHeap.vecU8Buf vecHeader
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

theorem newCapVecU8_zeroX : newCapVecU8 0#64 = 4#64 := by
  decide

/-- Split `memRegion q (cap.toNat * 24)` (`cap ≠ 0#64`) into slot 0's three 64-bit cells and the
remaining `(cap.toNat - 1) * 24` bytes at `q + 24#64`. -/
theorem memRegion_prev_slot0_cells (q cap : BitVec 64) (hcap : cap ≠ 0#64)
    (hbound : cap.toNat * 24 < 2 ^ 63) :
    memRegion q (cap.toNat * 24) =
      (∃∗ c2 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c0 : BitVec 64,
        (q ↦₆₄ c0) ∗ ((q + 8#64) ↦₆₄ c1) ∗ ((q + 16#64) ↦₆₄ c2)) ∗
      memRegion (q + 24#64) ((cap.toNat - 1) * 24) := by
  have hpos : 0 < cap.toNat := cap_pos_of_ne_zero hcap
  have h := memRegion_split_24_cells q 0 cap.toNat hpos hbound
  simpa only [Nat.zero_mul, Nat.sub_zero, Nat.zero_add, Nat.one_mul,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h

/-- Pack the 3 record header cells and slot-0 `vecU8` into `prevVecAt A r cap q [enc]` for any
nonzero capacity `cap`. -/
theorem prevVecAt_one_of_parts (A : RustAlloc) (r cap q : BitVec 64) (enc : List (BitVec 8))
    (hcap : cap ≠ 0#64) (hbound : cap.toNat * 24 < 2 ^ 63) (hq : q ≠ 0#64) :
    ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
      A.live q (cap.toNat * 24) 8 ∗ vecU8 A q enc ∗
      memRegion (q + 24#64) ((cap.toNat - 1) * 24)) ⊢
      prevVecAt A r cap q [enc] := by
  have hpos : 1 ≤ cap.toNat := cap_pos_of_ne_zero hcap
  rw [prevVecAt_one_eq A r cap q enc hcap, hdrP_eq]
  have hpull :
      ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64)) ∗
        ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q (cap.toNat * 24) 8 ∗ vecU8 A q enc ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) =
      ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
          A.live q (cap.toNat * 24) 8 ∗ vecU8 A q enc ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) := by
    ac_rfl
  rw [hpull]
  exact Entails.pure_right ⟨hpos, hbound, hq⟩ (Entails.refl _)

/-! ## Relocatable `[LibsignalPlacement]` Callee Contracts (Block `51`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed Proofs.libsignal.Hooks2
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
  (subroutine_ok_withLsCodeLoaded_of_withLsCl stackAt_serializeSub_splitX)

theorem L1_ArchiveAux_Placed : True := trivial

/-- Relocatable `__rust_dealloc` contract lifted to `serializeSubStackX`. -/
theorem dealloc_arch_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustDeallocSubSpecX A)) := by
  have hdealloc := subroutine_ok_withLsCodeLoaded_of_withLsCl
    (hC.alloc.dealloc (callerProg := callerProg))
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Proofs.libsignal.Stage1X.extHookStack))
    hdealloc
    (fun ⟨p, size, align⟩ s0 => ?_)
    (fun ⟨p, size, align⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [rustDeallocSubSpecX, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [rustDeallocSubSpecX, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack,
      stackAt_serializeSub_splitX s0.sp Proofs.libsignal.Stage1X.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

/-- Relocatable `RawVec<Vec<u8>>::grow_one` contract lifted from `withLsCl` at `extHookStack`
to `withLsCodeLoaded` at `serializeSubStackX`. -/
theorem growOne_arch_placed_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hGrow : subroutine_ok callerProg (lsmpl.base 621)
      (withLsCl lsmpl (growOneVecU8Spec A))) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCodeLoaded lsmpl (growOneSubSpecX A)) := by
  have hg : subroutine_ok callerProg (lsmpl.base 621)
      (withLsCodeLoaded lsmpl (growOneVecU8Spec A)) :=
    subroutine_ok_withLsCodeLoaded_of_withLsCl hGrow
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - CryptoVerification.LibsignalTripleRatchet.extHookStack))
    hg
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [growOneSubSpecX, growOneVecU8Spec,
      stackAt_serializeSub_splitX s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [growOneSubSpecX, growOneVecU8Spec,
      stackAt_serializeSub_splitX s0.sp CryptoVerification.LibsignalTripleRatchet.extHookStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

end Placed

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
