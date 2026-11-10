/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymE
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerializeLenExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SessionLenExt
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `SessionRecord::serialize`: Callee Stack Budget and Lifted Sub-Specs

Defines the callee stack budget `serializeSubStackX` below the 800-byte frame of
`SessionRecord::serialize` (`0x1857c`, Block `52`) and lifts every callee contract (`vecVecClone`,
`sessionLen`, `sessionClone`, `encode_varint`, `encode_raw`, drop glue, `__rust_alloc`, `shim`, and
`memcpy`) to consume and return `stackAt sp serializeSubStackX` as a single spatial atom.
-/

namespace CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open Proofs.libsignal.Hooks2

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

theorem L1_SerializeBodyHelpersX : True := trivial

/-! ## Stack budget below the 800-byte frame -/

/-- Callee stack budget inside `SessionRecord::serialize` after allocating its 800-byte frame. -/
abbrev serializeSubStackX : Nat :=
  64 + sessionCloneStackX + vecVecCloneStack + sessionLenStack + Proofs.libsignal.Stage1X.extHookStack +
    Prost.encodeVarintStackX + encodeRawStackX + Proofs.libsignal.Hooks2.doReserveStackX + dropSessionStructureLocal1StackX

theorem serializeStackX_eq : serializeStackX = serializeSubStackX + 800 := by
  decide

theorem stackAt_serializeSub_splitX (fp : BitVec 64) (S : Nat) (hS : S ≤ serializeSubStackX) :
    stackAt fp serializeSubStackX =
      memRegion (fp - BitVec.ofNat 64 serializeSubStackX) (serializeSubStackX - S) ∗
      stackAt fp S := by
  have hval : serializeSubStackX < 2 ^ 32 := by decide
  have h := stackAt_split_bottom fp S (serializeSubStackX - S) (by omega)
  have hsum : S + (serializeSubStackX - S) = serializeSubStackX := Nat.add_sub_of_le hS
  rwa [hsum] at h

/-- Framing/weakening of an `.inImage img` contract: the image facts pass through unchanged. -/
theorem subroutine_ok_frame_weaken_inImage {α : Type} {prog : Program} {entry : BitVec 64}
    {img : Obj.Image} {spec spec' : Spec α} (F : α → State → SepProp)
    (h : subroutine_ok prog entry (spec.inImage img))
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf ∗ F x s0 ⊢ spec'.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry (spec'.inImage img) := by
  refine subroutine_ok_frame_weaken F h (fun x s0 => ?_) hpost hpan hexit
    (hoom := fun x s0 sf => by simp only [Spec.inImage]; exact hoom x s0 sf)
  simp only [Spec.inImage, sepConj_assoc]
  exact sepConj_mono_right (hpre x s0)

theorem stackAt_serialize_baseX (sp : BitVec 64) :
    stackAt sp serializeStackX =
      stackAt (sp - 800#64) serializeSubStackX ∗
      memRegion (sp - 800#64) 368 ∗
      memRegion (sp - 432#64) 336 ∗
      cells (sp - 96#64) 12 := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp (serializeSubStackX + 704) 12 (by decide)
  rw [show serializeSubStackX + 704 + 8 * 12 = serializeStackX by decide] at h1
  have h2 : stackAt (sp - 96#64) (serializeSubStackX + 704) =
      memRegion (sp - 800#64) 704 ∗ stackAt (sp - 800#64) serializeSubStackX := by
    simp only [stackAt]
    have hsplit := memRegion_split (sp - 96#64 - BitVec.ofNat 64 (serializeSubStackX + 704))
      serializeSubStackX 704 (by decide)
    have e1 : sp - 96#64 - BitVec.ofNat 64 (serializeSubStackX + 704) =
        sp - 800#64 - BitVec.ofNat 64 serializeSubStackX := by
      rw [BitVec.sub_sub, BitVec.ofNat_add, ← BitVec.add_assoc,
        show (96#64 + BitVec.ofNat 64 serializeSubStackX + 704#64 : BitVec 64) =
          800#64 + BitVec.ofNat 64 serializeSubStackX by bv_omega,
        ← BitVec.sub_sub]
    have e2 : sp - 800#64 - BitVec.ofNat 64 serializeSubStackX + BitVec.ofNat 64 serializeSubStackX =
        sp - 800#64 := BitVec.sub_add_cancel _ _
    rw [e1, e2] at hsplit
    rw [e1, hsplit, sepConj_comm]
  have h3 := memRegion_split (sp - 800#64) 368 336 (by decide)
  have e3 : sp - 800#64 + BitVec.ofNat 64 368 = sp - 432#64 := bv_sub_add_lit sp 800 368
  rw [show 368 + 336 = 704 by rfl, e3] at h3
  rw [h1, h2, h3]
  ac_rfl

theorem repack_stack_someX (sp : BitVec 64) (q01 : BitVec 128) (w2 : BitVec 64) :
    (stackAt (sp - 800#64) serializeSubStackX ∗
      vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
      memRegion (sp - 776#64) 344 ∗
      ((sp - 432#64) ↦₁₂₈ q01) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStackX := by
  rw [stackAt_serialize_baseX sp, memRegion_split (sp - 800#64) 24 344 (by decide)]
  have e1 : sp - 800#64 + BitVec.ofNat 64 24 = sp - 776#64 := bv_sub_add_lit sp 800 24
  rw [e1]
  have hpull :
      (stackAt (sp - 800#64) serializeSubStackX ∗
        vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
        memRegion (sp - 776#64) 344 ∗
        ((sp - 432#64) ↦₁₂₈ q01) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStackX ∗
        (vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗ memRegion (sp - 776#64) 344) ∗
        (((sp - 432#64) ↦₁₂₈ q01) ∗ ((sp - 416#64) ↦₆₄ w2) ∗ memRegion (sp - 408#64) 312) ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right
    (sepConj_mono (sepConj_mono_left (vecHeader_entails_memRegion _ _ _ _))
      (sepConj_mono_left (repack_336_from_q01_w2 sp q01 w2)))

theorem repack_stack_noneX (sp w0 : BitVec 64) (q01 : BitVec 128) (w2 : BitVec 64)
    {bs336 : List (BitVec 8)} (h336 : bs336.length = 336) :
    (stackAt (sp - 800#64) serializeSubStackX ∗
      vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
      ((sp - 776#64) ↦₆₄ w0) ∗
      ((sp - 768#64) ↦ₛ bs336) ∗
      ((sp - 432#64) ↦₁₂₈ q01) ∗
      ((sp - 416#64) ↦₆₄ w2) ∗
      memRegion (sp - 408#64) 312 ∗
      cells (sp - 96#64) 12) ⊢
      stackAt sp serializeStackX := by
  refine Entails.trans ?_ (repack_stack_someX sp q01 w2)
  have h344 : (((sp - 776#64) ↦₆₄ w0) ∗ ((sp - 768#64) ↦ₛ bs336)) ⊢ memRegion (sp - 776#64) 344 := by
    rw [memRegion_split (sp - 776#64) 8 336 (by decide)]
    have e : sp - 776#64 + BitVec.ofNat 64 8 = sp - 768#64 := bv_sub_add_lit sp 776 8
    rw [e]
    refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
    have hb := pointsToBytes_entails_memRegion (sp - 768#64) bs336
    rwa [h336] at hb
  have hpull :
      (stackAt (sp - 800#64) serializeSubStackX ∗
        vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
        ((sp - 776#64) ↦₆₄ w0) ∗
        ((sp - 768#64) ↦ₛ bs336) ∗
        ((sp - 432#64) ↦₁₂₈ q01) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) =
      (stackAt (sp - 800#64) serializeSubStackX ∗
        vecHeader (sp - 800#64) 0#64 8#64 0#64 ∗
        (((sp - 776#64) ↦₆₄ w0) ∗ ((sp - 768#64) ↦ₛ bs336)) ∗
        ((sp - 432#64) ↦₁₂₈ q01) ∗
        ((sp - 416#64) ↦₆₄ w2) ∗
        memRegion (sp - 408#64) 312 ∗
        cells (sp - 96#64) 12) := by
    ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h344))

theorem stackAt_serialize_none_preX (sp : BitVec 64) :
    stackAt sp serializeStackX =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ bs336 : List (BitVec 8),
       ∃∗ w_none : BitVec 64,
        ⌜bs336.length = 336⌝ ∗
        stackAt (sp - 800#64) serializeSubStackX ∗
        memRegion (sp - 800#64) 24 ∗
        ((sp - 776#64) ↦₆₄ w_none) ∗
        memRegion (sp - 768#64) 336 ∗
        ((sp - 432#64) ↦ₛ bs336) ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  rw [stackAt_serialize_baseX sp, memRegion_368_split sp,
    memRegion_eq_exists_bytes (sp - 432#64) 336 (by decide), cells_12_eq sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine ProofLib.sepExists_congr fun c0 => ProofLib.sepExists_congr fun c1 =>
    ProofLib.sepExists_congr fun c2 => ProofLib.sepExists_congr fun c3 =>
    ProofLib.sepExists_congr fun c4 => ProofLib.sepExists_congr fun c5 =>
    ProofLib.sepExists_congr fun c6 => ProofLib.sepExists_congr fun c7 =>
    ProofLib.sepExists_congr fun c8 => ProofLib.sepExists_congr fun c9 =>
    ProofLib.sepExists_congr fun c10 => ProofLib.sepExists_congr fun c11 =>
    ProofLib.sepExists_congr fun bs336 => ProofLib.sepExists_congr fun w_none => ?_
  ac_rfl

theorem stackAt_serialize_some_preX (sp : BitVec 64) :
    stackAt sp serializeStackX =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        stackAt (sp - 800#64) serializeSubStackX ∗
        memRegion (sp - 800#64) 344 ∗
        memRegion (sp - 456#64) 24 ∗
        memRegion (sp - 432#64) 336 ∗
        ((sp - 96#64) ↦₆₄ c0) ∗ ((sp - 88#64) ↦₆₄ c1) ∗
        ((sp - 80#64) ↦₆₄ c2) ∗ ((sp - 72#64) ↦₆₄ c3) ∗
        ((sp - 64#64) ↦₆₄ c4) ∗ ((sp - 56#64) ↦₆₄ c5) ∗
        ((sp - 48#64) ↦₆₄ c6) ∗ ((sp - 40#64) ↦₆₄ c7) ∗
        ((sp - 32#64) ↦₆₄ c8) ∗ ((sp - 24#64) ↦₆₄ c9) ∗
        ((sp - 16#64) ↦₆₄ c10) ∗ ((sp - 8#64) ↦₆₄ c11)) := by
  rw [stackAt_serialize_baseX sp, memRegion_368_for_clone sp, cells_12_eq sp]
  simp only [sepExists_sepConj_right]
  refine ProofLib.sepExists_congr fun c0 => ProofLib.sepExists_congr fun c1 =>
    ProofLib.sepExists_congr fun c2 => ProofLib.sepExists_congr fun c3 =>
    ProofLib.sepExists_congr fun c4 => ProofLib.sepExists_congr fun c5 =>
    ProofLib.sepExists_congr fun c6 => ProofLib.sepExists_congr fun c7 =>
    ProofLib.sepExists_congr fun c8 => ProofLib.sepExists_congr fun c9 =>
    ProofLib.sepExists_congr fun c10 => ProofLib.sepExists_congr fun c11 => ?_
  ac_rfl

/-! ## Callee offsets on `SP2Ext` -/

theorem serialize_rel_fnAddrX (b : BitVec 64) (ext : String → Option (State → State))
    (name : String) (k : BitVec 64)
    (hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff serializeName) + k =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff name)) :
    (SP2Ext b ext).fnAddr serializeName + k = (SP2Ext b ext).fnAddr name := by
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase]
  rw [BitVec.add_assoc, hk]

theorem vecVecClone_fnAddrX (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr serializeName + bv% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") = (SP2Ext b ext).fnAddr vecVecCloneName :=
  serialize_rel_fnAddrX b ext _ _ (by
    rw [libsignalSessionCode_fnOff_serialize, libsignalSessionCode_fnOff_vecVecClone]; rfl)

theorem sessionClone_fnAddrX (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") = (SP2Ext b ext).fnAddr sessionCloneName :=
  serialize_rel_fnAddrX b ext _ _ (by
    rw [libsignalSessionCode_fnOff_serialize, libsignalSessionCode_fnOff_sessionClone]; rfl)

theorem sessionLen_fnAddrX (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize") = (SP2Ext b ext).fnAddr sessionLenName :=
  serialize_rel_fnAddrX b ext _ _ (by
    rw [libsignalSessionCode_fnOff_serialize, libsignalSessionCode_fnOff_sessionLen]; rfl)

theorem encodeVarint_fnAddrX (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) =
      (SP2Ext b ext).fnAddr Prost.encodeVarintName :=
  serialize_rel_fnAddrX b ext _ _ (by
    rw [libsignalSessionCode_fnOff_serialize, libsignalSessionCode_fnOff_encodeVarint]; rfl)

theorem encodeRaw_fnAddrX (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) =
      (SP2Ext b ext).fnAddr encodeRawName :=
  serialize_rel_fnAddrX b ext _ _ (by
    rw [libsignalSessionCode_fnOff_serialize, libsignalSessionCode_fnOff_encodeRaw]; rfl)

theorem dropLocal1_fnAddrX (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) =
      (SP2Ext b ext).fnAddr FromRecordCallees.dropSessionStructureLocal1Name :=
  serialize_rel_fnAddrX b ext _ _ (by
    rw [libsignalSessionCode_fnOff_serialize, libsignalSessionCode_fnOff_dropLocal1]; rfl)

/-! ## Lifted callee specs at `serializeSubStackX` -/

def vecVecCloneSubSpecX : Spec VecVecCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 0#64⌝ ∗
      memRegion x.dst 24 ∗ stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ vecHeader x.dst 0#64 8#64 0#64 ∗ stackAt s0.sp serializeSubStackX

theorem vecVecClone_sub_okX (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr serializeName + bv% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      vecVecCloneSubSpecX := by
  rw [vecVecClone_fnAddrX]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - vecVecCloneStack))
    (vecVecCloneEmpty_ok_ext b ext)
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [vecVecCloneSubSpecX, vecVecCloneEmptySpec,
      stackAt_serializeSub_splitX s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [vecVecCloneSubSpecX, vecVecCloneEmptySpec,
      stackAt_serializeSub_splitX s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

def sessionLenSubSpecX (A : RustAlloc) : Spec SessionLenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encSessionMem x.G x.s).length ∧ sf.trace = s0.trace⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ stackAt s0.sp serializeSubStackX

theorem sessionLen_sub_okX (A : RustAlloc) (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (SP2Ext b ext) ((SP2Ext b ext).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encoded_len" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      (sessionLenSubSpecX A) := by
  rw [sessionLen_fnAddrX]
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - sessionLenStack))
    (sessionLen_ok_ext A b ext)
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [sessionLenSubSpecX, sessionLenSpec,
      stackAt_serializeSub_splitX s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionLenSubSpecX, sessionLenSpec,
      stackAt_serializeSub_splitX s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

def sessionCloneSubSpecX (A : RustAlloc) : Spec SessionCloneGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src⌝ ∗
      sessionStateReprAt A x.src x.G x.s ∗ memRegion x.dst 344 ∗ A.pool ∗ stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.src x.G x.s ∗
      (∃∗ G' : SessionGhost, ⌜encSessionMem G' x.s = encSessionMem x.G x.s⌝ ∗
        sessionStateReprAt A x.dst G' x.s) ∗
      A.pool ∗ stackAt s0.sp serializeSubStackX
  onPanic := allocPanic

theorem sessionClone_sub_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hClone : SessionCloneOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr serializeName + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      ((sessionCloneSubSpecX A).inImage img) := by
  rw [sessionClone_fnAddrX]
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - sessionCloneStackX))
    hClone
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [sessionCloneSubSpecX, sessionCloneSpecX,
      stackAt_serializeSub_splitX s0.sp sessionCloneStackX (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionCloneSubSpecX, sessionCloneSpecX,
      stackAt_serializeSub_splitX s0.sp sessionCloneStackX (by decide)]
    exact Entails.of_eq (by ac_rfl)

def encodeVarintSubSpecX (A : RustAlloc) : Spec Prost.EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧ x.bs.length + 10 < 2 ^ 62⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = s0.trace⌝ ∗
      ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
      vecU8At A x.v cap' ptr' (x.bs ++ encodeVarint x.val)) ∗
      A.pool ∗ stackAt s0.sp serializeSubStackX
  onPanic := allocPanic

theorem encodeVarint_sub_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hEV : EncodeVarintOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      ((encodeVarintSubSpecX A).inImage img) := by
  rw [encodeVarint_fnAddrX]
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Prost.encodeVarintStackX))
    hEV
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [encodeVarintSubSpecX, Prost.encodeVarintSpecX,
      stackAt_serializeSub_splitX s0.sp Prost.encodeVarintStackX (by decide), sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hx0, hx1, hlen⟩
    exact Entails.pure_right ⟨hx0, hx1, Or.inr hlen⟩ (Entails.of_eq (by ac_rfl))
  · simp only [encodeVarintSubSpecX, Prost.encodeVarintSpecX,
      stackAt_serializeSub_splitX s0.sp Prost.encodeVarintStackX (by decide),
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    exact Entails.of_eq (by congr 1; funext cap'; congr 1; funext ptr'; ac_rfl)

def encodeRawSubSpecX (A : RustAlloc) : Spec EncodeRawGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encSessionMem x.G x.s).length < 2 ^ 32⌝ ∗
      sessionStateReprAt A x.ss x.G x.s ∗ vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.ss x.G x.s ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A x.v cap' ptr' (x.bs ++ encSessionMem x.G x.s)) ∗
      A.pool ∗ stackAt s0.sp serializeSubStackX
  onPanic := allocPanic

theorem encodeRaw_sub_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hRaw : EncodeRawOkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      ((encodeRawSubSpecX A).inImage img) := by
  rw [encodeRaw_fnAddrX]
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - encodeRawStackX))
    hRaw
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [encodeRawSubSpecX, encodeRawSpecX,
      stackAt_serializeSub_splitX s0.sp encodeRawStackX (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [encodeRawSubSpecX, encodeRawSpecX,
      stackAt_serializeSub_splitX s0.sp encodeRawStackX (by decide)]
    exact Entails.of_eq (by ac_rfl)

def dropLocal1SubSpecX (A : RustAlloc) : Spec DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp serializeSubStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp serializeSubStackX

theorem dropLocal1_sub_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hDrop : DropSessionStructureLocal1OkX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")))
      ((dropLocal1SubSpecX A).inImage img) := by
  rw [dropLocal1_fnAddrX]
  refine subroutine_ok_frame_weaken_inImage
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - dropSessionStructureLocal1StackX))
    hDrop
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [dropLocal1SubSpecX, dropSessionStructureLocal1SpecX,
      stackAt_serializeSub_splitX s0.sp dropSessionStructureLocal1StackX (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [dropLocal1SubSpecX, dropSessionStructureLocal1SpecX,
      stackAt_serializeSub_splitX s0.sp dropSessionStructureLocal1StackX (by decide)]
    exact Entails.of_eq (by ac_rfl)

def rustAllocSubSpecX (A : RustAlloc) : Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      LayoutOk size align⌝ ∗
      A.pool ∗ stackAt s.sp serializeSubStackX
  post := fun (size, align) s0 sf =>
    let p := sf.readReg64 .x0
    (if p = 0 then
       ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
     else
       ⌜p.toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
         A.live p size align ∗ memRegion p size) ∗
      A.pool ∗ stackAt s0.sp serializeSubStackX

theorem alloc_sub_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName +
        bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      ((rustAllocSubSpecX A).inImage img) := by
  have halloc := hC.alloc.alloc_ok_at serializeName
    (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) (by
      simp only [libsignalSessionCode_fnOff_serialize, arm64_norm])
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

def shimSubSpecX : Spec Unit where
  pre := fun _ s => stackAt s.sp serializeSubStackX
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp serializeSubStackX

theorem shim_sub_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName +
        bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      (shimSubSpecX.inImage img) := by
  have hshim := hC.alloc.shim_ok_at serializeName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) (by
      simp only [libsignalSessionCode_fnOff_serialize, arm64_norm])
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

def memcpySubSpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp serializeSubStackX
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp serializeSubStackX

theorem memcpy_sub_okX {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr serializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize"))
      (memcpySubSpecX.inImage img) := by
  have hmemcpy := hC.memcpy_ok_at serializeName (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::serialize")) (by
    simp only [libsignalSessionCode_fnOff_serialize, arm64_norm])
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

/-! ## Relocatable `[LibsignalPlacement]` lifted callee specs -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem L1_SerializeBodyHelpersX_Placed : True := trivial

theorem subroutine_ok_withLsCodeLoaded_of_withLsCl {α : Type} {prog : Program}
    {pl : MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCl pl spec)) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

theorem vecVecClone_placed_sub_okX [LibsignalPlacement]
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (blkPl_117).base (withLsCodeLoaded lsmpl vecVecCloneSubSpecX) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - vecVecCloneStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (vecVecCloneEmpty_placed_ok_cl (callerProg := callerProg)))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [vecVecCloneSubSpecX, vecVecCloneEmptySpec,
      stackAt_serializeSub_splitX s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [vecVecCloneSubSpecX, vecVecCloneEmptySpec,
      stackAt_serializeSub_splitX s0.sp vecVecCloneStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem sessionLen_placed_sub_okX [LibsignalPlacement] (A : RustAlloc)
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (blkPl_86).base (withLsCodeLoaded lsmpl (sessionLenSubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - sessionLenStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (sessionLen_placed_ok_cl A (callerProg := callerProg)))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [sessionLenSubSpecX, sessionLenSpec,
      stackAt_serializeSub_splitX s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionLenSubSpecX, sessionLenSpec,
      stackAt_serializeSub_splitX s0.sp sessionLenStack (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem sessionClone_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hClone : SessionClonePlacedOkX A H) :
    subroutine_ok callerProg (blkPl_80).base (withLsCodeLoaded lsmpl (sessionCloneSubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - sessionCloneStackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hClone))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [sessionCloneSubSpecX, sessionCloneSpecX,
      stackAt_serializeSub_splitX s0.sp sessionCloneStackX (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [sessionCloneSubSpecX, sessionCloneSpecX,
      stackAt_serializeSub_splitX s0.sp sessionCloneStackX (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem encodeVarint_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hEV : EncodeVarintPlacedOkX A H) :
    subroutine_ok callerProg (blkPl_10).base (withLsCodeLoaded lsmpl (encodeVarintSubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Prost.encodeVarintStackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hEV))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [encodeVarintSubSpecX, Prost.encodeVarintSpecX,
      stackAt_serializeSub_splitX s0.sp Prost.encodeVarintStackX (by decide), sepConj_assoc]
    apply Entails.pure_left; rintro ⟨hx0, hx1, hlen⟩
    exact Entails.pure_right ⟨hx0, hx1, Or.inr hlen⟩ (Entails.of_eq (by ac_rfl))
  · simp only [encodeVarintSubSpecX, Prost.encodeVarintSpecX,
      stackAt_serializeSub_splitX s0.sp Prost.encodeVarintStackX (by decide),
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    exact Entails.of_eq (by congr 1; funext cap'; congr 1; funext ptr'; ac_rfl)

theorem encodeRaw_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hRaw : EncodeRawPlacedOkX A H) :
    subroutine_ok callerProg (blkPl_14).base (withLsCodeLoaded lsmpl (encodeRawSubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - encodeRawStackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hRaw))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun x s0 sf => allocPanic_frame_entails x s0 sf _)
    (fun _ _ _ _ => rfl)
  · simp only [encodeRawSubSpecX, encodeRawSpecX,
      stackAt_serializeSub_splitX s0.sp encodeRawStackX (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [encodeRawSubSpecX, encodeRawSpecX,
      stackAt_serializeSub_splitX s0.sp encodeRawStackX (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem dropLocal1_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hDrop : DropSessionStructureLocal1PlacedOkX A H) :
    subroutine_ok callerProg (blkPl_6).base (withLsCodeLoaded lsmpl (dropLocal1SubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - dropSessionStructureLocal1StackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl
      (ls_subroutine_ok_cl_of_callee (callerProg := callerProg) hDrop))
    (fun x s0 => ?_)
    (fun x s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [dropLocal1SubSpecX, dropSessionStructureLocal1SpecX,
      stackAt_serializeSub_splitX s0.sp dropSessionStructureLocal1StackX (by decide)]
    exact Entails.of_eq (by ac_rfl)
  · simp only [dropLocal1SubSpecX, dropSessionStructureLocal1SpecX,
      stackAt_serializeSub_splitX s0.sp dropSessionStructureLocal1StackX (by decide)]
    exact Entails.of_eq (by ac_rfl)

theorem alloc_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustAllocSubSpecX A)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Proofs.libsignal.Stage1X.extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.alloc.alloc (callerProg := callerProg)))
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

theorem shim_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl shimSubSpecX) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - Proofs.libsignal.Stage1X.extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.alloc.shim (callerProg := callerProg)))
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

theorem memcpy_placed_sub_okX [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced A H) :
    subroutine_ok callerProg (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl memcpySubSpecX) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - CryptoVerification.LibsignalTripleRatchet.extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.memcpy (callerProg := callerProg)))
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

end Placed

end CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX
