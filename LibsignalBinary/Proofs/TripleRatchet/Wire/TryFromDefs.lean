/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefs
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPure
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.WireCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq

/-!
# Shared definitions and callee/hook wrappers for `SignalMessage::try_from`
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Wire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## Generic rebased program `tripleRatchetProgAtW` (`= tripleRatchetProgAtExt b abs`) and contract bundles for `Wire/TryFrom*` -/

/-- `tripleRatchetProgAtW b C ctl abs` is `tripleRatchetProgAtExt b abs = libsignalSessionCode.rebase b (Rust.withPanics abs)`,
retaining `(C : Crypto) (ctl : BitVec 64)` for binder compatibility (`uuid::Uuid::try_parse` is
in-image code, so there is no `UuidParser` binder). -/
noncomputable abbrev tripleRatchetProgAtW (b : BitVec 64) (_C : Crypto) (_ctl : BitVec 64)
    (abs : String → Option (State → State)) : Program :=
  tripleRatchetProgAtExt b abs

/-- Dealloc contract on `tripleRatchetProgAtExt img.base abs` used by `SignalMessage::try_from`. -/
structure AllocHooksW (img : Obj.Image) (A : RustAlloc) (abs : String → Option (State → State)) : Prop where
  dealloc : subroutine_ok (tripleRatchetProgAtExt img.base abs)
    ((tripleRatchetProgAtExt img.base abs).fnAddr deallocName)
    ((rustDeallocExternSpecWithStack A extHookStack).inImage img)

theorem AllocHooksW.of_contracts_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    AllocHooksW img A ext :=
  ⟨hA.dealloc⟩

theorem AllocHooksW.of_contracts {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    AllocHooksW img A ext :=
  AllocHooksW.of_contracts_x (AllocContractsX.of_AllocContracts hA)

/-- Extern contracts on `tripleRatchetProgAtExt img.base abs` used by `SignalMessage::try_from`. -/
structure TripleRatchetHooksW (img : Obj.Image) (_C : Crypto) (A : RustAlloc) (_S : SpqrModel)
    (abs : String → Option (State → State)) : Prop where
  alloc : AllocHooksW img A abs
  decodeErrorFrom : subroutine_ok (tripleRatchetProgAtExt img.base abs)
    ((tripleRatchetProgAtExt img.base abs).fnAddr decodeErrorFromName)
    ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img)
  decodeErrorPush : subroutine_ok (tripleRatchetProgAtExt img.base abs)
    ((tripleRatchetProgAtExt img.base abs).fnAddr decodeErrorPushName)
    ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img)
  decodeVarintSlow : subroutine_ok (tripleRatchetProgAtExt img.base abs)
    ((tripleRatchetProgAtExt img.base abs).fnAddr varintSlowName)
    ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img)

theorem TripleRatchetHooksW.of_contracts_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    TripleRatchetHooksW img C A S ext where
  alloc := AllocHooksW.of_contracts_x hC.toAllocContractsX
  decodeErrorFrom := hC.decode_error_from
  decodeErrorPush := hC.decode_error_push
  decodeVarintSlow := hC.decode_varint_slow

theorem TripleRatchetHooksW.of_contracts {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    TripleRatchetHooksW img C A S ext where
  alloc := AllocHooksW.of_contracts hC.toAllocContracts
  decodeErrorFrom :=
    subroutine_ok_inImage_of_subroutine_ok img
      (decodeErrorFromWithStack_of_decodeErrorFrom hC.decode_error_from)
  decodeErrorPush :=
    subroutine_ok_inImage_of_subroutine_ok img
      (decodeErrorPushExtern_of_decodeErrorPush
        (decodeErrorPushWithStack_of_decodeErrorPush hC.decode_error_push))
  decodeVarintSlow :=
    subroutine_ok_inImage_of_subroutine_ok img
      (decodeVarintSlowWithStack_of_decodeVarintSlow hC.decode_varint_slow)

theorem TripleRatchetHooksW.of_tripleRatchetProgAt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hS : TripleRatchetHooks C A S abs) :
    TripleRatchetHooksW img C A S (tripleRatchetExterns C ctl abs) :=
  TripleRatchetHooksW.of_contracts (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hS)

/-! ## Callee hypotheses on `tripleRatchetProgAtW` -/

/-- `subroutine_ok` for `Vec<u8>::into_boxed_slice` (`0x1afd4`). -/
def IntoBoxedSliceOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
    ((tripleRatchetProgAtW img.base C ctl abs).fnAddr intoBoxedSliceName)
    ((intoBoxedSliceSpecX A).inImage img)

/-- `subroutine_ok` for `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (`0xd0a0`). -/
def TryCloneFromRefOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
    ((tripleRatchetProgAtW img.base C ctl abs).fnAddr tryCloneFromRefName)
    ((tryCloneFromRefSpecX A).inImage img)

/-- `subroutine_ok` for `prost::encoding::decode_varint_slice` (`0x23008`). -/
def DecodeVarintSliceOkW (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
    ((tripleRatchetProgAtW img.base C ctl abs).fnAddr decodeVarintSliceName)
    ((decodeVarintSliceSpecX A).inImage img)

/-- `subroutine_ok` for `prost::encoding::int32::merge` (`0x2bc4`). -/
def Int32MergeOkW (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
    ((tripleRatchetProgAtW img.base C ctl abs).fnAddr int32MergeName)
    ((int32MergeSpecX A).inImage img)

/-- `subroutine_ok` for `prost::encoding::skip_field` (`0x1b34`). -/
def SkipFieldOkW (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
    ((tripleRatchetProgAtW img.base C ctl abs).fnAddr skipFieldName)
    ((skipFieldSpecX A).inImage img)

/-- `subroutine_ok` for `core::ptr::drop_in_place<prost::error::DecodeError>` (`0x242c`). -/
def DropDecodeErrorOkW (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
    ((tripleRatchetProgAtW img.base C ctl abs).fnAddr dropDecodeErrorName)
    ((dropDecodeErrorSpecX A).inImage img)

/-- `subroutine_ok` for `prost::encoding::bytes::merge` (`0x2788`). -/
def BytesMergeOkW (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
    ((tripleRatchetProgAtW img.base C ctl abs).fnAddr bytesMergeName)
    (bytesMergeSpecX A img)

/-- `subroutine_ok` for `core::ptr::drop_in_place<SignalProtocolError>` (`0x2374`). -/
def DropSpeOkW (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
    ((tripleRatchetProgAtW img.base C ctl abs).fnAddr dropSpeName)
    ((dropSpeSpecX A).inImage img)

/-! ## Page-aligned ADRP helper for `try_from` (`0x25868`) -/

theorem fnAddr_tryFrom_adrp {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) {k : BitVec 64}
    (hk : (bv% (ls_off% "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from") + k) &&& 0xfffffffffffff000#64 = bv% (page% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#1]" + 280)) := by rfl) :
    (((tripleRatchetProgAtW b C ctl abs).fnAddr tryFromName + k) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#1]" + 280)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from"), BitVec.add_assoc,
    adrp_page_of_aligned hb, hk]

/-! ## Hook lookup lemmas on `tripleRatchetProgAtW` -/

/-- `alloc::alloc::handle_alloc_error` stub panics on `tripleRatchetProgAtW`. -/
theorem panic_at_handle_alloc_error2 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by fnoff_eq) :
    (tripleRatchetProgAtW b C ctl abs).externAt?
      ((tripleRatchetProgAtW b C ctl abs).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_panicSymbol (hname := "alloc::alloc::handle_alloc_error") rfl hk
    (by fnoff_eq)
    (by fnoff_eq) (by simp [Rust.isPanicSymbol])

/-- `DecodeError::from` at call distance `k` from `name` on `tripleRatchetProgAtW`. -/
theorem decodeErrorFrom_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hS : TripleRatchetHooksW img C A S abs)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff decodeErrorFromName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img) := by
  rw [← Program.fnAddr_rel rfl rfl hk]
  exact hS.decodeErrorFrom

/-- `DecodeError::push` at call distance `k` from `name` on `tripleRatchetProgAtW`. -/
theorem decodeErrorPush_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hS : TripleRatchetHooksW img C A S abs)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff decodeErrorPushName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img) := by
  rw [← Program.fnAddr_rel rfl rfl hk]
  exact hS.decodeErrorPush

/-! ## In-image callee wrappers at call distance `k` from `name` on `tripleRatchetProgAtW` -/

theorem decodeVarintSlice_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : DecodeVarintSliceOkW img C A ctl abs) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "prost::encoding::varint::decode_varint_slice")) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((decodeVarintSliceSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice") hk]; exact h

theorem int32Merge_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Int32MergeOkW img C A ctl abs) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>")) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((int32MergeSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>") hk]; exact h

theorem skipField_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : SkipFieldOkW img C A ctl abs) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "prost::encoding::skip_field::<&mut &[u8]> [local#1]")) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((skipFieldSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "prost::encoding::skip_field::<&mut &[u8]> [local#1]") hk]; exact h

theorem dropDecodeError_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : DropDecodeErrorOkW img C A ctl abs) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]")) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((dropDecodeErrorSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#1]") hk]; exact h

theorem bytesMerge_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : BytesMergeOkW img C A ctl abs) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (bytesMergeSpecX A img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") hk]; exact h

theorem dropSpe_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : DropSpeOkW img C A ctl abs) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((dropSpeSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") hk]; exact h

theorem intoBoxedSlice_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : IntoBoxedSliceOk img C A ctl abs) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((intoBoxedSliceSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "<alloc::vec::Vec<u8>>::into_boxed_slice") hk]; exact h

theorem tryCloneFromRef_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : TryCloneFromRefOk img C A ctl abs) {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off) (hk : off + k = num% (ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")) :
    subroutine_ok (tripleRatchetProgAtW img.base C ctl abs)
      ((tripleRatchetProgAtW img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      ((tryCloneFromRefSpecX A).inImage img) := by
  rw [← Program.fnAddr_rel hfn (ls_lemma% fnOff "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in") hk]; exact h

/-! ## Relocatable `[LibsignalPlacement]` Definitions and Callee Contracts (Block `85`) -/

noncomputable abbrev tryFromPlacedProg [LibsignalPlacement] (H : LibsignalHooks) : Program :=
  (blkPC_85).rebase (blkPl_85).base H

/-- Synthetic `Obj.Image` whose `logFilterAddr` equals `lsLogFilterAddr` (`lsmpl.ρ "log::MAX_LOG_LEVEL_FILTER"`). -/
def tryFromPlacedImg [LibsignalPlacement] : Obj.Image :=
  { (default : Obj.Image) with base := lsLogFilterAddr - LibsignalSession.logFilterAddr { (default : Obj.Image) with base := 0 } }

@[simp, arm64_norm, wp_norm]
theorem logFilterAddr_tryFromPlacedImg [LibsignalPlacement] :
    LibsignalSession.logFilterAddr tryFromPlacedImg = lsLogFilterAddr := by
  simp only [tryFromPlacedImg, LibsignalSession.logFilterAddr]; bv_omega

@[simp, arm64_norm, wp_norm]
theorem logOff_tryFromPlacedImg [LibsignalPlacement] :
    logOff tryFromPlacedImg = (lsLogFilterAddr ↦₆₄ 0#64) := by
  simp only [logOff, logFilterAddr_tryFromPlacedImg]

theorem panic_at_handle_alloc_error2_placed [LibsignalPlacement]
    {H : LibsignalHooks}
    (h_panic : H lsAllocHandleErrorSym = some Rust.panicked) :
    (tryFromPlacedProg H).externAt?
      ((blkPl_85).ρ lsAllocHandleErrorSym) =
      some Rust.panicked :=
  new_externAt?_handle_alloc_error h_panic

structure AllocHooksWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  dealloc : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ lsRustDeallocSym)
    (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack A extHookStack))
  panic_alloc : H lsAllocHandleErrorSym = some Rust.panicked

structure TripleRatchetHooksWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop where
  alloc : AllocHooksWPlaced A H
  decodeErrorFrom : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ decodeErrorFromName)
    (withLsCodeRoLoaded lsmpl (decodeErrorFromSpecWithStack A (2 * extHookStack)))
  decodeErrorPush : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ decodeErrorPushName)
    (withLsCodeRoLoaded lsmpl (decodeErrorPushExternSpecWithStack A (2 * extHookStack)))
  decodeVarintSlow : subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ varintSlowName)
    (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)))

def IntoBoxedSliceOkPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ intoBoxedSliceName)
    (withLsCodeRoLoaded lsmpl (intoBoxedSliceSpecX A))

def TryCloneFromRefOkPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ tryCloneFromRefName)
    (withLsCodeRoLoaded lsmpl (tryCloneFromRefSpecX A))

def DecodeVarintSliceOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ decodeVarintSliceName)
    (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A))

def Int32MergeOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ int32MergeName)
    (withLsCodeRoLoaded lsmpl (int32MergeSpecX A))

def SkipFieldOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ skipFieldName)
    (withLsCodeRoLoaded lsmpl (skipFieldSpecX A))

def DropDecodeErrorOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ dropDecodeErrorName)
    (withLsCodeRoLoaded lsmpl (dropDecodeErrorSpecX A))

def BytesMergeOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ bytesMergeName)
    (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecX A))

def DropSpeOkWPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (tryFromPlacedProg H)
    ((blkPl_85).ρ dropSpeName)
    (withLsCodeRoLoaded lsmpl (dropSpeSpecX A))

end CryptoVerification.LibsignalTripleRatchet.Wire
