/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Callee Specifications and Kit for `message::merge<Chain> [local#5]`

Defines the `X`-regime callee specifications (`decodeVarint2SpecX`, `bytesMerge3Spec`), proves the
`RawVec<MessageKey>::grow_one` symbol-offset alias theorem `growOneMessageKey_ok_ext_x` and the
`AllocContractsX → Stage1X.AllocContractsX` bridge `c3_stage1Alloc_of_allocContractsX`, and defines
`Chain3CalleeKitExt` bundling the handshake `decode_varint [local#5]` and `bytes::merge [local#6]`
contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record (A0)
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X
open CryptoVerification.CodeLayout

/-- `message::merge<Chain> [local#5]` in `LibsignalSession` (484 instructions, 1936 bytes). -/
abbrev chainMerge5Name : String :=
  "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#4]"

/-- Alias kept inside `VerNe.Chain3` for continuity with the ported `Chain3` slice lemmas. -/
abbrev chainMerge3Name : String := chainMerge5Name

/-- `decode_varint::<&mut &[u8]> [local#5]` (145 instructions). -/
abbrev c3DecodeVarintName : String :=
  "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]"

/-- `bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]` (222 instructions). -/
abbrev c3BytesMergeName : String :=
  "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]"

/-- `RawVec<MessageKey>::grow_one` (shared stride-104/align-8 symbol with `growOneChainName`). -/
abbrev c3GrowOneName : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one"

/-- Stack budget for `decode_varint::<&mut &[u8]> [local#5]` under `Stage2ContractsX` (`32896` B). -/
abbrev decodeVarint2StackX : Nat := 0x40 + decodeVarintSlowStackX

/-- Contract of `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#5]` at
`decodeVarint2StackX`. -/
def decodeVarint2SpecX (A : RustAlloc) : Spec DecodeVarintSlowGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp decodeVarint2StackX
  post := fun x s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp decodeVarint2StackX ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack budget for `prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]`:
own frame `0xe0` (`224` B) plus `decodeVarint2StackX` (`32896` B) = `33120` B. -/
abbrev bytesMerge3Stack : Nat := 0xe0 + decodeVarint2StackX

/-- Raw contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]`. -/
def bytesMerge3RawSpec (A : RustAlloc) : Spec BytesMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      BytesMergeCapOk x.valCap x.bs.length⌝ ∗
      vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp bytesMerge3Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk cap' rest.length⌝ ∗ vecU8At A x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
          vecU8At A x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Contract of `prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#6]` in
loaded image `img`. -/
def bytesMerge3Spec (A : RustAlloc) (img : Obj.Image) : Spec BytesMergeGhost :=
  (bytesMerge3RawSpec A).inImage img

/-- `c3GrowOneName` and `growOneChainName` resolve to the exact same symbol offset in
`libsignalSessionCode`. -/
theorem growOneMessageKey_fnOff_eq_chain :
    libsignalSessionCode.fnOff c3GrowOneName =
      libsignalSessionCode.fnOff growOneChainName := by
  have h1 := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
  rw [h1, h2]

theorem growOneMessageKey_fnAddr_eq_chain (b : BitVec 64)
    (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase b H).fnAddr c3GrowOneName =
      (libsignalSessionCode.rebase b H).fnAddr growOneChainName := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, growOneMessageKey_fnOff_eq_chain]

/-- `RawVec<MessageKey>::grow_one` meets `(growOneChainSpecX A).inImage img` under
`Proofs.libsignal.Stage1X.AllocContractsX img A ext`. -/
theorem growOneMessageKey_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    OkAtX img.base ext c3GrowOneName ((growOneChainSpecX A).inImage img) := by
  unfold OkAtX SP2Ext contractProg
  rw [growOneMessageKey_fnAddr_eq_chain]
  exact Proofs.libsignal.Stage1X.growOneChain_ok_x hA

/-- `CryptoVerification.LibsignalTripleRatchet.AllocContractsX` entails
`Proofs.libsignal.Stage1X.AllocContractsX`. -/
theorem c3_stage1Alloc_of_allocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAlloc : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Proofs.libsignal.Stage1X.AllocContractsX img A ext where
  alloc := subroutine_ok_mono_entails hAlloc.alloc
    (fun ⟨_, _⟩ _ => Entails.refl _)
    (fun ⟨_, _⟩ _ _ => Entails.of_eq (by
      dsimp only [Spec.inImage,
        CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack]
      ac_rfl))
  dealloc := subroutine_ok_mono_entails hAlloc.dealloc
    (fun ⟨_, _, _⟩ _ => Entails.of_eq (by
      dsimp only [Spec.inImage,
        CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack]
      ac_rfl))
    (fun ⟨_, _, _⟩ _ _ => Entails.refl _)
  realloc := subroutine_ok_mono hAlloc.realloc
    (fun ⟨_, _, _, _, _⟩ _ _ h => by
      dsimp only [Spec.inImage,
        CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      obtain ⟨hinv, h⟩ := h
      refine ⟨hinv, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hb1, hb2, hl1, hl2⟩, h⟩ := h
      refine ⟨⟨hx0, hx1, hx2, hx3, hl1, hl2, hb1, hb2⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h)
    (fun ⟨_, _, _, _, _⟩ _ _ _ h => by
      dsimp only [Spec.inImage,
        CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.rustReallocSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocSpecWithStack] at h ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h)
  shim := hAlloc.shim extHookStack (by decide) (by decide)
  session_memmove := hAlloc.session_memmove extHookStack (by decide) (by decide)

/-- Callee kit bundling the handshake `decode_varint [local#5]` and `bytes::merge [local#6]` contracts,
parameterized over `A : RustAlloc`. -/
structure Chain3CalleeKitExt (A : RustAlloc) : Prop where
  dv : ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext →
    OkAtX img.base ext c3DecodeVarintName ((decodeVarint2SpecX A).inImage img)
  bm : ∀ (img : Obj.Image) (ext : String → Option (State → State)),
    Obj.Loads libsignalSessionImage img →
    CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext →
    OkAtX img.base ext c3BytesMergeName (bytesMerge3Spec A img)

abbrev Chain3CalleeKit : Prop := Chain3CalleeKitExt A0

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
