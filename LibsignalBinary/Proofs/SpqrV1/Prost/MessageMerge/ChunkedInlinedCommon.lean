/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
public import LibsignalBinary.Proofs.SpqrV1.Auth.Merge
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1State
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Shared Infrastructure for Inlined `V1State.Chunked.*` `message::merge` Subroutines

Shared symbol names, 128-byte stack-frame splitting lemmas, `decodeErrorAtStackLen` bounds,
capacity-bounded representation predicates (`*PBCapAt`), `Option::get_or_insert_with(Default::default)`
initialization bridges, pure `mergeField` step lemmas, and Hoare `Spec`s for the seven
`V1State.Chunked.*::merge` functions with inlined `Unchunked.*` sub-message loops (`HeaderSent`,
`KeysSampled`, `KeysUnsampled`, `HeaderReceived`, `NoHeaderReceived`, and `EkReceivedCt1Sampled`,
plus `ChainParams`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Symbol Names & Entry Offsets -/

abbrev chunkedKeysUnsampledMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::KeysUnsampled, &mut &[u8]>"

abbrev chunkedNoHeaderReceivedMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::NoHeaderReceived, &mut &[u8]>"

abbrev chunkedCt2SampledMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::Ct2Sampled, &mut &[u8]>"

abbrev chunkedHeaderReceivedMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderReceived, &mut &[u8]>"

abbrev chunkedKeysSampledMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::KeysSampled, &mut &[u8]>"

abbrev chunkedHeaderSentMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::HeaderSent, &mut &[u8]>"

abbrev chunkedEkReceivedCt1SampledMergeName : String :=
  "prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::EkReceivedCt1Sampled, &mut &[u8]>"

theorem chunkedKeysUnsampledMerge_fnOff :
    libsignalSessionCode.fnOff chunkedKeysUnsampledMergeName = 0x4b45c :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4b45c

theorem chunkedNoHeaderReceivedMerge_fnOff :
    libsignalSessionCode.fnOff chunkedNoHeaderReceivedMergeName = 0x4bdbc :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4bdbc

theorem chunkedCt2SampledMerge_fnOff :
    libsignalSessionCode.fnOff chunkedCt2SampledMergeName = 0x4a5f8 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4a5f8

theorem chunkedHeaderReceivedMerge_fnOff :
    libsignalSessionCode.fnOff chunkedHeaderReceivedMergeName = 0x4b7b4 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4b7b4

theorem chunkedKeysSampledMerge_fnOff :
    libsignalSessionCode.fnOff chunkedKeysSampledMergeName = 0x4b014 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4b014

theorem chunkedHeaderSentMerge_fnOff :
    libsignalSessionCode.fnOff chunkedHeaderSentMergeName = 0x4a9b8 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4a9b8

theorem chunkedEkReceivedCt1SampledMerge_fnOff :
    libsignalSessionCode.fnOff chunkedEkReceivedCt1SampledMergeName = 0x4c37c :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4c37c

/-! ## 2. 128-Byte Stack Frame & Sub-Stack Splitting Lemmas -/

/-- Sub-stack requirement below `s0.sp - 128#64` (`64 + skipField3Stack 98 = polyMergeStack`). -/
abbrev chunkedInlBelowStack : Nat := 64 + skipField3Stack 98

/-- Total stack requirement for `V1State.Chunked.*::merge` (`128 + chunkedInlBelowStack`). -/
abbrev chunkedInlStack : Nat := 128 + chunkedInlBelowStack

/-- Saved registers `[sp - 80 .. sp - 8]` for the 6 functions that spill `x26, x25` at `[sp, #0x40]`. -/
def chunkedInlSavedRegs10 (sp : BitVec 64) (s0 : State) : SepProp :=
  ((sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Callee-saved registers `x27, x28` not spilled by the 10-reg 128-byte prologue. -/
def ChunkedInl10CalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem stackAt_chunkedInl_prologue (sp : BitVec 64) :
    stackAt sp chunkedInlStack =
      stackAt (sp - 128#64) chunkedInlBelowStack ∗ memRegion (sp - 128#64) 48 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
        ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
        ((sp - 8#64) ↦₆₄ v9)) := by
  have h1 := ProofLib.stackAt_split_cells sp (48 + chunkedInlBelowStack) 10 (by decide)
  change stackAt sp chunkedInlStack = stackAt (sp - 80#64) (48 + chunkedInlBelowStack) ∗ cells (sp - 80#64) 10 at h1
  have h2 := memRegion_split' (b := sp - 80#64 - BitVec.ofNat 64 (48 + chunkedInlBelowStack))
    (b' := sp - 128#64) (n := chunkedInlBelowStack) (k := 48) (N := 48 + chunkedInlBelowStack) (by decide) (by bv_omega) (by decide)
  have h2_addr : sp - 80#64 - BitVec.ofNat 64 (48 + chunkedInlBelowStack) = sp - 128#64 - BitVec.ofNat 64 chunkedInlBelowStack := by bv_omega
  change stackAt (sp - 80#64) (48 + chunkedInlBelowStack) = _ at h2; rw [h2_addr] at h2
  change stackAt (sp - 80#64) (48 + chunkedInlBelowStack) = stackAt (sp - 128#64) chunkedInlBelowStack ∗ memRegion (sp - 128#64) 48 at h2
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v0) ∗ ((sp - 72#64) ↦₆₄ v1) ∗ ((sp - 64#64) ↦₆₄ v2) ∗
        ((sp - 56#64) ↦₆₄ v3) ∗ ((sp - 48#64) ↦₆₄ v4) ∗ ((sp - 40#64) ↦₆₄ v5) ∗
        ((sp - 32#64) ↦₆₄ v6) ∗ ((sp - 24#64) ↦₆₄ v7) ∗ ((sp - 16#64) ↦₆₄ v8) ∗
        ((sp - 8#64) ↦₆₄ v9)) := by cells_unfold
  rw [h1, h2, hc10]; ac_rfl

theorem stackAt_chunkedInl9_epilogue (sp : BitVec 64) (s0 : State) (v_pad : BitVec 64) :
    stackAt (sp - 128#64) chunkedInlBelowStack ∗
      memRegion (sp - 128#64) 48 ∗ polySavedRegs sp s0 v_pad ⊢
    stackAt sp chunkedInlStack := by
  rw [stackAt_chunkedInl_prologue]
  refine sepConj_mono_right (sepConj_mono_right ?_); unfold polySavedRegs
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x29))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x30))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x25))
  refine Entails.trans ?_ (Entails.sepExists_intro v_pad)
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x24))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x23))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x22))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x21))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x20))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x19))
  exact Entails.refl _

theorem stackAt_chunkedInl10_epilogue (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 128#64) chunkedInlBelowStack ∗
      memRegion (sp - 128#64) 48 ∗ chunkedInlSavedRegs10 sp s0 ⊢
    stackAt sp chunkedInlStack := by
  rw [stackAt_chunkedInl_prologue]
  refine sepConj_mono_right (sepConj_mono_right ?_); unfold chunkedInlSavedRegs10
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x29))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x30))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x26))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x25))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x24))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x23))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x22))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x21))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x20))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x19))
  exact Entails.refl _

abbrev chunkedInlBelowRest (sp : BitVec 64) (subStack : Nat) : SepProp :=
  memRegion (sp - 128#64 - BitVec.ofNat 64 chunkedInlBelowStack) (chunkedInlBelowStack - subStack)

private theorem bv_sub_128_add_cancel_inl (sp u w : BitVec 64) :
    sp - 128#64 - w = sp - 128#64 - (u + w) + u := by bv_omega

theorem chunkedInlBelow_split (sp : BitVec 64) (subStack : Nat) (hle : subStack ≤ chunkedInlBelowStack) :
    stackAt (sp - 128#64) chunkedInlBelowStack =
      chunkedInlBelowRest sp subStack ∗ stackAt (sp - 128#64) subStack := by
  simp only [chunkedInlBelowRest, stackAt]
  have hlen : chunkedInlBelowStack = (chunkedInlBelowStack - subStack) + subStack := by omega
  have hbound : chunkedInlBelowStack ≤ 2 ^ 64 := by
    simp only [chunkedInlBelowStack, skipField3Stack, decodeVarint2Stack, decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]; omega
  have hbit : BitVec.ofNat 64 chunkedInlBelowStack = BitVec.ofNat 64 (chunkedInlBelowStack - subStack) + BitVec.ofNat 64 subStack := by
    rw [← BitVec.ofNat_add, ← hlen]
  exact memRegion_split' (b := sp - 128#64 - BitVec.ofNat 64 chunkedInlBelowStack)
    (b' := sp - 128#64 - BitVec.ofNat 64 subStack) (n := chunkedInlBelowStack - subStack) (k := subStack)
    (N := chunkedInlBelowStack) hlen (by rw [hbit]; exact bv_sub_128_add_cancel_inl sp _ _) hbound

theorem chunkedInlBelow_entails (sp : BitVec 64) (subStack : Nat) (hle : subStack ≤ chunkedInlBelowStack) :
    chunkedInlBelowRest sp subStack ∗ stackAt (sp - 128#64) subStack ⊢
      stackAt (sp - 128#64) chunkedInlBelowStack :=
  Entails.of_eq (chunkedInlBelow_split sp subStack hle).symm

theorem chunkedInlBelow_eq_polyMerge (sp : BitVec 64) :
    stackAt (sp - 128#64) chunkedInlBelowStack = stackAt (sp - 128#64) polyMergeStack := rfl

theorem chunkedInlBelow_skipField98 (sp : BitVec 64) :
    stackAt (sp - 128#64) chunkedInlBelowStack =
      chunkedInlBelowRest sp (skipField3Stack 98) ∗ stackAt (sp - 128#64) (skipField3Stack 98) :=
  chunkedInlBelow_split sp (skipField3Stack 98) (by decide)

theorem chunkedInlBelow_skipField98_entails (sp : BitVec 64) :
    chunkedInlBelowRest sp (skipField3Stack 98) ∗ stackAt (sp - 128#64) (skipField3Stack 98) ⊢
      stackAt (sp - 128#64) chunkedInlBelowStack :=
  chunkedInlBelow_entails sp (skipField3Stack 98) (by decide)

theorem chunkedInlBelow_skipField97 (sp : BitVec 64) :
    stackAt (sp - 128#64) chunkedInlBelowStack =
      chunkedInlBelowRest sp (skipField3Stack 97) ∗ stackAt (sp - 128#64) (skipField3Stack 97) :=
  chunkedInlBelow_split sp (skipField3Stack 97) (by decide)

theorem chunkedInlBelow_skipField97_entails (sp : BitVec 64) :
    chunkedInlBelowRest sp (skipField3Stack 97) ∗ stackAt (sp - 128#64) (skipField3Stack 97) ⊢
      stackAt (sp - 128#64) chunkedInlBelowStack :=
  chunkedInlBelow_entails sp (skipField3Stack 97) (by decide)

theorem chunkedInlBelow_authMerge (sp : BitVec 64) :
    stackAt (sp - 128#64) chunkedInlBelowStack =
      chunkedInlBelowRest sp authMergeStack ∗ stackAt (sp - 128#64) authMergeStack :=
  chunkedInlBelow_split sp authMergeStack (by decide)

theorem chunkedInlBelow_authMerge_entails (sp : BitVec 64) :
    chunkedInlBelowRest sp authMergeStack ∗ stackAt (sp - 128#64) authMergeStack ⊢
      stackAt (sp - 128#64) chunkedInlBelowStack :=
  chunkedInlBelow_entails sp authMergeStack (by decide)

theorem chunkedInlBelow_bytesMerge3 (sp : BitVec 64) :
    stackAt (sp - 128#64) chunkedInlBelowStack =
      chunkedInlBelowRest sp bytesMerge3Stack ∗ stackAt (sp - 128#64) bytesMerge3Stack :=
  chunkedInlBelow_split sp bytesMerge3Stack (by decide)

theorem chunkedInlBelow_bytesMerge3_entails (sp : BitVec 64) :
    chunkedInlBelowRest sp bytesMerge3Stack ∗ stackAt (sp - 128#64) bytesMerge3Stack ⊢
      stackAt (sp - 128#64) chunkedInlBelowStack :=
  chunkedInlBelow_entails sp bytesMerge3Stack (by decide)

theorem chunkedInlBelow_decodeVarint2 (sp : BitVec 64) :
    stackAt (sp - 128#64) chunkedInlBelowStack =
      chunkedInlBelowRest sp decodeVarint2Stack ∗ stackAt (sp - 128#64) decodeVarint2Stack :=
  chunkedInlBelow_split sp decodeVarint2Stack (by decide)

theorem chunkedInlBelow_decodeVarint2_entails (sp : BitVec 64) :
    chunkedInlBelowRest sp decodeVarint2Stack ∗ stackAt (sp - 128#64) decodeVarint2Stack ⊢
      stackAt (sp - 128#64) chunkedInlBelowStack :=
  chunkedInlBelow_entails sp decodeVarint2Stack (by decide)

theorem chunkedInlBelow_decodeErrorHook (sp : BitVec 64) :
    stackAt (sp - 128#64) chunkedInlBelowStack =
      chunkedInlBelowRest sp decodeErrorHookStack ∗ stackAt (sp - 128#64) decodeErrorHookStack :=
  chunkedInlBelow_split sp decodeErrorHookStack (by decide)

theorem chunkedInlBelow_decodeErrorHook_entails (sp : BitVec 64) :
    chunkedInlBelowRest sp decodeErrorHookStack ∗ stackAt (sp - 128#64) decodeErrorHookStack ⊢
      stackAt (sp - 128#64) chunkedInlBelowStack :=
  chunkedInlBelow_entails sp decodeErrorHookStack (by decide)

/-! ## 3. `decodeErrorAtStackLen` Bound Entailment Lemmas (`n ≤ 2` and `n ≤ 3`) -/

theorem decodeErrorWith_zero_entails_le2_inl (A : RustAlloc) (e : BitVec 64) :
    decodeErrorAtStackLen A e 0 ⊢ ∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A e n := by
  refine Entails.trans ?_ (Entails.sepExists_intro 0)
  simp only [Nat.zero_le, pure_true, emp_sepConj]; exact Entails.refl _

theorem decodeErrorWith_one_entails_le2_inl (A : RustAlloc) (e : BitVec 64) :
    decodeErrorAtStackLen A e 1 ⊢ ∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A e n := by
  refine Entails.trans ?_ (Entails.sepExists_intro 1)
  rw [pure_sepConj_of_true (by decide : 1 ≤ 2)]; exact Entails.refl _

theorem decodeErrorWith_succ_of_le1_entails_le2_inl (A : RustAlloc) (e : BitVec 64) (n : Nat) (hn : n ≤ 1) :
    decodeErrorAtStackLen A e (n + 1) ⊢ ∃∗ k : Nat, ⌜k ≤ 2⌝ ∗ decodeErrorAtStackLen A e k := by
  refine Entails.trans ?_ (Entails.sepExists_intro (n + 1))
  rw [pure_sepConj_of_true (by omega : n + 1 ≤ 2)]; exact Entails.refl _

theorem decodeErrorWith_zero_entails_le3_inl (A : RustAlloc) (e : BitVec 64) :
    decodeErrorAtStackLen A e 0 ⊢ ∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A e n := by
  refine Entails.trans ?_ (Entails.sepExists_intro 0)
  simp only [Nat.zero_le, pure_true, emp_sepConj]; exact Entails.refl _

theorem decodeErrorWith_one_entails_le3_inl (A : RustAlloc) (e : BitVec 64) :
    decodeErrorAtStackLen A e 1 ⊢ ∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A e n := by
  refine Entails.trans ?_ (Entails.sepExists_intro 1)
  rw [pure_sepConj_of_true (by decide : 1 ≤ 3)]; exact Entails.refl _

theorem decodeErrorWith_succ_of_le1_entails_le3_inl (A : RustAlloc) (e : BitVec 64) (n : Nat) (hn : n ≤ 1) :
    decodeErrorAtStackLen A e (n + 1) ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A e k := by
  refine Entails.trans ?_ (Entails.sepExists_intro (n + 1))
  rw [pure_sepConj_of_true (by omega : n + 1 ≤ 3)]; exact Entails.refl _

theorem decodeErrorWith_succ_of_le2_entails_le3_inl (A : RustAlloc) (e : BitVec 64) (n : Nat) (hn : n ≤ 2) :
    decodeErrorAtStackLen A e (n + 1) ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A e k := by
  refine Entails.trans ?_ (Entails.sepExists_intro (n + 1))
  rw [pure_sepConj_of_true (by omega : n + 1 ≤ 3)]; exact Entails.refl _

theorem decodeErrorWith_le2_entails_le3_inl (A : RustAlloc) (e : BitVec 64) (n : Nat) (hn : n ≤ 2) :
    decodeErrorAtStackLen A e n ⊢ ∃∗ k : Nat, ⌜k ≤ 3⌝ ∗ decodeErrorAtStackLen A e k := by
  refine Entails.trans ?_ (Entails.sepExists_intro n)
  rw [pure_sepConj_of_true (by omega : n ≤ 3)]; exact Entails.refl _

/-! ## 4. Capacity-Bounded `Unchunked` & `Chunked` Predicates & Default-Init Bridges -/

/-- Capacity-bounded 56-byte `Unchunked2` (`KeysUnsampled`, `NoHeaderReceived`, `Ct2Sent`):
`auth` at `+0x00` (`48`B) and `epoch` at `+0x30` (`8`B). -/
def unchunked2CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) : SepProp :=
  optAuthenticatorPBCapAt A a bsLen auth ∗ ((a + 0x30#64) ↦₆₄ epoch)

theorem unchunked2CapAt_mono (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) {m n : Nat} (hle : m ≤ n) :
    unchunked2CapAt A a n epoch auth ⊢ unchunked2CapAt A a m epoch auth :=
  sepConj_mono_left (optAuthenticatorPBCapAt_mono A a auth hle)

theorem unchunked2CapAt_entails_unchunked2At (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (epoch : BitVec 64) (auth : Option ProtoAuthenticator) :
    unchunked2CapAt A a n epoch auth ⊢ unchunked2At A a epoch auth :=
  sepConj_mono_left (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A a n auth)

theorem memRegion_48_split_40_8 (a : BitVec 64) :
    memRegion (a + 8#64) 48 =
      memRegion (a + 8#64) 40 ∗ (∃∗ w : BitVec 64, ((a + 48#64) ↦₆₄ w)) := by
  have s1 := ProofLib.memRegion_split (a + 8#64) 40 8 (by decide)
  rw [s1, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-- Default-init of `Option<Unchunked2>` when `none`: writing `noneCap` (`0xffffffffffffffff#64`) at `a`
and `0#64` at `a + 48#64` (keeping `memRegion (a + 8#64) 40`) produces `unchunked2CapAt A a n 0#64 none`. -/
theorem default_unchunked2_entails_cap (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40 ∗ ((a + 48#64) ↦₆₄ 0#64) ⊢
    unchunked2CapAt A a n 0#64 none :=
  Entails.of_eq (by dsimp only [unchunked2CapAt, optAuthenticatorPBCapAt]; ac_rfl)

/-- Capacity-bounded `Option<V1State.Unchunked.KeysUnsampled>` at `a` (`56` bytes). -/
def optKeysUnsampledPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.Unchunked.KeysUnsampled → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some u => unchunked2CapAt A a bsLen u.epoch u.auth

/-- Capacity-bounded `Option<V1State.Unchunked.NoHeaderReceived>` at `a` (`56` bytes). -/
def optNoHeaderReceivedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.Unchunked.NoHeaderReceived → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some u => unchunked2CapAt A a bsLen u.epoch u.auth

/-- Capacity-bounded `Option<V1State.Unchunked.Ct2Sent>` at `a` (`56` bytes). -/
def optCt2SentPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.Unchunked.Ct2Sent → SepProp
  | none => (a ↦₆₄ noneCap2) ∗ memRegion (a + 8#64) 48
  | some u => unchunked2CapAt A a bsLen u.epoch u.auth

theorem optKeysUnsampledPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) {m n : Nat} (hle : m ≤ n) :
    optKeysUnsampledPBCapAt A a n opt ⊢ optKeysUnsampledPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked2CapAt_mono A a u.epoch u.auth hle

theorem optKeysUnsampledPBCapAt_entails (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.Unchunked.KeysUnsampled) :
    optKeysUnsampledPBCapAt A a n opt ⊢ optKeysUnsampledPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked2CapAt_entails_unchunked2At A a n u.epoch u.auth

theorem optNoHeaderReceivedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) {m n : Nat} (hle : m ≤ n) :
    optNoHeaderReceivedPBCapAt A a n opt ⊢ optNoHeaderReceivedPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked2CapAt_mono A a u.epoch u.auth hle

theorem optNoHeaderReceivedPBCapAt_entails (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.Unchunked.NoHeaderReceived) :
    optNoHeaderReceivedPBCapAt A a n opt ⊢ optNoHeaderReceivedPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked2CapAt_entails_unchunked2At A a n u.epoch u.auth

theorem optCt2SentPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) {m n : Nat} (hle : m ≤ n) :
    optCt2SentPBCapAt A a n opt ⊢ optCt2SentPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked2CapAt_mono A a u.epoch u.auth hle

theorem optCt2SentPBCapAt_entails (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.Unchunked.Ct2Sent) :
    optCt2SentPBCapAt A a n opt ⊢ optCt2SentPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked2CapAt_entails_unchunked2At A a n u.epoch u.auth

theorem pointsTo_zero_entails_vecU8CapAt_inl (A : RustAlloc) (a ptr : BitVec 64) (n : Nat) (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A a cap ptr []) := by
  refine Entails.trans ?_ (Entails.sepExists_right 0#64 (Entails.sepExists_right ptr (Entails.refl _)))
  refine Entails.pure_right (bytesMergeCapOk_zero (n := n)) ?_
  rw [vecU8At_eq_header_sep_buf, vecHeader]; unfold vecU8Buf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
  exact Entails.pure_right ⟨by decide, by decide, hptr⟩ (Entails.refl _)

/-- Capacity-bounded 80-byte `Unchunked3` (`HeaderReceived`, `EkSent`):
`v3: Vec<u8>` at `+0x00` (`24`B), `auth` at `+0x18` (`48`B), `epoch` at `+0x48` (`8`B). -/
def unchunked3CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) : SepProp :=
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v3) ∗
  optAuthenticatorPBCapAt A (a + 0x18#64) bsLen auth ∗
  ((a + 0x48#64) ↦₆₄ epoch)

theorem unchunked3CapAt_mono (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8))
    {m n : Nat} (hle : m ≤ n) :
    unchunked3CapAt A a n epoch auth v3 ⊢ unchunked3CapAt A a m epoch auth v3 :=
  sepConj_mono (vecU8CapAt_mono A a v3 hle)
    (sepConj_mono_left (optAuthenticatorPBCapAt_mono A (a + 0x18#64) auth hle))

theorem unchunked3CapAt_entails_unchunked3At (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 : List (BitVec 8)) :
    unchunked3CapAt A a n epoch auth v3 ⊢ unchunked3At A a epoch auth v3 :=
  sepConj_mono (vecU8CapAt_entails_vecU8 A a n v3)
    (sepConj_mono_left (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (a + 0x18#64) n auth))

theorem memRegion_unchunked3_none_split (a : BitVec 64) :
    memRegion (a + 8#64) 72 =
      ∃∗ v72 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((a + 8#64) ↦₆₄ v8) ∗ ((a + 16#64) ↦₆₄ v16) ∗ ((a + 24#64) ↦₆₄ v24) ∗
        memRegion (a + 32#64) 40 ∗ ((a + 72#64) ↦₆₄ v72) := by
  have s1 := memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 64) (N := 72) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 56) (N := 64) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := a + 24#64) (b' := a + 32#64) (n := 8) (k := 48) (N := 56) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := a + 32#64) (b' := a + 72#64) (n := 40) (k := 8) (N := 48) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, ProofLib.memRegion_eight (a + 8#64), ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64), ProofLib.memRegion_eight (a + 72#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem default_unchunked3_entails_cap (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ noneCap) ∗ memRegion (a + 32#64) 40 ∗ ((a + 72#64) ↦₆₄ 0#64) ⊢
      unchunked3CapAt A a n 0#64 none [] := by
  dsimp only [unchunked3CapAt, optAuthenticatorPBCapAt]
  have h1 := pointsTo_zero_entails_vecU8CapAt_inl A a 1#64 n (by decide)
  have h32 : a + 0x18#64 + 8#64 = a + 32#64 := by bv_lin
  rw [h32]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h1)

/-- Capacity-bounded `Option<V1State.Unchunked.HeaderReceived>` at `a` (`80` bytes). -/
def optHeaderReceivedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.Unchunked.HeaderReceived → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some u => unchunked3CapAt A a bsLen u.epoch u.auth u.hdr

/-- Capacity-bounded `Option<V1State.Unchunked.EkSent>` at `a` (`80` bytes). -/
def optEkSentPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.Unchunked.EkSent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72
  | some u => unchunked3CapAt A a bsLen u.epoch u.auth u.dk

theorem optHeaderReceivedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderReceived) {m n : Nat} (hle : m ≤ n) :
    optHeaderReceivedPBCapAt A a n opt ⊢ optHeaderReceivedPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked3CapAt_mono A a u.epoch u.auth u.hdr hle

theorem optHeaderReceivedPBCapAt_entails (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.Unchunked.HeaderReceived) :
    optHeaderReceivedPBCapAt A a n opt ⊢ optHeaderReceivedPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked3CapAt_entails_unchunked3At A a n u.epoch u.auth u.hdr

theorem optEkSentPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.EkSent) {m n : Nat} (hle : m ≤ n) :
    optEkSentPBCapAt A a n opt ⊢ optEkSentPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked3CapAt_mono A a u.epoch u.auth u.dk hle

theorem optEkSentPBCapAt_entails (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.Unchunked.EkSent) :
    optEkSentPBCapAt A a n opt ⊢ optEkSentPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked3CapAt_entails_unchunked3At A a n u.epoch u.auth u.dk

/-- Capacity-bounded 104-byte `Unchunked4` (`HeaderSent`):
`v3: Vec<u8>` at `+0x00`, `v4: Vec<u8>` at `+0x18`, `auth` at `+0x30`, `epoch` at `+0x60`. -/
def unchunked4CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator)
    (v3 v4 : List (BitVec 8)) : SepProp :=
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v3) ∗
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr v4) ∗
  optAuthenticatorPBCapAt A (a + 0x30#64) bsLen auth ∗
  ((a + 0x60#64) ↦₆₄ epoch)

theorem unchunked4CapAt_mono (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 : List (BitVec 8))
    {m n : Nat} (hle : m ≤ n) :
    unchunked4CapAt A a n epoch auth v3 v4 ⊢ unchunked4CapAt A a m epoch auth v3 v4 :=
  sepConj_mono (vecU8CapAt_mono A a v3 hle)
    (sepConj_mono (vecU8CapAt_mono A (a + 0x18#64) v4 hle)
      (sepConj_mono_left (optAuthenticatorPBCapAt_mono A (a + 0x30#64) auth hle)))

theorem unchunked4CapAt_entails_unchunked4At (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 : List (BitVec 8)) :
    unchunked4CapAt A a n epoch auth v3 v4 ⊢ unchunked4At A a epoch auth v3 v4 :=
  sepConj_mono (vecU8CapAt_entails_vecU8 A a n v3)
    (sepConj_mono (vecU8CapAt_entails_vecU8 A (a + 0x18#64) n v4)
      (sepConj_mono_left (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (a + 0x30#64) n auth)))

/-- Capacity-bounded `Option<V1State.Unchunked.HeaderSent>` at `a` (`104` bytes). -/
def optHeaderSentPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.Unchunked.HeaderSent → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 96
  | some u => unchunked4CapAt A a bsLen u.epoch u.auth u.ek u.dk

theorem optHeaderSentPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderSent) {m n : Nat} (hle : m ≤ n) :
    optHeaderSentPBCapAt A a n opt ⊢ optHeaderSentPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked4CapAt_mono A a u.epoch u.auth u.ek u.dk hle

theorem optHeaderSentPBCapAt_entails (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.Unchunked.HeaderSent) :
    optHeaderSentPBCapAt A a n opt ⊢ optHeaderSentPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked4CapAt_entails_unchunked4At A a n u.epoch u.auth u.ek u.dk

/-- Capacity-bounded 128-byte `Unchunked5` (`Ct1SentEkReceived`):
`v3` at `+0x00`, `v4` at `+0x18`, `v5` at `+0x30`, `auth` at `+0x48`, `epoch` at `+0x78`. -/
def unchunked5CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator)
    (v3 v4 v5 : List (BitVec 8)) : SepProp :=
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr v3) ∗
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr v4) ∗
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x30#64) cap ptr v5) ∗
  optAuthenticatorPBCapAt A (a + 0x48#64) bsLen auth ∗
  ((a + 0x78#64) ↦₆₄ epoch)

theorem unchunked5CapAt_mono (A : RustAlloc) (a : BitVec 64)
    (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8))
    {m n : Nat} (hle : m ≤ n) :
    unchunked5CapAt A a n epoch auth v3 v4 v5 ⊢ unchunked5CapAt A a m epoch auth v3 v4 v5 :=
  sepConj_mono (vecU8CapAt_mono A a v3 hle)
    (sepConj_mono (vecU8CapAt_mono A (a + 0x18#64) v4 hle)
      (sepConj_mono (vecU8CapAt_mono A (a + 0x30#64) v5 hle)
        (sepConj_mono_left (optAuthenticatorPBCapAt_mono A (a + 0x48#64) auth hle))))

theorem unchunked5CapAt_entails_unchunked5At (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (epoch : BitVec 64) (auth : Option ProtoAuthenticator) (v3 v4 v5 : List (BitVec 8)) :
    unchunked5CapAt A a n epoch auth v3 v4 v5 ⊢ unchunked5At A a epoch auth v3 v4 v5 :=
  sepConj_mono (vecU8CapAt_entails_vecU8 A a n v3)
    (sepConj_mono (vecU8CapAt_entails_vecU8 A (a + 0x18#64) n v4)
      (sepConj_mono (vecU8CapAt_entails_vecU8 A (a + 0x30#64) n v5)
        (sepConj_mono_left (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A (a + 0x48#64) n auth))))

/-- Capacity-bounded `Option<V1State.Unchunked.Ct1SentEkReceived>` at `a` (`128` bytes). -/
def optCt1SentEkReceivedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option V1State.Unchunked.Ct1SentEkReceived → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120
  | some u => unchunked5CapAt A a bsLen u.epoch u.auth u.es u.ek u.ct1

theorem optCt1SentEkReceivedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) {m n : Nat} (hle : m ≤ n) :
    optCt1SentEkReceivedPBCapAt A a n opt ⊢ optCt1SentEkReceivedPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked5CapAt_mono A a u.epoch u.auth u.es u.ek u.ct1 hle

theorem optCt1SentEkReceivedPBCapAt_entails (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    optCt1SentEkReceivedPBCapAt A a n opt ⊢ optCt1SentEkReceivedPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some u => exact unchunked5CapAt_entails_unchunked5At A a n u.epoch u.auth u.es u.ek u.ct1

/-! ## 5. `PolynomialDecoder` and `PolynomialEncoder` `Option` Default-Init Bridges -/

def OptPolyDecoderBound (opt : Option PolynomialDecoder) (bsLen : Nat) : Prop :=
  (opt.getD default).pts.length + bsLen < 2 ^ 56

theorem optPolyDecoderBound_mono {opt : Option PolynomialDecoder} {m n : Nat}
    (h : OptPolyDecoderBound opt n) (hle : m ≤ n) :
    OptPolyDecoderBound opt m := by
  unfold OptPolyDecoderBound at *; omega

theorem optPolyDecoderBound_of_merge {opt : Option PolynomialDecoder}
    {wt : Proto.WireType} {m' : PolynomialDecoder} {rest after : List (BitVec 8)}
    (h : OptPolyDecoderBound opt rest.length)
    (hm : (Proto.mergeMessage PolynomialDecoder.mergeField wt (opt.getD default) rest 98).toOption = some (m', after)) :
    OptPolyDecoderBound (some m') after.length := by
  unfold OptPolyDecoderBound at *
  have hle := polynomialDecoder_mergeMessage_pts_le hm
  dsimp only [Option.getD_some]
  omega

def OptPolyEncoderBound (opt : Option PolynomialEncoder) (bsLen : Nat) : Prop :=
  (opt.getD default).pts.length + bsLen < 2 ^ 56 ∧
  (opt.getD default).polys.length + bsLen < 2 ^ 56

theorem optPolyEncoderBound_mono {opt : Option PolynomialEncoder} {m n : Nat}
    (h : OptPolyEncoderBound opt n) (hle : m ≤ n) :
    OptPolyEncoderBound opt m := by
  rcases h with ⟨h1, h2⟩; exact ⟨by omega, by omega⟩

theorem optPolyEncoderBound_of_merge {opt : Option PolynomialEncoder}
    {wt : Proto.WireType} {m' : PolynomialEncoder} {rest after : List (BitVec 8)}
    (h : OptPolyEncoderBound opt rest.length)
    (hm : (Proto.mergeMessage PolynomialEncoder.mergeField wt (opt.getD default) rest 98).toOption = some (m', after)) :
    OptPolyEncoderBound (some m') after.length := by
  rcases h with ⟨h1, h2⟩
  obtain ⟨hle1, hle2⟩ := polynomialEncoder_mergeMessage_pts_polys_le hm
  exact ⟨by dsimp only [Option.getD_some]; omega, by dsimp only [Option.getD_some]; omega⟩

theorem optPolynomialDecoderPBAt_some_eq (A : RustAlloc) (a : BitVec 64) (d : PolynomialDecoder) :
    optPolynomialDecoderPBAt A a (some d) = protoPolynomialDecoderAt A a (polyDecoderToProto d) := rfl

theorem optPolynomialEncoderPBAt_some_eq (A : RustAlloc) (a : BitVec 64) (e : PolynomialEncoder) :
    optPolynomialEncoderPBAt A a (some e) = protoPolynomialEncoderAt A a (polyEncoderToProto e) := rfl

theorem optPolynomialDecoderPBAt_entails_exists (A : RustAlloc) (a : BitVec 64) (opt : Option PolynomialDecoder) :
    optPolynomialDecoderPBAt A a opt ⊢ ∃∗ opt' : Option PolynomialDecoder, optPolynomialDecoderPBAt A a opt' :=
  Entails.sepExists_intro opt

theorem protoPolynomialDecoderAt_exists_entails_opt_exists (A : RustAlloc) (a : BitVec 64) :
    (∃∗ d' : PolynomialDecoder, protoPolynomialDecoderAt A a (polyDecoderToProto d')) ⊢
      ∃∗ opt' : Option PolynomialDecoder, optPolynomialDecoderPBAt A a opt' :=
  ProofLib.Entails.sepExists_elim fun d' => Entails.sepExists_intro (P := optPolynomialDecoderPBAt A a) (some d')

theorem optPolynomialEncoderPBAt_entails_exists (A : RustAlloc) (a : BitVec 64) (opt : Option PolynomialEncoder) :
    optPolynomialEncoderPBAt A a opt ⊢ ∃∗ opt' : Option PolynomialEncoder, optPolynomialEncoderPBAt A a opt' :=
  Entails.sepExists_intro opt

theorem protoPolynomialEncoderAt_exists_entails_opt_exists (A : RustAlloc) (a : BitVec 64) :
    (∃∗ e' : PolynomialEncoder, protoPolynomialEncoderAt A a (polyEncoderToProto e')) ⊢
      ∃∗ opt' : Option PolynomialEncoder, optPolynomialEncoderPBAt A a opt' :=
  ProofLib.Entails.sepExists_elim fun e' => Entails.sepExists_intro (P := optPolynomialEncoderPBAt A a) (some e')

theorem pointsTo_zero_entails_vecVecU8At_inl (A : RustAlloc) (a ptr : BitVec 64) (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢ ProtoRepr.vecVecU8At A a [] := by
  rw [vecVecU8At_eq_exists_pin]
  refine Entails.trans ?_ (Entails.sepExists_right (VecPin.mk 0#64 ptr) (Entails.refl _))
  rw [vecVecU8PinnedAt_eq_header_buf]; unfold vecVecU8Buf vecBuf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  have hp : ([] : List (List (BitVec 8))).length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by decide, by decide, hptr⟩
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by dsimp only [List.length]; ac_rfl)

theorem memRegion_polyDecoder_none_split_inl (p : BitVec 64) :
    memRegion (p + 8#64) 32 =
      ∃∗ b32 : BitVec 8, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((p + 8#64) ↦₆₄ v8) ∗ ((p + 16#64) ↦₆₄ v16) ∗ ((p + 24#64) ↦₆₄ v24) ∗
        ((p + 32#64) ↦₈ b32) ∗ memRegion (p + 33#64) 7 := by
  have s1 := memRegion_split' (b := p + 8#64) (b' := p + 16#64) (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := p + 16#64) (b' := p + 24#64) (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := p + 24#64) (b' := p + 32#64) (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := p + 32#64) (b' := p + 33#64) (n := 1) (k := 7) (N := 8) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, ProofLib.memRegion_eight (p + 8#64), ProofLib.memRegion_eight (p + 16#64),
    ProofLib.memRegion_eight (p + 24#64), ProofLib.memRegion_one (p + 32#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem pointsTo64_zero_split_32_inl (a : BitVec 64) :
    (a ↦₆₄ 0#64) = (a ↦₃₂ 0#32) ∗ ((a + 4#64) ↦₃₂ 0#32) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  exact pointsToBytes_append a (unpack32 0#32) (unpack32 0#32)

theorem default_polyDecoder_entails_pb_inl (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7 ⊢
      protoPolynomialDecoderAt A p (polyDecoderToProto default) := by
  rw [← optPolynomialDecoderPBAt_some_eq]; unfold optPolynomialDecoderPBAt polynomialDecoderPBAt
  change _ ⊢ ProtoRepr.vecVecU8At A p [] ∗ ((p + 24#64) ↦₃₂ 0#32) ∗ ((p + 28#64) ↦₃₂ 0#32) ∗
    ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7
  have h1 := pointsTo_zero_entails_vecVecU8At_inl A p 8#64 (by decide)
  have h24 : ((p + 24#64) ↦₆₄ 0#64) = ((p + 24#64) ↦₃₂ 0#32) ∗ ((p + 28#64) ↦₃₂ 0#32) := by
    rw [pointsTo64_zero_split_32_inl (p + 24#64)]
    have h28 : p + 24#64 + 4#64 = p + 28#64 := by bv_lin
    rw [h28]
  rw [h24]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h1)

theorem memRegion_polyEncoder_none_split_inl (p : BitVec 64) :
    memRegion (p + 8#64) 48 =
      ∃∗ v48 : BitVec 32, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64,
      ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((p + 8#64) ↦₆₄ v8) ∗ ((p + 16#64) ↦₆₄ v16) ∗ ((p + 24#64) ↦₆₄ v24) ∗
        ((p + 32#64) ↦₆₄ v32) ∗ ((p + 40#64) ↦₆₄ v40) ∗ ((p + 48#64) ↦₃₂ v48) ∗ memRegion (p + 52#64) 4 := by
  have s1 := memRegion_split' (b := p + 8#64) (b' := p + 16#64) (n := 8) (k := 40) (N := 48) rfl (by bv_lin) (by decide)
  have s2 := memRegion_split' (b := p + 16#64) (b' := p + 24#64) (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  have s3 := memRegion_split' (b := p + 24#64) (b' := p + 32#64) (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have s4 := memRegion_split' (b := p + 32#64) (b' := p + 40#64) (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have s5 := memRegion_split' (b := p + 40#64) (b' := p + 48#64) (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  have s6 := memRegion_split' (b := p + 48#64) (b' := p + 52#64) (n := 4) (k := 4) (N := 8) rfl (by bv_lin) (by decide)
  rw [s1, s2, s3, s4, s5, s6, ProofLib.memRegion_eight (p + 8#64), ProofLib.memRegion_eight (p + 16#64),
    ProofLib.memRegion_eight (p + 24#64), ProofLib.memRegion_eight (p + 32#64), ProofLib.memRegion_eight (p + 40#64),
    ProofLib.memRegion_four (p + 48#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem default_polyEncoder_entails_pb_inl (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4 ⊢
      protoPolynomialEncoderAt A p (polyEncoderToProto default) := by
  rw [← optPolynomialEncoderPBAt_some_eq]; unfold optPolynomialEncoderPBAt polynomialEncoderPBAt
  change _ ⊢ ProtoRepr.vecVecU8At A p [] ∗ ProtoRepr.vecVecU8At A (p + 24#64) [] ∗ ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4
  have h1 := pointsTo_zero_entails_vecVecU8At_inl A p 8#64 (by decide)
  have h2 := pointsTo_zero_entails_vecVecU8At_inl A (p + 24#64) 8#64 (by decide)
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_lin
  have h40 : p + 24#64 + 16#64 = p + 40#64 := by bv_lin
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

/-! ## 6. Representation Predicates & Hoare `Spec`s for the 7 `V1State.Chunked.*` `merge` Functions -/

def chunkedKeysUnsampledPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.KeysUnsampled) : SepProp :=
  optKeysUnsampledPBAt A a m.uc

def chunkedKeysUnsampledPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.KeysUnsampled) : SepProp :=
  optKeysUnsampledPBCapAt A a bsLen m.uc

theorem chunkedKeysUnsampledPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.KeysUnsampled) {k n : Nat} (hle : k ≤ n) :
    chunkedKeysUnsampledPBCapAt A a n m ⊢ chunkedKeysUnsampledPBCapAt A a k m :=
  optKeysUnsampledPBCapAt_mono A a m.uc hle

theorem chunkedKeysUnsampledPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.KeysUnsampled) :
    chunkedKeysUnsampledPBCapAt A a n m ⊢ chunkedKeysUnsampledPBAt A a m :=
  optKeysUnsampledPBCapAt_entails A a n m.uc

theorem chunkedKeysUnsampledPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.KeysUnsampled) :
    chunkedKeysUnsampledPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.KeysUnsampled, chunkedKeysUnsampledPBAt A a m' :=
  Entails.sepExists_intro m

def chunkedNoHeaderReceivedPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.NoHeaderReceived) : SepProp :=
  optPolynomialDecoderPBAt A a m.receivingHdr ∗
    optNoHeaderReceivedPBAt A (a + 40#64) m.uc

def chunkedNoHeaderReceivedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.NoHeaderReceived) : SepProp :=
  optPolynomialDecoderPBAt A a m.receivingHdr ∗
    optNoHeaderReceivedPBCapAt A (a + 40#64) bsLen m.uc

theorem chunkedNoHeaderReceivedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.NoHeaderReceived) {k n : Nat} (hle : k ≤ n) :
    chunkedNoHeaderReceivedPBCapAt A a n m ⊢ chunkedNoHeaderReceivedPBCapAt A a k m :=
  sepConj_mono_right (optNoHeaderReceivedPBCapAt_mono A (a + 40#64) m.uc hle)

theorem chunkedNoHeaderReceivedPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.NoHeaderReceived) :
    chunkedNoHeaderReceivedPBCapAt A a n m ⊢ chunkedNoHeaderReceivedPBAt A a m :=
  sepConj_mono_right (optNoHeaderReceivedPBCapAt_entails A (a + 40#64) n m.uc)

theorem chunkedNoHeaderReceivedPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.NoHeaderReceived) :
    chunkedNoHeaderReceivedPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.NoHeaderReceived, chunkedNoHeaderReceivedPBAt A a m' :=
  Entails.sepExists_intro m

def chunkedCt2SampledPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.Ct2Sampled) : SepProp :=
  optPolynomialEncoderPBAt A a m.sendingCt2 ∗
    optCt2SentPBAt A (a + 56#64) m.uc

def chunkedCt2SampledPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.Ct2Sampled) : SepProp :=
  optPolynomialEncoderPBAt A a m.sendingCt2 ∗
    optCt2SentPBCapAt A (a + 56#64) bsLen m.uc

theorem chunkedCt2SampledPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.Ct2Sampled) {k n : Nat} (hle : k ≤ n) :
    chunkedCt2SampledPBCapAt A a n m ⊢ chunkedCt2SampledPBCapAt A a k m :=
  sepConj_mono_right (optCt2SentPBCapAt_mono A (a + 56#64) m.uc hle)

theorem chunkedCt2SampledPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.Ct2Sampled) :
    chunkedCt2SampledPBCapAt A a n m ⊢ chunkedCt2SampledPBAt A a m :=
  sepConj_mono_right (optCt2SentPBCapAt_entails A (a + 56#64) n m.uc)

theorem chunkedCt2SampledPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.Ct2Sampled) :
    chunkedCt2SampledPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.Ct2Sampled, chunkedCt2SampledPBAt A a m' :=
  Entails.sepExists_intro m

def chunkedHeaderReceivedPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.HeaderReceived) : SepProp :=
  optHeaderReceivedPBAt A a m.uc ∗
    optPolynomialDecoderPBAt A (a + 80#64) m.receivingEk

def chunkedHeaderReceivedPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.HeaderReceived) : SepProp :=
  optHeaderReceivedPBCapAt A a bsLen m.uc ∗
    optPolynomialDecoderPBAt A (a + 80#64) m.receivingEk

theorem chunkedHeaderReceivedPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.HeaderReceived) {k n : Nat} (hle : k ≤ n) :
    chunkedHeaderReceivedPBCapAt A a n m ⊢ chunkedHeaderReceivedPBCapAt A a k m :=
  sepConj_mono_left (optHeaderReceivedPBCapAt_mono A a m.uc hle)

theorem chunkedHeaderReceivedPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.HeaderReceived) :
    chunkedHeaderReceivedPBCapAt A a n m ⊢ chunkedHeaderReceivedPBAt A a m :=
  sepConj_mono_left (optHeaderReceivedPBCapAt_entails A a n m.uc)

theorem chunkedHeaderReceivedPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.HeaderReceived) :
    chunkedHeaderReceivedPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.HeaderReceived, chunkedHeaderReceivedPBAt A a m' :=
  Entails.sepExists_intro m

def chunkedKeysSampledPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.KeysSampled) : SepProp :=
  optHeaderSentPBAt A a m.uc ∗
    optPolynomialEncoderPBAt A (a + 104#64) m.sendingHdr

def chunkedKeysSampledPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.KeysSampled) : SepProp :=
  optHeaderSentPBCapAt A a bsLen m.uc ∗
    optPolynomialEncoderPBAt A (a + 104#64) m.sendingHdr

theorem chunkedKeysSampledPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.KeysSampled) {k n : Nat} (hle : k ≤ n) :
    chunkedKeysSampledPBCapAt A a n m ⊢ chunkedKeysSampledPBCapAt A a k m :=
  sepConj_mono_left (optHeaderSentPBCapAt_mono A a m.uc hle)

theorem chunkedKeysSampledPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.KeysSampled) :
    chunkedKeysSampledPBCapAt A a n m ⊢ chunkedKeysSampledPBAt A a m :=
  sepConj_mono_left (optHeaderSentPBCapAt_entails A a n m.uc)

theorem chunkedKeysSampledPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.KeysSampled) :
    chunkedKeysSampledPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.KeysSampled, chunkedKeysSampledPBAt A a m' :=
  Entails.sepExists_intro m

def chunkedHeaderSentPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.HeaderSent) : SepProp :=
  optEkSentPBCapAt A a bsLen m.uc ∗
    optPolynomialEncoderPBAt A (a + 80#64) m.sendingEk ∗
    optPolynomialDecoderPBAt A (a + 136#64) m.receivingCt1

theorem chunkedHeaderSentPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.HeaderSent) {k n : Nat} (hle : k ≤ n) :
    chunkedHeaderSentPBCapAt A a n m ⊢ chunkedHeaderSentPBCapAt A a k m :=
  sepConj_mono_left (optEkSentPBCapAt_mono A a m.uc hle)

theorem chunkedHeaderSentPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.HeaderSent) :
    chunkedHeaderSentPBCapAt A a n m ⊢ chunkedHeaderSentPBAt A a m :=
  sepConj_mono_left (optEkSentPBCapAt_entails A a n m.uc)

theorem chunkedHeaderSentPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.HeaderSent) :
    chunkedHeaderSentPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.HeaderSent, chunkedHeaderSentPBAt A a m' :=
  Entails.sepExists_intro m

def chunkedEkReceivedCt1SampledPBAt (A : RustAlloc) (a : BitVec 64) (m : V1State.Chunked.EkReceivedCt1Sampled) : SepProp :=
  optCt1SentEkReceivedPBAt A a m.uc ∗
    optPolynomialEncoderPBAt A (a + 128#64) m.sendingCt1

def chunkedEkReceivedCt1SampledPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (m : V1State.Chunked.EkReceivedCt1Sampled) : SepProp :=
  optCt1SentEkReceivedPBCapAt A a bsLen m.uc ∗
    optPolynomialEncoderPBAt A (a + 128#64) m.sendingCt1

theorem chunkedEkReceivedCt1SampledPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.EkReceivedCt1Sampled) {k n : Nat} (hle : k ≤ n) :
    chunkedEkReceivedCt1SampledPBCapAt A a n m ⊢ chunkedEkReceivedCt1SampledPBCapAt A a k m :=
  sepConj_mono_left (optCt1SentEkReceivedPBCapAt_mono A a m.uc hle)

theorem chunkedEkReceivedCt1SampledPBCapAt_entails_pb (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : V1State.Chunked.EkReceivedCt1Sampled) :
    chunkedEkReceivedCt1SampledPBCapAt A a n m ⊢ chunkedEkReceivedCt1SampledPBAt A a m :=
  sepConj_mono_left (optCt1SentEkReceivedPBCapAt_entails A a n m.uc)

theorem chunkedEkReceivedCt1SampledPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Chunked.EkReceivedCt1Sampled) :
    chunkedEkReceivedCt1SampledPBAt A a m ⊢ ∃∗ m' : V1State.Chunked.EkReceivedCt1Sampled, chunkedEkReceivedCt1SampledPBAt A a m' :=
  Entails.sepExists_intro m

structure ChunkedKeysUnsampledMergeGhost where
  (wt : WireType) (msgPtr : BitVec 64) (msg : V1State.Chunked.KeysUnsampled)
  (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))

def chunkedKeysUnsampledMergeSpec (A : RustAlloc) : Spec ChunkedKeysUnsampledMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63⌝ ∗
      chunkedKeysUnsampledPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp chunkedInlStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp chunkedInlStack ∗
      match (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedKeysUnsampledPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.KeysUnsampled, chunkedKeysUnsampledPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure ChunkedNoHeaderReceivedMergeGhost where
  (wt : WireType) (msgPtr : BitVec 64) (msg : V1State.Chunked.NoHeaderReceived)
  (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))

def chunkedNoHeaderReceivedMergeSpec (A : RustAlloc) : Spec ChunkedNoHeaderReceivedMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      OptPolyDecoderBound x.msg.receivingHdr x.bs.length⌝ ∗
      chunkedNoHeaderReceivedPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp chunkedInlStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp chunkedInlStack ∗
      match (Proto.mergeMessage V1State.Chunked.NoHeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedNoHeaderReceivedPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.NoHeaderReceived, chunkedNoHeaderReceivedPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure ChunkedCt2SampledMergeGhost where
  (wt : WireType) (msgPtr : BitVec 64) (msg : V1State.Chunked.Ct2Sampled)
  (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))

def chunkedCt2SampledMergeSpec (A : RustAlloc) : Spec ChunkedCt2SampledMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      OptPolyEncoderBound x.msg.sendingCt2 x.bs.length⌝ ∗
      chunkedCt2SampledPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp chunkedInlStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp chunkedInlStack ∗
      match (Proto.mergeMessage V1State.Chunked.Ct2Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedCt2SampledPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.Ct2Sampled, chunkedCt2SampledPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure ChunkedHeaderReceivedMergeGhost where
  (wt : WireType) (msgPtr : BitVec 64) (msg : V1State.Chunked.HeaderReceived)
  (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))

def chunkedHeaderReceivedMergeSpec (A : RustAlloc) : Spec ChunkedHeaderReceivedMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      OptPolyDecoderBound x.msg.receivingEk x.bs.length⌝ ∗
      chunkedHeaderReceivedPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp chunkedInlStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp chunkedInlStack ∗
      match (Proto.mergeMessage V1State.Chunked.HeaderReceived.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedHeaderReceivedPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.HeaderReceived, chunkedHeaderReceivedPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure ChunkedKeysSampledMergeGhost where
  (wt : WireType) (msgPtr : BitVec 64) (msg : V1State.Chunked.KeysSampled)
  (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))

def chunkedKeysSampledMergeSpec (A : RustAlloc) : Spec ChunkedKeysSampledMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      OptPolyEncoderBound x.msg.sendingHdr x.bs.length⌝ ∗
      chunkedKeysSampledPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp chunkedInlStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp chunkedInlStack ∗
      match (Proto.mergeMessage V1State.Chunked.KeysSampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedKeysSampledPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.KeysSampled, chunkedKeysSampledPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure ChunkedHeaderSentMergeGhost where
  (wt : WireType) (msgPtr : BitVec 64) (msg : V1State.Chunked.HeaderSent)
  (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))

def chunkedHeaderSentMergeSpec (A : RustAlloc) : Spec ChunkedHeaderSentMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      OptPolyEncoderBound x.msg.sendingEk x.bs.length ∧
      OptPolyDecoderBound x.msg.receivingCt1 x.bs.length⌝ ∗
      chunkedHeaderSentPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp chunkedInlStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp chunkedInlStack ∗
      match (Proto.mergeMessage V1State.Chunked.HeaderSent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedHeaderSentPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.HeaderSent, chunkedHeaderSentPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

structure ChunkedEkReceivedCt1SampledMergeGhost where
  (wt : WireType) (msgPtr : BitVec 64) (msg : V1State.Chunked.EkReceivedCt1Sampled)
  (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8))

def chunkedEkReceivedCt1SampledMergeSpec (A : RustAlloc) : Spec ChunkedEkReceivedCt1SampledMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      OptPolyEncoderBound x.msg.sendingCt1 x.bs.length⌝ ∗
      chunkedEkReceivedCt1SampledPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ A.pool ∗ stackAt s.sp chunkedInlStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗ stackAt s0.sp chunkedInlStack ∗
      match (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ chunkedEkReceivedCt1SampledPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ (∃∗ n : Nat, ⌜n ≤ 3⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Chunked.EkReceivedCt1Sampled, chunkedEkReceivedCt1SampledPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## 8. `SepWPpIn` Combinators for `.inImage img` Proofs -/

/-- `SepWPp` carrying `ImgCallInv img s` across basic blocks and subroutine calls. -/
def SepWPpIn (img : Obj.Image) (prog : Program) (ret : BitVec 64) (s : State)
    (P : SepProp) (Q Qp : State → SepProp → Prop) : Prop :=
  ImgCallInv img s → SepWPp prog ret s P Q Qp

namespace SepWPpIn

variable {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop}

theorem of_sepWP {mid : BitVec 64}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpIn img prog ret sm Pm Q Qp)) :
    SepWPpIn img prog ret s P Q Qp := by
  intro ⟨hF, hsym⟩ R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext ⟨hsteps.frozenLoaded hF, hsteps.symtab_eq.trans hsym⟩ R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem of_sepWP_ret (h : SepWP prog ret s P Q) : SepWPpIn img prog ret s P Q Qp :=
  fun _ => SepWPp.of_sepWP_ret h

theorem weaken_pre {P' : SepProp} (hent : P ⊢ P') (h : SepWPpIn img prog ret s P' Q Qp) :
    SepWPpIn img prog ret s P Q Qp :=
  fun hinv => SepWPp.weaken_pre hent (h hinv)

theorem call_frame {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpIn img prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPpIn img prog ret s P Q Qp :=
  fun ⟨hF, hsym⟩ => ProofLib.SepWPp.call_frame_frozen hcall hF hsym hpc hrun hsp hlr hspec hφ hP
    hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hFm hsymm => hnext sf hpcm hrunm hspm hcsm ⟨hFm, hsymm⟩) hoom

theorem call_frame_inImage {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpIn img prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPpIn img prog ret s P Q Qp :=
  fun ⟨hF, hsym⟩ => ProofLib.SepWPp.call_inImage_frame hcall hF hsym hpc hrun hsp hlr hspec hφ hP
    hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hFm hsymm => hnext sf hpcm hrunm hspm hcsm ⟨hFm, hsymm⟩) hoom

end SepWPpIn

/-- `SepWPp` carrying `LibsignalCodeRoLoaded pl s.mem` across basic blocks and subroutine calls. -/
def SepWPpLscro (pl : Obj.MultiPlacement) (prog : Program) (ret : BitVec 64) (s : State)
    (P : SepProp) (Q Qp : State → SepProp → Prop) : Prop :=
  LibsignalCodeRoLoaded pl s.mem → SepWPp prog ret s P Q Qp

namespace SepWPpLscro

variable {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
  {Q Qp : State → SepProp → Prop}

theorem of_sepWP {mid : BitVec 64}
    (h : SepWP prog mid s P (fun sm Pm => SepWPpLscro pl prog ret sm Pm Q Qp)) :
    SepWPpLscro pl prog ret s P Q Qp :=
  fun hli => SepWPp.of_sepWP_lscro hli h

theorem of_sepWP_ret (h : SepWP prog ret s P Q) : SepWPpLscro pl prog ret s P Q Qp :=
  fun _ => SepWPp.of_sepWP_ret h

theorem weaken_pre {P' : SepProp} (hent : P ⊢ P') (h : SepWPpLscro pl prog ret s P' Q Qp) :
    SepWPpLscro pl prog ret s P Q Qp :=
  fun hli => SepWPp.weaken_pre hent (h hli)

theorem call_frame {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLscro pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPpLscro pl prog ret s P Q Qp :=
  fun hli => SepWPp.call_frame_keep_lscro hcall hli hpc hrun hsp hlr hspec hφ hP hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hlim => hnext sf hpcm hrunm hspm hcsm hlim) hoom

theorem call_frame_lscro {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop} {T F : SepProp}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpLscro pl prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPpLscro pl prog ret s P Q Qp :=
  fun hli => SepWPp.call_frame_lscro hcall hli hpc hrun hsp hlr hspec hφ hP hexit hpanic
    (fun sf hpcm hrunm hspm hcsm hlim => hnext sf hpcm hrunm hspm hcsm hlim) hoom

end SepWPpLscro

end CryptoVerification.SpqrV1.Prost.MessageMerge

