/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedRepr
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefs
import ProofLib.SepLogic.WPp

/-!
# Shared Definitions & Bridges for Unchunked `prost::encoding::message::merge` (Blocks `311`–`312`)

Provides 112-byte (`0x70`) stack-frame decomposition helpers, capacity-bounded representation
predicates (`protoUnchunkedCt1SentCapAt`, `protoUnchunkedEkSentCt1ReceivedCapAt`), own-stack Hoare
contracts bridged to `ChunkedMerge.unchunked{Ct1Sent,EkSentCt1Received}MergeSpec`, and pure
`mergeField` step lemmas for `Unchunked.EkSentCt1Received::merge` (`0x51c00`, Block `311`) and
`Unchunked.Ct1Sent::merge` (`0x51e9c`, Block `312`).
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
open CryptoVerification.SpqrV1.Auth hiding Entails.sepExists_elim SepWPp.pure_elim bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] unchunkedCt1SentMerge_fnOff unchunkedEkSentCt1ReceivedMerge_fnOff

@[local simp, local arm64_norm]
theorem bv64_sub_zero_u (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
theorem bv64_add_zero_u (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

/-! ## 1. `112`-Byte (`0x70`) Stack Frame Helpers -/

/-- Exact own stack budget for `Ct1Sent::merge` (`0x51e9c`) and `EkSentCt1Received::merge` (`0x51c00`):
own frame `0x70` (`112`) bytes plus `skipField3Stack 97` (`= authMergeStack`). -/
abbrev unchunkedOwnStack : Nat := 112 + skipField3Stack 97

/-- Stack region below the 112-byte frame of `Ct1Sent::merge` / `EkSentCt1Received::merge`. -/
abbrev unchunkedMergeBelow (sp : BitVec 64) : SepProp :=
  stackAt (sp - 112#64) (skipField3Stack 97)

theorem unchunkedMergeBelow_eq_authMergeStack (sp : BitVec 64) :
    unchunkedMergeBelow sp = stackAt (sp - 112#64) authMergeStack := rfl

private theorem bv_sub_add_112 (sp v : BitVec 64) :
    sp - 112#64 = sp - (v + 112#64) + v := by bv_lin

private theorem bv_sub_112_sub (sp v : BitVec 64) :
    sp - 112#64 - v = sp - (v + 112#64) := by bv_lin

private theorem bv_sub_16_96 (sp : BitVec 64) :
    sp - 16#64 - 96#64 = sp - 112#64 := by bv_lin

private theorem bv_sub_16_88 (sp : BitVec 64) :
    sp - 16#64 - 88#64 = sp - 104#64 := by bv_lin

private theorem bv_sub_16_87 (sp : BitVec 64) :
    sp - 16#64 - 87#64 = sp - 103#64 := by bv_lin

private theorem bv_sub_16_86 (sp : BitVec 64) :
    sp - 16#64 - 86#64 = sp - 102#64 := by bv_lin

private theorem bv_sub_16_80 (sp : BitVec 64) :
    sp - 16#64 - 80#64 = sp - 96#64 := by bv_lin

theorem stackAt_unchunkedMerge (sp : BitVec 64) :
    stackAt sp unchunkedOwnStack =
      (∃∗ v19 : BitVec 64, ∃∗ v20 : BitVec 64, ∃∗ v21 : BitVec 64,
        ∃∗ v22 : BitVec 64, ∃∗ v23 : BitVec 64, ∃∗ v_lr : BitVec 64, ∃∗ v_fp : BitVec 64,
        unchunkedMergeBelow sp ∗
          memRegion (sp - 112#64) 48 ∗
          ((sp - 64#64) ↦₆₄ v_fp) ∗ ((sp - 56#64) ↦₆₄ v_lr) ∗
          ((sp - 48#64) ↦₆₄ v23) ∗ memRegion (sp - 40#64) 8 ∗
          ((sp - 32#64) ↦₆₄ v22) ∗ ((sp - 24#64) ↦₆₄ v21) ∗
          ((sp - 16#64) ↦₆₄ v20) ∗ ((sp - 8#64) ↦₆₄ v19)) := by
  simp only [stackAt, unchunkedMergeBelow]
  have hlen : unchunkedOwnStack = skipField3Stack 97 + 112 := by
    simp only [unchunkedOwnStack]; omega
  have hbound : unchunkedOwnStack ≤ 2 ^ 64 := by
    simp only [unchunkedOwnStack, skipField3Stack, decodeVarint2Stack,
      decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]
    omega
  have hbit : BitVec.ofNat 64 unchunkedOwnStack =
      BitVec.ofNat 64 (skipField3Stack 97) + 112#64 := by
    rw [hlen, BitVec.ofNat_add]
  have h1 := memRegion_split'
    (b := sp - BitVec.ofNat 64 unchunkedOwnStack)
    (b' := sp - 112#64)
    (n := skipField3Stack 97) (k := 112)
    (N := unchunkedOwnStack) hlen
    (by rw [hbit]; exact bv_sub_add_112 sp _)
    hbound
  have hsp_sub :
      sp - 112#64 - BitVec.ofNat 64 (skipField3Stack 97) =
        sp - BitVec.ofNat 64 unchunkedOwnStack := by
    rw [hbit]; exact bv_sub_112_sub sp _
  have h2 := memRegion_split' (b := sp - 112#64) (b' := sp - 64#64)
    (n := 48) (k := 64) (N := 112) rfl (by bv_lin) (by decide)
  have h3 := memRegion_split' (b := sp - 64#64) (b' := sp - 56#64)
    (n := 8) (k := 56) (N := 64) rfl (by bv_lin) (by decide)
  have h4 := memRegion_split' (b := sp - 56#64) (b' := sp - 48#64)
    (n := 8) (k := 48) (N := 56) rfl (by bv_lin) (by decide)
  have h5 := memRegion_split' (b := sp - 48#64) (b' := sp - 40#64)
    (n := 8) (k := 40) (N := 48) rfl (by bv_lin) (by decide)
  have h6 := memRegion_split' (b := sp - 40#64) (b' := sp - 32#64)
    (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  have h7 := memRegion_split' (b := sp - 32#64) (b' := sp - 24#64)
    (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have h8 := memRegion_split' (b := sp - 24#64) (b' := sp - 16#64)
    (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have h9 := memRegion_split' (b := sp - 16#64) (b' := sp - 8#64)
    (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  rw [hsp_sub, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    Prost.memRegion_eight (sp - 64#64), Prost.memRegion_eight (sp - 56#64),
    Prost.memRegion_eight (sp - 48#64),
    Prost.memRegion_eight (sp - 32#64), Prost.memRegion_eight (sp - 24#64),
    Prost.memRegion_eight (sp - 16#64), Prost.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem unchunkedMergeBelow_eq_skipBelow3 (sp : BitVec 64) :
    unchunkedMergeBelow sp = skipBelow3 (sp - 16#64) 98 := by
  simp only [unchunkedMergeBelow, skipBelow3, bv_sub_16_96 sp]

theorem unchunkedMergeBelow_leaf (sp : BitVec 64) :
    unchunkedMergeBelow sp =
      skipLeafRest3 (sp - 16#64) 98 ∗ stackAt (sp - 112#64) decodeVarint2Stack := by
  rw [unchunkedMergeBelow_eq_skipBelow3 sp, skipBelow3_leaf (sp - 16#64) 98 (by decide),
    bv_sub_16_96 sp]

theorem unchunkedMergeBelow_leaf_entails (sp : BitVec 64) :
    skipLeafRest3 (sp - 16#64) 98 ∗ stackAt (sp - 112#64) decodeVarint2Stack ⊢
      unchunkedMergeBelow sp :=
  Entails.of_eq (unchunkedMergeBelow_leaf sp).symm

theorem unchunkedMergeBelow_err (sp : BitVec 64) :
    unchunkedMergeBelow sp =
      skipErrRest3 (sp - 16#64) 98 ∗ stackAt (sp - 112#64) decodeErrorHookStack := by
  rw [unchunkedMergeBelow_eq_skipBelow3 sp, skipBelow3_err (sp - 16#64) 98 (by decide),
    bv_sub_16_96 sp]

theorem unchunkedMergeBelow_err_entails (sp : BitVec 64) :
    skipErrRest3 (sp - 16#64) 98 ∗ stackAt (sp - 112#64) decodeErrorHookStack ⊢
      unchunkedMergeBelow sp :=
  Entails.of_eq (unchunkedMergeBelow_err sp).symm

theorem unchunkedMergeBelow_bytesMerge3 (sp : BitVec 64) :
    unchunkedMergeBelow sp =
      skipBytesMergeRest3 (sp - 16#64) 98 ∗ stackAt (sp - 112#64) bytesMerge3Stack := by
  rw [unchunkedMergeBelow_eq_skipBelow3 sp,
    skipBelow3_bytesMerge3 (sp - 16#64) 98 (by decide) (by decide),
    bv_sub_16_96 sp]

theorem unchunkedMergeBelow_bytesMerge3_entails (sp : BitVec 64) :
    skipBytesMergeRest3 (sp - 16#64) 98 ∗ stackAt (sp - 112#64) bytesMerge3Stack ⊢
      unchunkedMergeBelow sp :=
  Entails.of_eq (unchunkedMergeBelow_bytesMerge3 sp).symm

theorem memRegion_48_split_112 (sp : BitVec 64) :
    memRegion (sp - 112#64) 48 =
      (∃∗ v : BitVec 64, (sp - 112#64) ↦₆₄ v) ∗ memRegion (sp - 104#64) 40 := by
  have h := memRegion_48_split_96 (sp - 16#64)
  simpa only [bv_sub_16_96, bv_sub_16_88] using h

theorem memRegion_48_split2_112 (sp : BitVec 64) :
    memRegion (sp - 112#64) 48 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((sp - 112#64) ↦₆₄ v1) ∗ ((sp - 104#64) ↦₆₄ v0)) ∗ memRegion (sp - 96#64) 32 := by
  have h := memRegion_48_split2 (sp - 16#64)
  simpa only [bv_sub_16_96, bv_sub_16_88, bv_sub_16_80] using h

theorem pointsTo64_memRegion32_entails_40_112 (sp v0 : BitVec 64) :
    ((sp - 104#64) ↦₆₄ v0) ∗ memRegion (sp - 96#64) 32 ⊢
      memRegion (sp - 104#64) 40 := by
  have h := pointsTo64_memRegion32_entails_40 (sp - 16#64) v0
  simpa only [bv_sub_16_96, bv_sub_16_88, bv_sub_16_80, bv_sub_add_lit] using h

theorem memRegion8_memRegion40_entails_48_112 (sp : BitVec 64) :
    memRegion (sp - 112#64) 8 ∗ memRegion (sp - 104#64) 40 ⊢
      memRegion (sp - 112#64) 48 := by
  have h := memRegion8_memRegion40_entails_48 (sp - 16#64)
  simpa only [bv_sub_16_96, bv_sub_16_88] using h

theorem pointsTo64_memRegion40_entails_48_112 (sp v0 : BitVec 64) :
    ((sp - 112#64) ↦₆₄ v0) ∗ memRegion (sp - 104#64) 40 ⊢
      memRegion (sp - 112#64) 48 := by
  have h := pointsTo64_memRegion40_entails_48 (sp - 16#64) v0
  simpa only [bv_sub_16_96, bv_sub_16_88] using h

theorem memRegion_48_wtErr112 (sp : BitVec 64) :
    memRegion (sp - 112#64) 48 =
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8, ∃∗ v0 : BitVec 64,
        ((sp - 112#64) ↦₆₄ v0) ∗ ((sp - 104#64) ↦₈ b0) ∗ ((sp - 103#64) ↦₈ b1)) ∗
        memRegion (sp - 102#64) 38 := by
  have h := memRegion_48_wtErr96 (sp - 16#64)
  simpa only [bv_sub_16_96, bv_sub_16_88, bv_sub_16_87, bv_sub_16_86] using h

theorem wtErr112_entails_memRegion40 (sp : BitVec 64) (b0 b1 : BitVec 8) :
    ((sp - 104#64) ↦₈ b0) ∗ ((sp - 103#64) ↦₈ b1) ∗ memRegion (sp - 102#64) 38 ⊢
      memRegion (sp - 104#64) 40 := by
  have h := wtErr96_entails_memRegion40 (sp - 16#64) b0 b1
  simpa only [bv_sub_16_88, bv_sub_16_87, bv_sub_16_86] using h

theorem iwt_cbnz_false_of_varint_u : (BitVec.ofNat 64 (WireType.varint).toNat == 0#64) = true := rfl

theorem iwt_cbnz_true_of_ne_varint_u {iwt : WireType} (hne : iwt ≠ .varint) :
    (BitVec.ofNat 64 iwt.toNat == 0#64) = false := by
  cases iwt <;> first | contradiction | decide

theorem tag_gt_two_branch {tag : Nat} (hgt : 2 < tag) (htag_lt : tag < 2 ^ 29) :
    (2#32 : BitVec 32).slt (BitVec.ofNat 32 tag) = true ∧
      (BitVec.ofNat 32 tag).sle 2#32 = false ∧
      (2#32 : BitVec 32).slt (BitVec.truncate 32 (BitVec.ofNat 64 tag)) = true ∧
      (BitVec.truncate 32 (BitVec.ofNat 64 tag)).sle 2#32 = false := by
  have hlt32 : tag < 2 ^ 32 := by omega
  have h1 : (2#32 : BitVec 32).slt (BitVec.ofNat 32 tag) = true := by
    simp only [BitVec.slt, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
    have h2 : ¬ 2 ^ 32 ≤ 2 * 2 := by decide
    have h3 : ¬ 2 ^ 32 ≤ 2 * tag := by omega
    simp only [h2, h3, ↓reduceIte, decide_eq_true_eq]
    omega
  have h2 : (BitVec.ofNat 32 tag).sle 2#32 = false := by
    simp only [BitVec.sle, BitVec.toInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32]
    have h2' : ¬ 2 ^ 32 ≤ 2 * 2 := by decide
    have h3' : ¬ 2 ^ 32 ≤ 2 * tag := by omega
    simp only [h2', h3', ↓reduceIte, decide_eq_false_iff_not]
    omega
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [sf_truncate32_ofNat64]; exact h1
  · rw [sf_truncate32_ofNat64]; exact h2

/-- High callee-saved registers `X24..X28` preserved (since `X19..X23` are saved on the stack). -/
def HighCalleeSaved24 (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
    s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
    s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
    s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
    s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
    calleeSavedVRegs s = calleeSavedVRegs s0

/-! ## 3. Capacity-Bounded Predicates for `Option<ProtoAuthenticator>`, `Ct1Sent`, `EkSentCt1Received` -/

/-- Capacity-bounded `Vec<u8>` at `a` (`24` bytes) with `BytesMergeCapOk cap bsLen`. -/
def vecU8CapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) (bs : List (BitVec 8)) : SepProp :=
  ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr bs

theorem vecU8CapAt_mono_u (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8))
    {m n : Nat} (hle : m ≤ n) :
    vecU8CapAt A a n bs ⊢ vecU8CapAt A a m bs :=
  Auth.vecU8CapAt_mono A a bs hle

theorem vecU8CapAt_entails_vecU8_u (A : RustAlloc) (a : BitVec 64) (n : Nat) (bs : List (BitVec 8)) :
    vecU8CapAt A a n bs ⊢ vecU8 A a bs :=
  Auth.vecU8CapAt_entails_vecU8 A a n bs

/-- Capacity-bounded `Option<ProtoAuthenticator>` at `a` (`48` bytes). -/
def optProtoAuthenticatorCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option ProtoAuthenticator → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some auth => authenticatorPBCapAt A a bsLen auth

theorem optProtoAuthenticatorCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (oauth : Option ProtoAuthenticator) {m n : Nat} (hle : m ≤ n) :
    optProtoAuthenticatorCapAt A a n oauth ⊢ optProtoAuthenticatorCapAt A a m oauth := by
  cases oauth with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBCapAt_mono A a auth hle

theorem optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (oauth : Option ProtoAuthenticator) :
    optProtoAuthenticatorCapAt A a n oauth ⊢ optProtoAuthenticatorAt A a oauth := by
  cases oauth with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBCapAt_entails_authenticatorPBAt A a n auth

theorem authenticatorPBAt_entails_optExists (A : RustAlloc) (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBAt A a auth ⊢ ∃∗ oauth : Option ProtoAuthenticator, optProtoAuthenticatorAt A a oauth :=
  Entails.sepExists_intro (P := optProtoAuthenticatorAt A a) (some auth)

theorem optProtoAuthenticatorAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (oauth : Option ProtoAuthenticator) :
    optProtoAuthenticatorAt A a oauth ⊢
      ∃∗ oauth' : Option ProtoAuthenticator, optProtoAuthenticatorAt A a oauth' :=
  Entails.sepExists_intro (P := optProtoAuthenticatorAt A a) oauth

theorem memRegion_40_split_5_cells (a : BitVec 64) :
    memRegion (a + 8#64) 40 =
      (∃∗ v5 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v3 : BitVec 64,
        ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗
          ((a + 24#64) ↦₆₄ v3) ∗ ((a + 32#64) ↦₆₄ v4) ∗
          ((a + 40#64) ↦₆₄ v5)) := by
  have h1 := memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 32) (N := 40) rfl (by bv_lin) (by decide)
  have h2 := memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 24) (N := 32) rfl (by bv_lin) (by decide)
  have h3 := memRegion_split' (b := a + 24#64) (b' := a + 32#64) (n := 8) (k := 16) (N := 24) rfl (by bv_lin) (by decide)
  have h4 := memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := 8) (N := 16) rfl (by bv_lin) (by decide)
  rw [h1, h2, h3, h4,
    Prost.memRegion_eight (a + 8#64), Prost.memRegion_eight (a + 16#64),
    Prost.memRegion_eight (a + 24#64), Prost.memRegion_eight (a + 32#64),
    Prost.memRegion_eight (a + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem vecU8At_zero_empty (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) =
      vecU8At A a 0#64 1#64 [] := by
  unfold vecU8At vecHeader
  have h_pure : (([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0) ↔ True :=
    iff_true_intro (by decide)
  have h_zero : ((0#64 : BitVec 64) = 0) ↔ True := iff_true_intro rfl
  rw [h_pure]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, h_zero, ↓reduceIte,
    pure_true, sepConj_emp, emp_sepConj]

theorem default_auth_cells_entails_cap (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      authenticatorPBCapAt A a n (default : ProtoAuthenticator) := by
  refine Entails.trans ?_ (authenticatorPBPinnedAt_zero_entails_cap A 1#64 1#64 a n default)
  unfold authenticatorPBPinnedAt
  have hd : (default : ProtoAuthenticator).rootKey = [] ∧ (default : ProtoAuthenticator).macKey = [] := ⟨rfl, rfl⟩
  have h32 : (a + 0x18#64) + 8#64 = a + 32#64 := by bv_lin
  have h40 : (a + 0x18#64) + 16#64 = a + 40#64 := by bv_lin
  have h0x18 : a + 0x18#64 = a + 24#64 := rfl
  rw [hd.1, hd.2, ← vecU8At_zero_empty A a, ← vecU8At_zero_empty A (a + 0x18#64), h32, h40, h0x18]
  exact Entails.of_eq (by ac_rfl)

theorem cap_add_one_ne_zero_of_lt63 {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false ∧ (cap + 1#64 != 0#64) = true := by
  have hne : cap + 1#64 ≠ 0#64 := by
    intro heq
    have h1 := congrArg BitVec.toNat heq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cap.toNat + 1 % 2 ^ 64 < 2 ^ 64)] at h1
    omega
  exact ⟨beq_eq_false_iff_ne.mpr hne, bne_iff_ne.mpr hne⟩

/-- Capacity-bounded `spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent` at `a` (`128` bytes). -/
def protoUnchunkedCt1SentCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (pb : V1State.Unchunked.Ct1Sent) : SepProp :=
  vecU8CapAt A a bsLen pb.hdr ∗
    vecU8CapAt A (a + 0x18#64) bsLen pb.es ∗
    vecU8CapAt A (a + 0x30#64) bsLen pb.ct1 ∗
    optProtoAuthenticatorCapAt A (a + 0x48#64) bsLen pb.auth ∗
    ((a + 0x78#64) ↦₆₄ pb.epoch)

theorem protoUnchunkedCt1SentCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (pb : V1State.Unchunked.Ct1Sent) {m n : Nat} (hle : m ≤ n) :
    protoUnchunkedCt1SentCapAt A a n pb ⊢ protoUnchunkedCt1SentCapAt A a m pb :=
  sepConj_mono (vecU8CapAt_mono A a pb.hdr hle)
    (sepConj_mono (vecU8CapAt_mono A (a + 0x18#64) pb.es hle)
      (sepConj_mono (vecU8CapAt_mono A (a + 0x30#64) pb.ct1 hle)
        (sepConj_mono_left (optProtoAuthenticatorCapAt_mono A (a + 0x48#64) pb.auth hle))))

theorem protoUnchunkedCt1SentCapAt_entails (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (pb : V1State.Unchunked.Ct1Sent) :
    protoUnchunkedCt1SentCapAt A a n pb ⊢ protoUnchunkedCt1SentAt A a pb :=
  sepConj_mono (vecU8CapAt_entails_vecU8 A a n pb.hdr)
    (sepConj_mono (vecU8CapAt_entails_vecU8 A (a + 0x18#64) n pb.es)
      (sepConj_mono (vecU8CapAt_entails_vecU8 A (a + 0x30#64) n pb.ct1)
        (sepConj_mono_left (optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt A (a + 0x48#64) n pb.auth))))

theorem protoUnchunkedCt1SentAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.Ct1Sent) :
    protoUnchunkedCt1SentAt A a m ⊢
      ∃∗ m' : V1State.Unchunked.Ct1Sent, protoUnchunkedCt1SentAt A a m' :=
  Entails.sepExists_intro m

/-- Capacity-bounded `spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received` at `a` (`104` bytes). -/
def protoUnchunkedEkSentCt1ReceivedCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (pb : V1State.Unchunked.EkSentCt1Received) : SepProp :=
  vecU8CapAt A a bsLen pb.dk ∗
    vecU8CapAt A (a + 0x18#64) bsLen pb.ct1 ∗
    optProtoAuthenticatorCapAt A (a + 0x30#64) bsLen pb.auth ∗
    ((a + 0x60#64) ↦₆₄ pb.epoch)

theorem protoUnchunkedEkSentCt1ReceivedCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (pb : V1State.Unchunked.EkSentCt1Received) {m n : Nat} (hle : m ≤ n) :
    protoUnchunkedEkSentCt1ReceivedCapAt A a n pb ⊢ protoUnchunkedEkSentCt1ReceivedCapAt A a m pb :=
  sepConj_mono (vecU8CapAt_mono A a pb.dk hle)
    (sepConj_mono (vecU8CapAt_mono A (a + 0x18#64) pb.ct1 hle)
      (sepConj_mono_left (optProtoAuthenticatorCapAt_mono A (a + 0x30#64) pb.auth hle)))

theorem protoUnchunkedEkSentCt1ReceivedCapAt_entails (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (pb : V1State.Unchunked.EkSentCt1Received) :
    protoUnchunkedEkSentCt1ReceivedCapAt A a n pb ⊢ protoUnchunkedEkSentCt1ReceivedAt A a pb :=
  sepConj_mono (vecU8CapAt_entails_vecU8 A a n pb.dk)
    (sepConj_mono (vecU8CapAt_entails_vecU8 A (a + 0x18#64) n pb.ct1)
      (sepConj_mono_left (optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt A (a + 0x30#64) n pb.auth)))

theorem protoUnchunkedEkSentCt1ReceivedAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (m : V1State.Unchunked.EkSentCt1Received) :
    protoUnchunkedEkSentCt1ReceivedAt A a m ⊢
      ∃∗ m' : V1State.Unchunked.EkSentCt1Received, protoUnchunkedEkSentCt1ReceivedAt A a m' :=
  Entails.sepExists_intro m

/-! ## 4. Specifications & Bridge to `ChunkedDefs` -/

/-- Exact 112-byte-frame contract of `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, &mut &[u8]>`
(`0x51e9c`, 181 instructions) at outer recursion depth `98`. -/
def unchunkedCt1SentMergeOwnSpec (A : RustAlloc) : Spec UnchunkedCt1SentMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63⌝ ∗
      protoUnchunkedCt1SentCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp unchunkedOwnStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp unchunkedOwnStack ∗
      match (Proto.mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ protoUnchunkedCt1SentCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Unchunked.Ct1Sent, protoUnchunkedCt1SentAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Exact 112-byte-frame contract of `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, &mut &[u8]>`
(`0x51c00`, 167 instructions) at outer recursion depth `98`. -/
def unchunkedEkSentCt1ReceivedMergeOwnSpec (A : RustAlloc) : Spec UnchunkedEkSentCt1ReceivedMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63⌝ ∗
      protoUnchunkedEkSentCt1ReceivedCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp unchunkedOwnStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp unchunkedOwnStack ∗
      match (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ protoUnchunkedEkSentCt1ReceivedCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : V1State.Unchunked.EkSentCt1Received, protoUnchunkedEkSentCt1ReceivedAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem stackAt_unchunkedMergeStack_eq_own (sp : BitVec 64) :
    stackAt sp unchunkedMergeStack =
      memRegion (sp - BitVec.ofNat 64 unchunkedMergeStack) 48 ∗
        stackAt sp unchunkedOwnStack := by
  simp only [stackAt]
  have hlen : unchunkedMergeStack = 48 + unchunkedOwnStack := by
    simp only [unchunkedMergeStack, unchunkedOwnStack, authMergeStack]; omega
  have hbound : unchunkedMergeStack ≤ 2 ^ 64 := by
    simp only [unchunkedMergeStack, authMergeStack, skipField3Stack, decodeVarint2Stack,
      decodeVarintSlowStack, decodeErrorHookStack, allocHookStack]
    omega
  have hbit : BitVec.ofNat 64 unchunkedMergeStack =
      48#64 + BitVec.ofNat 64 unchunkedOwnStack := by
    rw [hlen, BitVec.ofNat_add]
  exact memRegion_split'
    (b := sp - BitVec.ofNat 64 unchunkedMergeStack)
    (b' := sp - BitVec.ofNat 64 unchunkedOwnStack)
    (n := 48) (k := unchunkedOwnStack) (N := unchunkedMergeStack)
    hlen (by rw [hbit]; bv_lin) hbound

private theorem panic_anyHeap_frame_drop {s0 sf : State} {R_extra R : SepProp}
    (hq : sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ (R_extra ∗ R)) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  have hq' : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R_extra) ∗ R := by
    rwa [sepConj_assoc]
  exact allowPanic_frame (allocFailedIn_trans rfl) hq'

theorem subroutine_ok_unchunkedCt1SentMerge_of_own {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {img : Obj.Image} (h : subroutine_ok prog entry ((unchunkedCt1SentMergeOwnSpec A).inImage img)) :
    subroutine_ok prog entry ((unchunkedCt1SentMergeSpec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
  have hpre_eq : ((unchunkedCt1SentMergeSpec A).inImage img).pre x s0 ∗ R =
      ((unchunkedCt1SentMergeOwnSpec A).inImage img).pre x s0 ∗ (R_extra ∗ R) := by
    dsimp only [Spec.inImage, unchunkedCt1SentMergeSpec, unchunkedCt1SentMergeOwnSpec, R_extra,
      unchunkedCt1SentPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedCt1SentCapAt,
      vecU8CapAt, optProtoAuthenticatorCapAt]
    rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
    ac_rfl
  rw [hpre_eq] at hpre
  refine h.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpost_eq : ((unchunkedCt1SentMergeSpec A).inImage img).post x s0 sf ∗ R =
        ((unchunkedCt1SentMergeOwnSpec A).inImage img).post x s0 sf ∗ (R_extra ∗ R) := by
      dsimp only [Spec.inImage, unchunkedCt1SentMergeSpec, unchunkedCt1SentMergeOwnSpec, R_extra,
        unchunkedCt1SentPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedCt1SentCapAt,
        vecU8CapAt, optProtoAuthenticatorCapAt, ct1SentPBAt, unchunked5At,
        rustBytesVecAt, optAuthenticatorPBAt, protoUnchunkedCt1SentAt, optProtoAuthenticatorAt]
      rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
      ac_rfl
    rw [hpost_eq]
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, panic_anyHeap_frame_drop hq⟩)
  · dsimp only [Spec.inImage, unchunkedCt1SentMergeOwnSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [Spec.inImage, unchunkedCt1SentMergeOwnSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem subroutine_ok_unchunkedEkSentCt1ReceivedMerge_of_own {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {img : Obj.Image} (h : subroutine_ok prog entry ((unchunkedEkSentCt1ReceivedMergeOwnSpec A).inImage img)) :
    subroutine_ok prog entry ((unchunkedEkSentCt1ReceivedMergeSpec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
  have hpre_eq : ((unchunkedEkSentCt1ReceivedMergeSpec A).inImage img).pre x s0 ∗ R =
      ((unchunkedEkSentCt1ReceivedMergeOwnSpec A).inImage img).pre x s0 ∗ (R_extra ∗ R) := by
    dsimp only [Spec.inImage, unchunkedEkSentCt1ReceivedMergeSpec, unchunkedEkSentCt1ReceivedMergeOwnSpec, R_extra,
      unchunkedEkSentCt1ReceivedPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedEkSentCt1ReceivedCapAt,
      vecU8CapAt, optProtoAuthenticatorCapAt]
    rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
    ac_rfl
  rw [hpre_eq] at hpre
  refine h.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpost_eq : ((unchunkedEkSentCt1ReceivedMergeSpec A).inImage img).post x s0 sf ∗ R =
        ((unchunkedEkSentCt1ReceivedMergeOwnSpec A).inImage img).post x s0 sf ∗ (R_extra ∗ R) := by
      dsimp only [Spec.inImage, unchunkedEkSentCt1ReceivedMergeSpec, unchunkedEkSentCt1ReceivedMergeOwnSpec, R_extra,
        unchunkedEkSentCt1ReceivedPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedEkSentCt1ReceivedCapAt,
        vecU8CapAt, optProtoAuthenticatorCapAt, ekSentCt1ReceivedPBAt, unchunked4At,
        rustBytesVecAt, optAuthenticatorPBAt, protoUnchunkedEkSentCt1ReceivedAt, optProtoAuthenticatorAt]
      rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
      ac_rfl
    rw [hpost_eq]
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, panic_anyHeap_frame_drop hq⟩)
  · dsimp only [Spec.inImage, unchunkedEkSentCt1ReceivedMergeOwnSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [Spec.inImage, unchunkedEkSentCt1ReceivedMergeOwnSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem subroutine_ok_unchunkedCt1SentMerge_of_own_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeOwnSpec A))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
  have hpre_eq : (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A)).pre x s0 ∗ R =
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeOwnSpec A)).pre x s0 ∗ (R_extra ∗ R) := by
    dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeSpec, unchunkedCt1SentMergeOwnSpec, R_extra,
      unchunkedCt1SentPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedCt1SentCapAt,
      vecU8CapAt, optProtoAuthenticatorCapAt]
    rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
    ac_rfl
  rw [hpre_eq] at hpre
  refine h.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpost_eq : (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A)).post x s0 sf ∗ R =
        (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeOwnSpec A)).post x s0 sf ∗ (R_extra ∗ R) := by
      dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeSpec, unchunkedCt1SentMergeOwnSpec, R_extra,
        unchunkedCt1SentPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedCt1SentCapAt,
        vecU8CapAt, optProtoAuthenticatorCapAt, ct1SentPBAt, unchunked5At,
        rustBytesVecAt, optAuthenticatorPBAt, protoUnchunkedCt1SentAt, optProtoAuthenticatorAt]
      rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
      ac_rfl
    rw [hpost_eq]
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, panic_anyHeap_frame_drop hq⟩)
  · dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeOwnSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeOwnSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem subroutine_ok_unchunkedEkSentCt1ReceivedMerge_of_own_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeOwnSpec A))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
  have hpre_eq : (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A)).pre x s0 ∗ R =
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeOwnSpec A)).pre x s0 ∗ (R_extra ∗ R) := by
    dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeSpec, unchunkedEkSentCt1ReceivedMergeOwnSpec, R_extra,
      unchunkedEkSentCt1ReceivedPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedEkSentCt1ReceivedCapAt,
      vecU8CapAt, optProtoAuthenticatorCapAt]
    rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
    ac_rfl
  rw [hpre_eq] at hpre
  refine h.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hpost_eq : (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A)).post x s0 sf ∗ R =
        (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeOwnSpec A)).post x s0 sf ∗ (R_extra ∗ R) := by
      dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeSpec, unchunkedEkSentCt1ReceivedMergeOwnSpec, R_extra,
        unchunkedEkSentCt1ReceivedPBCapAt, optAuthenticatorPBCapAt, protoUnchunkedEkSentCt1ReceivedCapAt,
        vecU8CapAt, optProtoAuthenticatorCapAt, ekSentCt1ReceivedPBAt, unchunked4At,
        rustBytesVecAt, optAuthenticatorPBAt, protoUnchunkedEkSentCt1ReceivedAt, optProtoAuthenticatorAt]
      rw [stackAt_unchunkedMergeStack_eq_own s0.sp]
      ac_rfl
    rw [hpost_eq]
    exact hq
  · exact Or.inr (Or.inl ⟨hpan, panic_anyHeap_frame_drop hq⟩)
  · dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeOwnSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeOwnSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact False.elim hq.1

theorem decodeErrorWith_zero_entails_le2 (A : RustAlloc) (e : BitVec 64) :
    decodeErrorAtStackLen A e 0 ⊢ ∃∗ n : Nat, ⌜n ≤ 2⌝ ∗ decodeErrorAtStackLen A e n := by
  refine Entails.trans ?_ (Entails.sepExists_intro 0)
  simp only [Nat.zero_le, pure_true, emp_sepConj]
  exact Entails.refl _

theorem decodeErrorWith_succ_le1_entails_le2 (A : RustAlloc) (e : BitVec 64) {n : Nat} (hn : n ≤ 1) :
    decodeErrorAtStackLen A e (n + 1) ⊢ ∃∗ k : Nat, ⌜k ≤ 2⌝ ∗ decodeErrorAtStackLen A e k := by
  refine Entails.trans ?_ (Entails.sepExists_intro (n + 1))
  have hle : n + 1 ≤ 2 := by omega
  simp only [hle, pure_true, emp_sepConj]
  exact Entails.refl _

/-! ## 5. Pure Model Step Lemmas for `Ct1Sent.mergeField` and `EkSentCt1Received.mergeField` -/

theorem unchunkedCt1Sent_mergeField_tag1 (m : V1State.Unchunked.Ct1Sent) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.Ct1Sent.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then
        (decodeVarint rest).map (fun (v, rest') => ({ m with epoch := v }, rest'))
      else none := by
  unfold V1State.Unchunked.Ct1Sent.mergeField Proto.mergeUint64 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, beq_self_eq_true, ↓reduceIte]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem unchunkedCt1Sent_mergeField_tag2 (m : V1State.Unchunked.Ct1Sent) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.Ct1Sent.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with auth := some v }, rest')) := by
  unfold V1State.Unchunked.Ct1Sent.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases h : Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem unchunkedCt1Sent_mergeField_tag3 (m : V1State.Unchunked.Ct1Sent) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.Ct1Sent.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with hdr := v }, rest')) := by
  unfold V1State.Unchunked.Ct1Sent.mergeField
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> {
    have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']; rfl }

theorem unchunkedCt1Sent_mergeField_tag4 (m : V1State.Unchunked.Ct1Sent) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.Ct1Sent.mergeField m (BitVec.ofNat 32 4) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with es := v }, rest')) := by
  unfold V1State.Unchunked.Ct1Sent.mergeField
  simp only [show (BitVec.ofNat 32 4 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 4 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 4 == 3#32) = false from rfl,
    show (BitVec.ofNat 32 4 == 4#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> {
    have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']; rfl }

theorem unchunkedCt1Sent_mergeField_tag5 (m : V1State.Unchunked.Ct1Sent) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.Ct1Sent.mergeField m (BitVec.ofNat 32 5) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with ct1 := v }, rest')) := by
  unfold V1State.Unchunked.Ct1Sent.mergeField
  simp only [show (BitVec.ofNat 32 5 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 5 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 5 == 3#32) = false from rfl,
    show (BitVec.ofNat 32 5 == 4#32) = false from rfl,
    show (BitVec.ofNat 32 5 == 5#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> {
    have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']; rfl }

theorem unchunkedCt1Sent_mergeField_other (m : V1State.Unchunked.Ct1Sent) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat)
    (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2)
    (hne3 : tag ≠ 3) (hne4 : tag ≠ 4) (hne5 : tag ≠ 5) :
    (V1State.Unchunked.Ct1Sent.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have hb4 : (BitVec.ofNat 32 tag == 4#32) = false := (itag_beq_tag_false hne4 htag_lt (by decide)).1
  have hb5 : (BitVec.ofNat 32 tag == 5#32) = false := (itag_beq_tag_false hne5 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Unchunked.Ct1Sent.mergeField
  simp only [hb1, hb2, hb3, hb4, hb5, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest' <;> {
    have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl }

theorem unchunkedEkSentCt1Received_mergeField_tag1 (m : V1State.Unchunked.EkSentCt1Received) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.EkSentCt1Received.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      if iwt = .varint then
        (decodeVarint rest).map (fun (v, rest') => ({ m with epoch := v }, rest'))
      else none := by
  unfold V1State.Unchunked.EkSentCt1Received.mergeField Proto.mergeUint64 Proto.checkWireType
  cases iwt <;> simp only [codecWireTypeToProto, beq_self_eq_true, ↓reduceIte]
  case varint =>
    rcases hdv : Proto.decodeVarint rest with e | ⟨v, rest'⟩
    · have hdv' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
    · have hdv' : decodeVarint rest = some (v, rest') := by rw [← proto_decodeVarint_toOption rest, hdv]; rfl
      simp [hdv', Bind.bind, Except.bind, Except.toOption]
  all_goals rfl

theorem unchunkedEkSentCt1Received_mergeField_tag2 (m : V1State.Unchunked.EkSentCt1Received) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.EkSentCt1Received.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth').toOption.map
        (fun (v, rest') => ({ m with auth := some v }, rest')) := by
  unfold V1State.Unchunked.EkSentCt1Received.mergeField Proto.mergeOptMessage
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases h : Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest depth' with e | ⟨v, rest'⟩ <;> rfl

theorem unchunkedEkSentCt1Received_mergeField_tag3 (m : V1State.Unchunked.EkSentCt1Received) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.EkSentCt1Received.mergeField m (BitVec.ofNat 32 3) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with dk := v }, rest')) := by
  unfold V1State.Unchunked.EkSentCt1Received.mergeField
  simp only [show (BitVec.ofNat 32 3 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 3 == 3#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> {
    have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']; rfl }

theorem unchunkedEkSentCt1Received_mergeField_tag4 (m : V1State.Unchunked.EkSentCt1Received) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (V1State.Unchunked.EkSentCt1Received.mergeField m (BitVec.ofNat 32 4) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with ct1 := v }, rest')) := by
  unfold V1State.Unchunked.EkSentCt1Received.mergeField
  simp only [show (BitVec.ofNat 32 4 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 4 == 2#32) = false from rfl,
    show (BitVec.ofNat 32 4 == 3#32) = false from rfl,
    show (BitVec.ofNat 32 4 == 4#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩ <;> {
    have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']; rfl }

theorem unchunkedEkSentCt1Received_mergeField_other (m : V1State.Unchunked.EkSentCt1Received) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat)
    (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2)
    (hne3 : tag ≠ 3) (hne4 : tag ≠ 4) :
    (V1State.Unchunked.EkSentCt1Received.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have hb3 : (BitVec.ofNat 32 tag == 3#32) = false := (itag_beq_tag_false hne3 htag_lt (by decide)).1
  have hb4 : (BitVec.ofNat 32 tag == 4#32) = false := (itag_beq_tag_false hne4 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold V1State.Unchunked.EkSentCt1Received.mergeField
  simp only [hb1, hb2, hb3, hb4, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest' <;> {
    have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']; rfl }

end CryptoVerification.SpqrV1.Prost.MessageMerge
