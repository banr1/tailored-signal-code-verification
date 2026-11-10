/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.Repr
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Base Definitions and Step Lemmas for `Authenticator::merge`

Defines the decode table (`authMergeBin`), capacity-bounded `authenticatorPBCapAt` predicate,
`authMergeSpec` contract, pure `ProtoAuthenticator.mergeField` lemmas, and per-branch
step/exit lemmas for `prost::encoding::message::merge::<Authenticator, &mut &[u8]>` (`0x4df38`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

theorem Entails.sepExists_elim {α : Type} {P : α → SepProp} {Q : SepProp}
    (h : ∀ a, P a ⊢ Q) : (∃∗ a, P a) ⊢ Q :=
  Arm64.Entails.sepExists_elim h

theorem SepWPp.pure_elim {prog : Program} {ret_pc : BitVec 64} {s : State} {φ : Prop} {P : SepProp}
    {post panic : State → SepProp → Prop} (h : φ → SepWPp prog ret_pc s P post panic) :
    SepWPp prog ret_pc s (⌜φ⌝ ∗ P) post panic := by
  intro F hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 F hm.2 hL

theorem SepWPp.pure_elim2 {prog : Program} {ret_pc : BitVec 64} {s : State} {φ : Prop} {P Q : SepProp}
    {post panic : State → SepProp → Prop} (h : φ → SepWPp prog ret_pc s (P ∗ Q) post panic) :
    SepWPp prog ret_pc s (P ∗ ⌜φ⌝ ∗ Q) post panic := by
  apply SepWPp.weaken_pre (P' := ⌜φ⌝ ∗ (P ∗ Q)) (Entails.of_eq (by ac_rfl))
  exact SepWPp.pure_elim h

/-! ## Decode Table and Offset Lemmas -/

@[local simp, local arm64_norm]
theorem authMerge_fnOff :
    libsignalSessionCode.fnOff authMergeName = 0x48b40 :=
  libsignalSessionCode_fnOff_0x48b40

gen_decodes libsignalSessionCode_tree authMergeBin [ 0x48b40 → 0x48d14 ]

macro "authMerge_fetches " b:term:max H:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.SpqrV1.Auth.authMergeBin $b $H
    CryptoVerification.SpqrV1.Auth.authMerge_fnOff 0x48b40 $k0 $len)

theorem skipBelow3_97_eq_stackAt_96 (sp : BitVec 64) :
    skipBelow3 sp 97 = stackAt (sp - 96#64) (skipField3Stack 96) :=
  congrArg (stackAt (sp - 96#64)) (rfl : 97 * 0x60 + decodeVarint2Stack = skipField3Stack 96)

theorem memRegion_48_split_96 (sp : BitVec 64) :
    memRegion (sp - 96#64) 48 =
      (∃∗ v : BitVec 64, (sp - 96#64) ↦₆₄ v) ∗ memRegion (sp - 88#64) 40 := by
  rw [memRegion_48_split (sp - 96#64), bv_sub_add_lit sp 96 8]

theorem memRegion8_memRegion40_entails_48 (sp : BitVec 64) :
    memRegion (sp - 96#64) 8 ∗ memRegion (sp - 88#64) 40 ⊢
      memRegion (sp - 96#64) 48 := by
  have s1 := ProofLib.memRegion_split (sp - 96#64) 8 40 (by decide)
  rw [ProofLib.bv_sub_add_lit sp 96 8] at s1
  exact Entails.of_eq s1.symm

/-! ## Capacity-Bounded `AuthenticatorPB` Predicate and Specification -/

/-- `ProtoAuthenticator` at `a` (48 bytes) with `BytesMergeCapOk cap bsLen` on both
`root_key` (`a`) and `mac_key` (`a + 0x18`). -/
def authenticatorPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) : SepProp :=
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr auth.rootKey) ∗
  (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A (a + 0x18#64) cap ptr auth.macKey)

theorem vecU8CapAt_mono (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8))
    {m n : Nat} (hle : m ≤ n) :
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A a cap ptr bs) ⊢
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap m⌝ ∗ vecU8At A a cap ptr bs) := by
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.pure_left fun hok => ?_
  refine Entails.trans (Entails.pure_right (bytesMergeCapOk_mono hok hle) (Entails.refl _)) ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem authenticatorPBCapAt_mono (A : RustAlloc) (a : BitVec 64) (auth : ProtoAuthenticator)
    {m n : Nat} (hle : m ≤ n) :
    authenticatorPBCapAt A a n auth ⊢ authenticatorPBCapAt A a m auth :=
  sepConj_mono (vecU8CapAt_mono A a auth.rootKey hle)
    (vecU8CapAt_mono A (a + 0x18#64) auth.macKey hle)

theorem vecU8CapAt_entails_vecU8 (A : RustAlloc) (a : BitVec 64) (n : Nat) (bs : List (BitVec 8)) :
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap n⌝ ∗ vecU8At A a cap ptr bs) ⊢
      rustBytesVecAt A a bs := by
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.pure_left fun _ => ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem authenticatorPBCapAt_entails_authenticatorPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (auth : ProtoAuthenticator) :
    authenticatorPBCapAt A a n auth ⊢ authenticatorPBAt A a auth :=
  sepConj_mono (vecU8CapAt_entails_vecU8 A a n auth.rootKey)
    (vecU8CapAt_entails_vecU8 A (a + 0x18#64) n auth.macKey)

theorem authenticatorPBAt_entails_exists (A : RustAlloc) (a : BitVec 64) (m : ProtoAuthenticator) :
    authenticatorPBAt A a m ⊢ ∃∗ m' : ProtoAuthenticator, authenticatorPBAt A a m' :=
  Entails.sepExists_intro m

theorem authenticatorPBCapAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (m : ProtoAuthenticator) :
    authenticatorPBCapAt A a n m ⊢ ∃∗ m' : ProtoAuthenticator, authenticatorPBAt A a m' :=
  Entails.trans (authenticatorPBCapAt_entails_authenticatorPBAt A a n m)
    (authenticatorPBAt_entails_exists A a m)

theorem authenticatorPBPinnedAt_zero_entails_cap (A : RustAlloc) (p1 p2 a : BitVec 64)
    (n : Nat) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ⟨⟨0#64, p1⟩, ⟨0#64, p2⟩⟩ a auth ⊢
      authenticatorPBCapAt A a n auth := by
  unfold authenticatorPBPinnedAt authenticatorPBCapAt
  refine sepConj_mono ?_ ?_
  · refine Entails.trans (Entails.pure_right (bytesMergeCapOk_zero (n := n)) (Entails.refl _)) ?_
    exact Entails.sepExists_right 0#64 (Entails.sepExists_right p1 (Entails.refl _))
  · refine Entails.trans (Entails.pure_right (bytesMergeCapOk_zero (n := n)) (Entails.refl _)) ?_
    exact Entails.sepExists_right 0#64 (Entails.sepExists_right p2 (Entails.refl _))

theorem authenticatorPBAt_entails_cap_of_lt32 (A : RustAlloc) (a : BitVec 64)
    {n : Nat} (hn : n < 2 ^ 32) (auth : ProtoAuthenticator) :
    authenticatorPBAt A a auth ⊢ authenticatorPBCapAt A a n auth := by
  unfold authenticatorPBAt authenticatorPBCapAt rustBytesVecAt vecU8
  refine sepConj_mono ?_ ?_
  · refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    refine Entails.trans (Entails.pure_right (bytesMergeCapOk_of_len_lt32 (cap := cap) hn) (Entails.refl _)) ?_
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))
  · refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    refine Entails.trans (Entails.pure_right (bytesMergeCapOk_of_len_lt32 (cap := cap) hn) (Entails.refl _)) ?_
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

/-- Stack budget `skipField3Stack 97` (`96 + skipField3Stack 96`) for `Authenticator::merge`. -/
abbrev authMergeStack : Nat := skipField3Stack 97

/-- Ghost arguments for `Authenticator::merge` (`0x4df38`). -/
structure AuthMergeGhost where
  wt : WireType
  msgPtr : BitVec 64
  msg : ProtoAuthenticator
  bufRef : BitVec 64
  slot : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Specification of `prost::encoding::message::merge::<Authenticator, &mut &[u8]>` (`0x4df38`). -/
def authMergeSpec (A : RustAlloc) : Spec AuthMergeGhost where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63⌝ ∗
      authenticatorPBCapAt A x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool ∗ stackAt s.sp authMergeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗ A.pool ∗
      stackAt s0.sp authMergeStack ∗
      match (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption with
      | some (m', rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗ authenticatorPBCapAt A x.msgPtr rest.length m' ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
          (∃∗ n : Nat, ⌜n ≤ 1⌝ ∗ decodeErrorAtStackLen A (sf.readReg64 .x0) n) ∗
          (∃∗ m' : ProtoAuthenticator, authenticatorPBAt A x.msgPtr m') ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## Pure `mergeField` and `mergeBytes` Lemmas -/

theorem mergeBytes_length {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    rest.length < bs.length := by
  unfold mergeBytes at h
  split at h
  · contradiction
  · rcases hdv : decodeVarint bs with _ | ⟨len, r0⟩
    · rw [hdv] at h; contradiction
    · rw [hdv] at h; dsimp only at h
      split at h
      · contradiction
      · injection h with hpair; injection hpair with _ hr; subst hr
        have hlt := decodeVarint_length hdv
        rw [List.length_drop]
        omega

theorem mergeBytes_suffix {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    IsDropSuffix bs rest := by
  unfold mergeBytes at h
  split at h
  · contradiction
  · rcases hdv : decodeVarint bs with _ | ⟨len, r0⟩
    · rw [hdv] at h; contradiction
    · rw [hdv] at h; dsimp only at h
      split at h
      · contradiction
      · rename_i hge
        injection h with hpair; injection hpair with _ hr; subst hr
        have hsuf0 := decodeVarint_suffix hdv
        have hlt0 := decodeVarint_length hdv
        have hle_drop : (r0.drop len.toNat).length ≤ r0.length := by
          rw [List.length_drop]; omega
        have hsuf_drop : IsDropSuffix r0 (r0.drop len.toNat) := by
          unfold IsDropSuffix
          rw [List.length_drop, Nat.sub_sub_self (by omega)]
        exact suffix_trans (Nat.le_of_lt hlt0) hsuf0 hle_drop hsuf_drop

theorem protoAuthenticator_mergeField_tag1 (m : ProtoAuthenticator) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ProtoAuthenticator.mergeField m (BitVec.ofNat 32 1) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with rootKey := v }, rest')) := by
  unfold ProtoAuthenticator.mergeField
  simp only [beq_self_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩
  · have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']
    rfl
  · have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']
    rfl

theorem protoAuthenticator_mergeField_tag2 (m : ProtoAuthenticator) (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat) :
    (ProtoAuthenticator.mergeField m (BitVec.ofNat 32 2) (codecWireTypeToProto iwt) rest depth').toOption =
      (mergeBytes iwt rest).map (fun (v, rest') => ({ m with macKey := v }, rest')) := by
  unfold ProtoAuthenticator.mergeField
  simp only [show (BitVec.ofNat 32 2 == 1#32) = false from rfl,
    show (BitVec.ofNat 32 2 == 2#32) = true from rfl, Bool.false_eq_true, ↓reduceIte]
  rcases hmb : Proto.mergeBytes (codecWireTypeToProto iwt) rest with e | ⟨v, rest'⟩
  · have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']
    rfl
  · have hmb' := proto_mergeBytes_toOption (codecWireTypeToProto iwt) rest
    rw [hmb, protoWireTypeToCodec_codecWireTypeToProto] at hmb'
    dsimp [Except.toOption] at hmb'
    rw [← hmb']
    rfl

theorem protoAuthenticator_mergeField_other (m : ProtoAuthenticator) {tag : Nat} (iwt : WireType)
    (rest : List (BitVec 8)) (depth' : Nat)
    (htag_lt : tag < 2 ^ 32) (hne1 : tag ≠ 1) (hne2 : tag ≠ 2) :
    (ProtoAuthenticator.mergeField m (BitVec.ofNat 32 tag) (codecWireTypeToProto iwt) rest depth').toOption =
      (skipField (2 * rest.length + 2) depth' tag iwt rest).map (fun rest' => (m, rest')) := by
  have hb1 : (BitVec.ofNat 32 tag == 1#32) = false := (itag_beq_tag_false hne1 htag_lt (by decide)).1
  have hb2 : (BitVec.ofNat 32 tag == 2#32) = false := (itag_beq_tag_false hne2 htag_lt (by decide)).1
  have htag_toNat : (BitVec.ofNat 32 tag).toNat = tag := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htag_lt]
  unfold ProtoAuthenticator.mergeField
  simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte]
  rcases hsf : Proto.skipField (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth' with e | rest'
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']
    rfl
  · have hsf' := proto_skipField_toOption (codecWireTypeToProto iwt) (BitVec.ofNat 32 tag) rest depth'
    rw [hsf, htag_toNat, protoWireTypeToCodec_codecWireTypeToProto] at hsf'
    dsimp [Except.toOption] at hsf'
    rw [← hsf']
    rfl

theorem setWidth8_ofNat64_wt (iwt : WireType) :
    (BitVec.ofNat 64 iwt.toNat).setWidth 8 = BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> rfl

/-! ## Loop Invariant and Per-Branch Step Lemmas -/

abbrev authLoopPre (A : RustAlloc) (s0 : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : ProtoAuthenticator) (bs cur : List (BitVec 8)) : SepProp :=
  authenticatorPBCapAt A msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool ∗
    memRegion (s0.sp - 96#64) 48 ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
    skipBelow3 s0.sp 97

abbrev authErrFrame (A : RustAlloc) (s0 : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : ProtoAuthenticator) (bs : List (BitVec 8)) : SepProp :=
  authenticatorPBAt A msgPtr m ∗
    (bufRef ↦₆₄ slot) ∗
    memRegion slot 16 ∗
    (ptr ↦ₛ bs) ∗
    A.pool ∗
    ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
    ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

abbrev WppPost {α : Type} (spec : Spec α) (x : α) (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev WppPanic (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) ∧ sf.mem ⊨ anyHeap ∗ R

/-- Error return exit from `+0x074` when `x1 = err ≠ 0#64` owns `decodeErrorAtStackLen A err 0`. -/
theorem auth_err0_ret_exit {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {err : BitVec 64}
    (hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 116#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err)
    (herr : err ≠ 0#64)
    (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗
        memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  authMerge_fetches b H 116 24
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpec
  simp only [hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide), authErrFrame,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  wp_steps
  wp_done

/-- Error construction exit from `+0x064` via `DecodeError::from`. -/
theorem auth_from_err_exit {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffce68#64)
      (decodeErrorFromSpec A))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {w v_stk0 : BitVec 64}
    (hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hw : KindNoHeap w)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 100#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = w)
    (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ v_stk0) ∗
        memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  authMerge_fetches b H 100 40
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffce68#64)
  conv => arg 4; rw [skipBelow3_err s0.sp 97 (by decide), authErrFrame]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, w))
    (ret_pc := entry + 112#64) hFromCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpec
  simp only [decodeErrorFromSpec, hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 97 (by decide)) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A _) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48 s0.sp) (by sep_focus)
  wp_done

/-- Error context exit from `+0x1b4` via `DecodeError::push`. -/
theorem auth_push_err_exit {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffcb70#64)
      (decodeErrorPushSpec A))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {err : BitVec 64}
    (hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (herr : err ≠ 0#64)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 96#64)
    (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A err 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  authMerge_fetches b H 436 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 0xffffffffffffcb70#64)
  conv => arg 4; rw [skipBelow3_err s0.sp 97 (by decide), authErrFrame]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach
  refine SepWPp.call_frame (x := (s0.sp - 96#64, err, 0))
    (ret_pc := entry + 440#64) hPushCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by decide : 0 < 2 ^ 32)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpec
  simp only [decodeErrorPushSpec, hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 97 (by decide)) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48 s0.sp err) (by sep_focus)
  wp_done

/-- Unknown-tag step (`tag ≠ 1 ∧ tag ≠ 2`) at `+0x08c` via `skip_field [local#3]` at depth 96. -/
theorem auth_skip_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffdc3c#64)
      (skipField3Spec A))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 96 tag iwt rest = none →
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 96 tag iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 160#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 96#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' →
      ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (authMergeSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 140#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s)
    (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @auth_err0_ret_exit b A H x R s0
  authMerge_fetches b H 140 20
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffdc3c#64) hinv
  conv => arg 4; rw [authLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_97_eq_stackAt_96 s0.sp]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_keep (x := ⟨iwt, tag, 96, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 152#64) hSkipCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 96 < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 96 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP (mid := entry + 116#64)
    conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_97_eq_stackAt_96, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr rest.length m) (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [authErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_img (mid := entry + 160#64) hinvm
    conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_97_eq_stackAt_96, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps
    wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (Entails.of_eq (by dsimp only [authLoopPre]; ac_rfl))
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
      hinvm

/-- Tag 1 (`root_key` at `msgPtr`) step at `+0x0fc` via `bytes::merge [local#3]`. -/
theorem auth_tag1_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffcb70#64)
      (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xfffffffffffff204#64)
      ((bytesMerge3RawSpec A).inImage img))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 160#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 96#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' →
      ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with rootKey := v } x.bs rest')
        (WppPost (authMergeSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s)
    (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @auth_push_err_exit b A H hPushCall x R s0
  authMerge_fetches b H 252 24
  authMerge_fetches b H 404 32
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
  examples_hide_fetches
  conv =>
    arg 4
    rw [authLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2
  apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1
  apply SepWPp.exists_elim; intro ptr1
  apply SepWPp.pure_elim; intro hcap1
  apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_img (mid := entry + 0xfffffffffffff204#64) hinv
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_inImage (x := ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 264#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap1⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP (mid := entry + 436#64)
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A x.msgPtr cap1 ptr1 m.rootKey ∗ vecU8At A (x.msgPtr + 0x18#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 96#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [authErrFrame]; ac_rfl))
    exact hpush_exit hnone hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap2' : BytesMergeCapOk cap2 rest'.length := bytesMergeCapOk_mono hcap2 hrest'_le
    apply SepWPp.of_sepWP_img (mid := entry + 160#64) hinvm
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro cap1'
    apply SepWP.exists_elim; intro ptr1'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap1'⟩
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A x.msgPtr cap1' ptr1' v ∗ vecU8At A (x.msgPtr + 0x18#64) cap2 ptr2 m.macKey ⊢
          authenticatorPBCapAt A x.msgPtr rest'.length { m with rootKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps
    wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' :=
      authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with rootKey := v } x.bs rest')
      (Entails.of_eq (by dsimp only [authLoopPre]; ac_rfl))
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
      hinvm

/-- Tag 2 (`mac_key` at `msgPtr + 0x18`) step at `+0x0e4` via `bytes::merge [local#3]`. -/
theorem auth_tag2_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffcb70#64)
      (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xfffffffffffff204#64)
      ((bytesMerge3RawSpec A).inImage img))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 160#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 96#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' →
      ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with macKey := v } x.bs rest')
        (WppPost (authMergeSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s)
    (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @auth_push_err_exit b A H hPushCall x R s0
  authMerge_fetches b H 228 24
  authMerge_fetches b H 368 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
  examples_hide_fetches
  conv =>
    arg 4
    rw [authLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2
  apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1
  apply SepWPp.exists_elim; intro ptr1
  apply SepWPp.pure_elim; intro hcap1
  apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_img (mid := entry + 0xfffffffffffff204#64) hinv
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_inImage (x := ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 240#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap2⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP (mid := entry + 436#64)
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A x.msgPtr cap1 ptr1 m.rootKey ∗ vecU8At A (x.msgPtr + 24#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 96#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [authErrFrame]; ac_rfl))
    exact hpush_exit hnone hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap1' : BytesMergeCapOk cap1 rest'.length := bytesMergeCapOk_mono hcap1 hrest'_le
    apply SepWPp.of_sepWP_img (mid := entry + 160#64) hinvm
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro cap2'
    apply SepWP.exists_elim; intro ptr2'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap2'⟩
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A x.msgPtr cap1 ptr1 m.rootKey ∗ vecU8At A (x.msgPtr + 24#64) cap2' ptr2' v ⊢
          authenticatorPBCapAt A x.msgPtr rest'.length { m with macKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps
    wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' :=
      authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with macKey := v } x.bs rest')
      (Entails.of_eq (by dsimp only [authLoopPre]; ac_rfl))
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
      hinvm

end CryptoVerification.SpqrV1.Auth
