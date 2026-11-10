/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBase
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Shared Specifications for `unchunked::EkSentCt1Received` and `unchunked::Ct1Sent` `Message::encode`

Defines deterministic field and message allocator event transitions (`ekSentCt1ReceivedEncodeEvents`,
`ct1SentEncodeEvents`), envelope-parameterized and concrete `RustCliAllocBudget M` contracts, and
exact-capacity (`0`-allocation) specializations for `EkSentCt1Received::encode` and `Ct1Sent::encode`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeBytesField)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.SpqrV1.Auth
  (bytesField_1_length_of_ne_nil bytesField_2_length_of_ne_nil
   encodeAuthMsg encodeAuthMsg_length)
open CryptoVerification.SpqrV1.ProtoRepr
  (authenticatorPBEncodedLen ct1SentPBAt ct1SentPBEncodedLen ct1SentPBPinnedAt
   ekSentCt1ReceivedPBAt ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (Ct1SentEncodeGhost Ct1SentEncodePinnedGhost
   EkSentCt1ReceivedEncodeGhost EkSentCt1ReceivedEncodePinnedGhost
   bytesField3_len_of_ne_empty bytesField4_len_of_ne_empty bytesField5_len_of_ne_empty
   bytesFieldTagged encodeCt1SentMsg encodeCt1SentMsg_len_split
   encodeEkSentCt1ReceivedMsg encodeEkSentCt1ReceivedMsg_len_split
   msgHeaderBytes optAuthField2Bytes
   u64Field1Bytes u64Field1Bytes_len_of_ne_zero unchunkedMsgEncodeStackOf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (pushBytesStep pushBytesStep_of_spare reserveStep reserveStep_of_spare)

/-! ## 1. Deterministic Field & Message Allocator Event Transitions -/

/-- Capacity-and-events transition of an optional `u64` varint field with a 1-byte tag (`1#32`). -/
def u64Field1Step (cap len : Nat) (val : BitVec 64) : Nat × List AllocEvent :=
  if val == 0#64 then
    (cap, [])
  else
    pushBytesStep ((encodeVarint val).length + 1) cap len

theorem u64Field1Step_of_spare {cap len : Nat} {val : BitVec 64}
    (h : len + (u64Field1Bytes val).length ≤ cap) :
    u64Field1Step cap len val = (cap, []) := by
  unfold u64Field1Step
  by_cases hz : val == 0#64
  · simp only [hz, ↓reduceIte]
  · have hzf : (val == 0#64) = false := Bool.eq_false_iff.mpr hz
    have hne : val ≠ 0#64 := beq_eq_false_iff_ne.mp hzf
    have hlen := u64Field1Bytes_len_of_ne_zero hne
    simp only [hzf, Bool.false_eq_true, ↓reduceIte]
    exact pushBytesStep_of_spare _ _ _ (by omega)

/-- Capacity-and-events transition of an optional `bytes` field with a 1-byte tag (`1#32..5#32`). -/
def optBytesField1ByteTagStep (cap len : Nat) (bs : List (BitVec 8)) : Nat × List AllocEvent :=
  if bs.isEmpty then
    (cap, [])
  else
    let vlen := (encodeVarint (BitVec.ofNat 64 bs.length)).length
    let s1 := pushBytesStep (vlen + 1) cap len
    let s2 := reserveStep s1.1 (len + 1 + vlen) bs.length
    (s2.1, s1.2 ++ s2.2)

theorem optBytesField1ByteTagStep_of_spare {cap len : Nat} {bs : List (BitVec 8)}
    {fieldLen : Nat}
    (hne : bs.isEmpty = false →
      fieldLen = 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length)
    (h : len + fieldLen ≤ cap) :
    optBytesField1ByteTagStep cap len bs = (cap, []) := by
  unfold optBytesField1ByteTagStep
  cases he : bs.isEmpty
  · have hlen := hne he
    dsimp only [Bool.false_eq_true, ↓reduceIte]
    have hs1 : pushBytesStep ((encodeVarint (BitVec.ofNat 64 bs.length)).length + 1) cap len =
        (cap, []) :=
      pushBytesStep_of_spare _ _ _ (by omega)
    rw [hs1]
    have hs2 : reserveStep cap (len + 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length)
        bs.length = (cap, []) :=
      reserveStep_of_spare (by omega)
    rw [hs2]
    rfl
  · rfl

/-- Capacity-and-events transition of `Authenticator::encode` (`tag = 2#32`). -/
def authEncodeStep (cap len : Nat) (auth : AuthenticatorPB) : Nat × List AllocEvent :=
  let hdrVlen := (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length
  let s1 := pushBytesStep (hdrVlen + 1) cap len
  let rkLen := (encodeBytesField 1#32 auth.rootKey).length
  let s2 := optBytesField1ByteTagStep s1.1 (len + 1 + hdrVlen) auth.rootKey
  let s3 := optBytesField1ByteTagStep s2.1 (len + 1 + hdrVlen + rkLen) auth.macKey
  (s3.1, s1.2 ++ s2.2 ++ s3.2)

theorem authEncodeStep_of_spare {cap len : Nat} {auth : AuthenticatorPB}
    (h : len + (encodeAuthMsg auth).length ≤ cap) :
    authEncodeStep cap len auth = (cap, []) := by
  rw [encodeAuthMsg_length] at h
  dsimp only [authEncodeStep]
  have hs1 : pushBytesStep
      ((encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length + 1) cap len =
      (cap, []) :=
    pushBytesStep_of_spare _ _ _ (by omega)
  rw [hs1]
  have hs2 : optBytesField1ByteTagStep cap
      (len + 1 + (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length)
      auth.rootKey = (cap, []) :=
    optBytesField1ByteTagStep_of_spare
      (fieldLen := (encodeBytesField 1#32 auth.rootKey).length)
      (fun he => bytesField_1_length_of_ne_nil (List.isEmpty_eq_false_iff.mp he))
      (by omega)
  rw [hs2]
  have hs3 : optBytesField1ByteTagStep cap
      (len + 1 + (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length +
        (encodeBytesField 1#32 auth.rootKey).length)
      auth.macKey = (cap, []) :=
    optBytesField1ByteTagStep_of_spare
      (fieldLen := (encodeBytesField 2#32 auth.macKey).length)
      (fun he => bytesField_2_length_of_ne_nil (List.isEmpty_eq_false_iff.mp he))
      (by omega)
  rw [hs3]
  rfl

/-- Capacity-and-events transition of `auth: Option<Authenticator>` (field 2). -/
def optAuthField2Step (cap len : Nat) : Option AuthenticatorPB → Nat × List AllocEvent
  | none => (cap, [])
  | some auth => authEncodeStep cap len auth

theorem optAuthField2Step_of_spare {cap len : Nat} {optAuth : Option AuthenticatorPB}
    (h : len + (optAuthField2Bytes optAuth).length ≤ cap) :
    optAuthField2Step cap len optAuth = (cap, []) := by
  cases optAuth with
  | none => rfl
  | some auth =>
    have hsome : optAuthField2Bytes (some auth) = encodeAuthMsg auth := rfl
    rw [hsome] at h
    exact authEncodeStep_of_spare h

def ekSentCt1ReceivedPinnedToUnpinned (x : EkSentCt1ReceivedEncodePinnedGhost) :
    EkSentCt1ReceivedEncodeGhost :=
  ⟨x.msgA, x.m, x.v, x.cap, x.ptr, x.bs⟩

def ct1SentPinnedToUnpinned (x : Ct1SentEncodePinnedGhost) : Ct1SentEncodeGhost :=
  ⟨x.msgA, x.m, x.v, x.cap, x.ptr, x.bs⟩

/-- Deterministic `AllocEvent` list emitted by `EkSentCt1Received::encode` on `x`. -/
def ekSentCt1ReceivedEncodeEvents (x : EkSentCt1ReceivedEncodeGhost) : List AllocEvent :=
  let innerLen := ekSentCt1ReceivedPBEncodedLen x.m
  let hdrVlen := (encodeVarint (BitVec.ofNat 64 innerLen)).length
  let s1 := pushBytesStep (hdrVlen + 1) x.cap.toNat x.bs.length
  let l1 := x.bs.length + (msgHeaderBytes innerLen).length
  let s2 := u64Field1Step s1.1 l1 x.m.epoch
  let l2 := l1 + (u64Field1Bytes x.m.epoch).length
  let s3 := optAuthField2Step s2.1 l2 x.m.auth
  let l3 := l2 + (optAuthField2Bytes x.m.auth).length
  let s4 := optBytesField1ByteTagStep s3.1 l3 x.m.dk
  let l4 := l3 + (bytesFieldTagged 3#32 x.m.dk).length
  let s5 := optBytesField1ByteTagStep s4.1 l4 x.m.ct1
  s1.2 ++ s2.2 ++ s3.2 ++ s4.2 ++ s5.2

/-- Callee-fixed allocator event envelope of `EkSentCt1Received::encode`. -/
def EkSentCt1ReceivedEncodeEnv (x : EkSentCt1ReceivedEncodeGhost) (evs : List AllocEvent) : Prop :=
  evs = ekSentCt1ReceivedEncodeEvents x

/-- Deterministic `AllocEvent` list emitted by `Ct1Sent::encode` on `x`. -/
def ct1SentEncodeEvents (x : Ct1SentEncodeGhost) : List AllocEvent :=
  let innerLen := ct1SentPBEncodedLen x.m
  let hdrVlen := (encodeVarint (BitVec.ofNat 64 innerLen)).length
  let s1 := pushBytesStep (hdrVlen + 1) x.cap.toNat x.bs.length
  let l1 := x.bs.length + (msgHeaderBytes innerLen).length
  let s2 := u64Field1Step s1.1 l1 x.m.epoch
  let l2 := l1 + (u64Field1Bytes x.m.epoch).length
  let s3 := optAuthField2Step s2.1 l2 x.m.auth
  let l3 := l2 + (optAuthField2Bytes x.m.auth).length
  let s4 := optBytesField1ByteTagStep s3.1 l3 x.m.hdr
  let l4 := l3 + (bytesFieldTagged 3#32 x.m.hdr).length
  let s5 := optBytesField1ByteTagStep s4.1 l4 x.m.es
  let l5 := l4 + (bytesFieldTagged 4#32 x.m.es).length
  let s6 := optBytesField1ByteTagStep s5.1 l5 x.m.ct1
  s1.2 ++ s2.2 ++ s3.2 ++ s4.2 ++ s5.2 ++ s6.2

/-- Callee-fixed allocator event envelope of `Ct1Sent::encode`. -/
def Ct1SentEncodeEnv (x : Ct1SentEncodeGhost) (evs : List AllocEvent) : Prop :=
  evs = ct1SentEncodeEvents x

theorem ekSentCt1ReceivedEncodeEvents_of_spare {x : EkSentCt1ReceivedEncodeGhost}
    (h : x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat) :
    ekSentCt1ReceivedEncodeEvents x = [] := by
  rw [encodeEkSentCt1ReceivedMsg_len_split] at h
  have hhdr : (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length =
      1 + (encodeVarint (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen x.m))).length := by
    simp only [msgHeaderBytes, List.length_append, List.length_singleton]
  dsimp only [ekSentCt1ReceivedEncodeEvents]
  have hs1 : pushBytesStep
      ((encodeVarint (BitVec.ofNat 64 (ekSentCt1ReceivedPBEncodedLen x.m))).length + 1)
      x.cap.toNat x.bs.length = (x.cap.toNat, []) :=
    pushBytesStep_of_spare _ _ _ (by omega)
  rw [hs1]
  have hs2 : u64Field1Step x.cap.toNat
      (x.bs.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length) x.m.epoch =
      (x.cap.toNat, []) :=
    u64Field1Step_of_spare (by omega)
  rw [hs2]
  have hs3 : optAuthField2Step x.cap.toNat
      (x.bs.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length +
        (u64Field1Bytes x.m.epoch).length) x.m.auth = (x.cap.toNat, []) :=
    optAuthField2Step_of_spare (by omega)
  rw [hs3]
  have hs4 : optBytesField1ByteTagStep x.cap.toNat
      (x.bs.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length +
        (u64Field1Bytes x.m.epoch).length + (optAuthField2Bytes x.m.auth).length) x.m.dk =
      (x.cap.toNat, []) :=
    optBytesField1ByteTagStep_of_spare
      (fieldLen := (bytesFieldTagged 3#32 x.m.dk).length)
      bytesField3_len_of_ne_empty
      (by omega)
  rw [hs4]
  have hs5 : optBytesField1ByteTagStep x.cap.toNat
      (x.bs.length + (msgHeaderBytes (ekSentCt1ReceivedPBEncodedLen x.m)).length +
        (u64Field1Bytes x.m.epoch).length + (optAuthField2Bytes x.m.auth).length +
        (bytesFieldTagged 3#32 x.m.dk).length) x.m.ct1 = (x.cap.toNat, []) :=
    optBytesField1ByteTagStep_of_spare
      (fieldLen := (bytesFieldTagged 4#32 x.m.ct1).length)
      bytesField4_len_of_ne_empty
      (by omega)
  rw [hs5]
  rfl

theorem ct1SentEncodeEvents_of_spare {x : Ct1SentEncodeGhost}
    (h : x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat) :
    ct1SentEncodeEvents x = [] := by
  rw [encodeCt1SentMsg_len_split] at h
  have hhdr : (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length =
      1 + (encodeVarint (BitVec.ofNat 64 (ct1SentPBEncodedLen x.m))).length := by
    simp only [msgHeaderBytes, List.length_append, List.length_singleton]
  dsimp only [ct1SentEncodeEvents]
  have hs1 : pushBytesStep
      ((encodeVarint (BitVec.ofNat 64 (ct1SentPBEncodedLen x.m))).length + 1)
      x.cap.toNat x.bs.length = (x.cap.toNat, []) :=
    pushBytesStep_of_spare _ _ _ (by omega)
  rw [hs1]
  have hs2 : u64Field1Step x.cap.toNat
      (x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length) x.m.epoch =
      (x.cap.toNat, []) :=
    u64Field1Step_of_spare (by omega)
  rw [hs2]
  have hs3 : optAuthField2Step x.cap.toNat
      (x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length +
        (u64Field1Bytes x.m.epoch).length) x.m.auth = (x.cap.toNat, []) :=
    optAuthField2Step_of_spare (by omega)
  rw [hs3]
  have hs4 : optBytesField1ByteTagStep x.cap.toNat
      (x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length +
        (u64Field1Bytes x.m.epoch).length + (optAuthField2Bytes x.m.auth).length) x.m.hdr =
      (x.cap.toNat, []) :=
    optBytesField1ByteTagStep_of_spare
      (fieldLen := (bytesFieldTagged 3#32 x.m.hdr).length)
      bytesField3_len_of_ne_empty
      (by omega)
  rw [hs4]
  have hs5 : optBytesField1ByteTagStep x.cap.toNat
      (x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length +
        (u64Field1Bytes x.m.epoch).length + (optAuthField2Bytes x.m.auth).length +
        (bytesFieldTagged 3#32 x.m.hdr).length) x.m.es = (x.cap.toNat, []) :=
    optBytesField1ByteTagStep_of_spare
      (fieldLen := (bytesFieldTagged 4#32 x.m.es).length)
      bytesField4_len_of_ne_empty
      (by omega)
  rw [hs5]
  have hs6 : optBytesField1ByteTagStep x.cap.toNat
      (x.bs.length + (msgHeaderBytes (ct1SentPBEncodedLen x.m)).length +
        (u64Field1Bytes x.m.epoch).length + (optAuthField2Bytes x.m.auth).length +
        (bytesFieldTagged 3#32 x.m.hdr).length + (bytesFieldTagged 4#32 x.m.es).length) x.m.ct1 =
      (x.cap.toNat, []) :=
    optBytesField1ByteTagStep_of_spare
      (fieldLen := (bytesFieldTagged 5#32 x.m.ct1).length)
      bytesField5_len_of_ne_empty
      (by omega)
  rw [hs6]
  rfl

/-! ## 2. Budget-Threaded Specifications of `encode<EkSentCt1Received>` & `encode<Ct1Sent>` -/

/-- Envelope-parameterized pinned budget specification of `EkSentCt1Received::encode`. -/
def ekSentCt1ReceivedEncodePinnedSpecOfEnv (resStack : Nat)
    (Env : EkSentCt1ReceivedEncodeGhost → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodePinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (Env (ekSentCt1ReceivedPinnedToUnpinned x))⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
      (∃∗ evs : List AllocEvent, ⌜Env (ekSentCt1ReceivedPinnedToUnpinned x) evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)

/-- Envelope-parameterized unpinned budget specification of `EkSentCt1Received::encode`. -/
def ekSentCt1ReceivedEncodeSpecOfEnv (resStack : Nat)
    (Env : EkSentCt1ReceivedEncodeGhost → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      ekSentCt1ReceivedPBAt A.repAlloc x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBAt A.repAlloc x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
      (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)

abbrev ekSentCt1ReceivedEncodePinnedSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodePinnedGhost × M.σ) :=
  ekSentCt1ReceivedEncodePinnedSpecOfEnv resStack EkSentCt1ReceivedEncodeEnv A lim

abbrev ekSentCt1ReceivedEncodeSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodeGhost × M.σ) :=
  ekSentCt1ReceivedEncodeSpecOfEnv resStack EkSentCt1ReceivedEncodeEnv A lim

abbrev ekSentCt1ReceivedEncodePinnedSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodePinnedGhost × M.σ) :=
  ekSentCt1ReceivedEncodePinnedSpecOf doReserveStack A lim

abbrev ekSentCt1ReceivedEncodePinnedSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodePinnedGhost × M.σ) :=
  ekSentCt1ReceivedEncodePinnedSpecOf doReserveStackX A lim

abbrev ekSentCt1ReceivedEncodeSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodeGhost × M.σ) :=
  ekSentCt1ReceivedEncodeSpecOf doReserveStack A lim

abbrev ekSentCt1ReceivedEncodeSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodeGhost × M.σ) :=
  ekSentCt1ReceivedEncodeSpecOf doReserveStackX A lim

/-- Exact-capacity (`0`-allocation) pinned budget specification of `EkSentCt1Received::encode`. -/
def ekSentCt1ReceivedEncodeExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodePinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeEkSentCt1ReceivedMsg x.m) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)

theorem subroutine_ok_ekSentCt1ReceivedExact_of_pinned {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hok : subroutine_ok prog entry (ekSentCt1ReceivedEncodePinnedSpecOf resStack A lim)) :
    subroutine_ok prog entry (ekSentCt1ReceivedEncodeExactSpecOf resStack A lim) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [ekSentCt1ReceivedEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hfit⟩, hmem⟩ := hpre
  have hevs0 : ekSentCt1ReceivedEncodeEvents (ekSentCt1ReceivedPinnedToUnpinned x) = [] :=
    ekSentCt1ReceivedEncodeEvents_of_spare hfit
  have hfits : FitsEnv M lim st
      (EkSentCt1ReceivedEncodeEnv (ekSentCt1ReceivedPinnedToUnpinned x)) := by
    unfold EkSentCt1ReceivedEncodeEnv
    rw [FitsEnv.eq_iff, hevs0]; trivial
  have hpre' : s0.mem ⊨
      (ekSentCt1ReceivedEncodePinnedSpecOf resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [ekSentCt1ReceivedEncodePinnedSpecOf, ekSentCt1ReceivedEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inl hfit, hfits⟩, hmem⟩
  refine (hok.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [ekSentCt1ReceivedEncodePinnedSpecOf, ekSentCt1ReceivedEncodePinnedSpecOfEnv] at hq
    dsimp only [ekSentCt1ReceivedEncodeExactSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨htr, hq⟩ := hq
    refine ⟨htr, ?_⟩
    have hq' : sf.mem ⊨
        (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeEkSentCt1ReceivedMsg x.m)) ∗
        ((∃∗ evs : List AllocEvent,
            ⌜EkSentCt1ReceivedEncodeEnv (ekSentCt1ReceivedPinnedToUnpinned x) evs⌝ ∗
            A.pool lim (M.stepEvents evs st) sf) ∗
          (ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
            stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R)) := by
      convert hq using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq'
    obtain ⟨cap', hq'⟩ := hq'
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq'
    obtain ⟨ptr', hq'⟩ := hq'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
    obtain ⟨⟨_, hpres⟩, hq'⟩ := hq'
    obtain ⟨rfl, rfl⟩ := hpres hfit
    have hq'' : sf.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜EkSentCt1ReceivedEncodeEnv (ekSentCt1ReceivedPinnedToUnpinned x) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗
        (ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
          vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeEkSentCt1ReceivedMsg x.m) ∗
          stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R) := by
      convert hq' using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq''
    obtain ⟨evs, hq''⟩ := hq''
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq''
    obtain ⟨hevs, hq''⟩ := hq''
    dsimp only [EkSentCt1ReceivedEncodeEnv] at hevs
    rw [hevs, hevs0] at hq''
    dsimp only [AllocCostModel.stepEvents] at hq''
    convert hq'' using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-- Envelope-parameterized pinned budget specification of `Ct1Sent::encode`. -/
def ct1SentEncodePinnedSpecOfEnv (resStack : Nat)
    (Env : Ct1SentEncodeGhost → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodePinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeCt1SentMsg x.m).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (Env (ct1SentPinnedToUnpinned x))⌝ ∗
      ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeCt1SentMsg x.m)) ∗
      (∃∗ evs : List AllocEvent, ⌜Env (ct1SentPinnedToUnpinned x) evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)

/-- Envelope-parameterized unpinned budget specification of `Ct1Sent::encode`. -/
def ct1SentEncodeSpecOfEnv (resStack : Nat)
    (Env : Ct1SentEncodeGhost → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeCt1SentMsg x.m).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      ct1SentPBAt A.repAlloc x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBAt A.repAlloc x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeCt1SentMsg x.m)) ∗
      (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)

abbrev ct1SentEncodePinnedSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodePinnedGhost × M.σ) :=
  ct1SentEncodePinnedSpecOfEnv resStack Ct1SentEncodeEnv A lim

abbrev ct1SentEncodeSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodeGhost × M.σ) :=
  ct1SentEncodeSpecOfEnv resStack Ct1SentEncodeEnv A lim

abbrev ct1SentEncodePinnedSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodePinnedGhost × M.σ) :=
  ct1SentEncodePinnedSpecOf doReserveStack A lim

abbrev ct1SentEncodePinnedSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodePinnedGhost × M.σ) :=
  ct1SentEncodePinnedSpecOf doReserveStackX A lim

abbrev ct1SentEncodeSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodeGhost × M.σ) :=
  ct1SentEncodeSpecOf doReserveStack A lim

abbrev ct1SentEncodeSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodeGhost × M.σ) :=
  ct1SentEncodeSpecOf doReserveStackX A lim

/-- Exact-capacity (`0`-allocation) pinned budget specification of `Ct1Sent::encode`. -/
def ct1SentEncodeExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodePinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat⌝ ∗
      ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (unchunkedMsgEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeCt1SentMsg x.m) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (unchunkedMsgEncodeStackOf resStack)

theorem subroutine_ok_ct1SentExact_of_pinned {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hok : subroutine_ok prog entry (ct1SentEncodePinnedSpecOf resStack A lim)) :
    subroutine_ok prog entry (ct1SentEncodeExactSpecOf resStack A lim) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [ct1SentEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hfit⟩, hmem⟩ := hpre
  have hevs0 : ct1SentEncodeEvents (ct1SentPinnedToUnpinned x) = [] :=
    ct1SentEncodeEvents_of_spare hfit
  have hfits : FitsEnv M lim st (Ct1SentEncodeEnv (ct1SentPinnedToUnpinned x)) := by
    unfold Ct1SentEncodeEnv
    rw [FitsEnv.eq_iff, hevs0]; trivial
  have hpre' : s0.mem ⊨ (ct1SentEncodePinnedSpecOf resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [ct1SentEncodePinnedSpecOf, ct1SentEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inl hfit, hfits⟩, hmem⟩
  refine (hok.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [ct1SentEncodePinnedSpecOf, ct1SentEncodePinnedSpecOfEnv] at hq
    dsimp only [ct1SentEncodeExactSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨htr, hq⟩ := hq
    refine ⟨htr, ?_⟩
    have hq' : sf.mem ⊨
        (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
          ⌜x.cap.toNat ≤ cap'.toNat ∧
            (x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeCt1SentMsg x.m)) ∗
        ((∃∗ evs : List AllocEvent,
            ⌜Ct1SentEncodeEnv (ct1SentPinnedToUnpinned x) evs⌝ ∗
            A.pool lim (M.stepEvents evs st) sf) ∗
          (ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
            stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R)) := by
      convert hq using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq'
    obtain ⟨cap', hq'⟩ := hq'
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq'
    obtain ⟨ptr', hq'⟩ := hq'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
    obtain ⟨⟨_, hpres⟩, hq'⟩ := hq'
    obtain ⟨rfl, rfl⟩ := hpres hfit
    have hq'' : sf.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜Ct1SentEncodeEnv (ct1SentPinnedToUnpinned x) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗
        (ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
          vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeCt1SentMsg x.m) ∗
          stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R) := by
      convert hq' using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq''
    obtain ⟨evs, hq''⟩ := hq''
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq''
    obtain ⟨hevs, hq''⟩ := hq''
    dsimp only [Ct1SentEncodeEnv] at hevs
    rw [hevs, hevs0] at hq''
    dsimp only [AllocCostModel.stepEvents] at hq''
    convert hq'' using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
