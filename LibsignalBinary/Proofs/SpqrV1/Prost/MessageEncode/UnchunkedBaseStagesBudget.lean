/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Stage-Sequence Allocator Envelopes for `unchunked` `Message::encode`

Defines sequential capacity-monotone stage envelopes (`CapAfter`, `StageSeqEnv`, `hdrFieldEnv`,
`u64Field1Env`, `optAuthField2Env`, `optBytesField1ByteTagEnv`) and message-level envelopes
(`EkSentCt1ReceivedEncodeEnvS`, `Ct1SentEncodeEnvS`), specializing `UnchunkedBaseBudget` contracts
and proving spare-capacity bridges to the exact-capacity specifications.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.SpqrV1.Auth (encodeAuthMsg)
open CryptoVerification.SpqrV1.ProtoRepr
  (ct1SentPBEncodedLen ct1SentPBPinnedAt
   ekSentCt1ReceivedPBEncodedLen ekSentCt1ReceivedPBPinnedAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (Ct1SentEncodeGhost Ct1SentEncodePinnedGhost
   EkSentCt1ReceivedEncodeGhost EkSentCt1ReceivedEncodePinnedGhost
   bytesField3_len_of_ne_empty bytesField4_len_of_ne_empty bytesField5_len_of_ne_empty
   bytesFieldTagged encodeCt1SentMsg encodeCt1SentMsg_len_split
   encodeEkSentCt1ReceivedMsg encodeEkSentCt1ReceivedMsg_len_split
   msgHeaderBytes optAuthField2Bytes u64Field1Bytes unchunkedMsgEncodeStackOf)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents fitsEvents_append
   RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushBytesEvents pushBytesEvents_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
  (AuthEncodeEnv authEncodeEnv_eq_nil_of_spare authEncodeEnv_events authEncodeEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (reserveStep reserveStep_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
  (ct1SentEncodeExactSpecOf ct1SentEncodePinnedSpecOfEnv ct1SentEncodeSpecOfEnv
   ct1SentPinnedToUnpinned ekSentCt1ReceivedEncodeExactSpecOf
   ekSentCt1ReceivedEncodePinnedSpecOfEnv ekSentCt1ReceivedEncodeSpecOfEnv
   ekSentCt1ReceivedPinnedToUnpinned u64Field1Step u64Field1Step_of_spare)

/-! ## 1. Stage-Sequence Allocator Event Envelopes -/

/-- Post-stage capacity relation when appending `add` bytes onto a `Vec<u8>` of length `len` and
initial capacity `cap`: capacity never decreases, and stays equal to `cap` when `len + add ≤ cap`. -/
def CapAfter (cap : BitVec 64) (len add : Nat) (cap' : BitVec 64) : Prop :=
  cap.toNat ≤ cap'.toNat ∧ (len + add ≤ cap.toNat → cap' = cap)

theorem CapAfter.refl (cap : BitVec 64) (len add : Nat) : CapAfter cap len add cap :=
  ⟨Nat.le_refl _, fun _ => rfl⟩

/-- Sequential allocator event envelope for a stage `E` (appending `add` bytes onto a buffer of
capacity `cap` and length `len`, yielding post-stage capacity `cap'` with `CapAfter cap len add cap'`)
followed by continuation envelope `K cap'`. -/
def StageSeqEnv (cap : BitVec 64) (len add : Nat) (E : List AllocEvent → Prop)
    (K : BitVec 64 → List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  ∃ evs₁ evs₂ cap', evs = evs₁ ++ evs₂ ∧ E evs₁ ∧ CapAfter cap len add cap' ∧ K cap' evs₂

theorem StageSeqEnv.intro {cap : BitVec 64} {len add : Nat} {E : List AllocEvent → Prop}
    {K : BitVec 64 → List AllocEvent → Prop} {evs₁ evs₂ : List AllocEvent} {cap' : BitVec 64}
    (he₁ : E evs₁) (hcap : CapAfter cap len add cap') (hk : K cap' evs₂) :
    StageSeqEnv cap len add E K (evs₁ ++ evs₂) :=
  ⟨evs₁, evs₂, cap', rfl, he₁, hcap, hk⟩

theorem StageSeqEnv.nonempty {cap : BitVec 64} {len add : Nat} {E : List AllocEvent → Prop}
    {K : BitVec 64 → List AllocEvent → Prop}
    (hE : ∃ evs₁, E evs₁) (hK : ∃ evs₂, K cap evs₂) :
    ∃ evs, StageSeqEnv cap len add E K evs := by
  obtain ⟨evs₁, he₁⟩ := hE
  obtain ⟨evs₂, hk⟩ := hK
  exact ⟨evs₁ ++ evs₂, StageSeqEnv.intro he₁ (CapAfter.refl cap len add) hk⟩

theorem FitsEnv.stageSeq_left {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {cap : BitVec 64} {len add : Nat} {E : List AllocEvent → Prop}
    {K : BitVec 64 → List AllocEvent → Prop}
    (h : FitsEnv M lim st (StageSeqEnv cap len add E K))
    (hK : ∃ evs₂, K cap evs₂) :
    FitsEnv M lim st E := by
  obtain ⟨evs₂, hk⟩ := hK
  intro evs₁ he₁
  exact ((fitsEvents_append M lim evs₁ evs₂ st).mp
    (h (evs₁ ++ evs₂) (StageSeqEnv.intro he₁ (CapAfter.refl cap len add) hk))).1

theorem FitsEnv.stageSeq_right {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {cap cap' : BitVec 64} {len add : Nat} {E : List AllocEvent → Prop}
    {K : BitVec 64 → List AllocEvent → Prop} {evs₁ : List AllocEvent}
    (h : FitsEnv M lim st (StageSeqEnv cap len add E K))
    (he₁ : E evs₁) (hcap : CapAfter cap len add cap') :
    FitsEnv M lim (M.stepEvents evs₁ st) (K cap') := by
  intro evs₂ hk
  exact ((fitsEvents_append M lim evs₁ evs₂ st).mp
    (h (evs₁ ++ evs₂) (StageSeqEnv.intro he₁ hcap hk))).2

theorem stageSeqEnv_eq_nil_of_spare {cap : BitVec 64} {len add : Nat}
    {E : List AllocEvent → Prop} {K : BitVec 64 → List AllocEvent → Prop}
    {evs : List AllocEvent}
    (hspare : len + add ≤ cap.toNat)
    (hE : ∀ e, E e → e = [])
    (hK : ∀ e, K cap e → e = [])
    (hev : StageSeqEnv cap len add E K evs) :
    evs = [] := by
  obtain ⟨evs₁, evs₂, cap', rfl, he₁, hcap, hk⟩ := hev
  rw [hcap.2 hspare] at hk
  rw [hE evs₁ he₁, hK evs₂ hk]
  rfl

/-- Stage 1 envelope: outer length-delimited message header (`0x0a` + `encode_varint innerLen`). -/
def hdrFieldEnv (cap : BitVec 64) (len innerLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = pushBytesEvents ((encodeVarint (BitVec.ofNat 64 innerLen)).length + 1) cap.toNat len

theorem hdrFieldEnv_nonempty (cap : BitVec 64) (len innerLen : Nat) :
    ∃ evs, hdrFieldEnv cap len innerLen evs :=
  ⟨_, rfl⟩

theorem hdrFieldEnv_eq_nil_of_spare {cap : BitVec 64} {len innerLen : Nat} {evs : List AllocEvent}
    (h : len + (msgHeaderBytes innerLen).length ≤ cap.toNat)
    (hev : hdrFieldEnv cap len innerLen evs) : evs = [] := by
  have hhdr : (msgHeaderBytes innerLen).length =
      1 + (encodeVarint (BitVec.ofNat 64 innerLen)).length := by
    simp only [msgHeaderBytes, List.length_append, List.length_singleton]
  exact hev.trans (pushBytesEvents_of_spare _ _ _ (by omega))

/-- Stage 2 envelope: optional `u64` varint field (`tag = 1#32`). -/
def u64Field1Env (cap : BitVec 64) (len : Nat) (val : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = (u64Field1Step cap.toNat len val).2

theorem u64Field1Env_nonempty (cap : BitVec 64) (len : Nat) (val : BitVec 64) :
    ∃ evs, u64Field1Env cap len val evs :=
  ⟨_, rfl⟩

theorem u64Field1Env_eq_nil_of_spare {cap : BitVec 64} {len : Nat} {val : BitVec 64}
    {evs : List AllocEvent}
    (h : len + (u64Field1Bytes val).length ≤ cap.toNat)
    (hev : u64Field1Env cap len val evs) : evs = [] := by
  rw [hev, u64Field1Step_of_spare h]

/-- Stage 3 envelope: optional `Authenticator` nested message field (`tag = 2#32`). -/
def optAuthField2Env (cap : BitVec 64) (len : Nat) :
    Option AuthenticatorPB → List AllocEvent → Prop
  | none => (· = [])
  | some auth => fun evs =>
      ∃ authA v ptr : BitVec 64, ∃ bs : List (BitVec 8),
        bs.length = len ∧ AuthEncodeEnv ⟨authA, auth, v, cap, ptr, bs⟩ evs

theorem optAuthField2Env_nonempty (cap : BitVec 64) (len : Nat)
    (optAuth : Option AuthenticatorPB) :
    ∃ evs, optAuthField2Env cap len optAuth evs := by
  cases optAuth with
  | none => exact ⟨[], rfl⟩
  | some auth =>
    exact ⟨authEncodeEvents ⟨0#64, auth, 0#64, cap, 0#64, List.replicate len 0#8⟩,
      0#64, 0#64, 0#64, List.replicate len 0#8, List.length_replicate,
      authEncodeEnv_events _⟩

theorem optAuthField2Env_eq_nil_of_spare {cap : BitVec 64} {len : Nat}
    {optAuth : Option AuthenticatorPB} {evs : List AllocEvent}
    (h : len + (optAuthField2Bytes optAuth).length ≤ cap.toNat)
    (hev : optAuthField2Env cap len optAuth evs) : evs = [] := by
  cases optAuth with
  | none => exact hev
  | some auth =>
    obtain ⟨authA, v, ptr, bs, hbs_len, hev'⟩ := hev
    have hsome : optAuthField2Bytes (some auth) = encodeAuthMsg auth := rfl
    rw [hsome, ← hbs_len] at h
    exact authEncodeEnv_eq_nil_of_spare h hev'

/-- Envelope of an optional `bytes` field with a 1-byte tag (`tag ∈ {3, 4, 5}`):
either empty (`[]`), or `pushBytesEvents (vlen + 1) cap len` (yielding existential `cap_mid`)
followed by `(reserveStep cap_mid (len + 1 + vlen) bs.length).2`. -/
def optBytesField1ByteTagEnv (cap : BitVec 64) (len : Nat) (bs : List (BitVec 8)) :
    List AllocEvent → Prop :=
  if bs.isEmpty then
    (· = [])
  else
    let vlen := (encodeVarint (BitVec.ofNat 64 bs.length)).length
    StageSeqEnv cap len (1 + vlen)
      (· = pushBytesEvents (vlen + 1) cap.toNat len)
      (fun cap_mid evs => evs = (reserveStep cap_mid.toNat (len + 1 + vlen) bs.length).2)

theorem optBytesField1ByteTagEnv_nonempty (cap : BitVec 64) (len : Nat) (bs : List (BitVec 8)) :
    ∃ evs, optBytesField1ByteTagEnv cap len bs evs := by
  unfold optBytesField1ByteTagEnv
  cases bs.isEmpty
  · exact StageSeqEnv.nonempty ⟨_, rfl⟩ ⟨_, rfl⟩
  · exact ⟨[], rfl⟩

theorem optBytesField1ByteTagEnv_of_empty {cap : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (he : bs.isEmpty = true) :
    optBytesField1ByteTagEnv cap len bs [] := by
  simp only [optBytesField1ByteTagEnv, he, ↓reduceIte]

theorem optBytesField1ByteTagEnv_of_ne_empty {cap cap_mid : BitVec 64} {len : Nat}
    {bs : List (BitVec 8)} (he : bs.isEmpty = false)
    (hcap : CapAfter cap len (1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length) cap_mid) :
    optBytesField1ByteTagEnv cap len bs
      (pushBytesEvents ((encodeVarint (BitVec.ofNat 64 bs.length)).length + 1) cap.toNat len ++
        (reserveStep cap_mid.toNat
          (len + 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length) bs.length).2) := by
  simp only [optBytesField1ByteTagEnv, he, Bool.false_eq_true, ↓reduceIte]
  exact StageSeqEnv.intro rfl hcap rfl

theorem fitsEvents_optBytesTag_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {cap : BitVec 64} {len : Nat} {bs : List (BitVec 8)} (he : bs.isEmpty = false)
    (h : FitsEnv M lim st (optBytesField1ByteTagEnv cap len bs)) :
    FitsEvents M lim st
      (pushBytesEvents ((encodeVarint (BitVec.ofNat 64 bs.length)).length + 1) cap.toNat len) := by
  simp only [optBytesField1ByteTagEnv, he, Bool.false_eq_true, ↓reduceIte] at h
  exact FitsEnv.stageSeq_left h ⟨_, rfl⟩ _ rfl

theorem fitsEvents_optBytesReserve_of_fitsEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {cap cap_mid : BitVec 64} {len : Nat} {bs : List (BitVec 8)} (he : bs.isEmpty = false)
    (h : FitsEnv M lim st (optBytesField1ByteTagEnv cap len bs))
    (hcap : CapAfter cap len (1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length) cap_mid) :
    FitsEvents M lim
      (M.stepEvents
        (pushBytesEvents ((encodeVarint (BitVec.ofNat 64 bs.length)).length + 1) cap.toNat len) st)
      ((reserveStep cap_mid.toNat
        (len + 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length) bs.length).2) := by
  simp only [optBytesField1ByteTagEnv, he, Bool.false_eq_true, ↓reduceIte] at h
  exact FitsEnv.stageSeq_right h rfl hcap _ rfl

theorem optBytesField1ByteTagEnv_eq_nil_of_spare {cap : BitVec 64} {len : Nat}
    {bs : List (BitVec 8)} {fieldLen : Nat} {evs : List AllocEvent}
    (hne : bs.isEmpty = false →
      fieldLen = 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length)
    (h : len + fieldLen ≤ cap.toNat)
    (hev : optBytesField1ByteTagEnv cap len bs evs) : evs = [] := by
  unfold optBytesField1ByteTagEnv at hev
  cases he : bs.isEmpty
  · rw [he] at hev
    dsimp only [Bool.false_eq_true, ↓reduceIte] at hev
    have hlen := hne he
    refine stageSeqEnv_eq_nil_of_spare (by omega)
      (fun _ he₁ => he₁.trans (pushBytesEvents_of_spare _ _ _ (by omega)))
      (fun _ hk => hk.trans ?_) hev
    rw [reserveStep_of_spare (by omega)]
  · rw [he] at hev
    exact hev

/-- Stage-sequence allocator event envelope of `EkSentCt1Received::encode`. -/
def EkSentCt1ReceivedEncodeEnvS (x : EkSentCt1ReceivedEncodeGhost) : List AllocEvent → Prop :=
  let innerLen := ekSentCt1ReceivedPBEncodedLen x.m
  let l0 := x.bs.length
  let a1 := (msgHeaderBytes innerLen).length
  let l1 := l0 + a1
  let a2 := (u64Field1Bytes x.m.epoch).length
  let l2 := l1 + a2
  let a3 := (optAuthField2Bytes x.m.auth).length
  let l3 := l2 + a3
  let a4 := (bytesFieldTagged 3#32 x.m.dk).length
  let l4 := l3 + a4
  StageSeqEnv x.cap l0 a1 (hdrFieldEnv x.cap l0 innerLen) fun cap1 =>
    StageSeqEnv cap1 l1 a2 (u64Field1Env cap1 l1 x.m.epoch) fun cap2 =>
      StageSeqEnv cap2 l2 a3 (optAuthField2Env cap2 l2 x.m.auth) fun cap3 =>
        StageSeqEnv cap3 l3 a4 (optBytesField1ByteTagEnv cap3 l3 x.m.dk) fun cap4 =>
          optBytesField1ByteTagEnv cap4 l4 x.m.ct1

/-- Stage-sequence allocator event envelope of `Ct1Sent::encode`. -/
def Ct1SentEncodeEnvS (x : Ct1SentEncodeGhost) : List AllocEvent → Prop :=
  let innerLen := ct1SentPBEncodedLen x.m
  let l0 := x.bs.length
  let a1 := (msgHeaderBytes innerLen).length
  let l1 := l0 + a1
  let a2 := (u64Field1Bytes x.m.epoch).length
  let l2 := l1 + a2
  let a3 := (optAuthField2Bytes x.m.auth).length
  let l3 := l2 + a3
  let a4 := (bytesFieldTagged 3#32 x.m.hdr).length
  let l4 := l3 + a4
  let a5 := (bytesFieldTagged 4#32 x.m.es).length
  let l5 := l4 + a5
  StageSeqEnv x.cap l0 a1 (hdrFieldEnv x.cap l0 innerLen) fun cap1 =>
    StageSeqEnv cap1 l1 a2 (u64Field1Env cap1 l1 x.m.epoch) fun cap2 =>
      StageSeqEnv cap2 l2 a3 (optAuthField2Env cap2 l2 x.m.auth) fun cap3 =>
        StageSeqEnv cap3 l3 a4 (optBytesField1ByteTagEnv cap3 l3 x.m.hdr) fun cap4 =>
          StageSeqEnv cap4 l4 a5 (optBytesField1ByteTagEnv cap4 l4 x.m.es) fun cap5 =>
            optBytesField1ByteTagEnv cap5 l5 x.m.ct1

theorem ekSentCt1ReceivedEncodeEnvS_eq_nil_of_spare {x : EkSentCt1ReceivedEncodeGhost}
    {evs : List AllocEvent}
    (h : x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat)
    (hev : EkSentCt1ReceivedEncodeEnvS x evs) : evs = [] := by
  rw [encodeEkSentCt1ReceivedMsg_len_split] at h
  refine stageSeqEnv_eq_nil_of_spare (by omega)
    (fun _ h1 => hdrFieldEnv_eq_nil_of_spare (by omega) h1) (fun _ hrest1 => ?_) hev
  refine stageSeqEnv_eq_nil_of_spare (by omega)
    (fun _ h2 => u64Field1Env_eq_nil_of_spare (by omega) h2) (fun _ hrest2 => ?_) hrest1
  refine stageSeqEnv_eq_nil_of_spare (by omega)
    (fun _ h3 => optAuthField2Env_eq_nil_of_spare (by omega) h3) (fun _ hrest3 => ?_) hrest2
  refine stageSeqEnv_eq_nil_of_spare (by omega)
    (fun _ h4 => optBytesField1ByteTagEnv_eq_nil_of_spare bytesField3_len_of_ne_empty (by omega) h4)
    (fun _ h5 => optBytesField1ByteTagEnv_eq_nil_of_spare bytesField4_len_of_ne_empty (by omega) h5)
    hrest3

theorem fitsEnv_ekSentCt1ReceivedEncodeS_of_spare {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : EkSentCt1ReceivedEncodeGhost}
    (h : x.bs.length + (encodeEkSentCt1ReceivedMsg x.m).length ≤ x.cap.toNat) :
    FitsEnv M lim st (EkSentCt1ReceivedEncodeEnvS x) := by
  intro evs hev
  rw [ekSentCt1ReceivedEncodeEnvS_eq_nil_of_spare h hev]
  trivial

theorem ct1SentEncodeEnvS_eq_nil_of_spare {x : Ct1SentEncodeGhost} {evs : List AllocEvent}
    (h : x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat)
    (hev : Ct1SentEncodeEnvS x evs) : evs = [] := by
  rw [encodeCt1SentMsg_len_split] at h
  refine stageSeqEnv_eq_nil_of_spare (by omega)
    (fun _ h1 => hdrFieldEnv_eq_nil_of_spare (by omega) h1) (fun _ hrest1 => ?_) hev
  refine stageSeqEnv_eq_nil_of_spare (by omega)
    (fun _ h2 => u64Field1Env_eq_nil_of_spare (by omega) h2) (fun _ hrest2 => ?_) hrest1
  refine stageSeqEnv_eq_nil_of_spare (by omega)
    (fun _ h3 => optAuthField2Env_eq_nil_of_spare (by omega) h3) (fun _ hrest3 => ?_) hrest2
  refine stageSeqEnv_eq_nil_of_spare (by omega)
    (fun _ h4 => optBytesField1ByteTagEnv_eq_nil_of_spare bytesField3_len_of_ne_empty (by omega) h4)
    (fun _ hrest4 => ?_) hrest3
  refine stageSeqEnv_eq_nil_of_spare (by omega)
    (fun _ h5 => optBytesField1ByteTagEnv_eq_nil_of_spare bytesField4_len_of_ne_empty (by omega) h5)
    (fun _ h6 => optBytesField1ByteTagEnv_eq_nil_of_spare bytesField5_len_of_ne_empty (by omega) h6)
    hrest4

theorem fitsEnv_ct1SentEncodeS_of_spare {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {x : Ct1SentEncodeGhost}
    (h : x.bs.length + (encodeCt1SentMsg x.m).length ≤ x.cap.toNat) :
    FitsEnv M lim st (Ct1SentEncodeEnvS x) := by
  intro evs hev
  rw [ct1SentEncodeEnvS_eq_nil_of_spare h hev]
  trivial

/-! ## 2. Stage-Sequence Budget Specifications & Exact-Capacity Bridges -/

abbrev ekSentCt1ReceivedEncodePinnedSpecOfS (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodePinnedGhost × M.σ) :=
  ekSentCt1ReceivedEncodePinnedSpecOfEnv resStack EkSentCt1ReceivedEncodeEnvS A lim

abbrev ekSentCt1ReceivedEncodeSpecOfS (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodeGhost × M.σ) :=
  ekSentCt1ReceivedEncodeSpecOfEnv resStack EkSentCt1ReceivedEncodeEnvS A lim

abbrev ekSentCt1ReceivedEncodePinnedSpecS {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodePinnedGhost × M.σ) :=
  ekSentCt1ReceivedEncodePinnedSpecOfS doReserveStack A lim

abbrev ekSentCt1ReceivedEncodePinnedSpecXS {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodePinnedGhost × M.σ) :=
  ekSentCt1ReceivedEncodePinnedSpecOfS doReserveStackX A lim

abbrev ekSentCt1ReceivedEncodeSpecS {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodeGhost × M.σ) :=
  ekSentCt1ReceivedEncodeSpecOfS doReserveStack A lim

abbrev ekSentCt1ReceivedEncodeSpecXS {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EkSentCt1ReceivedEncodeGhost × M.σ) :=
  ekSentCt1ReceivedEncodeSpecOfS doReserveStackX A lim

theorem subroutine_ok_ekSentCt1ReceivedExact_of_pinnedS {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hok : subroutine_ok prog entry (ekSentCt1ReceivedEncodePinnedSpecOfS resStack A lim)) :
    subroutine_ok prog entry (ekSentCt1ReceivedEncodeExactSpecOf resStack A lim) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [ekSentCt1ReceivedEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hfit⟩, hmem⟩ := hpre
  have hfits : FitsEnv M lim st
      (EkSentCt1ReceivedEncodeEnvS (ekSentCt1ReceivedPinnedToUnpinned x)) :=
    fitsEnv_ekSentCt1ReceivedEncodeS_of_spare hfit
  have hpre' : s0.mem ⊨
      (ekSentCt1ReceivedEncodePinnedSpecOfS resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [ekSentCt1ReceivedEncodePinnedSpecOfS, ekSentCt1ReceivedEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inl hfit, hfits⟩, hmem⟩
  refine (hok.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [ekSentCt1ReceivedEncodePinnedSpecOfS, ekSentCt1ReceivedEncodePinnedSpecOfEnv] at hq
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
            ⌜EkSentCt1ReceivedEncodeEnvS (ekSentCt1ReceivedPinnedToUnpinned x) evs⌝ ∗
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
          ⌜EkSentCt1ReceivedEncodeEnvS (ekSentCt1ReceivedPinnedToUnpinned x) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗
        (ekSentCt1ReceivedPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
          vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeEkSentCt1ReceivedMsg x.m) ∗
          stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R) := by
      convert hq' using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq''
    obtain ⟨evs, hq''⟩ := hq''
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq''
    obtain ⟨hevs, hq''⟩ := hq''
    rw [ekSentCt1ReceivedEncodeEnvS_eq_nil_of_spare hfit hevs] at hq''
    dsimp only [AllocCostModel.stepEvents] at hq''
    convert hq'' using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

abbrev ct1SentEncodePinnedSpecOfS (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodePinnedGhost × M.σ) :=
  ct1SentEncodePinnedSpecOfEnv resStack Ct1SentEncodeEnvS A lim

abbrev ct1SentEncodeSpecOfS (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodeGhost × M.σ) :=
  ct1SentEncodeSpecOfEnv resStack Ct1SentEncodeEnvS A lim

abbrev ct1SentEncodePinnedSpecS {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodePinnedGhost × M.σ) :=
  ct1SentEncodePinnedSpecOfS doReserveStack A lim

abbrev ct1SentEncodePinnedSpecXS {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodePinnedGhost × M.σ) :=
  ct1SentEncodePinnedSpecOfS doReserveStackX A lim

abbrev ct1SentEncodeSpecS {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodeGhost × M.σ) :=
  ct1SentEncodeSpecOfS doReserveStack A lim

abbrev ct1SentEncodeSpecXS {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (Ct1SentEncodeGhost × M.σ) :=
  ct1SentEncodeSpecOfS doReserveStackX A lim

theorem subroutine_ok_ct1SentExact_of_pinnedS {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hok : subroutine_ok prog entry (ct1SentEncodePinnedSpecOfS resStack A lim)) :
    subroutine_ok prog entry (ct1SentEncodeExactSpecOf resStack A lim) := by
  apply subroutine_ok_outcome_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  dsimp only [ct1SentEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hfit⟩, hmem⟩ := hpre
  have hfits : FitsEnv M lim st (Ct1SentEncodeEnvS (ct1SentPinnedToUnpinned x)) :=
    fitsEnv_ct1SentEncodeS_of_spare hfit
  have hpre' : s0.mem ⊨ (ct1SentEncodePinnedSpecOfS resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [ct1SentEncodePinnedSpecOfS, ct1SentEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inl hfit, hfits⟩, hmem⟩
  refine (hok.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [ct1SentEncodePinnedSpecOfS, ct1SentEncodePinnedSpecOfEnv] at hq
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
            ⌜Ct1SentEncodeEnvS (ct1SentPinnedToUnpinned x) evs⌝ ∗
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
          ⌜Ct1SentEncodeEnvS (ct1SentPinnedToUnpinned x) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sf) ∗
        (ct1SentPBPinnedAt A.repAlloc x.g x.msgA x.m ∗
          vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeCt1SentMsg x.m) ∗
          stackAt s0.sp (unchunkedMsgEncodeStackOf resStack) ∗ R) := by
      convert hq' using 1; sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq''
    obtain ⟨evs, hq''⟩ := hq''
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq''
    obtain ⟨hevs, hq''⟩ := hq''
    rw [ct1SentEncodeEnvS_eq_nil_of_spare hfit hevs] at hq''
    dsimp only [AllocCostModel.stepEvents] at hq''
    convert hq'' using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
