/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.Proof
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint

/-!
# Tight Budget Pool & Canonical Codec Helpers for `Chunked.KeysSampled::merge` (Block `304`)

Provides the `SpqrTightEvs ops cum 2560`-backed allocator pool predicate `b304PoolAt`, `FitsEnv`
step projections, `bytesMergeEventsCore` tight 2-op / `19,578` B cost lemma, and canonical
`tlb_lenPrefixed` round-trip evaluations for Block `304`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common

open Arm64 ProofLib SepProp
open CryptoVerification.LibsignalSpqrV1
  (Bytes PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (WireType mergeMessage)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix)
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_authenticator loopsTo_ch_keysSampled loopsTo_polyEncoder
   mergeMessage_encode proto_encodeVarint_length)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs spqrAllocTightCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ValidAuthPB tlb_ValidChunkedKeysSampledPB tlb_ValidOptAuthPB
   tlb_ValidPolyEncoderPB tlb_ValidUcHeaderSentPB tlb_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget (BytesMerge3EnvCore)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (decodeVarint2Env_eq_nil_of_some)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

/-! ## 1. Tight Allocator Pool Token (`b304PoolAt`) & `FitsEnv` Combinators -/

/-- Tight `SpqrTightEvs ops cum 2560`-backed allocator pool assertion from initial cost-model
state `st`. -/
def b304PoolAt {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (ops cum : Nat) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜SpqrTightEvs ops cum 2560 evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

theorem b304PoolAt_init {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s : State) :
    A.pool lim st s ⊢ b304PoolAt A lim st 0 0 s := by
  unfold b304PoolAt
  refine Entails.sepExists_right [] ?_
  rw [M.stepEvents_nil]
  exact Entails.pure_right (SpqrTightEvs.nil 0 0 2560) (Entails.refl _)

theorem b304PoolAt_eq_of_vmPreserved {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {ops cum : Nat} {s1 s2 : State}
    (hvm : VmPreserved s1 s2) :
    b304PoolAt A lim st ops cum s2 = b304PoolAt A lim st ops cum s1 := by
  simp only [b304PoolAt, A.pool_of_vmPreserved hvm]

theorem b304PoolAt_of_vmPreserved {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {ops cum : Nat} {s1 s2 : State}
    (hvm : VmPreserved s1 s2) :
    b304PoolAt A lim st ops cum s1 ⊢ b304PoolAt A lim st ops cum s2 :=
  Entails.of_eq (b304PoolAt_eq_of_vmPreserved hvm).symm

theorem b304PoolAt_mono {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) {ops₁ ops₂ cum₁ cum₂ : Nat} (hops : ops₁ ≤ ops₂) (hcum : cum₁ ≤ cum₂)
    (s : State) :
    b304PoolAt A lim st ops₁ cum₁ s ⊢ b304PoolAt A lim st ops₂ cum₂ s := by
  unfold b304PoolAt
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  refine Entails.pure_left fun hevs => ?_
  exact Entails.pure_right (hevs.mono hops hcum (Nat.le_refl 2560)) (Entails.refl _)

theorem b304PoolAt_step_nil {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) {ops cum : Nat} {evs₁ evs₂ : List AllocEvent} {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    (h₁ : SpqrTightEvs ops cum 2560 evs₁) (hnil : evs₂ = []) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s1 ⊢
      b304PoolAt A lim st ops cum s2 := by
  subst hnil
  rw [M.stepEvents_nil]
  unfold b304PoolAt
  refine Entails.sepExists_right evs₁ ?_
  exact Entails.pure_right h₁ (Entails.of_eq (A.pool_of_vmPreserved hvm).symm)

theorem b304PoolAt_step {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) {ops₁ ops₂ cum₁ cum₂ r₂ : Nat} {evs₁ evs₂ : List AllocEvent} {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    (h₁ : SpqrTightEvs ops₁ cum₁ 2560 evs₁)
    (h₂ : SpqrTightEvs ops₂ cum₂ r₂ evs₂)
    (hr₂ : r₂ ≤ 2560) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s1 ⊢
      b304PoolAt A lim st (ops₁ + ops₂) (cum₁ + cum₂) s2 := by
  unfold b304PoolAt
  refine Entails.sepExists_right (evs₁ ++ evs₂) ?_
  have h12 : SpqrTightEvs (ops₁ + ops₂) (cum₁ + cum₂) 2560 (evs₁ ++ evs₂) :=
    (h₁.append h₂).mono (Nat.le_refl _) (Nat.le_refl _) (Nat.max_le.mpr ⟨Nat.le_refl 2560, hr₂⟩)
  rw [← M.stepEvents_append]
  exact Entails.pure_right h12 (Entails.of_eq (A.pool_of_vmPreserved hvm).symm)

theorem b304_fitsEnv_step_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {maxOps ops₁ ops₂ cum₁ cum₂ r₂ : Nat} {evs₁ : List AllocEvent}
    {E₂ : List AllocEvent → Prop}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560))
    (h₁ : SpqrTightEvs ops₁ cum₁ 2560 evs₁)
    (hSub : ∀ evs₂, E₂ evs₂ → SpqrTightEvs ops₂ cum₂ r₂ evs₂)
    (hOps : ops₁ + ops₂ ≤ maxOps)
    (hCum : cum₁ + cum₂ ≤ 384723)
    (hReq : r₂ ≤ 2560) :
    FitsEnv M lim (M.stepEvents evs₁ st) E₂ := by
  intro evs₂ hE₂
  have h₂ := hSub evs₂ hE₂
  have h12 : SpqrTightEvs maxOps 384723 2560 (evs₁ ++ evs₂) :=
    (h₁.append h₂).mono hOps hCum (Nat.max_le.mpr ⟨Nat.le_refl 2560, hReq⟩)
  exact ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) h12)).2

theorem b304_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits} {st' : M.σ}
    {bs rest : List (BitVec 8)} {v : BitVec 64}
    (hd : CryptoVerification.LibsignalProtoCodec.decodeVarint bs = some (v, rest)) :
    FitsEnv M lim st' (DecodeVarint2Env bs) := by
  intro evs hevs
  have hnil : evs = [] := decodeVarint2Env_eq_nil_of_some hd hevs
  subst hnil
  exact FitsEnv.nil [] rfl

theorem b304_bytesMerge3Env_spqrTight_2560
    {bs v rest : List (BitVec 8)} {evs : List AllocEvent}
    (hm : CryptoVerification.LibsignalProtoCodec.mergeBytes .lengthDelimited bs = some (v, rest))
    (hv : v.length ≤ 2560)
    (hevs : BytesMerge3EnvCore .lengthDelimited 0#64 bs evs) :
    SpqrTightEvs 2 19578 2560 evs := by
  change evs = bytesMergeEventsCore .lengthDelimited 0#64 bs at hevs
  subst hevs
  unfold bytesMergeEventsCore
  rw [hm]
  by_cases hz : v.length = 0
  · simp only [hz, ↓reduceIte]
    exact SpqrTightEvs.nil 2 19578 2560
  · simp only [hz, ↓reduceIte]
    have hcap0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have hnle : ¬ (v.length ≤ 0) := by omega
    have hres_le : reserveCap 0 0 v.length ≤ 2560 := by
      dsimp [reserveCap]
      omega
    have hcost : spqrAllocTightCost 2560 = 9789 := by decide
    have h1 : SpqrTightEvs 1 9789 2560 (rustAllocEvents v.length 1) := by
      rw [← hcost]
      exact SpqrTightEvs.rustAlloc hv (by decide)
    have h2 : SpqrTightEvs 1 9789 2560 (doReserveClearEvents (0#64 : BitVec 64).toNat v.length) := by
      rw [hcap0]
      unfold doReserveClearEvents
      simp only [hnle, ↓reduceIte]
      rw [← hcost]
      exact SpqrTightEvs.rustAlloc hres_le (by decide)
    have h3 : SpqrTightEvs 0 0 0 (rustDeallocEvents v.length 1) :=
      SpqrTightEvs.rustDealloc v.length 1
    exact ((h1.append h2).append h3).mono (by decide) (by decide) (by decide)

/-! ## 2. Suffix & Canonical Wire Length Bounds -/

theorem isDropSuffix_refl (bs : List (BitVec 8)) : IsDropSuffix bs bs := by
  unfold IsDropSuffix
  simp

theorem isDropSuffix_append_right (pre post : List (BitVec 8)) :
    IsDropSuffix (pre ++ post) post := by
  unfold IsDropSuffix
  have hsub : (pre ++ post).length - post.length = pre.length := by simp
  rw [hsub, List.drop_left]

theorem isDropSuffix_cons_tail (b : BitVec 8) (rest : List (BitVec 8)) :
    IsDropSuffix (b :: rest) rest :=
  isDropSuffix_append_right [b] rest

private theorem proto_encodeKey_length_le (tag : BitVec 32) (wt : WireType) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeKey tag wt).length ≤ 10 := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeKey
  exact (proto_encodeVarint_length _).2

private theorem proto_encodeUint32Field_length_le (tag v : BitVec 32) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint32Field tag v).length ≤ 20 := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeUint32Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := proto_encodeKey_length_le tag .varint
    have h2 := (proto_encodeVarint_length (v.zeroExtend 64)).2
    omega

private theorem proto_encodeUint64Field_length_le (tag : BitVec 32) (v : BitVec 64) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field tag v).length ≤ 20 := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := proto_encodeKey_length_le tag .varint
    have h2 := (proto_encodeVarint_length v).2
    omega

private theorem proto_encodeBytesUncond_length_le (tag : BitVec 32) (v : Bytes) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond tag v).length ≤ 20 + v.length := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond
  simp only [List.length_append]
  have h1 := proto_encodeKey_length_le tag .lengthDelimited
  have h2 := (proto_encodeVarint_length (BitVec.ofNat 64 v.length)).2
  omega

private theorem proto_encodeBytesField_length_le (tag : BitVec 32) (v : Bytes) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField tag v).length ≤ 20 + v.length := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField
  split
  · simp
  · exact proto_encodeBytesUncond_length_le tag v

private theorem proto_encodeOptMessage_length_le {N : Type} (encodeRaw : N → Bytes)
    (tag : BitVec 32) (opt : Option N) {B : Nat}
    (hB : ∀ n, opt = some n → (encodeRaw n).length ≤ B) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage encodeRaw tag opt).length ≤
      20 + B := by
  cases opt with
  | none =>
    simp [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage]
  | some n =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage]
    simp only [List.length_append]
    have h0 := proto_encodeKey_length_le tag .lengthDelimited
    have h1 := (proto_encodeVarint_length (BitVec.ofNat 64 (encodeRaw n).length)).2
    have h2 := hB n rfl
    omega

private theorem proto_encodeRepeatedBytes_length_le (tag : BitVec 32) (vs : List Bytes)
    (hv : ∀ s ∈ vs, s.length ≤ 2560) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeRepeatedBytes tag vs).length ≤
      vs.length * 2580 := by
  induction vs with
  | nil =>
    simp [CryptoVerification.LibsignalSpqrV1.Proto.encodeRepeatedBytes]
  | cons s tl ih =>
    have hcons :
        CryptoVerification.LibsignalSpqrV1.Proto.encodeRepeatedBytes tag (s :: tl) =
          CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond tag s ++
            CryptoVerification.LibsignalSpqrV1.Proto.encodeRepeatedBytes tag tl := rfl
    rw [hcons, List.length_append, List.length_cons]
    have hs : s.length ≤ 2560 := hv s List.mem_cons_self
    have h1 := proto_encodeBytesUncond_length_le tag s
    have h2 := ih (fun w hw => hv w (List.mem_cons_of_mem s hw))
    rw [Nat.succ_mul]
    omega

theorem validAuthPB_encodeRaw_len_le {a : ProtoAuthenticator} (ha : tlb_ValidAuthPB a) :
    (ProtoAuthenticator.encodeRaw a).length ≤ 104 := by
  rcases ha with ⟨hr, hm⟩
  unfold ProtoAuthenticator.encodeRaw
  simp only [List.length_append]
  have h1 := proto_encodeBytesField_length_le 1#32 a.rootKey
  have h2 := proto_encodeBytesField_length_le 2#32 a.macKey
  omega

theorem validUcHeaderSentPB_encodeRaw_len_le {u : V1State.Unchunked.HeaderSent}
    (hu : tlb_ValidUcHeaderSentPB u) :
    (V1State.Unchunked.HeaderSent.encodeRaw u).length ≤ 3736 := by
  rcases hu with ⟨hauth, hek, hdk⟩
  unfold V1State.Unchunked.HeaderSent.encodeRaw
  simp only [List.length_append]
  have h1 := proto_encodeUint64Field_length_le 1#32 u.epoch
  have h2 := proto_encodeOptMessage_length_le ProtoAuthenticator.encodeRaw 2#32 u.auth
    (fun a ha => validAuthPB_encodeRaw_len_le (hauth a ha))
  have h3 := proto_encodeBytesField_length_le 3#32 u.ek
  have h4 := proto_encodeBytesField_length_le 4#32 u.dk
  omega

theorem validPolyEncoderPB_encodeRaw_len_le {e : PolynomialEncoder}
    (he : tlb_ValidPolyEncoderPB e) :
    (PolynomialEncoder.encodeRaw e).length ≤ 41300 := by
  rcases he with ⟨_, hsum, hpts, hpolys⟩
  unfold PolynomialEncoder.encodeRaw
  simp only [List.length_append]
  have h1 := proto_encodeUint32Field_length_le 1#32 e.idx
  have h2 := proto_encodeRepeatedBytes_length_le 2#32 e.pts hpts
  have h3 := proto_encodeRepeatedBytes_length_le 3#32 e.polys hpolys
  have h23 : e.pts.length * 2580 + e.polys.length * 2580 ≤ 16 * 2580 := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right 2580 hsum
  omega

theorem validChunkedKeysSampledPB_encodeRaw_len_le {pb : V1State.Chunked.KeysSampled}
    (hpb : tlb_ValidChunkedKeysSampledPB pb) :
    (V1State.Chunked.KeysSampled.encodeRaw pb).length ≤ 45076 := by
  rcases hpb with ⟨huc, hhdr⟩
  unfold V1State.Chunked.KeysSampled.encodeRaw
  simp only [List.length_append]
  have h1 := proto_encodeOptMessage_length_le V1State.Unchunked.HeaderSent.encodeRaw 1#32 pb.uc
    (fun u hu => validUcHeaderSentPB_encodeRaw_len_le (huc u hu))
  have h2 := proto_encodeOptMessage_length_le PolynomialEncoder.encodeRaw 2#32 pb.sendingHdr
    (fun e he => validPolyEncoderPB_encodeRaw_len_le (hhdr e he))
  omega

/-! ## 3. Canonical Wire Step & `Proto.mergeMessage` Round-Trip Lemmas -/

theorem codec_decodeVarint_encodeVarint (v : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.LibsignalProtoCodec.decodeVarint
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ rest) = some (v, rest) := by
  rw [CryptoVerification.SpqrV1.Auth.protoEncodeVarint_eq_codec v]
  exact CryptoVerification.LibsignalProtoCodec.decodeVarint_encodeVarint v rest

theorem codec_decodeVarint_tlb_lenPrefixed (raw rest : Bytes) :
    CryptoVerification.LibsignalProtoCodec.decodeVarint (tlb_lenPrefixed raw rest) =
      some (BitVec.ofNat 64 raw.length, raw ++ rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  exact codec_decodeVarint_encodeVarint (BitVec.ofNat 64 raw.length) (raw ++ rest)

theorem codec_mergeBytes_encode (v rest : Bytes) (hv : v.length < 2 ^ 64) :
    CryptoVerification.LibsignalProtoCodec.mergeBytes .lengthDelimited
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 v.length) ++
        v ++ rest) = some (v, rest) := by
  rw [List.append_assoc, CryptoVerification.SpqrV1.Auth.protoEncodeVarint_eq_codec]
  exact CryptoVerification.LibsignalProtoCodec.mergeBytes_encode v rest hv

theorem proto_mergeMessage_authenticator_canonical (a : ProtoAuthenticator) (rest : Bytes)
    (ha : tlb_ValidAuthPB a) :
    (mergeMessage ProtoAuthenticator.mergeField .lengthDelimited default
      (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) rest) 97).toOption = some (a, rest) := by
  have hlen : (ProtoAuthenticator.encodeRaw a).length < 2 ^ 64 := by
    have := validAuthPB_encodeRaw_len_le ha
    omega
  unfold tlb_lenPrefixed
  rw [List.append_assoc,
    mergeMessage_encode ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw
      default a 97 rest (loopsTo_authenticator a hlen) hlen (by decide)]
  rfl

theorem proto_mergeMessage_polyEncoder_canonical (e : PolynomialEncoder) (rest : Bytes)
    (he : tlb_ValidPolyEncoderPB e) :
    (mergeMessage PolynomialEncoder.mergeField .lengthDelimited default
      (tlb_lenPrefixed (PolynomialEncoder.encodeRaw e) rest) 98).toOption = some (e, rest) := by
  have hlen : (PolynomialEncoder.encodeRaw e).length < 2 ^ 64 := by
    have := validPolyEncoderPB_encodeRaw_len_le he
    omega
  unfold tlb_lenPrefixed
  rw [List.append_assoc,
    mergeMessage_encode PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw
      default e 98 rest (loopsTo_polyEncoder e hlen) hlen (by decide)]
  rfl

theorem proto_mergeMessage_keysSampled_canonical (pb : V1State.Chunked.KeysSampled) (rest : Bytes)
    (hpb : tlb_ValidChunkedKeysSampledPB pb) :
    (mergeMessage V1State.Chunked.KeysSampled.mergeField .lengthDelimited default
      (tlb_lenPrefixed (V1State.Chunked.KeysSampled.encodeRaw pb) rest) 99).toOption =
        some (pb, rest) := by
  have hlen : (V1State.Chunked.KeysSampled.encodeRaw pb).length < 2 ^ 64 := by
    have := validChunkedKeysSampledPB_encodeRaw_len_le hpb
    omega
  unfold tlb_lenPrefixed
  rw [List.append_assoc,
    mergeMessage_encode V1State.Chunked.KeysSampled.mergeField 2
      V1State.Chunked.KeysSampled.encodeRaw default pb 99 rest
      (loopsTo_ch_keysSampled pb hlen) hlen (by decide)]
  rfl

/-! ## 4. Explicit Wire Prefix Decompositions for Tags `1..4` -/

theorem encodeOptMessage_tag1_some {N : Type} (encodeRaw : N → Bytes) (n : N) (rest : Bytes) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage encodeRaw 1#32 (some n) ++ rest =
      0x0a#8 :: tlb_lenPrefixed (encodeRaw n) rest := by
  dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, tlb_lenPrefixed]
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [0x0a#8] := by
    decide
  rw [hk]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

theorem encodeOptMessage_tag2_some {N : Type} (encodeRaw : N → Bytes) (n : N) (rest : Bytes) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage encodeRaw 2#32 (some n) ++ rest =
      0x12#8 :: tlb_lenPrefixed (encodeRaw n) rest := by
  dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, tlb_lenPrefixed]
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := by
    decide
  rw [hk]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

theorem encodeUint64Field_tag1_of_ne (v : BitVec 64) (hv : v ≠ 0#64) (rest : Bytes) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 v ++ rest =
      0x08#8 :: (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ rest) := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field
  have hbeq : (v == 0#64) = false := beq_eq_false_iff_ne.mpr hv
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .varint = [0x08#8] := by
    decide
  rw [hbeq]
  simp only [Bool.false_eq_true, ↓reduceIte, hk, List.cons_append, List.nil_append]

theorem encodeBytesField_tag3_of_ne (v rest : Bytes) (hv : v ≠ []) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 v ++ rest =
      0x1a#8 ::
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 v.length) ++
          v ++ rest) := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond
  have hne : v.isEmpty = false := List.isEmpty_eq_false_iff.mpr hv
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] := by
    decide
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte, hk, List.cons_append, List.nil_append, List.append_assoc]

theorem encodeBytesField_tag4_of_ne (v rest : Bytes) (hv : v ≠ []) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 v ++ rest =
      0x22#8 ::
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 v.length) ++
          v ++ rest) := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond
  have hne : v.isEmpty = false := List.isEmpty_eq_false_iff.mpr hv
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] := by
    decide
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte, hk, List.cons_append, List.nil_append, List.append_assoc]

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common
