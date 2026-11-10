/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightP297PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLenBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderTightPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import ProofLib.Hoare.SubroutineOk
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Placed Budget Contracts for `PolynomialDecoder::merge` & `PolynomialEncoder::merge` (Blocks `296`–`297`)

Proves `tlb_PolyDecoderMergePlacedTightOkOf` (Block `296`) and exports
`tlb_PolyEncoderMergePlacedTightOkOf` (Block `297`) within `SpqrTightEvs maxOps 342615 2560`
(`35 ≤ maxOps`: at most `3` `Vec<Vec<u8>>` `grow_one` operations up to `384` B plus `16 × 2`
`bytes::merge` allocations up to `2,560` B) under zero-initial-capacity guards on canonical
`tlb_Poly{Decoder,Encoder}Dom` inputs, falling back to `Poly{Decoder,Encoder}MergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyMergeTightPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalSessionLib ls_blockPlacement_base lsmpl)
open CryptoVerification.LibsignalSpqrV1
  (Bytes PolynomialDecoder PolynomialEncoder ProtoPolynomialDecoder ProtoPolynomialEncoder)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBoolField encodeBytesUncond encodeKey encodeRepeatedBytes encodeUint32Field encodeVarint
   encodeVarintAux mergeMessage)
open CryptoVerification.LibsignalTripleRatchet (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter sliceCursorAt)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialDecoderGhost ProtoPolynomialEncoderGhost protoPolynomialDecoderAt
   protoPolynomialDecoderPinnedAt protoPolynomialEncoderAt protoPolynomialEncoderPinnedAt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (protoPolynomialDecoderAt_eq_exists_pinned protoPolynomialEncoderAt_eq_exists_pinned)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyDecoderMergeGhost PolyEncoderMergeGhost SepWPp.elim_lscroProp WppPost blkPC_296 blkPC_297
   blkPl_296 blkPl_297 codecWireTypeToProto polyDecoderToProto polyEncoderToProto polyMergeStack
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp withLscroProp)
open CryptoVerification.SpqrV1Sync.Codec
  (length_le_encodeRepeatedBytes loopsTo_polyDecoder loopsTo_polyEncoder mergeMessage_encode)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_PolyDecoderDom tlb_PolyDecoderGuardedEnvOf tlb_PolyDecoderMergePlacedTightOk
   tlb_PolyDecoderMergePlacedTightOkOf tlb_PolyEncoderDom tlb_PolyEncoderGuardedEnvOf
   tlb_PolyEncoderMergePlacedTightOk tlb_PolyEncoderMergePlacedTightOkOf tlb_ValidPolyDecoderPB
   tlb_ValidPolyEncoderPB tlb_domHeap tlb_domHeap_of_dom tlb_domHeap_of_not_dom
   tlb_fitsEnv_fallback_of_not_dom tlb_lenPrefixed tlb_polyDecoderMergeTightSpecOfEnv
   tlb_polyDecoderZeroCapAt tlb_polyDecoderZeroCapAt_of_ptr tlb_polyEncoderMergeTightSpecOfEnv
   tlb_polyEncoderZeroCapAt tlb_polyEncoderZeroCapAt_of_ptrs)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergeEnv PolyDecoderMergePostEnv PolyEncoderMergeEnv PolyEncoderMergePostEnv
   WppBudgetPanic bytesMerge3RawBudgetSpec polyDecoderMergePostEnv_imp_pre polyDecoderMergeSpec
   polyDecoderMergeSpecOfEnv polyEncoderMergePostEnv_imp_pre polyEncoderMergeSpec
   polyEncoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlacedBudget
  (polyDecoderMerge_cro_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderTightPlacedBudgetAux
  (e2p_polyDecoderMerge_dom_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
  (polyEncoderMerge_cro_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Valid Doubling Capacities & Zero-Cap `ProtoPolynomial{Decoder,Encoder}` Predicates -/

/-- Valid `Vec<Vec<u8>>` capacities along Rust `RawVec::grow_one` doubling from `0`:
`0 → 4 → 8 → 16` (or `≥ 16`, where no further grow occurs on `≤ 16` elements). -/
def e2p_ValidPolyVecCap (cap : Nat) : Prop :=
  cap = 0 ∨ cap = 4 ∨ cap = 8 ∨ 16 ≤ cap

/-- Remaining `grow_one` operations needed on `≤ 16` total pushes starting from `cap`. -/
def e2p_polyGrowRemOps (cap : Nat) : Nat :=
  if 16 ≤ cap then 0
  else if 8 ≤ cap then 1
  else if 4 ≤ cap then 2
  else 3

theorem e2p_polyGrowRemOps_zero : e2p_polyGrowRemOps 0 = 3 := rfl

theorem e2p_validPolyVecCap_zero : e2p_ValidPolyVecCap 0 := Or.inl rfl

theorem e2p_validPolyVecCap_step {cap : Nat} (hv : e2p_ValidPolyVecCap cap) (hlt : cap < 16) :
    e2p_ValidPolyVecCap (max (2 * cap) 4) ∧
      max (2 * cap) 4 * 24 ≤ 384 ∧
      e2p_polyGrowRemOps (max (2 * cap) 4) + 1 ≤ e2p_polyGrowRemOps cap := by
  rcases hv with rfl | rfl | rfl | hge
  · refine ⟨Or.inr (Or.inl rfl), by decide, by decide⟩
  · refine ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, by decide⟩
  · refine ⟨Or.inr (Or.inr (Or.inr (by decide))), by decide, by decide⟩
  · omega

/-- Domain-guarded `ProtoPolynomialDecoder`: requires `g.pts.cap = 0#64` when `Dom x` holds,
and matches unpinned `protoPolynomialDecoderAt` on `¬ Dom x`. -/
def e2p_protoPolynomialDecoderDomAt (Dom : PolyDecoderMergeGhost → Prop) (A : RustAlloc)
    (x : PolyDecoderMergeGhost) : SepProp :=
  ∃∗ g : ProtoPolynomialDecoderGhost,
    ⌜Dom x → g.pts.cap = 0#64⌝ ∗
      protoPolynomialDecoderPinnedAt A g x.msgPtr (polyDecoderToProto x.msg)

/-- Domain-guarded `ProtoPolynomialEncoder`: requires `g.pts.cap = 0#64 ∧ g.polys.cap = 0#64`
when `Dom x` holds, and matches unpinned `protoPolynomialEncoderAt` on `¬ Dom x`. -/
def e2p_protoPolynomialEncoderDomAt (Dom : PolyEncoderMergeGhost → Prop) (A : RustAlloc)
    (x : PolyEncoderMergeGhost) : SepProp :=
  ∃∗ g : ProtoPolynomialEncoderGhost,
    ⌜Dom x → g.pts.cap = 0#64 ∧ g.polys.cap = 0#64⌝ ∗
      protoPolynomialEncoderPinnedAt A g x.msgPtr (polyEncoderToProto x.msg)

theorem e2p_satisfies_decoderAt_of_domAt {Dom : PolyDecoderMergeGhost → Prop}
    {A : RustAlloc} {x : PolyDecoderMergeGhost} {R : SepProp} {mem : Memory}
    (hm : mem ⊨ e2p_protoPolynomialDecoderDomAt Dom A x ∗ R) :
    mem ⊨ protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto x.msg) ∗ R := by
  rw [e2p_protoPolynomialDecoderDomAt, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨g, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rw [protoPolynomialDecoderAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨g, hm.2⟩

theorem e2p_satisfies_encoderAt_of_domAt {Dom : PolyEncoderMergeGhost → Prop}
    {A : RustAlloc} {x : PolyEncoderMergeGhost} {R : SepProp} {mem : Memory}
    (hm : mem ⊨ e2p_protoPolynomialEncoderDomAt Dom A x ∗ R) :
    mem ⊨ protoPolynomialEncoderAt A x.msgPtr (polyEncoderToProto x.msg) ∗ R := by
  rw [e2p_protoPolynomialEncoderDomAt, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨g, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rw [protoPolynomialEncoderAt_eq_exists_pinned, sepExists_sepConj_left, satisfies_sepExists]
  exact ⟨g, hm.2⟩

/-! ## 2. Guarded Zero-Cap Specifications (`Dom` → `ZeroCap`, `¬ Dom` → Unpinned `At`) -/

/-- `Dom`-zero-cap guarded specification of `PolynomialDecoder::merge` (`Block 296`). -/
def e2p_polyDecoderMergeZeroCapSpecOfEnv {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : PolyDecoderMergeGhost → List AllocEvent → Prop) :
    Spec (PolyDecoderMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.msg.pts.length + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      e2p_protoPolynomialDecoderDomAt tlb_PolyDecoderDom A.repAlloc x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp polyMergeStack
  post := (polyDecoderMergeSpecOfEnv A lim PreEnv PostEnv).post

/-- `Dom`-zero-cap guarded specification of `PolynomialEncoder::merge` (`Block 297`). -/
def e2p_polyEncoderMergeZeroCapSpecOfEnv {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop) :
    Spec (PolyEncoderMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.msg.pts.length + x.bs.length < 2 ^ 56 ∧
      x.msg.polys.length + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      e2p_protoPolynomialEncoderDomAt tlb_PolyEncoderDom A.repAlloc x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp polyMergeStack
  post := (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv).post

/-! ## 3. Canonical `encodeRaw` Round-Trip & Wire-Size Bounds -/

private theorem e2p_encodeVarint_len_le_11 (v : BitVec 64) : (encodeVarint v).length ≤ 11 := by
  unfold encodeVarint
  suffices ∀ k (w : BitVec 64), (encodeVarintAux k w).length ≤ k + 1 from this 10 v
  intro k
  induction k with
  | zero => intro _; simp [encodeVarintAux]
  | succ k ih =>
    intro w
    simp only [encodeVarintAux]
    split
    · simp
    · simp only [List.length_cons]
      have := ih (w >>> 7)
      omega

private theorem e2p_encodeRepeatedBytes_len_bound (tag : BitVec 32) (vs : List Bytes)
    (hmax : ∀ s ∈ vs, s.length ≤ 2560) :
    (encodeRepeatedBytes tag vs).length ≤ vs.length * 2582 := by
  induction vs with
  | nil => simp [encodeRepeatedBytes]
  | cons v vs ih =>
    have hv : v.length ≤ 2560 := hmax v List.mem_cons_self
    have hih := ih (fun s hs => hmax s (List.mem_cons_of_mem _ hs))
    have hcons : encodeRepeatedBytes tag (v :: vs) =
        encodeBytesUncond tag v ++ encodeRepeatedBytes tag vs := rfl
    rw [hcons, List.length_append, List.length_cons]
    have hk : (encodeKey tag .lengthDelimited).length ≤ 11 :=
      e2p_encodeVarint_len_le_11 _
    have hl : (encodeVarint (BitVec.ofNat 64 v.length)).length ≤ 11 :=
      e2p_encodeVarint_len_le_11 _
    simp only [encodeBytesUncond, List.length_append]
    omega

theorem e2p_polyDecoder_encodeRaw_len_lt {pb : PolynomialDecoder}
    (hpb : tlb_ValidPolyDecoderPB pb) :
    (PolynomialDecoder.encodeRaw pb).length < 2 ^ 63 := by
  rcases hpb with ⟨hlen, hmax⟩
  unfold PolynomialDecoder.encodeRaw
  simp only [List.length_append]
  have h1 : (encodeUint32Field 1#32 pb.ptsNeeded).length ≤ 22 := by
    unfold encodeUint32Field
    split
    · simp
    · simp only [List.length_append]
      have hk : (encodeKey 1#32 .varint).length ≤ 11 := e2p_encodeVarint_len_le_11 _
      have hv : (encodeVarint (pb.ptsNeeded.zeroExtend 64)).length ≤ 11 :=
        e2p_encodeVarint_len_le_11 _
      omega
  have h2 : (encodeUint32Field 2#32 pb.polys).length ≤ 22 := by
    unfold encodeUint32Field
    split
    · simp
    · simp only [List.length_append]
      have hk : (encodeKey 2#32 .varint).length ≤ 11 := e2p_encodeVarint_len_le_11 _
      have hv : (encodeVarint (pb.polys.zeroExtend 64)).length ≤ 11 :=
        e2p_encodeVarint_len_le_11 _
      omega
  have h3 := e2p_encodeRepeatedBytes_len_bound 3#32 pb.pts hmax
  have h4 : (encodeBoolField 4#32 pb.isComplete).length ≤ 12 := by
    unfold encodeBoolField
    split
    · simp only [List.length_append, List.length_singleton]
      have hk : (encodeKey 4#32 .varint).length ≤ 11 := e2p_encodeVarint_len_le_11 _
      omega
    · simp
  omega

/-- Canonical `encodeRaw` round-trip for `PolynomialDecoder::merge`: under `tlb_ValidPolyDecoderPB pb`,
`mergeMessage PolynomialDecoder.mergeField .lengthDelimited default (tlb_lenPrefixed (encodeRaw pb) rest) 98`
succeeds with `.ok (pb, rest)`. -/
theorem e2p_mergeMessage_polyDecoder_of_valid {pb : PolynomialDecoder} (rest : Bytes)
    (hpb : tlb_ValidPolyDecoderPB pb) :
    mergeMessage PolynomialDecoder.mergeField .lengthDelimited default
        (tlb_lenPrefixed (PolynomialDecoder.encodeRaw pb) rest) 98 =
      .ok (pb, rest) := by
  have hlt63 := e2p_polyDecoder_encodeRaw_len_lt hpb
  have hlt64 : (PolynomialDecoder.encodeRaw pb).length < 2 ^ 64 := by omega
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  exact mergeMessage_encode PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw default pb
    98 rest (loopsTo_polyDecoder pb hlt64) hlt64 (by decide)

theorem e2p_polyEncoder_encodeRaw_len_lt {pb : PolynomialEncoder}
    (hpb : tlb_ValidPolyEncoderPB pb) :
    (PolynomialEncoder.encodeRaw pb).length < 2 ^ 63 := by
  rcases hpb with ⟨_, hlen, hpts, hpolys⟩
  unfold PolynomialEncoder.encodeRaw
  simp only [List.length_append]
  have h1 : (encodeUint32Field 1#32 pb.idx).length ≤ 22 := by
    unfold encodeUint32Field
    split
    · simp
    · simp only [List.length_append]
      have hk : (encodeKey 1#32 .varint).length ≤ 11 := e2p_encodeVarint_len_le_11 _
      have hv : (encodeVarint (pb.idx.zeroExtend 64)).length ≤ 11 := e2p_encodeVarint_len_le_11 _
      omega
  have h2 := e2p_encodeRepeatedBytes_len_bound 2#32 pb.pts hpts
  have h3 := e2p_encodeRepeatedBytes_len_bound 3#32 pb.polys hpolys
  omega

/-- Canonical `encodeRaw` round-trip for `PolynomialEncoder::merge`. -/
theorem e2p_mergeMessage_polyEncoder_of_valid {pb : PolynomialEncoder} (rest : Bytes)
    (hpb : tlb_ValidPolyEncoderPB pb) :
    mergeMessage PolynomialEncoder.mergeField .lengthDelimited default
        (tlb_lenPrefixed (PolynomialEncoder.encodeRaw pb) rest) 98 =
      .ok (pb, rest) := by
  have hlt63 := e2p_polyEncoder_encodeRaw_len_lt hpb
  have hlt64 : (PolynomialEncoder.encodeRaw pb).length < 2 ^ 64 := by omega
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  exact mergeMessage_encode PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw default pb
    98 rest (loopsTo_polyEncoder pb hlt64) hlt64 (by decide)

/-! ## 4. Block-Program Rebase Helper & Tight Contracts (`Blocks 296 & 297`) -/

private theorem e2p_rebase_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (libsignalSessionLib.blockPlacement lsmpl j).base spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec := by
  have h' : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H)
      (libsignalSessionLib.blockPlacement lsmpl j).base spec :=
    hcallee.eq_blockProgram ▸ h
  rwa [ls_blockPlacement_base (i := j)] at h'

private theorem e2p_domAt_entails_tlb_domHeap_decoder (A : RustAlloc) (x : PolyDecoderMergeGhost) :
    e2p_protoPolynomialDecoderDomAt tlb_PolyDecoderDom A x ⊢
      tlb_domHeap tlb_PolyDecoderDom
        (fun x => tlb_polyDecoderZeroCapAt A x.msgPtr (polyDecoderToProto x.msg))
        (fun x => protoPolynomialDecoderAt A x.msgPtr (polyDecoderToProto x.msg)) x := by
  classical
  unfold e2p_protoPolynomialDecoderDomAt
  refine Entails.sepExists_elim fun g => Entails.pure_left fun hcap => ?_
  by_cases hDom : tlb_PolyDecoderDom x
  · rw [tlb_domHeap_of_dom hDom]
    rcases g with ⟨⟨cap, ptr⟩⟩
    have hc0 : cap = 0#64 := hcap hDom
    subst hc0
    exact tlb_polyDecoderZeroCapAt_of_ptr A ptr x.msgPtr (polyDecoderToProto x.msg)
  · rw [tlb_domHeap_of_not_dom hDom, protoPolynomialDecoderAt_eq_exists_pinned]
    exact Entails.sepExists_right g (Entails.refl _)

private noncomputable def e2p_polyDecoderDomOnlySpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) : Spec (PolyDecoderMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜tlb_PolyDecoderDom x⌝ ∗
      (tlb_polyDecoderMergeTightSpecOfEnv A lim
        (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps)).pre (x, st) s
  post := (tlb_polyDecoderMergeTightSpecOfEnv A lim
    (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps)).post

private theorem e2p_polyDecoderDomOnly_cro_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {maxOps : Nat}
    (hOps : 35 ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (blkPl_296).base
      (withLsCodeRoLoaded lsmpl (e2p_polyDecoderDomOnlySpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2p_polyDecoderDomOnlySpec
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply SepWPp.elim_lscroProp; intro hinv0
  change SepWPp _ _ _ _
    (WppPost (polyDecoderMergeSpecOfEnv A lim
      (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps)) (x, st0) R s0)
    (WppBudgetPanic (polyDecoderMergeSpecOfEnv A lim
      (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps)) (x, st0) R s0)
  unfold tlb_polyDecoderMergeTightSpecOfEnv
  dsimp only
  apply SepWPp.pure_elim; intro hDom
  apply SepWPp.pure_elim; rintro ⟨h_1, h_2, h_3, h_bound, hFit0⟩
  rcases hDom with ⟨hwt_p, hmsg0, pb, rest_fin, hpb, hbs_eq⟩
  have hwt_ld : x.wt = .lengthDelimited := by
    cases hx : x.wt <;> simp [hx, codecWireTypeToProto] at hwt_p
    rfl
  have hDom' : tlb_PolyDecoderDom x := ⟨hwt_p, hmsg0, pb, rest_fin, hpb, hbs_eq⟩
  have hsome_top :
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        some (pb, rest_fin) := by
    rw [hwt_p, hmsg0, hbs_eq, e2p_mergeMessage_polyDecoder_of_valid rest_fin hpb]
    rfl
  have hFit_tight : FitsEnv M lim st0 (SpqrTightEvs maxOps 342615 2560) :=
    FitsEnv.mono (fun _ ht => Or.inl ⟨hDom', ht⟩) hFit0
  rw [tlb_domHeap_of_dom hDom']
  unfold tlb_polyDecoderZeroCapAt
  conv => arg 4; simp only [sepExists_sepConj_left]
  apply SepWPp.exists_elim; intro ptr0
  exact e2p_polyDecoderMerge_dom_sepWPp hOps hVarintCall hSkipCall hBytesCall hGrowCall
    hDom' hwt_ld hmsg0 hpb hsome_top hpc hrun hsp_align' h_1 h_2 h_3 h_bound hFit_tight hinv0

/-- Guarded-tight contract for Block `296` (`PolynomialDecoder::merge`) on
`tlb_polyDecoderMergeTightSpecOfEnv` (`35 ≤ maxOps`). -/
theorem e2p_tlb_polyDecoderMerge_cro_placed_tight_ok_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {maxOps : Nat}
    (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (blkPl_296).base
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps))) := by
  classical
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align _hcl
  by_cases hDom : tlb_PolyDecoderDom x
  · refine (e2p_polyDecoderDomOnly_cro_ok hOps hVarintCall hSkipCall hBytesCall hGrowCall).mono_outcome
      (x, st0) R s0 hpc hrun ?_ hsp_align (fun _ hout => hout)
    obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [withLsCodeRoLoaded, e2p_polyDecoderDomOnlySpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hDom, hp⟩
  · have hpre_fb :
        s0.mem ⊨ (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)).pre (x, st0) s0 ∗ R := by
      obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hpre
      unfold tlb_polyDecoderMergeTightSpecOfEnv at hp
      unfold withLsCodeRoLoaded polyDecoderMergeSpec polyDecoderMergeSpecOfEnv
      dsimp only at hp ⊢
      rw [tlb_domHeap_of_not_dom hDom] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcro, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1,
        tlb_fitsEnv_fallback_of_not_dom hDom hp.1.2.2.2.2⟩, hp.2⟩
    refine (polyDecoderMerge_cro_placed_ok_of_contracts
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall).mono_outcome
      (x, st0) R s0 hpc hrun hpre_fb hsp_align fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | hp | hex | hoom
    · refine Or.inl ⟨hret, hcc, ?_⟩
      unfold withLsCodeRoLoaded polyDecoderMergeSpec polyDecoderMergeSpecOfEnv at hq
      unfold withLsCodeRoLoaded tlb_polyDecoderMergeTightSpecOfEnv polyDecoderMergeSpecOfEnv
      dsimp only at hq ⊢
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (Entails.sepExists_mono fun evs =>
          Entails.pure_left fun h1 => Entails.pure_right
            (Or.inr ⟨hDom, polyDecoderMergePostEnv_imp_pre h1⟩) (Entails.refl _)))))) hq
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr hoom))

/-- Guarded-tight contract `tlb_PolyDecoderMergePlacedTightOkOf` (`35 ≤ maxOps`) on
`libsignalSessionLib.blockProgram lsmpl 296`. -/
theorem e2p_tlb_polyDecoderMerge_placed_ok_tight_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    {maxOps : Nat} (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    tlb_PolyDecoderMergePlacedTightOkOf A lim maxOps ext := by
  have hprog :
      ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext)) =
        libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext) :=
    (inferInstance :
      IsLsBlockProg ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext))
        296 (Rust.withPanics ext)).eq_blockProgram
  exact e2p_rebase_to_blockProgram (j := 296)
    (e2p_tlb_polyDecoderMerge_cro_placed_tight_ok_of hOps
      (hprog.symm ▸ hFromCall) (hprog.symm ▸ hPushCall) (hprog.symm ▸ hVarintCall)
      (hprog.symm ▸ hSkipCall) (hprog.symm ▸ hBytesCall) (hprog.symm ▸ hGrowCall))

/-- Default `35`-op guarded-tight contract `tlb_PolyDecoderMergePlacedTightOk` on Block `296`. -/
theorem e2p_tlb_polyDecoderMerge_placed_ok_tight [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    tlb_PolyDecoderMergePlacedTightOk A lim ext :=
  e2p_tlb_polyDecoderMerge_placed_ok_tight_of (Nat.le_refl 35)
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- Guarded-tight contract for Block `296` (`PolynomialDecoder::merge`) on
`e2p_polyDecoderMergeZeroCapSpecOfEnv` at `tlb_PolyDecoderGuardedEnvOf maxOps` (`35 ≤ maxOps`). -/
theorem e2p_polyDecoderMerge_cro_placed_tight_ok_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {maxOps : Nat}
    (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (blkPl_296).base
      (withLsCodeRoLoaded lsmpl
        (e2p_polyDecoderMergeZeroCapSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps))) := by
  refine subroutine_ok_mono
    (e2p_tlb_polyDecoderMerge_cro_placed_tight_ok_of hOps
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall)
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun _ _ _ _ hq => hq)
  obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [withLsCodeRoLoaded, e2p_polyDecoderMergeZeroCapSpecOfEnv,
    tlb_polyDecoderMergeTightSpecOfEnv] at hp ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  refine ⟨hcro, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
    (e2p_domAt_entails_tlb_domHeap_decoder A.repAlloc x)))) hp

/-- Guarded-tight contract for Block `296` (`PolynomialDecoder::merge`) on
`libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext)`. -/
theorem e2p_polyDecoderMerge_blockProgram_tight_ok_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    {maxOps : Nat} (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext))
      (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (e2p_polyDecoderMergeZeroCapSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf maxOps) (tlb_PolyDecoderGuardedEnvOf maxOps))) :=
  e2p_rebase_to_blockProgram (j := 296)
    (e2p_polyDecoderMerge_cro_placed_tight_ok_of hOps
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall)

/-- Guarded-tight contract for Block `297` (`PolynomialEncoder::merge`) on
`e2p_polyEncoderMergeZeroCapSpecOfEnv` (`35 ≤ maxOps`). -/
theorem e2p_polyEncoderMerge_cro_placed_tight_ok_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {maxOps : Nat}
    (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (blkPl_297).base
      (withLsCodeRoLoaded lsmpl
        (e2p_polyEncoderMergeZeroCapSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf maxOps) (tlb_PolyEncoderGuardedEnvOf maxOps))) :=
  E2aTightP297PlacedBudget.e2p297_polyEncoderMerge_cro_placed_tight_ok_of hOps
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- Guarded-tight contract `tlb_PolyEncoderMergePlacedTightOkOf` (`35 ≤ maxOps`) on
`libsignalSessionLib.blockProgram lsmpl 297`. -/
theorem e2p_tlb_polyEncoderMerge_placed_ok_tight_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    {maxOps : Nat} (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    tlb_PolyEncoderMergePlacedTightOkOf A lim maxOps ext :=
  E2aTightP297PlacedBudget.e2p297_tlb_polyEncoderMerge_placed_ok_tight_of hOps
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- Default `35`-op guarded-tight contract `tlb_PolyEncoderMergePlacedTightOk` on Block `297`. -/
theorem e2p_tlb_polyEncoderMerge_placed_ok_tight [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    tlb_PolyEncoderMergePlacedTightOk A lim ext :=
  E2aTightP297PlacedBudget.e2p297_tlb_polyEncoderMerge_placed_ok_tight
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall

/-- Guarded-tight contract for Block `297` (`PolynomialEncoder::merge`) on
`libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext)`. -/
theorem e2p_polyEncoderMerge_blockProgram_tight_ok_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    {maxOps : Nat} (hOps : 35 ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (lsmpl.base 621) (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (e2p_polyEncoderMergeZeroCapSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf maxOps) (tlb_PolyEncoderGuardedEnvOf maxOps))) :=
  e2p_rebase_to_blockProgram (j := 297)
    (e2p_polyEncoderMerge_cro_placed_tight_ok_of hOps
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyMergeTightPlacedBudget
