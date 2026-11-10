/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceivedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Canonical Inner `Unchunked.NoHeaderReceived` Tight Budget Step for Block `308`

Provides `SpqrTightEvs` pool predicates, zero-capacity default initialization folds, `FitsEnv`
transfer lemmas, and the canonical Tag `1` (`uc : Option V1State.Unchunked.NoHeaderReceived`) step
for `Chunked.NoHeaderReceived::merge` on Block `308`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC308UcAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap
  (RustAlloc vecAt vecBuf vecHeader vecU8At vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix key_shr32_of_lt key_wt_some
   sf_truncate32_ofNat64 sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join
   sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.LibsignalSpqrV1
  (Bytes PolynomialDecoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (noneCap2 optPolynomialDecoderPBAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Auth
  (WppPost authenticatorPBCapAt memRegion_40_cells optAuthenticatorPBCapAt
   optAuthenticatorPBCapAt_mono setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Poly (protoPolynomialDecoderPinnedAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedInl10CalleeSaved ChunkedNoHeaderReceivedMergeGhost SepWPpLscro
   blkPC_308 blkPl_308 bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedInlBelowStack chunkedInlBelow_authMerge chunkedInlBelow_authMerge_entails
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails
   chunkedInlSavedRegs10 chunkedNoHeaderReceivedMerge_fnOff
   chunkedNoHeaderReceivedPBCapAt cmp_len_limit_of_eq cmp_len_limit_of_gt
   codecWireTypeToProto default_unchunked2_entails_cap
   memRegion_48_split_40_8 optNoHeaderReceivedPBCapAt pointsTo64_zero_split_32_inl
   polyDecoderToProto unchunked2CapAt unchunked2CapAt_mono)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_authenticator mergeMessage_encode proto_decodeVarint_encodeVarint)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved fitsEvents_append)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthDom tlb_AuthGuardedEnvOf tlb_ChunkedNoHeaderReceivedDom
   tlb_ChunkedNoHeaderReceivedGuardedEnvOf tlb_PolyDecoderDom tlb_PolyDecoderGuardedEnvOf
   tlb_ValidAuthPB tlb_ValidUcNoHeaderReceivedPB tlb_authMergeTightSpecOfEnv
   tlb_authenticatorZeroCapAt tlb_domHeap_of_dom tlb_fitsEnv_guarded_of_dom
   tlb_guardedEnv_tight_of_dom tlb_lenPrefixed tlb_polyDecoderZeroCapAt
   tlb_polyDecoderZeroCapAt_of_ptr tlb_vecU8ZeroCapAt tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergePostEnv authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedNoHeaderReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some sepWPpLscro_of_vm)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedNoHeaderReceivedMerge_fnOff

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

/-! ## 1. Canonical Domain Spec & Tight Pool Loop Bundles -/

/-- Canonical-domain restriction of `chunkedNoHeaderReceivedMergeSpecOfEnv` at `maxOps`:
identical `.post`, with `⌜tlb_ChunkedNoHeaderReceivedDom x⌝` conjoined in `.pre`. -/
noncomputable def e2kc_chunkedNoHeaderReceivedDomSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat) :
    Spec (ChunkedNoHeaderReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜tlb_ChunkedNoHeaderReceivedDom x⌝ ∗
      (chunkedNoHeaderReceivedMergeSpecOfEnv A lim
        (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps)
        (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps)).pre (x, st) s
  post := (chunkedNoHeaderReceivedMergeSpecOfEnv A lim
    (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps)
    (tlb_ChunkedNoHeaderReceivedGuardedEnvOf maxOps)).post

/-- Tight event-pool invariant carrying `SpqrTightEvs ops cum req evs`. -/
def e2kc_tightPoolAt {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (ops cum req : Nat) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜SpqrTightEvs ops cum req evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

theorem e2kc_tightPoolAt_of_vmPreserved {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {ops cum req : Nat} {s1 s2 : State}
    (hvm : VmPreserved s1 s2) :
    e2kc_tightPoolAt A lim st ops cum req s1 = e2kc_tightPoolAt A lim st ops cum req s2 := by
  unfold e2kc_tightPoolAt
  congr 1; funext evs
  rw [A.pool_of_vmPreserved hvm]

theorem e2kc_pool_entails_tightPoolAt_init {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ e2kc_tightPoolAt A lim st 0 0 0 s :=
  Entails.sepExists_right [] (Entails.pure_right (SpqrTightEvs.nil 0 0 0) (Entails.refl _))

theorem e2kc_tightPoolAt_mono {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {o1 o2 c1 c2 r1 r2 : Nat} {s : State}
    (ho : o1 ≤ o2) (hc : c1 ≤ c2) (hr : r1 ≤ r2) :
    e2kc_tightPoolAt A lim st o1 c1 r1 s ⊢ e2kc_tightPoolAt A lim st o2 c2 r2 s := by
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  exact sepConj_mono_left (Entails.pure_mono fun h => h.mono ho hc hr)

theorem e2kc_pool_entails_tightPoolAt_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {ops cum req : Nat}
    {evs evs_dv : List AllocEvent}
    (hevs : SpqrTightEvs ops cum req evs) (hnil : evs_dv = []) :
    A.pool lim (M.stepEvents evs_dv (M.stepEvents evs st)) s ⊢
      e2kc_tightPoolAt A lim st ops cum req s := by
  subst hnil
  unfold e2kc_tightPoolAt
  simpa only [AllocCostModel.stepEvents, List.foldl_nil] using
    (Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _)))

theorem e2kc_pool_entails_tightPoolAt_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    {o1 c1 r1 o2 c2 r2 o3 c3 r3 : Nat} {evs1 evs2 : List AllocEvent}
    (ho : o1 + o2 ≤ o3) (hc : c1 + c2 ≤ c3) (hr : max r1 r2 ≤ r3)
    (h1 : SpqrTightEvs o1 c1 r1 evs1) (h2 : SpqrTightEvs o2 c2 r2 evs2) :
    A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s ⊢
      e2kc_tightPoolAt A lim st o3 c3 r3 s := by
  have hstep : M.stepEvents evs2 (M.stepEvents evs1 st) = M.stepEvents (evs1 ++ evs2) st := by
    simp only [AllocCostModel.stepEvents, List.foldl_append]
  rw [hstep]
  exact Entails.sepExists_right (evs1 ++ evs2)
    (Entails.pure_right ((h1.append h2).mono ho hc hr) (Entails.refl _))

/-- Tight outer loop-header bundle at `entry + 168#64`. -/
def e2kc_loopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.NoHeaderReceived) (bs cur : List (BitVec 8))
    (ops cum req : Nat) : SepProp :=
  e2kc_tightPoolAt A lim st ops cum req s ∗
    chunkedNoHeaderReceivedPBCapAt A.repAlloc msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur

/-- Tight inner `uc` loop-header bundle at `entry + 408#64`. -/
def e2kc_ucLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (hdr : Option PolynomialDecoder) (uc : V1State.Unchunked.NoHeaderReceived)
    (bs cur : List (BitVec 8)) (ops cum req : Nat) : SepProp :=
  e2kc_tightPoolAt A lim st ops cum req s ∗
    optPolynomialDecoderPBAt A.repAlloc msgPtr hdr ∗
    unchunked2CapAt A.repAlloc (msgPtr + 0x28#64) cur.length uc.epoch uc.auth ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur

/-! ## 2. `FitsEnv`, Codec Decode, and Zero-Cap Init Fold Helpers -/

theorem e2kc_fitsEnv_step {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {maxOps o1 c1 r1 : Nat} {evs1 : List AllocEvent} {P : List AllocEvent → Prop}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560))
    (_h1 : SpqrTightEvs o1 c1 r1 evs1)
    (himp : ∀ evs2, P evs2 → SpqrTightEvs maxOps 345567 2560 (evs1 ++ evs2)) :
    FitsEnv M lim (M.stepEvents evs1 st) P :=
  fun evs2 hp =>
    ((fitsEvents_append M lim evs1 evs2 st).mp (hFit (evs1 ++ evs2) (himp evs2 hp))).2

theorem e2kc_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {maxOps ops cum req : Nat} {cur : Bytes} {p : BitVec 64 × Bytes} {evs : List AllocEvent}
    (ho : ops ≤ maxOps) (hc : cum ≤ 345567) (hr : req ≤ 2560)
    (hd : decodeVarint cur = some p)
    (hevs : SpqrTightEvs ops cum req evs)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560)) :
    FitsEnv M lim (M.stepEvents evs st) (DecodeVarint2Env cur) :=
  e2kc_fitsEnv_step hFit hevs fun evs2 hdv => by
    rw [decodeVarint2Env_eq_nil_of_some hd hdv, List.append_nil]
    exact hevs.mono ho hc hr

theorem e2kc_fitsEnv_authTight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {authOps maxOps : Nat} {x_auth : CryptoVerification.SpqrV1.Auth.AuthMergeGhost}
    {evs : List AllocEvent}
    (hAuthDom : tlb_AuthDom x_auth)
    (ho : authOps ≤ maxOps)
    (hevs : SpqrTightEvs 0 0 0 evs)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560)) :
    FitsEnv M lim (M.stepEvents evs st) (tlb_AuthGuardedEnvOf authOps x_auth) :=
  tlb_fitsEnv_guarded_of_dom hAuthDom <|
    e2kc_fitsEnv_step hFit hevs fun evs2 h2 =>
      (hevs.append h2).mono (by omega) (by decide) (by decide)

theorem e2kc_fitsEnv_polyTight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {authOps decOps maxOps : Nat}
    {x_poly : CryptoVerification.SpqrV1.Prost.MessageMerge.PolyDecoderMergeGhost}
    {evs : List AllocEvent}
    (hPolyDom : tlb_PolyDecoderDom x_poly)
    (hOps : authOps + decOps ≤ maxOps)
    (hevs : SpqrTightEvs authOps 2952 32 evs)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560)) :
    FitsEnv M lim (M.stepEvents evs st) (tlb_PolyDecoderGuardedEnvOf decOps x_poly) :=
  tlb_fitsEnv_guarded_of_dom hPolyDom <|
    e2kc_fitsEnv_step hFit hevs fun evs2 h2 =>
      (hevs.append h2).mono hOps (by decide) (by decide)

theorem e2kc_decodeVarint_encodeVarint (v : BitVec 64) (rest : Bytes) :
    decodeVarint (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ rest) =
      some (v, rest) := by
  rw [← proto_decodeVarint_toOption, proto_decodeVarint_encodeVarint]
  rfl

theorem e2kc_isDropSuffix_append_left (pre cur : Bytes) :
    IsDropSuffix (pre ++ cur) cur := by
  unfold IsDropSuffix
  rw [List.length_append, Nat.add_sub_cancel, List.drop_left]

theorem e2kc_pointsTo_zero_entails_vecU8ZeroCapAt (A : RustAlloc) (a ptr : BitVec 64)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      tlb_vecU8ZeroCapAt A a [] := by
  refine Entails.trans ?_ (tlb_vecU8ZeroCapAt_of_ptr A a ptr [])
  rw [vecU8At_eq_header_sep_buf, vecHeader]; unfold vecU8Buf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
  have hp : ([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧
      (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 := ⟨by decide, by decide, hptr⟩
  exact Entails.pure_right hp (Entails.refl _)

theorem e2kc_default_cells_entails_authZeroCap (A : RustAlloc) (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ⊢
      tlb_authenticatorZeroCapAt A a (default : ProtoAuthenticator) := by
  unfold tlb_authenticatorZeroCapAt
  have h1 := e2kc_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2kc_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 0x18#64) 1#64 (by decide)
  simp only [arm64_norm] at h2
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 h2)

theorem e2kc_default_cells_entails_polyDecoderZeroCap (A : RustAlloc) (p : BitVec 64) :
    ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7) ⊢
      tlb_polyDecoderZeroCapAt A p (polyDecoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyDecoderZeroCapAt_of_ptr A 8#64 p (polyDecoderToProto default))
  unfold protoPolynomialDecoderPinnedAt polyDecoderToProto
  have hvec : (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ⊢
      CryptoVerification.SpqrV1.Poly.vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] := by
    unfold CryptoVerification.SpqrV1.Poly.vecVecU8PinnedAt vecAt vecHeader vecBuf
    have hc0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [hc0, ↓reduceIte, sepConj_emp]
    refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
    have hp : ([] : List (List (BitVec 8))).length ≤ (0 : BitVec 64).toNat ∧
        (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0 :=
      ⟨by decide, by decide, by decide⟩
    exact Entails.pure_right hp (Entails.refl _)
  have hsplit := pointsTo64_zero_split_32_inl (p + 24#64)
  simp only [arm64_norm] at hsplit
  change _ ⊢ CryptoVerification.SpqrV1.Poly.vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    ((p + 24#64) ↦₃₂ 0#32) ∗ ((p + 28#64) ↦₃₂ 0#32) ∗
    ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7
  refine Entails.trans (Entails.of_eq (show
    ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7) =
    (((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64)) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hvec (sepConj_mono (Entails.of_eq hsplit) (Entails.refl _))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Canonical Inner `uc` Steps (Block `308`, Tag `1`) -/

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_308).base

/-- Canonical inner key decode at `entry + 408#64` when `cur = [keyByte] ++ rest` (`keyByte ∈ {8, 18}`). -/
theorem e2kc_uc_decode_known_key_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps ops cum req : Nat}
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedNoHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {uc : V1State.Unchunked.NoHeaderReceived}
    {cur rest : Bytes} {key : BitVec 64} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560))
    (ho : ops ≤ maxOps) (hc : cum ≤ 345567) (hr : req ≤ 2560)
    (hgt_lim : ¬ cur.length ≤ innerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag : ¬ key.toNat / 8 < 1)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_308).base + 460#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (e2kc_ucLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest ops cum req)
        (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_308).base + 408#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (e2kc_ucLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs cur ops cum req)
      (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hshr := key_shr32_of_lt hk_lt
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt hitag
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2kc_ucLoopPre, e2kc_tightPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 428#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19, stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hcur_lt (e2kc_fitsEnv_decodeVarint2_of_some ho hc hr hd hevs hFit))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 460#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_mono A.repAlloc (x.msgPtr + 0x28#64) uc.epoch uc.auth hrest_le_cur) (by sep_focus)
      apply SepWP.fold
        (e2kc_pool_entails_tightPoolAt_nil A lim st sm hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := e2kc_ucLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest ops cum req)
        (by dsimp only [e2kc_ucLoopPre]; rw [← e2kc_tightPoolAt_of_vmPreserved hvm2]; sep_entail)
      exact hcont _
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hsm1, hand_wt])
        (by simp only [arm64_norm, wp_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm, hx21_m])
        (by simp only [arm64_norm, wp_norm, hx22_m])
        (by simp only [arm64_norm, wp_norm, hx23_m])
        (by simp only [arm64_norm, wp_norm, hx24_m])
        (by simp only [arm64_norm, wp_norm, hx25_m])
        (by simp only [arm64_norm, wp_norm, hx26_m])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

/-- Canonical inner `epoch` (`uint64`, Tag `1`) step at `entry + 408#64`. -/
theorem e2kc_uc_epoch_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedNoHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {epoch : BitVec 64}
    {afterEpoch : Bytes} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch))
    (hafter_gt : ∀ b tl, CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch = b :: tl →
      ¬ (b :: tl ++ afterEpoch).length ≤ innerLimit)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_308).base + 408#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (e2kc_ucLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr hdr
          { epoch := epoch, auth := none } x.bs afterEpoch 0 0 0)
        (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_308).base + 408#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (e2kc_ucLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr hdr
        default x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch) 0 0 0)
      (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  by_cases hep : epoch = 0#64
  · subst hep
    have hdef_eq : ({ epoch := 0#64, auth := none } : V1State.Unchunked.NoHeaderReceived) = default := rfl
    rw [hdef_eq] at hcont
    simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field, beq_self_eq_true,
      ↓reduceIte, List.nil_append] using
      hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  · have hk8 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .varint = [8#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch =
        8#8 :: CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint epoch := by
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field,
        beq_iff_eq, hep, ↓reduceIte, hk8, List.singleton_append]
    have hgt : ¬ (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch).length ≤ innerLimit := by
      rw [henc]; exact hafter_gt 8#8 _ henc
    let rest1 := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint epoch ++ afterEpoch
    have hd_key : decodeVarint (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch) =
        some (8#64, rest1) := by
      rw [henc, List.cons_append]; rfl
    have hcur_lt : (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch).length < 2 ^ 63 :=
      Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2kc_uc_decode_known_key_placed (iwt := .varint) hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest1_le_cur : rest1.length ≤ (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch).length :=
      Nat.le_of_lt (decodeVarint_length hd_key)
    have hrest1_le : rest1.length ≤ x.bs.length := Nat.le_trans hrest1_le_cur hcur_le
    have hrest1_lt : rest1.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest1_le hbs_lt
    have hrest1_suf : IsDropSuffix x.bs rest1 :=
      suffix_trans hcur_le hcur_suf hrest1_le_cur (decodeVarint_suffix hd_key)
    let rest1Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest1.length)
    have hdv_ep : decodeVarint rest1 = some (epoch, afterEpoch) :=
      e2kc_decodeVarint_encodeVarint epoch afterEpoch
    have hafter_le_rest1 : afterEpoch.length ≤ rest1.length := Nat.le_of_lt (decodeVarint_length hdv_ep)
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [e2kc_ucLoopPre, e2kc_tightPoolAt,
        sliceCursorAfter_eq_split hrest1_le hrest1_suf, chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, rest1Ptr, rest1⟩, M.stepEvents evs st))
        (ret_pc := entry + 532#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
            simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1, hx19_1, stackAt_decodeVarint2_raw_eq]; try rfl)
        (And.intro hrest1_lt (e2kc_fitsEnv_decodeVarint2_of_some (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hdv_ep hevs hFit))
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 408#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv_ep, unchunked2CapAt,
          stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest1_le hrest1_suf hafter_le_rest1) (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x28#64) none hafter_le_rest1) (by sep_focus)
        apply SepWP.fold
          (e2kc_pool_entails_tightPoolAt_nil A lim st sm hevs (decodeVarint2Env_eq_nil_of_some hdv_ep hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := e2kc_ucLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            hdr { epoch := epoch, auth := none } x.bs afterEpoch 0 0 0)
          (by dsimp only [e2kc_ucLoopPre, unchunked2CapAt];
              rw [← e2kc_tightPoolAt_of_vmPreserved hvm2]; simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

/-- Canonical inner `auth` (`Option ProtoAuthenticator`, Tag `2`) step at `entry + 408#64`. -/
theorem e2kc_uc_auth_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {authOps maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTight : subroutine_ok ((blkPC_308).rebase (blkPl_308).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    {x : ChunkedNoHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialDecoder} {ucPb : V1State.Unchunked.NoHeaderReceived}
    {afterUc : Bytes} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560))
    (ho : authOps ≤ maxOps)
    (hValidUc : tlb_ValidUcNoHeaderReceivedPB ucPb)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      ProtoAuthenticator.encodeRaw 2#32 ucPb.auth ++ afterUc).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      ProtoAuthenticator.encodeRaw 2#32 ucPb.auth ++ afterUc))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_308).base + 408#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 afterUc.length →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s'
        (e2kc_ucLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr hdr ucPb x.bs afterUc authOps 2952 32)
        (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_308).base + 408#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 afterUc.length)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_308).rebase (blkPl_308).base H) (s0.readReg64 Reg.lr) s
      (e2kc_ucLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr hdr
        { epoch := ucPb.epoch, auth := none } x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          ProtoAuthenticator.encodeRaw 2#32 ucPb.auth ++ afterUc) 0 0 0)
      (WppPost (e2kc_chunkedNoHeaderReceivedDomSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  rcases ucPb with ⟨ep, _ | authPb⟩
  · simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append] using
      SepWPpLscro.weaken_pre
        (by dsimp only [e2kc_ucLoopPre]; exact sepConj_mono_left (e2kc_tightPoolAt_mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)))
        (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs)
  · have hValidAuth : tlb_ValidAuthPB authPb := hValidUc authPb rfl
    let authPayload := tlb_lenPrefixed (ProtoAuthenticator.encodeRaw authPb) afterUc
    have hk18 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [18#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        ProtoAuthenticator.encodeRaw 2#32 (some authPb) ++ afterUc = [18#8] ++ authPayload := by
      dsimp only [authPayload, tlb_lenPrefixed]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk18, List.append_assoc]
    dsimp only at hcur_le hcur_suf ⊢
    rw [henc] at hcur_le hcur_suf ⊢
    have hgt : ¬ ([18#8] ++ authPayload).length ≤ afterUc.length := by
      simp only [List.singleton_append, List.length_cons, authPayload, tlb_lenPrefixed, List.length_append]; omega
    have hd_key : decodeVarint ([18#8] ++ authPayload) = some (18#64, authPayload) := rfl
    have hcur_lt : ([18#8] ++ authPayload).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2kc_uc_decode_known_key_placed (iwt := .lengthDelimited) hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hpay_le_cur : authPayload.length ≤ ([18#8] ++ authPayload).length := by simp
    have hpay_le : authPayload.length ≤ x.bs.length := Nat.le_trans hpay_le_cur hcur_le
    have hpay_lt : authPayload.length < 2 ^ 63 := Nat.lt_of_le_of_lt hpay_le hbs_lt
    have hpay_suf : IsDropSuffix x.bs authPayload :=
      suffix_trans hcur_le hcur_suf hpay_le_cur (decodeVarint_suffix hd_key)
    let payPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - authPayload.length)
    let x_auth : CryptoVerification.SpqrV1.Auth.AuthMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr + 0x28#64, default, x.bufRef, x.slot, payPtr, authPayload⟩
    have hAuthDom : tlb_AuthDom x_auth := ⟨rfl, rfl, authPb, afterUc, hValidAuth, rfl⟩
    have hlenAuth : (ProtoAuthenticator.encodeRaw authPb).length < 2 ^ 64 := by
      have : (ProtoAuthenticator.encodeRaw authPb).length ≤ authPayload.length := by
        simp [authPayload, tlb_lenPrefixed]; omega
      omega
    have hmergeAuth : (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto .lengthDelimited) default authPayload 97).toOption =
        some (authPb, afterUc) := by
      have hm := mergeMessage_encode ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw
        default authPb 97 afterUc (loopsTo_authenticator authPb hlenAuth) hlenAuth (by decide)
      simpa only [codecWireTypeToProto, authPayload, tlb_lenPrefixed, List.append_assoc, Except.toOption] using
        congrArg Except.toOption hm
    have hafter_le_pay : afterUc.length ≤ authPayload.length := by
      simp [authPayload, tlb_lenPrefixed]; omega
    apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
    by_vm_steps
      (conv => arg 4; rw [e2kc_ucLoopPre, e2kc_tightPoolAt, unchunked2CapAt,
        optAuthenticatorPBCapAt, memRegion_40_cells (x.msgPtr + 0x28#64),
        sliceCursorAfter_eq_split hpay_le hpay_suf, chunkedInlBelow_authMerge s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
      apply SepWP.exists_elim; intro w1
      apply SepWP.exists_elim; intro w2
      apply SepWP.exists_elim; intro w3
      apply SepWP.exists_elim; intro w4
      apply SepWP.exists_elim; intro w5
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      have hdef := e2kc_default_cells_entails_authZeroCap A.repAlloc (x.msgPtr + 0x28#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_auth, M.stepEvents evs st))
        (ret_pc := entry + 512#64) hAuthTight
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by dsimp only [tlb_authMergeTightSpecOfEnv, x_auth];
            rw [tlb_domHeap_of_dom hAuthDom];
            simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt]; try rfl)
        (And.intro hpay_lt (e2kc_fitsEnv_authTight hAuthDom ho hevs hFit))
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 408#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_authMergeTightSpecOfEnv, authMergeSpecOfEnv,
          AuthMergePostEnv, x_auth, hmergeAuth,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_auth
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_auth⟩, hsm0⟩
        apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hpay_le hpay_suf hafter_le_pay) (by sep_focus)
        apply SepWP.fold
          (e2kc_pool_entails_tightPoolAt_append A lim st sm
            (o3 := authOps) (c3 := 2952) (r3 := 32)
            (by omega) (by decide) (by decide) hevs
            (tlb_guardedEnv_tight_of_dom hAuthDom hevs_auth))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := e2kc_ucLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr hdr
            { epoch := ep, auth := some authPb } x.bs afterUc authOps 2952 32)
          (by dsimp only [e2kc_ucLoopPre, unchunked2CapAt, optAuthenticatorPBCapAt];
              rw [← e2kc_tightPoolAt_of_vmPreserved hvm2];
              simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeTightPlacedBudgetC308UcAux
