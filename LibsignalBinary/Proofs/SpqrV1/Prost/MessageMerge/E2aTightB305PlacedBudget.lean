/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Guarded-Tight Placed Budget Proof for `Chunked.KeysUnsampled::merge` (Block `305`)

**Checked by Lean.**

Proves `tlb_ChunkedKeysUnsampledMergePlacedTightOkOf` on Block `305` within
`SpqrTightEvs maxOps 2952 32` (`authOps ≤ maxOps`, default `4`: inlined `Unchunked.KeysUnsampled`
with `epoch : BitVec 64` at `0` B and `auth : Option ProtoAuthenticator` at `2,952` B) on canonical
`tlb_ChunkedKeysUnsampledDom` inputs, falling back to `ChunkedKeysUnsampledMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB305PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns
   libsignalSessionLib ls_blockPlacement_base ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack keys_ls_subroutine_ok_of_block_cro
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix key_shr32_of_lt key_wt_some
   pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join
   sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (Bytes ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost WppPost authenticatorPBCapAt memRegion_40_cells optAuthenticatorPBCapAt
   optAuthenticatorPBCapAt_mono setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.ProtoRepr (noneCap2)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedKeysUnsampledMergeGhost PolyCalleeSaved SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedInlBelowStack chunkedInlBelow_authMerge chunkedInlBelow_authMerge_entails
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails chunkedInlStack
   chunkedKeysUnsampledMerge_fnOff chunkedKeysUnsampledPBCapAt chunkedKeysUnsampledPBCapAt_mono
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto default_unchunked2_entails_cap
   memRegion_48_split_40_8 optKeysUnsampledPBCapAt polySavedRegs polySavedRegsAny
   polySavedRegs_entails_any proto_mergeMessage_suffix stackAt_chunkedInl9_epilogue
   stackAt_chunkedInl_prologue subroutine_ok_withLsCodeRoLoaded_of_withLscroProp unchunked2CapAt
   unchunked2CapAt_mono withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_305 blkPl_305)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_ch_keysUnsampled mergeMessage_encode proto_encodeVarint_length)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved fitsEvents_append)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthDom tlb_AuthGuardedEnvOf tlb_AuthMergePlacedTightOk tlb_AuthMergePlacedTightOkOf
   tlb_ChunkedKeysUnsampledDom tlb_ChunkedKeysUnsampledGuardedEnvOf
   tlb_ChunkedKeysUnsampledMergePlacedTightOk tlb_ChunkedKeysUnsampledMergePlacedTightOkOf
   tlb_ChunkedKeysUnsampledTightEnvOf tlb_ValidAuthPB tlb_ValidChunkedKeysUnsampledPB
   tlb_ValidUcKeysUnsampledPB tlb_authMergeTightSpecOfEnv tlb_authenticatorZeroCapAt
   tlb_domHeap_of_dom tlb_fitsEnv_fallback_of_not_dom tlb_fitsEnv_guarded_of_dom
   tlb_guardedEnv_tight_of_dom tlb_lenPrefixed tlb_vecU8ZeroCapAt)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergePostEnv authMergeSpec authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedKeysUnsampledMergeEnv ChunkedKeysUnsampledMergePostEnv chunkedKeysUnsampledMergeSpec
   chunkedKeysUnsampledMergeSpecOfEnv chunkedKeysUnsampledMergePostEnv_imp_pre)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledClPlacedBudget
  (chunked_keys_unsampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some sepWPpLscro_of_ret_vm
   sepWPpLscro_of_vm sepWPpLscro_pure_elim vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common
  (b304_fitsEnv_decodeVarint2_of_some codec_decodeVarint_encodeVarint
   codec_decodeVarint_tlb_lenPrefixed encodeOptMessage_tag1_some encodeOptMessage_tag2_some
   encodeUint64Field_tag1_of_ne isDropSuffix_refl proto_mergeMessage_authenticator_canonical
   validAuthPB_encodeRaw_len_le)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Own-Block ↔ `blkPC_305` Callee Transfer & Fallback Contract -/

private theorem e2b305_lift_cl_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (@ls_subroutine_ok_of_block _ _ callerProg
      (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ (lsmpl.base j) spec
      hcallee _ _ _ _ hi hj hj_unmut)

private theorem e2b305_lift_cro_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ (lsmpl.base j) spec
    hcallee _ _ _ _ hi hj hj_unmut

private theorem e2b305_own_of_blk_cro [LibsignalPlacement] {α : Type}
    {ext : String → Option (State → State)} {spec : Spec α}
    (h : subroutine_ok ((blkPC_305).rebase (blkPl_305).base (Rust.withPanics ext))
      (blkPl_305).base (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl spec) := by
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_305).rebase (blkPl_305).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 305)] at h
  exact h

/-- Own-block Kleene fallback contract for `Block 305` (`Chunked.KeysUnsampled::merge`) derived from
the five own-block callee contracts (`261`, `257`, `291`, `263`, `295`). -/
theorem e2b305_chunkedKeysUnsampled_merge_placed_fallback_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)) := by
  have hok := chunked_keys_unsampled_merge_cl_placed_ok_of_contracts
    (e2b305_lift_cl_of_own
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_261).rebase (CryptoVerification.blkPl_261).base (fun _ => none)))
      hFrom)
    (e2b305_lift_cl_of_own
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase (CryptoVerification.RecordCodecs.Placed.blkPl_257).base (fun _ => none)))
      hPush)
    (e2b305_lift_cl_of_own
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_291).rebase (CryptoVerification.blkPl_291).base (fun _ => none)))
      hVarint)
    (e2b305_lift_cl_of_own
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_263).rebase (CryptoVerification.blkPl_263).base (fun _ => none)))
      hSkip)
    (e2b305_lift_cro_of_own
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase (CryptoVerification.blkPl_295).base (fun _ => none)))
      hAuthBase)
  exact e2b305_own_of_blk_cro hok

/-! ## 2. Pure Wire Bounds, Round-Trips, Zero-Cap Fold, & Tight Pool Combinators -/

private theorem e2b305_wt_eq_lengthDelimited {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) :
    wt = .lengthDelimited := by
  cases wt <;> simp [codecWireTypeToProto] at h ⊢

private theorem e2b305_encodeKey_length_le (tag : BitVec 32)
    (wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeKey tag wt).length ≤ 10 := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeKey
  exact (proto_encodeVarint_length _).2

private theorem e2b305_encodeUint64Field_length_le (tag : BitVec 32) (v : BitVec 64) :
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field tag v).length ≤ 20 := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := e2b305_encodeKey_length_le tag .varint
    have h2 := (proto_encodeVarint_length v).2
    omega

private theorem e2b305_encodeOptMessage_length_le {N : Type} (encodeRaw : N → Bytes)
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
    have h0 := e2b305_encodeKey_length_le tag .lengthDelimited
    have h1 := (proto_encodeVarint_length (BitVec.ofNat 64 (encodeRaw n).length)).2
    have h2 := hB n rfl
    omega

private theorem e2b305_validUcKeysUnsampledPB_encodeRaw_len_le
    {u : V1State.Unchunked.KeysUnsampled} (hu : tlb_ValidUcKeysUnsampledPB u) :
    (V1State.Unchunked.KeysUnsampled.encodeRaw u).length ≤ 144 := by
  unfold V1State.Unchunked.KeysUnsampled.encodeRaw
  simp only [List.length_append]
  have h1 := e2b305_encodeUint64Field_length_le 1#32 u.epoch
  have h2 := e2b305_encodeOptMessage_length_le ProtoAuthenticator.encodeRaw 2#32 u.auth
    (fun a ha => validAuthPB_encodeRaw_len_le (hu a ha))
  omega

private theorem e2b305_validChunkedKeysUnsampledPB_encodeRaw_len_le
    {pb : V1State.Chunked.KeysUnsampled} (hpb : tlb_ValidChunkedKeysUnsampledPB pb) :
    (V1State.Chunked.KeysUnsampled.encodeRaw pb).length ≤ 164 := by
  unfold V1State.Chunked.KeysUnsampled.encodeRaw
  exact e2b305_encodeOptMessage_length_le V1State.Unchunked.KeysUnsampled.encodeRaw 1#32 pb.uc
    (fun u hu => e2b305_validUcKeysUnsampledPB_encodeRaw_len_le (hpb u hu))

private theorem e2b305_tlb_lenPrefixed_pos (raw rest : Bytes) :
    0 < (tlb_lenPrefixed raw rest).length := by
  unfold tlb_lenPrefixed
  simp only [List.length_append]
  have h1 := (proto_encodeVarint_length (BitVec.ofNat 64 raw.length)).1
  omega

private theorem e2b305_encodeVarint_pos (v : BitVec 64) :
    0 < (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v).length :=
  (proto_encodeVarint_length v).1

private theorem e2b305_proto_mergeMessage_keysUnsampled_canonical
    (pb : V1State.Chunked.KeysUnsampled) (rest : Bytes)
    (hpb : tlb_ValidChunkedKeysUnsampledPB pb) :
    (mergeMessage V1State.Chunked.KeysUnsampled.mergeField .lengthDelimited default
      (tlb_lenPrefixed (V1State.Chunked.KeysUnsampled.encodeRaw pb) rest) 99).toOption =
        some (pb, rest) := by
  have hlen : (V1State.Chunked.KeysUnsampled.encodeRaw pb).length < 2 ^ 64 := by
    have := e2b305_validChunkedKeysUnsampledPB_encodeRaw_len_le hpb
    omega
  unfold tlb_lenPrefixed
  rw [List.append_assoc,
    mergeMessage_encode V1State.Chunked.KeysUnsampled.mergeField 2
      V1State.Chunked.KeysUnsampled.encodeRaw default pb 99 rest
      (loopsTo_ch_keysUnsampled pb hlen) hlen (by decide)]
  rfl

private theorem e2b305_decodeVarint_0x0a (rest : List (BitVec 8)) :
    decodeVarint (0x0a#8 :: rest) = some (0x0a#64, rest) := by
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x0a#64 = [0x0a#8] := by decide
  change decodeVarint ([0x0a#8] ++ rest) = some (0x0a#64, rest)
  rw [← hk]
  exact codec_decodeVarint_encodeVarint 0x0a#64 rest

private theorem e2b305_decodeVarint_0x08 (rest : List (BitVec 8)) :
    decodeVarint (0x08#8 :: rest) = some (0x08#64, rest) := by
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x08#64 = [0x08#8] := by decide
  change decodeVarint ([0x08#8] ++ rest) = some (0x08#64, rest)
  rw [← hk]
  exact codec_decodeVarint_encodeVarint 0x08#64 rest

private theorem e2b305_decodeVarint_0x12 (rest : List (BitVec 8)) :
    decodeVarint (0x12#8 :: rest) = some (0x12#64, rest) := by
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x12#64 = [0x12#8] := by decide
  change decodeVarint ([0x12#8] ++ rest) = some (0x12#64, rest)
  rw [← hk]
  exact codec_decodeVarint_encodeVarint 0x12#64 rest

private theorem e2b305_cells_entails_vecU8ZeroCapAt (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      tlb_vecU8ZeroCapAt A v [] := by
  unfold tlb_vecU8ZeroCapAt vecU8At vecHeader
  refine Entails.sepExists_right 1#64 ?_
  dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  simp (config := { decide := true }) only [↓reduceIte, ne_eq, not_false_eq_true, and_self,
    true_and, and_true, pure_true, sepConj_emp, emp_sepConj]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem e2b305_default_cells_entails_authenticatorZeroCapAt
    (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      tlb_authenticatorZeroCapAt A a default := by
  unfold tlb_authenticatorZeroCapAt
  have h24 : a + 0x18#64 = a + 24#64 := rfl
  have h32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have h40 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hd1 : (default : ProtoAuthenticator).rootKey = [] := rfl
  have hd2 : (default : ProtoAuthenticator).macKey = [] := rfl
  rw [h24, hd1, hd2, ← h32, ← h40]
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ (((a + 24#64) + 8#64) ↦₆₄ 1#64) ∗ (((a + 24#64) + 16#64) ↦₆₄ 0#64) =
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      (((a + 24#64) ↦₆₄ 0#64) ∗ (((a + 24#64) + 8#64) ↦₆₄ 1#64) ∗ (((a + 24#64) + 16#64) ↦₆₄ 0#64)))) ?_
  exact sepConj_mono (e2b305_cells_entails_vecU8ZeroCapAt A a)
    (e2b305_cells_entails_vecU8ZeroCapAt A (a + 24#64))

private def e2b305_poolAt {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (ops cum : Nat) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜SpqrTightEvs ops cum 32 evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem e2b305_poolAt_eq_of_vmPreserved {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {ops cum : Nat} {s1 s2 : State}
    (hvm : VmPreserved s1 s2) :
    e2b305_poolAt A lim st ops cum s2 = e2b305_poolAt A lim st ops cum s1 := by
  simp only [e2b305_poolAt, A.pool_of_vmPreserved hvm]

private theorem e2b305_poolAt_mono {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {ops₁ ops₂ cum₁ cum₂ : Nat}
    (hops : ops₁ ≤ ops₂) (hcum : cum₁ ≤ cum₂) (s : State) :
    e2b305_poolAt A lim st ops₁ cum₁ s ⊢ e2b305_poolAt A lim st ops₂ cum₂ s := by
  unfold e2b305_poolAt
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  refine Entails.pure_left fun hevs => ?_
  exact Entails.pure_right (hevs.mono hops hcum (Nat.le_refl 32)) (Entails.refl _)

private theorem e2b305_poolAt_step_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {ops cum : Nat} {evs₁ evs₂ : List AllocEvent} {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    (h₁ : SpqrTightEvs ops cum 32 evs₁) (hnil : evs₂ = []) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s1 ⊢
      e2b305_poolAt A lim st ops cum s2 := by
  subst hnil
  rw [M.stepEvents_nil]
  unfold e2b305_poolAt
  refine Entails.sepExists_right evs₁ ?_
  exact Entails.pure_right h₁ (Entails.of_eq (A.pool_of_vmPreserved hvm).symm)

private theorem e2b305_poolAt_step_nil0 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {evs : List AllocEvent} (hnil : evs = []) :
    A.pool lim (M.stepEvents evs st) s ⊢ e2b305_poolAt A lim st 0 0 s :=
  e2b305_poolAt_step_nil (evs₁ := []) A lim st (VmPreserved.refl s)
    (SpqrTightEvs.nil 0 0 32) hnil

private theorem e2b305_poolAt_step_auth {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {authOps : Nat} {evs₁ evs₂ : List AllocEvent} {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    (h₁ : SpqrTightEvs 0 0 32 evs₁)
    (h₂ : SpqrTightEvs authOps 2952 32 evs₂) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s1 ⊢
      e2b305_poolAt A lim st authOps 2952 s2 := by
  unfold e2b305_poolAt
  refine Entails.sepExists_right (evs₁ ++ evs₂) ?_
  have h12 : SpqrTightEvs authOps 2952 32 (evs₁ ++ evs₂) :=
    (h₁.append h₂).mono (by omega) (by decide) (by decide)
  rw [← M.stepEvents_append]
  exact Entails.pure_right h12 (Entails.of_eq (A.pool_of_vmPreserved hvm).symm)

private theorem e2b305_fitsEnv_auth_of_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {authOps maxOps : Nat} {evs₁ : List AllocEvent} {g : AuthMergeGhost}
    (hOps : authOps ≤ maxOps)
    (hFit : FitsEnv M lim st (tlb_ChunkedKeysUnsampledTightEnvOf maxOps))
    (h₁ : SpqrTightEvs 0 0 32 evs₁)
    (hDom : tlb_AuthDom g) :
    FitsEnv M lim (M.stepEvents evs₁ st) (tlb_AuthGuardedEnvOf authOps g) := by
  apply tlb_fitsEnv_guarded_of_dom hDom
  intro evs₂ h₂
  have h12 : SpqrTightEvs maxOps 2952 32 (evs₁ ++ evs₂) :=
    (h₁.append h₂).mono (by omega) (by decide) (by decide)
  exact ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) h12)).2

private theorem e2b305_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (maxOps : Nat) (x : ChunkedKeysUnsampledMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.KeysUnsampled) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedKeysUnsampledDom x)
    (hsome : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps 2952 32 evs) :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedKeysUnsampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (chunkedKeysUnsampledMergeSpecOfEnv A lim
      (tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps)
      (tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps)).post (x, st) s0 sf := by
  dsimp only [chunkedKeysUnsampledMergeSpecOfEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedKeysUnsampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedInlStack ∗
          (chunkedKeysUnsampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  have hPost : tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps x evs := Or.inl ⟨hDom, hevs⟩
  have hPool : A.pool lim (M.stepEvents evs st) s ⊢
      ∃∗ evs' : List AllocEvent,
        ⌜tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps x evs'⌝ ∗
          A.pool lim (M.stepEvents evs' st) sf :=
    Entails.sepExists_right evs (Entails.pure_right hPost (Entails.of_eq (A.pool_of_vmPreserved hvm).symm))
  exact sepConj_mono_right (sepConj_mono hPool
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

private theorem e2b305_fallback_post_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (maxOps : Nat) (x : ChunkedKeysUnsampledMergeGhost)
    (s0 sf : State) (hNotDom : ¬ tlb_ChunkedKeysUnsampledDom x) :
    (chunkedKeysUnsampledMergeSpec A lim).post (x, st) s0 sf ∗ emp ⊢
    (chunkedKeysUnsampledMergeSpecOfEnv A lim
      (tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps)
      (tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps)).post (x, st) s0 sf := by
  rw [sepConj_emp]
  dsimp only [chunkedKeysUnsampledMergeSpec, chunkedKeysUnsampledMergeSpecOfEnv]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono ?_ (Entails.refl _)))
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  refine Entails.pure_left fun hevs => ?_
  exact Entails.pure_right (Or.inr ⟨hNotDom, chunkedKeysUnsampledMergePostEnv_imp_pre hevs⟩)
    (Entails.refl _)

/-! ## 3. Guarded-Tight VM Step Segments (`blkPC_305`) -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedKeysUnsampledMerge_fnOff

private theorem e2b305_stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private abbrev e2b305_TargetSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) : Spec (ChunkedKeysUnsampledMergeGhost × M.σ) :=
  chunkedKeysUnsampledMergeSpecOfEnv A lim
    (tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps)
    (tlb_ChunkedKeysUnsampledGuardedEnvOf maxOps)

private def e2b305_LoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (ops cum : Nat) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.KeysUnsampled) (bs cur : List (BitVec 8)) : SepProp :=
  chunkedKeysUnsampledPBCapAt A.repAlloc msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    polySavedRegsAny s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    e2b305_poolAt A lim st ops cum s

private def e2b305_UcLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (ops cum : Nat) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (uc : V1State.Unchunked.KeysUnsampled) (bs cur : List (BitVec 8)) : SepProp :=
  unchunked2CapAt A.repAlloc msgPtr cur.length uc.epoch uc.auth ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    polySavedRegsAny s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    e2b305_poolAt A lim st ops cum s

section TightSteps

set_option quotPrecheck false in
local notation "entry" => (blkPl_305).base

private theorem e2b305_prologue_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hpc : s0.pc = (blkPl_305).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (h_1 : (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat)
    (h_2 : s0.readReg64 .x1 = x.msgPtr) (h_3 : s0.readReg64 .x2 = x.bufRef)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hwt_ld : x.wt = .lengthDelimited)
    (hdv0 : decodeVarint x.bs = some (len, rest0))
    (hge_len : ¬ rest0.length < len.toNat)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_305).base + 188#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (rest0.length - len.toNat) →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (e2b305_LoopPre A lim st 0 0 s0 s' x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s0
      (chunkedKeysUnsampledPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
        A.pool lim st s0 ∗ stackAt s0.sp chunkedInlStack)
      (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hule := ule_len_of_ge hge_len hrest0_lt
  have hsub := bv_len_sub_limit hge_len
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    wp_steps
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st))
      (ret_pc := entry + 56#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2b305_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
      (by exact ⟨by simp only [arm64_norm, wp_norm, h_3], hbs_lt,
        b304_fitsEnv_decodeVarint2_of_some hdv0⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 188#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2b305_stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
      apply SepWP.fold
        (e2b305_poolAt_step_nil0 A lim st sm (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
        (by sep_focus)
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← e2b305_poolAt_eq_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b305_LoopPre A lim st 0 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
        (by dsimp only [e2b305_LoopPre, sliceCursorAfter]; sep_entail)
      exact hcont _
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hsm1, hsub])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx26_m],
         by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b305_outer_ok_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ops cum maxOps : Nat} {H : String → Option (State → State)}
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hDom : tlb_ChunkedKeysUnsampledDom x)
    (hOps : ops ≤ maxOps) (hCum : cum ≤ 2952)
    (heq_lim : cur.length = outerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hsome : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hpc : s.pc = (blkPl_305).base + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (e2b305_LoopPre A lim st ops cum s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2b305_LoopPre, e2b305_poolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, polySavedRegsAny, polySavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm,
      arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.exists_elim; intro v_pad
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl9_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
    have hcur_fold :
        (x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length) ∗
          (x.ptr ↦ₛ x.bs.take (x.bs.length - cur.length)) ∗ (curPtr ↦ₛ cur) ⊢
        sliceCursorAfter x.slot x.ptr x.bs cur := by
      rw [sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
      dsimp only [curPtr]
      exact Entails.of_eq (by sep_ac_rfl)
    apply SepWP.fold hcur_fold (by dsimp only [curPtr]; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx26, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (e2b305_ok_exit_entails A lim st maxOps x s0 s _ m cur evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm])
        (hevs.mono hOps hCum (Nat.le_refl 32)))

private theorem e2b305_outer_dispatch_tag1 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {outerLimit : Nat}
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_305).base + 256#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (e2b305_LoopPre A lim st 0 0 s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_305).base + 248#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 1#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (e2b305_LoopPre A lim st 0 0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply sepWPpLscro_of_vm (mid := entry + 256#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    apply SepWPpLscro.weaken_pre
      (P' := e2b305_LoopPre A lim st 0 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (by dsimp only [e2b305_LoopPre]; rw [e2b305_poolAt_eq_of_vmPreserved hvm1]; exact Entails.refl _)
    exact hcont _
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [arm64_norm, wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htr])
      (by simp only [arm64_norm, wp_norm, hx8]) (by simp only [arm64_norm, wp_norm, hx19])
      (by simp only [arm64_norm, wp_norm, hx20]) (by simp only [arm64_norm, wp_norm, hx21])
      (by simp only [arm64_norm, wp_norm, hx22]) (by simp only [arm64_norm, wp_norm, hx23])
      (by simp only [arm64_norm, wp_norm, hx24])
      ⟨by simp only [arm64_norm, wp_norm, hx26],
       by simp only [arm64_norm, wp_norm, hx27],
       by simp only [arm64_norm, wp_norm, hx28],
       by simp only [arm64_norm, wp_norm, hvregs]⟩

private theorem e2b305_outer_decode_tag1 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {outerLimit : Nat}
    (hgt_lim : ¬ (0x0a#8 :: rest).length ≤ outerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : (0x0a#8 :: rest).length ≤ x.bs.length)
    (hcur_lt : (0x0a#8 :: rest).length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs (0x0a#8 :: rest))
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_305).base + 256#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (e2b305_LoopPre A lim st 0 0 s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_305).base + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (e2b305_LoopPre A lim st 0 0 s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs (0x0a#8 :: rest))
      (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let cur := 0x0a#8 :: rest
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hd : decodeVarint cur = some (0x0a#64, rest) := e2b305_decodeVarint_0x0a rest
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hk_ge : ¬ 2 ^ 32 ≤ (0x0a#64 : BitVec 64).toNat := by decide
  have hshr := key_shr32_of_lt hk_ge
  have hwt : WireType.ofNat? ((0x0a#64 : BitVec 64).toNat % 8) = some .lengthDelimited := by decide
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := (0x0a#64 : BitVec 64).toNat / 8) (by decide)
  have hitag0 : ¬ (0x0a#64 : BitVec 64).toNat / 8 < 1 := by decide
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
  have hcbz_tag64 : (BitVec.ofNat 64 ((0x0a#64 : BitVec 64).toNat / 8) == 0#64) = false := by decide
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b305_LoopPre, e2b305_poolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 208#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19,
            e2b305_stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hcur_lt (b304_fitsEnv_decodeVarint2_of_some hd))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 248#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        e2b305_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      have hnil := decodeVarint2Env_eq_nil_of_some hd hevs_v
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
      apply SepWP.fold (e2b305_poolAt_step_nil A lim st (VmPreserved.refl sm) hevs hnil) (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := e2b305_LoopPre A lim st 0 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (by dsimp only [e2b305_LoopPre]; rw [e2b305_poolAt_eq_of_vmPreserved hvm2]; sep_entail)
      exact e2b305_outer_dispatch_tag1 hcont
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
        ⟨by simp only [arm64_norm, wp_norm, hx26_m],
         by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b305_uc_init_enter [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {rest : List (BitVec 8)} {len : BitVec 64} {rest0 : List (BitVec 8)} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hdv0 : decodeVarint rest = some (len, rest0))
    (hge_len : ¬ rest0.length < len.toNat)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_305).base + 344#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 (rest0.length - len.toNat) →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (e2b305_UcLoopPre A lim st 0 0 s0 s' x.msgPtr x.bufRef x.slot x.ptr default x.bs rest0)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_305).base + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (e2b305_LoopPre A lim st 0 0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs rest)
      (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  have huc_def : (default : V1State.Chunked.KeysUnsampled).uc = none := rfl
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hrest0_le_rest : rest0.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_rest hrest_le
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
  have hrest0_suf : IsDropSuffix x.bs rest0 :=
    suffix_trans hrest_le hrest_suf hrest0_le_rest (decodeVarint_suffix hdv0)
  have hule := ule_len_of_ge hge_len hrest0_lt
  have hsub := bv_len_sub_limit hge_len
  have hafter276 : ∀ s1 : State,
      s1.pc = (blkPl_305).base + 276#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot →
      s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s1
        (e2b305_UcLoopPre A lim st 0 0 s0 s1 x.msgPtr x.bufRef x.slot x.ptr default x.bs rest)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
    intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
    obtain ⟨hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [e2b305_UcLoopPre, e2b305_poolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
        chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
        (ret_pc := entry + 292#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, e2b305_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx19_1], hrest_lt,
          b304_fitsEnv_decodeVarint2_of_some hdv0⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 344#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
          e2b305_stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_dv
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold
          (unchunked2CapAt_mono A.repAlloc x.msgPtr
            (default : V1State.Unchunked.KeysUnsampled).epoch
            (default : V1State.Unchunked.KeysUnsampled).auth hrest0_le_rest)
          (by sep_focus)
        apply SepWP.fold
          (e2b305_poolAt_step_nil A lim st (VmPreserved.refl sm) hevs
            (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
          (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt])
        (conv => arg 4; simp only [sepConj_assoc])
        wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← e2b305_poolAt_eq_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := e2b305_UcLoopPre A lim st 0 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr default x.bs rest0)
          (by dsimp only [e2b305_UcLoopPre, sliceCursorAfter]; sep_entail)
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
          (by simp only [arm64_norm, wp_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
  apply sepWPpLscro_of_vm (mid := entry + 276#64)
  by_vm_steps
    (conv => arg 4; rw [e2b305_LoopPre, chunkedKeysUnsampledPBCapAt, huc_def,
      optKeysUnsampledPBCapAt, memRegion_48_split_40_8 x.msgPtr])
    (conv => arg 4; simp only [noneCap2, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v48
    wp_steps
    have hdef : (x.msgPtr ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.msgPtr + 8#64) 40 ∗
        ((x.msgPtr + 48#64) ↦₆₄ 0#64) ⊢
        unchunked2CapAt A.repAlloc x.msgPtr rest.length
          (default : V1State.Unchunked.KeysUnsampled).epoch
          (default : V1State.Unchunked.KeysUnsampled).auth :=
      default_unchunked2_entails_cap A.repAlloc x.msgPtr rest.length
    apply SepWP.fold hdef (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    apply SepWPpLscro.weaken_pre
      (P' := e2b305_UcLoopPre A lim st 0 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr default x.bs rest)
      (by dsimp only [e2b305_UcLoopPre]; rw [e2b305_poolAt_eq_of_vmPreserved hvm0]; sep_entail)
    exact hafter276 _
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrun])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsp])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htr])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx8])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24])
      ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28],
       by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs]⟩

private theorem e2b305_uc_decode_key_known [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.KeysUnsampled}
    {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_ge : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag0 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_305).base + 396#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (e2b305_UcLoopPre A lim st 0 0 s0 s' x.msgPtr x.bufRef x.slot x.ptr uc x.bs rest)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_305).base + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (e2b305_UcLoopPre A lim st 0 0 s0 s x.msgPtr x.bufRef x.slot x.ptr uc x.bs cur)
      (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hshr := key_shr32_of_lt hk_ge
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b305_UcLoopPre, e2b305_poolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 364#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19,
            e2b305_stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hcur_lt (b304_fitsEnv_decodeVarint2_of_some hd))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 396#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        e2b305_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_mono A.repAlloc x.msgPtr uc.epoch uc.auth hrest_le_cur) (by sep_focus)
      apply SepWP.fold
        (e2b305_poolAt_step_nil A lim st (VmPreserved.refl sm) hevs
          (decodeVarint2Env_eq_nil_of_some hd hevs_v))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← e2b305_poolAt_eq_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b305_UcLoopPre A lim st 0 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr uc x.bs rest)
        (by dsimp only [e2b305_UcLoopPre]; sep_entail)
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
        ⟨by simp only [arm64_norm, wp_norm, hx26_m],
         by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b305_uc_tag1_varint_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.KeysUnsampled}
    {rest rest' : List (BitVec 8)} {v : BitVec 64} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hdv : decodeVarint rest = some (v, rest'))
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_305).base + 344#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (e2b305_UcLoopPre A lim st 0 0 s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc with epoch := v } x.bs rest')
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_305).base + 396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 1#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (e2b305_UcLoopPre A lim st 0 0 s0 s x.msgPtr x.bufRef x.slot x.ptr uc x.bs rest)
      (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
  have h456 : ∀ s1 : State,
      s1.pc = (blkPl_305).base + 456#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 0#5) = 0#64 →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot →
      s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 24#5) = 1#64 →
      s1.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit →
      PolyCalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s1
        (e2b305_UcLoopPre A lim st 0 0 s0 s1 x.msgPtr x.bufRef x.slot x.ptr uc x.bs rest)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    obtain ⟨hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [e2b305_UcLoopPre, e2b305_poolAt,
        sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
        (ret_pc := entry + 468#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
            simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1, hx19_1,
              e2b305_stackAt_decodeVarint2_raw_eq]; try rfl)
        (And.intro hrest_lt (b304_fitsEnv_decodeVarint2_of_some hdv))
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 344#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, unchunked2CapAt,
          e2b305_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc x.msgPtr uc.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (e2b305_poolAt_step_nil A lim st (VmPreserved.refl sm) hevs
            (decodeVarint2Env_eq_nil_of_some hdv hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← e2b305_poolAt_eq_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := e2b305_UcLoopPre A lim st 0 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { uc with epoch := v } x.bs rest')
          (by dsimp only [e2b305_UcLoopPre, unchunked2CapAt]; simp only [arm64_norm]; sep_entail)
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
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
  apply sepWPpLscro_of_vm (mid := entry + 456#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    apply SepWPpLscro.weaken_pre
      (P' := e2b305_UcLoopPre A lim st 0 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr uc x.bs rest)
      (by dsimp only [e2b305_UcLoopPre]; rw [e2b305_poolAt_eq_of_vmPreserved hvm0]; exact Entails.refl _)
    exact h456 _
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [arm64_norm, wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htr])
      (by simp only [arm64_norm, wp_norm, hx0])
      (by simp only [arm64_norm, wp_norm, hx19]) (by simp only [arm64_norm, wp_norm, hx20])
      (by simp only [arm64_norm, wp_norm, hx21]) (by simp only [arm64_norm, wp_norm, hx22])
      (by simp only [arm64_norm, wp_norm, hx23]) (by simp only [arm64_norm, wp_norm, hx24])
      (by simp only [arm64_norm, wp_norm, hx25])
      ⟨by simp only [arm64_norm, wp_norm, hx26],
       by simp only [arm64_norm, wp_norm, hx27],
       by simp only [arm64_norm, wp_norm, hx28],
       by simp only [arm64_norm, wp_norm, hvregs]⟩

private theorem e2b305_uc_tag2_auth_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {H : String → Option (State → State)}
    (hAuthTightCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ep : BitVec 64} {a : ProtoAuthenticator} {rest_outer : List (BitVec 8)}
    {outerLimit innerLimit : Nat}
    (hOps : authOps ≤ maxOps)
    (hFitTight : FitsEnv M lim st (tlb_ChunkedKeysUnsampledTightEnvOf maxOps))
    (ha_valid : tlb_ValidAuthPB a)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) rest_outer).length ≤ x.bs.length)
    (hrest_lt : (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) rest_outer).length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) rest_outer))
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_305).base + 344#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (e2b305_UcLoopPre A lim st authOps 2952 s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { epoch := ep, auth := some a } x.bs rest_outer)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_305).base + 396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (e2b305_UcLoopPre A lim st 0 0 s0 s x.msgPtr x.bufRef x.slot x.ptr
        { epoch := ep, auth := none } x.bs
        (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) rest_outer))
      (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let rest := tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) rest_outer
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let g_auth : AuthMergeGhost :=
    ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot, restPtr, rest⟩
  have hAuthDom : tlb_AuthDom g_auth := ⟨rfl, rfl, a, rest_outer, ha_valid, rfl⟩
  have hauth_res : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto .lengthDelimited) default rest 97).toOption =
      some (a, rest_outer) :=
    proto_mergeMessage_authenticator_canonical a rest_outer ha_valid
  have hrest'_le : rest_outer.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
  have h436 : ∀ s2 : State,
      s2.pc = (blkPl_305).base + 436#64 →
      s2.status = .Running → s2.sp = s0.sp - 128#64 → s2.trace = s0.trace →
      s2.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat →
      s2.readReg64 (Reg.gpr 19#5) = x.bufRef → s2.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s2.readReg64 (Reg.gpr 21#5) = x.slot →
      s2.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s2.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s2.readReg64 (Reg.gpr 24#5) = 1#64 →
      s2.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit →
      PolyCalleeSaved s0 s2 →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s2
        (tlb_authenticatorZeroCapAt A.repAlloc x.msgPtr default ∗
          ((x.msgPtr + 48#64) ↦₆₄ ep) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          e2b305_poolAt A lim st 0 0 s2)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hcs2
    obtain ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ := hcs2
    apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
    by_vm_steps
      (conv => arg 4; rw [e2b305_poolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
        chunkedInlBelow_authMerge s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro
        (spec := tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))
        (x := (g_auth, M.stepEvents evs st))
        (ret_pc := entry + 448#64) hAuthTightCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun2])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp2]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [tlb_authMergeTightSpecOfEnv]
              arg 2
              rw [tlb_domHeap_of_dom hAuthDom]
              dsimp only [g_auth]
              simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp2])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_2, setWidth8_ofNat64_wt]; rfl,
          by simp only [arm64_norm, wp_norm, hx20_2]; rfl,
          by simp only [arm64_norm, wp_norm, hx19_2]; rfl,
          hrest_lt,
          e2b305_fitsEnv_auth_of_tight hOps hFitTight hevs hAuthDom⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp2,
        hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hvregs_2]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 344#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_authMergeTightSpecOfEnv, authMergeSpecOfEnv, g_auth,
          hauth_res, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          arm64_norm, wp_norm, hsp2])
        apply SepWP.exists_elim; intro evs_auth
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_auth⟩, hsm0⟩
        have hTight2 : SpqrTightEvs authOps 2952 32 evs_auth :=
          tlb_guardedEnv_tight_of_dom hAuthDom hevs_auth
        apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold
          (e2b305_poolAt_step_auth A lim st (VmPreserved.refl sm) hevs hTight2)
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← e2b305_poolAt_eq_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := e2b305_UcLoopPre A lim st authOps 2952 s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { epoch := ep, auth := some a } x.bs rest_outer)
          (by dsimp only [e2b305_UcLoopPre, unchunked2CapAt, optAuthenticatorPBCapAt];
              simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr2])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
  have h412 : ∀ s1 : State,
      s1.pc = (blkPl_305).base + 412#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot →
      s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s1.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 24#5) = 1#64 →
      s1.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit →
      PolyCalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s1
        (e2b305_UcLoopPre A lim st 0 0 s0 s1 x.msgPtr x.bufRef x.slot x.ptr
          { epoch := ep, auth := none } x.bs rest)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    obtain ⟨hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    apply sepWPpLscro_of_vm (mid := entry + 436#64)
    by_vm_steps
      (conv => arg 4; rw [e2b305_UcLoopPre, unchunked2CapAt, optAuthenticatorPBCapAt, memRegion_40_cells x.msgPtr])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w1
      apply SepWP.exists_elim; intro w2
      apply SepWP.exists_elim; intro w3
      apply SepWP.exists_elim; intro w4
      apply SepWP.exists_elim; intro w5
      wp_steps
      apply SepWP.fold (e2b305_default_cells_entails_authenticatorZeroCapAt A.repAlloc x.msgPtr) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_init => ?_⟩
      rw [← e2b305_poolAt_eq_of_vmPreserved hvm_init]
      apply SepWPpLscro.weaken_pre
        (P' := tlb_authenticatorZeroCapAt A.repAlloc x.msgPtr default ∗
          ((x.msgPtr + 48#64) ↦₆₄ ep) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗
          (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
          e2b305_poolAt A lim st 0 0 _)
        (Entails.of_eq (by sep_ac_rfl))
      exact h436 _
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [arm64_norm, wp_norm, hsp1]) (by simp only [arm64_norm, wp_norm, htr1])
        (by simp only [arm64_norm, wp_norm, hx0_1])
        (by simp only [arm64_norm, wp_norm, hx19_1]) (by simp only [arm64_norm, wp_norm, hx20_1])
        (by simp only [arm64_norm, wp_norm, hx21_1]) (by simp only [arm64_norm, wp_norm, hx22_1])
        (by simp only [arm64_norm, wp_norm, hx23_1]) (by simp only [arm64_norm, wp_norm, hx24_1])
        (by simp only [arm64_norm, wp_norm, hx25_1])
        ⟨by simp only [arm64_norm, wp_norm, hx26_1],
         by simp only [arm64_norm, wp_norm, hx27_1],
         by simp only [arm64_norm, wp_norm, hx28_1],
         by simp only [arm64_norm, wp_norm, hvregs_1]⟩
  apply sepWPpLscro_of_vm (mid := entry + 412#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    apply SepWPpLscro.weaken_pre
      (P' := e2b305_UcLoopPre A lim st 0 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { epoch := ep, auth := none } x.bs rest)
      (by dsimp only [e2b305_UcLoopPre]; rw [e2b305_poolAt_eq_of_vmPreserved hvm0]; exact Entails.refl _)
    exact h412 _
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [arm64_norm, wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htr])
      (by simp only [arm64_norm, wp_norm, hx0])
      (by simp only [arm64_norm, wp_norm, hx19]) (by simp only [arm64_norm, wp_norm, hx20])
      (by simp only [arm64_norm, wp_norm, hx21]) (by simp only [arm64_norm, wp_norm, hx22])
      (by simp only [arm64_norm, wp_norm, hx23]) (by simp only [arm64_norm, wp_norm, hx24])
      (by simp only [arm64_norm, wp_norm, hx25])
      ⟨by simp only [arm64_norm, wp_norm, hx26],
       by simp only [arm64_norm, wp_norm, hx27],
       by simp only [arm64_norm, wp_norm, hx28],
       by simp only [arm64_norm, wp_norm, hvregs]⟩

private theorem e2b305_uc_ok_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ops cum maxOps : Nat} {H : String → Option (State → State)}
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.KeysUnsampled}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (heq_lim : cur.length = innerLimit)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_305).base + 188#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (e2b305_LoopPre A lim st ops cum s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := some uc } x.bs cur)
        (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_305).base + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerLimit)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (e2b305_UcLoopPre A lim st ops cum s0 s x.msgPtr x.bufRef x.slot x.ptr uc x.bs cur)
      (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply sepWPpLscro_of_vm (mid := entry + 188#64)
  by_vm_steps
    (conv => arg 4; rw [e2b305_UcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt])
    wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    rw [← e2b305_poolAt_eq_of_vmPreserved hvm]
    apply SepWPpLscro.weaken_pre
      (P' := e2b305_LoopPre A lim st ops cum s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { uc := some uc } x.bs cur)
      (by dsimp only [e2b305_LoopPre, chunkedKeysUnsampledPBCapAt,
            optKeysUnsampledPBCapAt, unchunked2CapAt, sliceCursorAfter]; sep_entail)
    exact hcont _
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm, htr])
      (by simp only [arm64_norm, wp_norm, hx19])
      (by simp only [arm64_norm, wp_norm, hx20])
      (by simp only [arm64_norm, wp_norm, hx21])
      (by simp only [arm64_norm, wp_norm, hx22])
      (by simp only [arm64_norm, wp_norm, hx23])
      (by simp only [arm64_norm, wp_norm, hx24])
      ⟨by simp only [arm64_norm, wp_norm, hx26],
       by simp only [arm64_norm, wp_norm, hx27],
       by simp only [arm64_norm, wp_norm, hx28],
       by simp only [arm64_norm, wp_norm, hvregs]⟩

private theorem e2b305_blk305_tight_ok_of_callees [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {H : String → Option (State → State)}
    (hOps : authOps ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hFallbackCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 305)
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim))) :
    subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (blkPl_305).base
      (withLsCodeRoLoaded lsmpl (e2b305_TargetSpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2b305_TargetSpec chunkedKeysUnsampledMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  rintro ⟨h_1, h_2, h_3, hbs_lt, hFit⟩
  by_cases hDom : tlb_ChunkedKeysUnsampledDom x
  · have hDomSave := hDom
    rcases hDom with ⟨hwt_p, hmsg_def, pb, rest_outer, hpb_valid, hbs_eq⟩
    have hwt_ld : x.wt = .lengthDelimited := e2b305_wt_eq_lengthDelimited hwt_p
    have hFitTight : FitsEnv M lim st (tlb_ChunkedKeysUnsampledTightEnvOf maxOps) :=
      fun evs ht => hFit evs (Or.inl ⟨hDomSave, ht⟩)
    have hsome_top : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, rest_outer) := by
      rw [hwt_p, hmsg_def, hbs_eq]
      exact e2b305_proto_mergeMessage_keysUnsampled_canonical pb rest_outer hpb_valid
    let raw := V1State.Chunked.KeysUnsampled.encodeRaw pb
    have hraw_le : raw.length ≤ 164 := e2b305_validChunkedKeysUnsampledPB_encodeRaw_len_le hpb_valid
    have hraw_lt64 : raw.length < 2 ^ 64 := by omega
    have hraw_toNat : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_lt64]
    have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw.length, raw ++ rest_outer) := by
      rw [hbs_eq]; exact codec_decodeVarint_tlb_lenPrefixed raw rest_outer
    have hge_outer : ¬ (raw ++ rest_outer).length < (BitVec.ofNat 64 raw.length).toNat := by
      rw [hraw_toNat, List.length_append]; omega
    have hlim_outer_eq : (raw ++ rest_outer).length - (BitVec.ofNat 64 raw.length).toNat = rest_outer.length := by
      rw [hraw_toNat, List.length_append]; omega
    have hrest0_le : (raw ++ rest_outer).length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
    have hrest0_lt : (raw ++ rest_outer).length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
    have hrest0_suf : IsDropSuffix x.bs (raw ++ rest_outer) := decodeVarint_suffix hdv0
    refine e2b305_prologue_ok hVarintCall hpc hrun hsp_align h_1 h_2 h_3 hbs_lt hwt_ld hdv0 hge_outer ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
    rw [hlim_outer_eq] at hx22_1
    rw [hmsg_def]
    rcases huc : pb.uc with _ | u
    · have hpb_def : pb = default := by cases pb; simp_all; rfl
      have hraw_nil : raw = [] := by
        dsimp only [raw, V1State.Chunked.KeysUnsampled.encodeRaw]
        rw [huc]; rfl
      have hr0_eq : raw ++ rest_outer = rest_outer := by rw [hraw_nil, List.nil_append]
      rw [hr0_eq] at hrest0_le hrest0_suf
      rw [hr0_eq]
      rw [← hpb_def]
      exact e2b305_outer_ok_exit hDomSave (Nat.zero_le maxOps) (Nat.zero_le 2952)
        rfl hsp_align hrest0_le hrest0_suf hsome_top
        hpc1 hrun1 hsp1 htr1 hx21_1 hx22_1 hcs1
    · have hpb_eq : pb = { uc := some u } := by cases pb; simp_all
      have hu_valid : tlb_ValidUcKeysUnsampledPB u := hpb_valid u huc
      let ucRaw := V1State.Unchunked.KeysUnsampled.encodeRaw u
      let afterTag1 := tlb_lenPrefixed ucRaw rest_outer
      have hraw_eq : raw ++ rest_outer = 0x0a#8 :: afterTag1 := by
        dsimp only [raw, V1State.Chunked.KeysUnsampled.encodeRaw, afterTag1, ucRaw]
        rw [huc]
        exact encodeOptMessage_tag1_some V1State.Unchunked.KeysUnsampled.encodeRaw u rest_outer
      rw [hraw_eq] at hrest0_le hrest0_lt hrest0_suf
      rw [hraw_eq]
      have hgt_outer : ¬ (0x0a#8 :: afterTag1).length ≤ rest_outer.length := by
        dsimp only [afterTag1, tlb_lenPrefixed]
        simp only [List.length_cons, List.length_append]
        have := (proto_encodeVarint_length (BitVec.ofNat 64 ucRaw.length)).1
        omega
      refine e2b305_outer_decode_tag1 hVarintCall hgt_outer hsp_align
        hrest0_le hrest0_lt hrest0_suf ?_
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
      intro s2 hpc2 hrun2 hsp2 htr2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hcs2
      have hafter1_le_cur : afterTag1.length ≤ (0x0a#8 :: afterTag1).length := Nat.le_succ _
      have hafter1_le : afterTag1.length ≤ x.bs.length := Nat.le_trans hafter1_le_cur hrest0_le
      have hafter1_lt : afterTag1.length < 2 ^ 63 := Nat.lt_of_le_of_lt hafter1_le hbs_lt
      have hafter1_suf : IsDropSuffix x.bs afterTag1 :=
        suffix_trans hrest0_le hrest0_suf hafter1_le_cur
          (decodeVarint_suffix (e2b305_decodeVarint_0x0a afterTag1))
      have hucRaw_le : ucRaw.length ≤ 144 := e2b305_validUcKeysUnsampledPB_encodeRaw_len_le hu_valid
      have hucRaw_toNat : (BitVec.ofNat 64 ucRaw.length).toNat = ucRaw.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ucRaw.length < 2 ^ 64)]
      have hdv_uc : decodeVarint afterTag1 = some (BitVec.ofNat 64 ucRaw.length, ucRaw ++ rest_outer) :=
        codec_decodeVarint_tlb_lenPrefixed ucRaw rest_outer
      have hge_uc : ¬ (ucRaw ++ rest_outer).length < (BitVec.ofNat 64 ucRaw.length).toNat := by
        rw [hucRaw_toNat, List.length_append]; omega
      have hlim_uc_eq : (ucRaw ++ rest_outer).length - (BitVec.ofNat 64 ucRaw.length).toNat = rest_outer.length := by
        rw [hucRaw_toNat, List.length_append]; omega
      have huc0_le_a1 : (ucRaw ++ rest_outer).length ≤ afterTag1.length :=
        Nat.le_of_lt (decodeVarint_length hdv_uc)
      have huc0_le : (ucRaw ++ rest_outer).length ≤ x.bs.length := Nat.le_trans huc0_le_a1 hafter1_le
      have huc0_lt : (ucRaw ++ rest_outer).length < 2 ^ 63 := Nat.lt_of_le_of_lt huc0_le hbs_lt
      have huc0_suf : IsDropSuffix x.bs (ucRaw ++ rest_outer) :=
        suffix_trans hafter1_le hafter1_suf huc0_le_a1 (decodeVarint_suffix hdv_uc)
      refine e2b305_uc_init_enter hVarintCall hsp_align hbs_lt hafter1_le hafter1_lt hafter1_suf
        hdv_uc hge_uc ?_
        hpc2 hrun2 hsp2 htr2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hcs2
      intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hcs3
      rw [hlim_uc_eq] at hx25_3
      let afterEp :=
        CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          ProtoAuthenticator.encodeRaw 2#32 u.auth ++ rest_outer
      have hucRaw_split : ucRaw ++ rest_outer =
          CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 u.epoch ++ afterEp := by
        dsimp only [ucRaw, V1State.Unchunked.KeysUnsampled.encodeRaw, afterEp]
        rw [List.append_assoc]
      have hAfterEp : ∀ (s4 : State),
          IsDropSuffix x.bs afterEp →
          afterEp.length ≤ x.bs.length →
          s4.pc = (blkPl_305).base + 344#64 →
          s4.status = .Running → s4.sp = s0.sp - 128#64 → s4.trace = s0.trace →
          s4.readReg64 (Reg.gpr 19#5) = x.bufRef → s4.readReg64 (Reg.gpr 20#5) = x.msgPtr →
          s4.readReg64 (Reg.gpr 21#5) = x.slot →
          s4.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_outer.length →
          s4.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
          s4.readReg64 (Reg.gpr 24#5) = 1#64 →
          s4.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 rest_outer.length →
          PolyCalleeSaved s0 s4 →
          SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s4
            (e2b305_UcLoopPre A lim st 0 0 s0 s4 x.msgPtr x.bufRef x.slot x.ptr
              { epoch := u.epoch, auth := none } x.bs afterEp)
            (WppPost (e2b305_TargetSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
        intro s4 haEp_suf haEp_le hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hcs4
        have haEp_lt : afterEp.length < 2 ^ 63 := Nat.lt_of_le_of_lt haEp_le hbs_lt
        rcases hauth : u.auth with _ | a
        · have hu_eq : ({ epoch := u.epoch, auth := none } : V1State.Unchunked.KeysUnsampled) = u := by
            cases u; simp_all
          have haEp_eq : afterEp = rest_outer := by
            dsimp only [afterEp, CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage]
            rw [hauth, List.nil_append]
          rw [haEp_eq] at haEp_suf haEp_le
          rw [haEp_eq, hu_eq]
          refine e2b305_uc_ok_exit rfl haEp_le haEp_suf ?_
            hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hcs4
          intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hcs5
          rw [← hpb_eq]
          exact e2b305_outer_ok_exit hDomSave (Nat.zero_le maxOps) (Nat.zero_le 2952)
            rfl hsp_align haEp_le haEp_suf hsome_top
            hpc5 hrun5 hsp5 htr5 hx21_5 hx22_5 hcs5
        · have hu_eq : ({ epoch := u.epoch, auth := some a } : V1State.Unchunked.KeysUnsampled) = u := by
            cases u; simp_all
          have ha_valid : tlb_ValidAuthPB a := hu_valid a hauth
          let authSlice := tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) rest_outer
          have haEp_eq : afterEp = 0x12#8 :: authSlice := by
            dsimp only [afterEp, authSlice]
            rw [hauth]
            exact encodeOptMessage_tag2_some ProtoAuthenticator.encodeRaw a rest_outer
          rw [haEp_eq] at haEp_suf haEp_le haEp_lt
          rw [haEp_eq]
          have hgt_tag2 : ¬ (0x12#8 :: authSlice).length ≤ rest_outer.length := by
            dsimp only [authSlice, tlb_lenPrefixed]
            simp only [List.length_cons, List.length_append]
            omega
          have hd_12 : decodeVarint (0x12#8 :: authSlice) = some (0x12#64, authSlice) :=
            e2b305_decodeVarint_0x12 authSlice
          have hauth_le_aEp : authSlice.length ≤ (0x12#8 :: authSlice).length := Nat.le_succ _
          have hauth_le : authSlice.length ≤ x.bs.length := Nat.le_trans hauth_le_aEp haEp_le
          have hauth_lt : authSlice.length < 2 ^ 63 := Nat.lt_of_le_of_lt hauth_le hbs_lt
          have hauth_suf : IsDropSuffix x.bs authSlice :=
            suffix_trans haEp_le haEp_suf hauth_le_aEp (decodeVarint_suffix hd_12)
          refine e2b305_uc_decode_key_known hVarintCall hgt_tag2 hsp_align haEp_le haEp_lt haEp_suf
            hd_12 (by decide) (show WireType.ofNat? ((0x12#64 : BitVec 64).toNat % 8) = some .lengthDelimited by decide)
            (by decide) ?_
            hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hcs4
          intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hcs5
          have hx1_5' : s5.readReg64 (Reg.gpr 1#5) = 2#64 := hx1_5
          refine e2b305_uc_tag2_auth_ok hAuthTightCall hOps hFitTight ha_valid hsp_align
            hauth_le hauth_lt hauth_suf ?_
            hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5' hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hcs5
          intro s6 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hcs6
          have hro_le_auth : rest_outer.length ≤ authSlice.length := by
            dsimp only [authSlice, tlb_lenPrefixed]; simp only [List.length_append]; omega
          have hro_le : rest_outer.length ≤ x.bs.length := Nat.le_trans hro_le_auth hauth_le
          have hauth_res0 := proto_mergeMessage_authenticator_canonical a rest_outer ha_valid
          have hro_suf : IsDropSuffix x.bs rest_outer :=
            suffix_trans hauth_le hauth_suf hro_le_auth (proto_mergeMessage_suffix hauth_res0).2
          rw [hu_eq]
          refine e2b305_uc_ok_exit rfl hro_le hro_suf ?_
            hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hcs6
          intro s7 hpc7 hrun7 hsp7 htr7 hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7 hcs7
          rw [← hpb_eq]
          exact e2b305_outer_ok_exit hDomSave hOps (Nat.le_refl 2952)
            rfl hsp_align hro_le hro_suf hsome_top
            hpc7 hrun7 hsp7 htr7 hx21_7 hx22_7 hcs7
      by_cases hep : u.epoch = 0#64
      · have hsplit0 : ucRaw ++ rest_outer = afterEp := by
          rw [hucRaw_split, hep]
          dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field]
          simp
        have hdef_uc : (default : V1State.Unchunked.KeysUnsampled) = { epoch := u.epoch, auth := none } := by
          rw [hep]; rfl
        rw [hsplit0] at huc0_suf huc0_le
        rw [hsplit0, hdef_uc]
        exact hAfterEp s3 huc0_suf huc0_le hpc3 hrun3 hsp3 htr3
          hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hcs3
      · let epRest := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint u.epoch ++ afterEp
        have hsplit1 : ucRaw ++ rest_outer = 0x08#8 :: epRest := by
          rw [hucRaw_split]
          exact encodeUint64Field_tag1_of_ne u.epoch hep afterEp
        rw [hsplit1] at huc0_suf huc0_le huc0_lt
        rw [hsplit1]
        have hgt_ep : ¬ (0x08#8 :: epRest).length ≤ rest_outer.length := by
          dsimp only [epRest, afterEp]
          simp only [List.length_cons, List.length_append]
          have := e2b305_encodeVarint_pos u.epoch
          omega
        have hd_08 : decodeVarint (0x08#8 :: epRest) = some (0x08#64, epRest) :=
          e2b305_decodeVarint_0x08 epRest
        have hepRest_le_uc0 : epRest.length ≤ (0x08#8 :: epRest).length := Nat.le_succ _
        have hepRest_le : epRest.length ≤ x.bs.length := Nat.le_trans hepRest_le_uc0 huc0_le
        have hepRest_lt : epRest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hepRest_le hbs_lt
        have hepRest_suf : IsDropSuffix x.bs epRest :=
          suffix_trans huc0_le huc0_suf hepRest_le_uc0 (decodeVarint_suffix hd_08)
        have hdv_ep : decodeVarint epRest = some (u.epoch, afterEp) :=
          codec_decodeVarint_encodeVarint u.epoch afterEp
        have haEp_le_ep : afterEp.length ≤ epRest.length := Nat.le_of_lt (decodeVarint_length hdv_ep)
        have haEp_le : afterEp.length ≤ x.bs.length := Nat.le_trans haEp_le_ep hepRest_le
        have haEp_suf : IsDropSuffix x.bs afterEp :=
          suffix_trans hepRest_le hepRest_suf haEp_le_ep (decodeVarint_suffix hdv_ep)
        refine e2b305_uc_decode_key_known hVarintCall hgt_ep hsp_align huc0_le huc0_lt huc0_suf
          hd_08 (by decide) (show WireType.ofNat? ((0x08#64 : BitVec 64).toNat % 8) = some .varint by decide)
          (by decide) ?_
          hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hcs3
        intro s4' hpc4' hrun4' hsp4' htr4' hx0_4' hx1_4' hx19_4' hx20_4' hx21_4' hx22_4' hx23_4' hx24_4' hx25_4' hcs4'
        refine e2b305_uc_tag1_varint_ok hVarintCall hsp_align hepRest_le hepRest_lt hepRest_suf
          hdv_ep ?_
          hpc4' hrun4' hsp4' htr4' hx0_4' hx1_4' hx19_4' hx20_4' hx21_4' hx22_4' hx23_4' hx24_4' hx25_4' hcs4'
        intro s5' hpc5' hrun5' hsp5' htr5' hx19_5' hx20_5' hx21_5' hx22_5' hx23_5' hx24_5' hx25_5' hcs5'
        exact hAfterEp s5' haEp_suf haEp_le hpc5' hrun5' hsp5' htr5'
          hx19_5' hx20_5' hx21_5' hx22_5' hx23_5' hx24_5' hx25_5' hcs5'
  · have hFitFb : FitsEnv M lim st (ChunkedKeysUnsampledMergeEnv x) :=
      tlb_fitsEnv_fallback_of_not_dom hDom hFit
    refine call_budget_lscro
      (spec := chunkedKeysUnsampledMergeSpec A lim)
      (x := (x, st))
      (ret_pc := s0.readReg64 Reg.lr)
      (F := emp)
      hFallbackCall
      (by rw [← ls_blockPlacement_base (i := 305)]; exact hpc)
      hrun hsp_align rfl
      (by dsimp only [chunkedKeysUnsampledMergeSpec, chunkedKeysUnsampledMergeSpecOfEnv])
      (by exact ⟨h_1, h_2, h_3, hbs_lt, hFitFb⟩)
      (by rw [sepConj_emp]) ?_
    intro sf hpcm hrunm hspm hcsm
    exact SepWPpLscro.of_sepWP_ret (SepWP.done hpcm hrunm
      ⟨fun hm => Satisfies.of_entails hm
         (sepConj_mono_left (e2b305_fallback_post_entails A lim st maxOps x s0 sf hDom)),
       hspm, hcsm⟩)

end TightSteps

/-! ## 4. Exported Guarded-Tight Placed Contracts (`Block 305`) -/

/-- Guarded-tight contract `tlb_ChunkedKeysUnsampledMergePlacedTightOkOf` (`cumCap = 2,952` B,
`maxReq = 32` B, `authOps ≤ maxOps`) from an explicit `hFallback` contract on Block `305`. -/
theorem e2b305_chunkedKeysUnsampled_merge_placed_tight_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps ≤ maxOps)
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim))) :
    tlb_ChunkedKeysUnsampledMergePlacedTightOkOf A lim maxOps ext := by
  have hok := e2b305_blk305_tight_ok_of_callees hOps
    (e2b305_lift_cl_of_own
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_291).rebase (CryptoVerification.blkPl_291).base (fun _ => none)))
      hVarint)
    (e2b305_lift_cro_of_own
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase (CryptoVerification.blkPl_295).base (fun _ => none)))
      hAuthTight)
    (e2b305_lift_cro_of_own
      (IsLsBlockProg.externs_eq (prog := (blkPC_305).rebase (blkPl_305).base (fun _ => none)))
      hFallback)
  exact e2b305_own_of_blk_cro hok

/-- Guarded-tight contract `tlb_ChunkedKeysUnsampledMergePlacedTightOkOf` (`cumCap = 2,952` B,
`maxReq = 32` B, `authOps ≤ maxOps`) from own-block callee contracts (`261`, `257`, `291`, `263`, `295`). -/
theorem e2b305_chunkedKeysUnsampled_merge_placed_tight_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext) :
    tlb_ChunkedKeysUnsampledMergePlacedTightOkOf A lim maxOps ext :=
  e2b305_chunkedKeysUnsampled_merge_placed_tight_of_fallback hOps hVarint hAuthTight
    (e2b305_chunkedKeysUnsampled_merge_placed_fallback_of_contracts
      hFrom hPush hVarint hSkip hAuthBase)

/-- Default `2`-op-per-`bytes` (`maxOps = 4`) corollary from `hFallback`. -/
theorem e2b305_chunkedKeysUnsampled_merge_placed_tight_default_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOk A lim ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 305 (Rust.withPanics ext))
      (lsmpl.base 305) (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim))) :
    tlb_ChunkedKeysUnsampledMergePlacedTightOk A lim ext :=
  e2b305_chunkedKeysUnsampled_merge_placed_tight_of_fallback
    (Nat.le_refl 4) hVarint hAuthTight hFallback

/-- Default `2`-op-per-`bytes` (`maxOps = 4`) corollary from own-block callee contracts. -/
theorem e2b305_chunkedKeysUnsampled_merge_placed_tight_default_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOk A lim ext) :
    tlb_ChunkedKeysUnsampledMergePlacedTightOk A lim ext :=
  e2b305_chunkedKeysUnsampled_merge_placed_tight_of_contracts
    (Nat.le_refl 4) hFrom hPush hVarint hSkip hAuthBase hAuthTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB305PlacedBudget
