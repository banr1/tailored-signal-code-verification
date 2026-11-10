/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudget
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Guarded-Tight Placed Budget Proofs for `Unchunked.EkSentCt1Received::merge` & `Unchunked.Ct1Sent::merge` (Blocks `311`–`312`)

Proves `tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf` on Block `311` within
`SpqrTightEvs maxOps 42108 2560` (`authOps + 4 ≤ maxOps`, default `8 = 4 + 2 + 2` for `auth`, `dk`,
and `ct1`) and `tlb_UcCt1SentMergePlacedTightOkOf` on Block `312` within
`SpqrTightEvs maxOps 46102 2560` (`authOps + 6 ≤ maxOps`, default `10 = 4 + 2 + 2 + 2` for `auth`,
`hdr`, `es`, and `ct1`) under zero-initial-capacity guards on canonical wire inputs.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightU311PlacedBudgetR2

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_311 blkPC_312 blkPl_311 blkPl_312
   libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib ls_blockPlacement_base lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorAtStackLen decodeErrorHookStack keys_ls_subroutine_ok_of_block_cro reserveCap
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix bv32_zeroExtend_ofNat bytesMergeCapOk_zero
   decodeVarint_suffix key_shr32_of_lt key_wt_some sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost WppPost authMergeStack authenticatorPBCapAt setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.ProtoRepr
  (authenticatorPBAt ct1SentPBAt ekSentCt1ReceivedPBAt optAuthenticatorPBAt rustBytesVecAt
   unchunked4At unchunked5At)
open CryptoVerification.SpqrV1.Drop
  (optProtoAuthenticatorAt protoUnchunkedCt1SentAt protoUnchunkedEkSentCt1ReceivedAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost UnchunkedEkSentCt1ReceivedMergeGhost unchunkedMergeStack)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (HighCalleeSaved24 SepWPpLscro bv64_add_zero_u bv64_sub_zero_u bv_len_sub_limit
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto memRegion_40_split_5_cells
   optAuthenticatorPBCapAt optProtoAuthenticatorCapAt optProtoAuthenticatorCapAt_mono
   protoUnchunkedCt1SentCapAt protoUnchunkedEkSentCt1ReceivedCapAt stackAt_unchunkedMerge
   stackAt_unchunkedMergeStack_eq_own subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   unchunkedCt1SentPBCapAt unchunkedEkSentCt1ReceivedPBCapAt unchunkedMergeBelow
   unchunkedMergeBelow_bytesMerge3 unchunkedMergeBelow_bytesMerge3_entails
   unchunkedMergeBelow_eq_authMergeStack unchunkedMergeBelow_leaf unchunkedMergeBelow_leaf_entails
   unchunkedOwnStack vecU8Buf vecU8At_eq_header_sep_buf vecU8CapAt vecU8CapAt_mono_u
   withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs spqrAllocTightCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthDom tlb_AuthGuardedEnvOf tlb_AuthMergePlacedTightOkOf tlb_GuardedEnv
   tlb_UcCt1SentDom tlb_UcCt1SentGuardedEnvOf tlb_UcCt1SentMergePlacedTightOk
   tlb_UcCt1SentMergePlacedTightOkOf tlb_UcEkSentCt1ReceivedDom
   tlb_UcEkSentCt1ReceivedGuardedEnvOf tlb_UcEkSentCt1ReceivedMergePlacedTightOk
   tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf tlb_ValidUcCt1SentPB
   tlb_ValidUcEkSentCt1ReceivedPB tlb_authMergeTightSpecOfEnv tlb_authenticatorZeroCapAt
   tlb_domHeap tlb_domHeap_of_dom tlb_domHeap_of_not_dom tlb_fitsEnv_fallback_of_not_dom
   tlb_fitsEnv_guarded_of_dom tlb_guardedEnv_tight_of_dom tlb_lenPrefixed tlb_optAuthZeroCapAt
   tlb_ucCt1SentMergeTightSpecOfEnv tlb_ucCt1SentZeroCapAt
   tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv tlb_ucEkSentCt1ReceivedZeroCapAt
   tlb_vecU8ZeroCapAt)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergeEnv authMergeSpec authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
  (bytesMerge3RawSpec bytesMerge3RawSpec_eq_polyCommon)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (UnchunkedCt1SentMergeEnv UnchunkedEkSentCt1ReceivedMergeEnv
   decodeErrorPushMergeBudgetSpec unchunkedCt1SentMergePostEnv_imp_pre
   unchunkedCt1SentMergeSpec unchunkedCt1SentMergeSpecOfEnv
   unchunkedEkSentCt1ReceivedMergePostEnv_imp_pre
   unchunkedEkSentCt1ReceivedMergeSpec unchunkedEkSentCt1ReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some sepWPpLscro_of_ret_vm
   sepWPpLscro_of_vm sepWPpLscro_pure_elim vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
  (unchunkedCt1SentMergeOwnSpecOfEnv unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudget
  (unchunkedCt1SentMerge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedBudget
  (unchunkedEkSentCt1ReceivedMerge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux
  (unchunkedSavedRegs)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepClPlacedBudget
  (ekSentSavedRegs)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore doReserveClearEvents)

private theorem e2u311_sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem e2u311_pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem e2u311_status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem e2u311_pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem e2u311_trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem e2u311_readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem e2u311_readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem e2u311_readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem e2u311_calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero_u bv64_add_zero_u
attribute [local arm64_norm ↓, local wp_norm ↓]
  e2u311_sp_setMem_pre e2u311_pc_setMem_pre e2u311_status_setMem_pre e2u311_pstate_setMem_pre
  e2u311_trace_setMem_pre e2u311_readReg64_setMem_pre e2u311_readReg32_setMem_pre
  e2u311_readReg_setMem_pre e2u311_calleeSavedVRegs_setMem_pre

/-! ## 1. Cross-Block Transfer Helper -/

private theorem e2u311_ls_subroutine_ok_cro_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

/-! ## 2. Per-Field Bound Predicates & Parametric Canonical Domains -/

/-- Explicit per-field length bounds for `ProtoAuthenticator`. -/
def e2u311_ValidAuthPBOf (maxRoot maxMac : Nat) (m : ProtoAuthenticator) : Prop :=
  m.rootKey.length ≤ maxRoot ∧ m.macKey.length ≤ maxMac

/-- Explicit per-field length bounds for `Option ProtoAuthenticator`. -/
def e2u311_ValidOptAuthPBOf (maxRoot maxMac : Nat) (a : Option ProtoAuthenticator) : Prop :=
  ∀ v, a = some v → e2u311_ValidAuthPBOf maxRoot maxMac v

/-- Per-field length bounds for `V1State.Unchunked.EkSentCt1Received` (Block `311`),
definitionally equal to `tlb_ValidUcEkSentCt1ReceivedPB` at `(32, 32, 2400, 960)`. -/
def e2u311_ValidUcEkSentCt1ReceivedPBOf (maxRoot maxMac maxDk maxCt1 : Nat)
    (m : V1State.Unchunked.EkSentCt1Received) : Prop :=
  e2u311_ValidOptAuthPBOf maxRoot maxMac m.auth ∧
  m.dk.length ≤ maxDk ∧
  m.ct1.length ≤ maxCt1

/-- Per-field length bounds for `V1State.Unchunked.Ct1Sent` (Block `312`),
definitionally equal to `tlb_ValidUcCt1SentPB` at `(32, 32, 64, 2080, 960)`. -/
def e2u311_ValidUcCt1SentPBOf (maxRoot maxMac maxHdr maxEs maxCt1 : Nat)
    (m : V1State.Unchunked.Ct1Sent) : Prop :=
  e2u311_ValidOptAuthPBOf maxRoot maxMac m.auth ∧
  m.hdr.length ≤ maxHdr ∧
  m.es.length ≤ maxEs ∧
  m.ct1.length ≤ maxCt1

/-- Parametric canonical domain for `ProtoAuthenticator::merge` (Block `295`). -/
def e2u311_AuthDomOf (maxRoot maxMac : Nat) (x : AuthMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, e2u311_ValidAuthPBOf maxRoot maxMac pb ∧
      x.bs = tlb_lenPrefixed (ProtoAuthenticator.encodeRaw pb) rest

/-- Parametric canonical domain for `Unchunked.EkSentCt1Received::merge` (Block `311`). -/
def e2u311_UcEkSentCt1ReceivedDomOf (maxRoot maxMac maxDk maxCt1 : Nat)
    (x : UnchunkedEkSentCt1ReceivedMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, e2u311_ValidUcEkSentCt1ReceivedPBOf maxRoot maxMac maxDk maxCt1 pb ∧
      x.bs = tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw pb) rest

/-- Parametric canonical domain for `Unchunked.Ct1Sent::merge` (Block `312`). -/
def e2u311_UcCt1SentDomOf (maxRoot maxMac maxHdr maxEs maxCt1 : Nat)
    (x : UnchunkedCt1SentMergeGhost) : Prop :=
  codecWireTypeToProto x.wt = .lengthDelimited ∧ x.msg = default ∧
    ∃ pb rest, e2u311_ValidUcCt1SentPBOf maxRoot maxMac maxHdr maxEs maxCt1 pb ∧
      x.bs = tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw pb) rest

theorem e2u311_authDomOf_32_eq : e2u311_AuthDomOf 32 32 = tlb_AuthDom := rfl

theorem e2u311_validUcEkSentCt1ReceivedPBOf_default_eq :
    e2u311_ValidUcEkSentCt1ReceivedPBOf 32 32 2400 960 = tlb_ValidUcEkSentCt1ReceivedPB := rfl

theorem e2u311_ucEkSentCt1ReceivedDomOf_default_eq :
    e2u311_UcEkSentCt1ReceivedDomOf 32 32 2400 960 = tlb_UcEkSentCt1ReceivedDom := rfl

theorem e2u311_validUcCt1SentPBOf_default_eq :
    e2u311_ValidUcCt1SentPBOf 32 32 64 2080 960 = tlb_ValidUcCt1SentPB := rfl

theorem e2u311_ucCt1SentDomOf_default_eq :
    e2u311_UcCt1SentDomOf 32 32 64 2080 960 = tlb_UcCt1SentDom := rfl

/-! ## 3. Default-Init Zero-Capacity Helpers over `tlb_*ZeroCapAt` -/

theorem e2u311_pointsTo_zero_entails_vecU8ZeroCapAt (A : RustAlloc) (a ptr : BitVec 64)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      tlb_vecU8ZeroCapAt A a [] := by
  unfold tlb_vecU8ZeroCapAt
  refine Entails.trans ?_ (Entails.sepExists_right ptr (Entails.refl _))
  rw [vecU8At_eq_header_sep_buf, vecHeader]
  unfold vecU8Buf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
  have hp : ([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧
      (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by decide, by decide, hptr⟩
  exact Entails.pure_right hp (Entails.refl _)

/-- Niche-initialization cells for `Option<ProtoAuthenticator>::none → Some(default)` entail
`tlb_authenticatorZeroCapAt A a default`. -/
theorem e2u311_default_auth_cells_entails_zeroCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      tlb_authenticatorZeroCapAt A a default := by
  unfold tlb_authenticatorZeroCapAt
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗ tlb_vecU8ZeroCapAt A (a + 24#64) []
  have h1 := e2u311_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2u311_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 24#64) 1#64 (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 h2)

/-- Default `Option::none → Some(default)` initialization cells entail
`tlb_ucEkSentCt1ReceivedZeroCapAt A a default`. -/
theorem e2u311_default_ekSentCt1Received_entails_zeroCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 48#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 56#64) 40 ∗
      ((a + 96#64) ↦₆₄ 0#64) ⊢
      tlb_ucEkSentCt1ReceivedZeroCapAt A a default := by
  unfold tlb_ucEkSentCt1ReceivedZeroCapAt
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗ tlb_vecU8ZeroCapAt A (a + 24#64) [] ∗
    (((a + 48#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 48#64 + 8#64) 40) ∗
    ((a + 96#64) ↦₆₄ 0#64)
  have h1 := e2u311_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2u311_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 24#64) 1#64 (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by rw [BitVec.add_assoc]; rfl
  rw [h32, h40] at h2
  rw [h56]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

/-- Default `Option::none → Some(default)` initialization cells entail
`tlb_ucCt1SentZeroCapAt A a default`. -/
theorem e2u311_default_ct1Sent_entails_zeroCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 80#64) 40 ∗
      ((a + 120#64) ↦₆₄ 0#64) ⊢
      tlb_ucCt1SentZeroCapAt A a default := by
  unfold tlb_ucCt1SentZeroCapAt
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗ tlb_vecU8ZeroCapAt A (a + 24#64) [] ∗
    tlb_vecU8ZeroCapAt A (a + 48#64) [] ∗
    (((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 72#64 + 8#64) 40) ∗
    ((a + 120#64) ↦₆₄ 0#64)
  have h1 := e2u311_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2u311_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 24#64) 1#64 (by decide)
  have h3 := e2u311_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 48#64) 1#64 (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by rw [BitVec.add_assoc]; rfl
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by rw [BitVec.add_assoc]; rfl
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by rw [BitVec.add_assoc]; rfl
  rw [h32, h40] at h2
  rw [h56, h64] at h3
  rw [h80]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _))))

/-! ## 4. Domain-Parameterized Specs (Definitionally `tlb_*MergeTightSpecOfEnv` at Default Bounds) -/

/-- Domain-parameterized zero-cap-on-`Dom` contract for `ProtoAuthenticator::merge` (Block `295`);
definitionally `tlb_authMergeTightSpecOfEnv` when `Dom = tlb_AuthDom`. -/
noncomputable def e2u311_authMergeTightSpecDomOf {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (Dom : AuthMergeGhost → Prop)
    (PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop) :
    Spec (AuthMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      tlb_domHeap Dom
        (fun x => tlb_authenticatorZeroCapAt A.repAlloc x.msgPtr x.msg)
        (fun x => authenticatorPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg) x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp authMergeStack
  post := (authMergeSpecOfEnv A lim PreEnv PostEnv).post

/-- Domain-parameterized zero-cap-on-`Dom` contract for `Unchunked.EkSentCt1Received::merge`
(Block `311`); definitionally `tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv` when
`Dom = tlb_UcEkSentCt1ReceivedDom`. -/
noncomputable def e2u311_ucEkSentCt1ReceivedMergeTightSpecDomOf {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Dom : UnchunkedEkSentCt1ReceivedMergeGhost → Prop)
    (PreEnv PostEnv : UnchunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop) :
    Spec (UnchunkedEkSentCt1ReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      tlb_domHeap Dom
        (fun x => tlb_ucEkSentCt1ReceivedZeroCapAt A.repAlloc x.msgPtr x.msg)
        (fun x => unchunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg) x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedMergeStack
  post := (unchunkedEkSentCt1ReceivedMergeSpecOfEnv A lim PreEnv PostEnv).post

/-- Domain-parameterized zero-cap-on-`Dom` contract for `Unchunked.Ct1Sent::merge` (Block `312`);
definitionally `tlb_ucCt1SentMergeTightSpecOfEnv` when `Dom = tlb_UcCt1SentDom`. -/
noncomputable def e2u311_ucCt1SentMergeTightSpecDomOf {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Dom : UnchunkedCt1SentMergeGhost → Prop)
    (PreEnv PostEnv : UnchunkedCt1SentMergeGhost → List AllocEvent → Prop) :
    Spec (UnchunkedCt1SentMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      tlb_domHeap Dom
        (fun x => tlb_ucCt1SentZeroCapAt A.repAlloc x.msgPtr x.msg)
        (fun x => unchunkedCt1SentPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg) x ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedMergeStack
  post := (unchunkedCt1SentMergeSpecOfEnv A lim PreEnv PostEnv).post

theorem e2u311_authMergeTightSpecDomOf_default_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop) :
    e2u311_authMergeTightSpecDomOf A lim (e2u311_AuthDomOf 32 32) PreEnv PostEnv =
      tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv := rfl

theorem e2u311_ucEkSentCt1ReceivedMergeTightSpecDomOf_default_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : UnchunkedEkSentCt1ReceivedMergeGhost → List AllocEvent → Prop) :
    e2u311_ucEkSentCt1ReceivedMergeTightSpecDomOf A lim
      (e2u311_UcEkSentCt1ReceivedDomOf 32 32 2400 960) PreEnv PostEnv =
      tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv A lim PreEnv PostEnv := rfl

theorem e2u311_ucCt1SentMergeTightSpecDomOf_default_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : UnchunkedCt1SentMergeGhost → List AllocEvent → Prop) :
    e2u311_ucCt1SentMergeTightSpecDomOf A lim
      (e2u311_UcCt1SentDomOf 32 32 64 2080 960) PreEnv PostEnv =
      tlb_ucCt1SentMergeTightSpecOfEnv A lim PreEnv PostEnv := rfl

/-! ## 4b. Tight `BytesMerge`, Pool Accumulator, and Canonical `Proto` Round-Trip Helpers -/

private theorem e2u311_bytesMerge_zeroCap_tight
    (x : BytesMergeGhost) (v rest : List (BitVec 8)) (maxLen : Nat)
    (hwt : x.wt = .lengthDelimited)
    (hcap : x.valCap = 0#64)
    (hmb : mergeBytes .lengthDelimited x.bs = some (v, rest))
    (hv : v.length ≤ maxLen)
    {evs : List AllocEvent} (hevs : BytesMergeEnv x evs) :
    SpqrTightEvs 2 (2 * spqrAllocTightCost (Nat.max 8 maxLen)) (Nat.max 8 maxLen) evs := by
  unfold BytesMergeEnv at hevs
  subst hevs
  unfold bytesMergeEventsCore
  have hcap0 : x.valCap.toNat = 0 := by rw [hcap]; rfl
  simp only [hwt, hmb, hcap0]
  by_cases hv0 : v.length = 0
  · simp only [hv0, ↓reduceIte]
    exact SpqrTightEvs.nil _ _ _
  · have hnle : ¬ v.length ≤ 0 := by omega
    simp only [hv0, ↓reduceIte, doReserveClearEvents, hnle]
    let R := Nat.max 8 maxLen
    have hvR : v.length ≤ R := Nat.le_trans hv (Nat.le_max_right 8 maxLen)
    have hresR : reserveCap 0 0 v.length ≤ R := by
      have h8 : 8 ≤ R := Nat.le_max_left 8 maxLen
      dsimp [reserveCap]
      omega
    have h1 : SpqrTightEvs 1 (spqrAllocTightCost R) R (rustAllocEvents v.length 1) :=
      SpqrTightEvs.rustAlloc hvR (by decide)
    have h2 : SpqrTightEvs 1 (spqrAllocTightCost R) R
        (rustAllocEvents (reserveCap 0 0 v.length) 1) :=
      SpqrTightEvs.rustAlloc hresR (by decide)
    have h3 : SpqrTightEvs 0 0 0 (rustDeallocEvents v.length 1) :=
      SpqrTightEvs.rustDealloc v.length 1
    have h123 := (h1.append h2).append h3
    change SpqrTightEvs 2 (2 * spqrAllocTightCost R) R _
    refine h123.mono (by omega) (by omega) ?_
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.le_refl R, Nat.le_refl R⟩, Nat.zero_le R⟩

private theorem e2u311_fitsEnv_step_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {o₁ c₁ r₁ o₂ c₂ r₂ maxOps cumCap maxReq : Nat}
    {evs₁ : List AllocEvent} {E : List AllocEvent → Prop}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hevs₁ : SpqrTightEvs o₁ c₁ r₁ evs₁)
    (hE : ∀ evs₂, E evs₂ → SpqrTightEvs o₂ c₂ r₂ evs₂)
    (hOps : o₁ + o₂ ≤ maxOps) (hCum : c₁ + c₂ ≤ cumCap)
    (hReq : Nat.max r₁ r₂ ≤ maxReq) :
    FitsEnv M lim (M.stepEvents evs₁ st) E :=
  fun evs₂ h2 =>
    ((LibsignalBinary.Heap.fitsEvents_append M lim evs₁ evs₂ st).mp
      (hFit (evs₁ ++ evs₂) ((hevs₁.append (hE evs₂ h2)).mono hOps hCum hReq))).2

private def e2u311_tightPoolAt {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (ops cum req : Nat) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜SpqrTightEvs ops cum req evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem e2u311_pool_entails_tightPoolAt_zero {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ e2u311_tightPoolAt A lim st 0 0 0 s :=
  Entails.sepExists_right [] (Entails.pure_right (SpqrTightEvs.nil 0 0 0) (Entails.refl _))

private theorem e2u311_tightPoolAt_transport {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ops cum req : Nat)
    {s₁ s₂ : State} (hvm : VmPreserved s₁ s₂) :
    e2u311_tightPoolAt A lim st ops cum req s₁ = e2u311_tightPoolAt A lim st ops cum req s₂ := by
  unfold e2u311_tightPoolAt
  congr 1
  funext evs
  rw [A.pool_transport lim (M.stepEvents evs st) s₁ s₂ hvm]

private theorem e2u311_tightPoolAt_mono {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {o₁ c₁ r₁ o₂ c₂ r₂ : Nat}
    (hOps : o₁ ≤ o₂) (hCum : c₁ ≤ c₂) (hReq : r₁ ≤ r₂) (s : State) :
    e2u311_tightPoolAt A lim st o₁ c₁ r₁ s ⊢ e2u311_tightPoolAt A lim st o₂ c₂ r₂ s := by
  unfold e2u311_tightPoolAt
  refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
  exact Entails.sepExists_right evs
    (Entails.pure_right (hevs.mono hOps hCum hReq) (Entails.refl _))

private theorem e2u311_contByte_eq (v : BitVec 64) :
    (v.truncate 8 ||| 0x80#8) = (((v &&& 127) ||| 128).setWidth 8) := by
  ext i hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  · simp [BitVec.truncate_eq_setWidth]
  · simp [BitVec.truncate_eq_setWidth]
  · simp [BitVec.truncate_eq_setWidth]
  · simp [BitVec.truncate_eq_setWidth]
  · simp [BitVec.truncate_eq_setWidth]
  · simp [BitVec.truncate_eq_setWidth]
  · simp [BitVec.truncate_eq_setWidth]
  · simp [BitVec.truncate_eq_setWidth]
  · omega

private theorem e2u311_proto_encodeVarintAux_eq :
    ∀ (k : Nat) (v : BitVec 64), 0 < k → v.toNat < 2 ^ (7 * k) →
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux k v =
        CryptoVerification.LibsignalProtoCodec.encodeVarintAux k v
  | 0, _, hk, _ => absurd hk (Nat.lt_irrefl 0)
  | k + 1, v, _, hv => by
    have hlt_iff : (v < 0x80#64) ↔ v.toNat < 128 := BitVec.lt_def
    by_cases hlt : v.toNat < 128
    · have hlt' : v < 0x80#64 := hlt_iff.mpr hlt
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
        CryptoVerification.LibsignalProtoCodec.encodeVarintAux, hlt, hlt', ↓reduceIte,
        BitVec.truncate_eq_setWidth]
    · have hlt' : ¬ v < 0x80#64 := fun h => hlt (hlt_iff.mp h)
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exfalso; exact hlt hv
      · have hw' : (v >>> 7).toNat < 2 ^ (7 * k) := by
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
          apply Nat.div_lt_of_lt_mul
          have he : 7 * (k + 1) = 7 + 7 * k := by omega
          rw [he, Nat.pow_add] at hv
          exact hv
        simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
          CryptoVerification.LibsignalProtoCodec.encodeVarintAux, hlt, hlt', ↓reduceIte]
        rw [e2u311_contByte_eq, e2u311_proto_encodeVarintAux_eq k (v >>> 7) hk hw']

private theorem e2u311_proto_encodeVarint_eq (v : BitVec 64) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v =
      CryptoVerification.LibsignalProtoCodec.encodeVarint v :=
  e2u311_proto_encodeVarintAux_eq 10 v (by decide)
    (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) (by decide)))

private theorem e2u311_codec_decodeVarint_proto_encodeVarint
    (v : BitVec 64) (rest : List (BitVec 8)) :
    decodeVarint (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ rest) =
      some (v, rest) := by
  rw [e2u311_proto_encodeVarint_eq]
  exact CryptoVerification.LibsignalProtoCodec.decodeVarint_encodeVarint v rest

private theorem e2u311_proto_decodeVarint_encodeVarint
    (v : BitVec 64) (rest : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ rest) = .ok (v, rest) := by
  have h := CryptoVerification.SpqrV1.Prost.BytesMerge.proto_decodeVarint_toOption
    (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ rest)
  rw [e2u311_codec_decodeVarint_proto_encodeVarint] at h
  cases hd : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ rest) <;>
    simp [hd, Except.toOption] at h
  exact congrArg Except.ok h

private theorem e2u311_proto_encodeVarint_pos (v : BitVec 64) :
    0 < (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v).length := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
    CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux
  split <;> simp

private theorem e2u311_takeExact_append :
    ∀ (xs ys : List (BitVec 8)),
      CryptoVerification.LibsignalSpqrV1.Proto.takeExact xs.length (xs ++ ys) = .ok (xs, ys)
  | [], ys => rfl
  | x :: xs, ys => by
    simp only [List.length_cons, List.cons_append,
      CryptoVerification.LibsignalSpqrV1.Proto.takeExact, e2u311_takeExact_append xs ys,
      bind, Except.bind]

private theorem e2u311_codec_mergeBytes_lenPrefixed
    (v rest : List (BitVec 8)) (hv : v.length < 2 ^ 64) :
    mergeBytes .lengthDelimited (tlb_lenPrefixed v rest) = some (v, rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc, e2u311_proto_encodeVarint_eq]
  exact CryptoVerification.LibsignalProtoCodec.mergeBytes_encode v rest hv

private theorem e2u311_proto_mergeBytes_lenPrefixed
    (v rest : List (BitVec 8)) (hv : v.length < 2 ^ 64) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited
        (tlb_lenPrefixed v rest) = .ok (v, rest) := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes
    CryptoVerification.LibsignalSpqrV1.Proto.checkWireType tlb_lenPrefixed
  rw [List.append_assoc]
  have hl : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    e2u311_proto_decodeVarint_encodeVarint, bind, Except.bind, hl, e2u311_takeExact_append]

private theorem e2u311_lenPrefixed_sub_lt {raw after : List (BitVec 8)} {B : Nat}
    (h : (tlb_lenPrefixed raw after).length < B) :
    raw.length < B ∧ after.length < B ∧ 0 < B := by
  have hp := e2u311_proto_encodeVarint_pos (BitVec.ofNat 64 raw.length)
  unfold tlb_lenPrefixed at h
  simp only [List.length_append] at h
  exact ⟨by omega, by omega, by omega⟩

private theorem e2u311_bytesField_len_lt {tag : BitVec 32} {v : List (BitVec 8)} {B : Nat}
    (h0 : 0 < B)
    (h : (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField tag v).length < B) :
    v.length < B := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond at h
  by_cases he : v.isEmpty = true
  · rw [List.isEmpty_iff.mp he]; exact h0
  · simp only [he, Bool.false_eq_true, ↓reduceIte, List.length_append] at h
    omega

private def e2u311_LoopsTo {M : Type}
    (mf : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      List (BitVec 8) → Nat →
      Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (M × List (BitVec 8)))
    (depth : Nat) (m : M) (bs : List (BitVec 8)) (r : M) : Prop :=
  ∀ fuel, bs.length ≤ fuel →
    CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop mf fuel m bs depth = .ok r

private theorem e2u311_loopsTo_nil {M : Type}
    (mf : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      List (BitVec 8) → Nat →
      Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (M × List (BitVec 8)))
    (depth : Nat) (m : M) :
    e2u311_LoopsTo mf depth m [] m := by
  intro fuel _
  cases fuel <;> rfl

private theorem e2u311_loopsTo_cons {M : Type}
    {mf : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      List (BitVec 8) → Nat →
      Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (M × List (BitVec 8))}
    {depth : Nat} {m m' r : M} {b : BitVec 8} {tag : BitVec 32}
    {wt : CryptoVerification.LibsignalSpqrV1.Proto.WireType}
    {body tail : List (BitVec 8)}
    (hkey : CryptoVerification.LibsignalSpqrV1.Proto.decodeKey (b :: (body ++ tail)) =
      .ok ((tag, wt), body ++ tail))
    (hmf : mf m tag wt (body ++ tail) depth = .ok (m', tail))
    (hcont : e2u311_LoopsTo mf depth m' tail r) :
    e2u311_LoopsTo mf depth m ((b :: body) ++ tail) r := by
  intro fuel hfuel
  rcases fuel with _ | fuel'
  · simp at hfuel
  · rw [List.cons_append] at hfuel ⊢
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.mergeFieldsLoop, hkey, bind,
      Except.bind, hmf]
    have htail : tail.length ≤ fuel' := by
      simp only [List.length_cons, List.length_append] at hfuel
      omega
    exact hcont fuel' htail

private theorem e2u311_mergeMessage_of_loopsTo {M : Type}
    {mf : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      List (BitVec 8) → Nat →
      Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (M × List (BitVec 8))}
    {depth : Nat} {m r : M} {raw after : List (BitVec 8)}
    (hraw : raw.length < 2 ^ 64)
    (hloop : e2u311_LoopsTo mf depth m raw r) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage mf .lengthDelimited m
        (tlb_lenPrefixed raw after) (depth + 1) = .ok (r, after) := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
    CryptoVerification.LibsignalSpqrV1.Proto.checkWireType tlb_lenPrefixed
  rw [List.append_assoc]
  have hl : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    e2u311_proto_decodeVarint_encodeVarint, bind, Except.bind, hl,
    e2u311_takeExact_append, hloop raw.length (Nat.le_refl _)]

private theorem e2u311_loopsTo_bytesField {M : Type}
    {mf : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      List (BitVec 8) → Nat →
      Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (M × List (BitVec 8))}
    {depth : Nat} {m m' r : M} {tag : BitVec 32} {keyByte : BitVec 8}
    {v tail : List (BitVec 8)}
    (hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey tag .lengthDelimited = [keyByte])
    (hdkey : ∀ s, CryptoVerification.LibsignalSpqrV1.Proto.decodeKey (keyByte :: s) =
      .ok ((tag, .lengthDelimited), s))
    (hnil : v = [] → m' = m)
    (hv_lt : v.length < 2 ^ 64)
    (hmf : ∀ s, mf m tag .lengthDelimited s depth =
      (do let (x, bs') ← CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited s
          if x = v then .ok (m', bs') else mf m tag .lengthDelimited s depth))
    (hcont : e2u311_LoopsTo mf depth m' tail r) :
    e2u311_LoopsTo mf depth m
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField tag v ++ tail) r := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond
  by_cases hv0 : v.isEmpty = true
  · simp only [hv0, ↓reduceIte, List.nil_append]
    rw [← hnil (List.isEmpty_iff.mp hv0)]
    exact hcont
  · simp only [hv0, Bool.false_eq_true, ↓reduceIte]
    rw [hk]
    change e2u311_LoopsTo mf depth m
      ((keyByte :: (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
        (BitVec.ofNat 64 v.length) ++ v)) ++ tail) r
    refine e2u311_loopsTo_cons (tag := tag) (wt := .lengthDelimited) (hdkey _) ?_ hcont
    rw [hmf]
    change (do
        let (x, bs') ← CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes
          .lengthDelimited (tlb_lenPrefixed v tail)
        if x = v then .ok (m', bs') else mf m tag .lengthDelimited (tlb_lenPrefixed v tail) depth) =
      .ok (m', tail)
    simp only [e2u311_proto_mergeBytes_lenPrefixed v tail hv_lt, bind, Except.bind, ↓reduceIte]

private theorem e2u311_protoAuth_mergeMessage_roundtrip
    (a : ProtoAuthenticator) (after : List (BitVec 8)) (d : Nat)
    (hraw : (ProtoAuthenticator.encodeRaw a).length < 2 ^ 64) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage ProtoAuthenticator.mergeField
        .lengthDelimited default (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) after)
        (d + 1) = .ok (a, after) := by
  have hraw0 : 0 < (2 ^ 64 : Nat) := by decide
  have hsplit : (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 1#32 a.rootKey).length +
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 2#32 a.macKey).length < 2 ^ 64 := by
    simpa [ProtoAuthenticator.encodeRaw, List.length_append] using hraw
  have hrk : a.rootKey.length < 2 ^ 64 :=
    e2u311_bytesField_len_lt (tag := 1#32) hraw0
      (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hsplit)
  have hmk : a.macKey.length < 2 ^ 64 :=
    e2u311_bytesField_len_lt (tag := 2#32) hraw0
      (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hsplit)
  refine e2u311_mergeMessage_of_loopsTo hraw ?_
  unfold ProtoAuthenticator.encodeRaw
  refine e2u311_loopsTo_bytesField (tag := 1#32)
    (m' := { rootKey := a.rootKey, macKey := [] })
    (keyByte := 0x0a#8) rfl (fun _ => rfl)
    (fun hn => by rw [hn]; rfl) hrk
    (fun s => by
      simp only [ProtoAuthenticator.mergeField, beq_self_eq_true, ↓reduceIte]
      rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited s with _ | ⟨x, bs'⟩
      · rfl
      · simp only [bind, Except.bind]
        split
        · rename_i hx; rw [hx]; rfl
        · rfl) ?_
  simpa only [List.append_nil] using
    e2u311_loopsTo_bytesField (tag := 2#32) (m' := a) (tail := [])
      (keyByte := 0x12#8) rfl (fun _ => rfl)
      (fun hn => by cases a; dsimp only at hn; subst hn; rfl) hmk
      (fun s => by
        simp only [ProtoAuthenticator.mergeField, show (2#32 == 1#32) = false from rfl,
          beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
        rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited s with _ | ⟨x, bs'⟩
        · rfl
        · simp only [bind, Except.bind]
          split
          · rename_i hx; cases a; rw [hx]
          · rfl)
      (e2u311_loopsTo_nil _ _ _)

private theorem e2u311_loopsTo_uint64_tag1 {M : Type}
    {mf : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      List (BitVec 8) → Nat →
      Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (M × List (BitVec 8))}
    {depth : Nat} {m m' r : M} {v : BitVec 64} {tail : List (BitVec 8)}
    (hz : v = 0#64 → m' = m)
    (hmf : ∀ s, mf m 1#32 .varint s depth =
      (do let (x, bs') ← CryptoVerification.LibsignalSpqrV1.Proto.mergeUint64 .varint s
          if x = v then .ok (m', bs') else mf m 1#32 .varint s depth))
    (hcont : e2u311_LoopsTo mf depth m' tail r) :
    e2u311_LoopsTo mf depth m
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 v ++ tail) r := by
  unfold CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field
  by_cases hv0 : (v == 0#64) = true
  · simp only [hv0, ↓reduceIte, List.nil_append]
    rw [← hz (eq_of_beq hv0)]
    exact hcont
  · simp only [hv0, Bool.false_eq_true, ↓reduceIte]
    have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .varint = [0x08#8] := rfl
    rw [hk]
    change e2u311_LoopsTo mf depth m
      ((0x08#8 :: CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v) ++ tail) r
    refine e2u311_loopsTo_cons (tag := 1#32) (wt := .varint) rfl ?_ hcont
    rw [hmf]
    unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeUint64
      CryptoVerification.LibsignalSpqrV1.Proto.checkWireType
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      e2u311_proto_decodeVarint_encodeVarint, bind, Except.bind]

private theorem e2u311_loopsTo_optAuth_tag2 {M : Type}
    {mf : M → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      List (BitVec 8) → Nat →
      Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (M × List (BitVec 8))}
    {d : Nat} {m m' r : M} {opt : Option ProtoAuthenticator} {tail : List (BitVec 8)}
    (hnone : opt = none → m' = m)
    (hraw : ∀ a, opt = some a → (ProtoAuthenticator.encodeRaw a).length < 2 ^ 64)
    (hmf : ∀ a s, opt = some a →
      mf m 2#32 .lengthDelimited s (d + 1) =
        (do let (v, bs') ← CryptoVerification.LibsignalSpqrV1.Proto.mergeOptMessage
              ProtoAuthenticator.mergeField .lengthDelimited none s (d + 1)
            if v = some a then .ok (m', bs') else mf m 2#32 .lengthDelimited s (d + 1)))
    (hcont : e2u311_LoopsTo mf (d + 1) m' tail r) :
    e2u311_LoopsTo mf (d + 1) m
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw
        2#32 opt ++ tail) r := by
  cases opt with
  | none =>
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
    rw [← hnone rfl]
    exact hcont
  | some a =>
    have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := rfl
    have hcons :
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          ProtoAuthenticator.encodeRaw 2#32 (some a)) ++ tail =
        0x12#8 :: tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) tail := by
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk,
        e2u311_proto_encodeVarint_eq, tlb_lenPrefixed,
        List.cons_append, List.nil_append, List.append_assoc]
    rw [hcons]
    refine e2u311_loopsTo_cons (tag := 2#32) (wt := .lengthDelimited) rfl ?_ hcont
    rw [hmf a _ rfl]
    unfold CryptoVerification.LibsignalSpqrV1.Proto.mergeOptMessage
    have hrt := e2u311_protoAuth_mergeMessage_roundtrip a tail d (hraw a rfl)
    unfold tlb_lenPrefixed at hrt
    simp only [Option.getD, hrt, bind, Except.bind, ↓reduceIte]

private theorem e2u311_optAuth_encode_sub_lt {opt : Option ProtoAuthenticator} {B : Nat}
    (h : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw
      2#32 opt).length < B) :
    ∀ a, opt = some a → (ProtoAuthenticator.encodeRaw a).length < B := by
  rintro a rfl
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, List.length_append] at h
  omega

private theorem e2u311_ekSentCt1Received_mergeMessage_roundtrip
    (pb : V1State.Unchunked.EkSentCt1Received) (after : List (BitVec 8))
    (hbs : (tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw pb) after).length <
      2 ^ 64) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
        V1State.Unchunked.EkSentCt1Received.mergeField .lengthDelimited default
        (tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw pb) after) 98 =
      .ok (pb, after) := by
  have ⟨hraw, _, h0⟩ := e2u311_lenPrefixed_sub_lt hbs
  have hsum :
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 pb.epoch).length +
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw
        2#32 pb.auth).length +
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 pb.dk).length +
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 pb.ct1).length <
        2 ^ 64 := by
    simpa [V1State.Unchunked.EkSentCt1Received.encodeRaw, List.length_append, Nat.add_assoc]
      using hraw
  have hauth_lt : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      ProtoAuthenticator.encodeRaw 2#32 pb.auth).length < 2 ^ 64 := by
    revert hsum; generalize (2 ^ 64 : Nat) = B; omega
  have hdk_lt : pb.dk.length < 2 ^ 64 :=
    e2u311_bytesField_len_lt (tag := 3#32) h0 (by revert hsum; generalize (2 ^ 64 : Nat) = B; omega)
  have hct1_lt : pb.ct1.length < 2 ^ 64 :=
    e2u311_bytesField_len_lt (tag := 4#32) h0 (by revert hsum; generalize (2 ^ 64 : Nat) = B; omega)
  refine e2u311_mergeMessage_of_loopsTo (depth := 97) hraw ?_
  unfold V1State.Unchunked.EkSentCt1Received.encodeRaw
  simp only [List.append_assoc]
  refine e2u311_loopsTo_uint64_tag1
    (m' := { epoch := pb.epoch, auth := none, dk := [], ct1 := [] })
    (fun hz => by rw [hz]; rfl)
    (fun s => by
      simp only [V1State.Unchunked.EkSentCt1Received.mergeField, beq_self_eq_true, ↓reduceIte]
      rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeUint64 .varint s with _ | ⟨x, bs'⟩
      · rfl
      · simp only [bind, Except.bind]
        split
        · rename_i hx; rw [hx]; rfl
        · rfl) ?_
  refine e2u311_loopsTo_optAuth_tag2 (d := 96)
    (m' := { epoch := pb.epoch, auth := pb.auth, dk := [], ct1 := [] })
    (fun hn => by rw [hn])
    (e2u311_optAuth_encode_sub_lt hauth_lt)
    (fun a s ha => by
      simp only [V1State.Unchunked.EkSentCt1Received.mergeField,
        show (2#32 == 1#32) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeOptMessage
          ProtoAuthenticator.mergeField .lengthDelimited none s 97 with _ | ⟨v, bs'⟩
      · rfl
      · simp only [bind, Except.bind]
        split
        · rename_i hv; rw [hv, ha]
        · rfl) ?_
  refine e2u311_loopsTo_bytesField (tag := 3#32)
    (m' := { epoch := pb.epoch, auth := pb.auth, dk := pb.dk, ct1 := [] })
    (keyByte := 0x1a#8) rfl (fun _ => rfl)
    (fun hn => by rw [hn]) hdk_lt
    (fun s => by
      simp only [V1State.Unchunked.EkSentCt1Received.mergeField,
        show (3#32 == 1#32) = false from rfl, show (3#32 == 2#32) = false from rfl,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited s with _ | ⟨x, bs'⟩
      · rfl
      · simp only [bind, Except.bind]
        split
        · rename_i hx; rw [hx]
        · rfl) ?_
  simpa only [List.append_nil] using
    e2u311_loopsTo_bytesField (tag := 4#32) (m' := pb) (tail := [])
      (keyByte := 0x22#8) rfl (fun _ => rfl)
      (fun hn => by cases pb; dsimp only at hn; subst hn; rfl) hct1_lt
      (fun s => by
        simp only [V1State.Unchunked.EkSentCt1Received.mergeField,
          show (4#32 == 1#32) = false from rfl, show (4#32 == 2#32) = false from rfl,
          show (4#32 == 3#32) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
        rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited s with _ | ⟨x, bs'⟩
        · rfl
        · simp only [bind, Except.bind]
          split
          · rename_i hx; cases pb; rw [hx]
          · rfl)
      (e2u311_loopsTo_nil _ _ _)

private theorem e2u311_ct1Sent_mergeMessage_roundtrip
    (pb : V1State.Unchunked.Ct1Sent) (after : List (BitVec 8))
    (hbs : (tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw pb) after).length < 2 ^ 64) :
    CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage
        V1State.Unchunked.Ct1Sent.mergeField .lengthDelimited default
        (tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw pb) after) 98 =
      .ok (pb, after) := by
  have ⟨hraw, _, h0⟩ := e2u311_lenPrefixed_sub_lt hbs
  have hsum :
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 pb.epoch).length +
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw
        2#32 pb.auth).length +
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 pb.hdr).length +
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 pb.es).length +
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 pb.ct1).length <
        2 ^ 64 := by
    simpa [V1State.Unchunked.Ct1Sent.encodeRaw, List.length_append, Nat.add_assoc]
      using hraw
  have hauth_lt : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      ProtoAuthenticator.encodeRaw 2#32 pb.auth).length < 2 ^ 64 := by
    revert hsum; generalize (2 ^ 64 : Nat) = B; omega
  have hhdr_lt : pb.hdr.length < 2 ^ 64 :=
    e2u311_bytesField_len_lt (tag := 3#32) h0 (by revert hsum; generalize (2 ^ 64 : Nat) = B; omega)
  have hes_lt : pb.es.length < 2 ^ 64 :=
    e2u311_bytesField_len_lt (tag := 4#32) h0 (by revert hsum; generalize (2 ^ 64 : Nat) = B; omega)
  have hct1_lt : pb.ct1.length < 2 ^ 64 :=
    e2u311_bytesField_len_lt (tag := 5#32) h0 (by revert hsum; generalize (2 ^ 64 : Nat) = B; omega)
  refine e2u311_mergeMessage_of_loopsTo (depth := 97) hraw ?_
  unfold V1State.Unchunked.Ct1Sent.encodeRaw
  simp only [List.append_assoc]
  refine e2u311_loopsTo_uint64_tag1
    (m' := { epoch := pb.epoch, auth := none, hdr := [], es := [], ct1 := [] })
    (fun hz => by rw [hz]; rfl)
    (fun s => by
      simp only [V1State.Unchunked.Ct1Sent.mergeField, beq_self_eq_true, ↓reduceIte]
      rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeUint64 .varint s with _ | ⟨x, bs'⟩
      · rfl
      · simp only [bind, Except.bind]
        split
        · rename_i hx; rw [hx]; rfl
        · rfl) ?_
  refine e2u311_loopsTo_optAuth_tag2 (d := 96)
    (m' := { epoch := pb.epoch, auth := pb.auth, hdr := [], es := [], ct1 := [] })
    (fun hn => by rw [hn])
    (e2u311_optAuth_encode_sub_lt hauth_lt)
    (fun a s ha => by
      simp only [V1State.Unchunked.Ct1Sent.mergeField,
        show (2#32 == 1#32) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeOptMessage
          ProtoAuthenticator.mergeField .lengthDelimited none s 97 with _ | ⟨v, bs'⟩
      · rfl
      · simp only [bind, Except.bind]
        split
        · rename_i hv; rw [hv, ha]
        · rfl) ?_
  refine e2u311_loopsTo_bytesField (tag := 3#32)
    (m' := { epoch := pb.epoch, auth := pb.auth, hdr := pb.hdr, es := [], ct1 := [] })
    (keyByte := 0x1a#8) rfl (fun _ => rfl)
    (fun hn => by rw [hn]) hhdr_lt
    (fun s => by
      simp only [V1State.Unchunked.Ct1Sent.mergeField,
        show (3#32 == 1#32) = false from rfl, show (3#32 == 2#32) = false from rfl,
        beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited s with _ | ⟨x, bs'⟩
      · rfl
      · simp only [bind, Except.bind]
        split
        · rename_i hx; rw [hx]
        · rfl) ?_
  refine e2u311_loopsTo_bytesField (tag := 4#32)
    (m' := { epoch := pb.epoch, auth := pb.auth, hdr := pb.hdr, es := pb.es, ct1 := [] })
    (keyByte := 0x22#8) rfl (fun _ => rfl)
    (fun hn => by rw [hn]) hes_lt
    (fun s => by
      simp only [V1State.Unchunked.Ct1Sent.mergeField,
        show (4#32 == 1#32) = false from rfl, show (4#32 == 2#32) = false from rfl,
        show (4#32 == 3#32) = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
      rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited s with _ | ⟨x, bs'⟩
      · rfl
      · simp only [bind, Except.bind]
        split
        · rename_i hx; rw [hx]
        · rfl) ?_
  simpa only [List.append_nil] using
    e2u311_loopsTo_bytesField (tag := 5#32) (m' := pb) (tail := [])
      (keyByte := 0x2a#8) rfl (fun _ => rfl)
      (fun hn => by cases pb; dsimp only at hn; subst hn; rfl) hct1_lt
      (fun s => by
        simp only [V1State.Unchunked.Ct1Sent.mergeField,
          show (5#32 == 1#32) = false from rfl, show (5#32 == 2#32) = false from rfl,
          show (5#32 == 3#32) = false from rfl, show (5#32 == 4#32) = false from rfl,
          beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
        rcases CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes .lengthDelimited s with _ | ⟨x, bs'⟩
        · rfl
        · simp only [bind, Except.bind]
          split
          · rename_i hx; cases pb; rw [hx]
          · rfl)
      (e2u311_loopsTo_nil _ _ _)

/-! ## 4c. Block `311` (`EkSentCt1Received::merge`) Canonical-`Dom` Tight Proofs -/

private theorem e2u311_stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem e2u311_wt_eq_lengthDelimited {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) : wt = .lengthDelimited := by
  cases wt <;> first | rfl | cases h

private theorem e2u311_isDropSuffix_of_append {xs pre ys : List (BitVec 8)}
    (h : xs = pre ++ ys) : IsDropSuffix xs ys := by
  subst h
  unfold IsDropSuffix
  have hl : (pre ++ ys).length - ys.length = pre.length := by
    rw [List.length_append]; omega
  rw [hl, List.drop_left]

private theorem e2u311_decodeVarint2Env_tight_of_some {bs : List (BitVec 8)} {v : BitVec 64}
    {rest : List (BitVec 8)} (hdv : decodeVarint bs = some (v, rest)) :
    ∀ evs, DecodeVarint2Env bs evs → SpqrTightEvs 0 0 0 evs := by
  intro evs h
  rw [decodeVarint2Env_eq_nil_of_some hdv h]
  exact SpqrTightEvs.nil 0 0 0

private theorem e2u311_tightPoolAt_nil_step {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {o c r : Nat} {bs rest : List (BitVec 8)} {v : BitVec 64}
    {evs evs_v : List AllocEvent} (sm : State)
    (hdv : decodeVarint bs = some (v, rest))
    (hevs : SpqrTightEvs o c r evs) (hevs_v : DecodeVarint2Env bs evs_v) :
    A.pool lim (M.stepEvents evs_v (M.stepEvents evs st)) sm ⊢
      e2u311_tightPoolAt A lim st o c r sm := by
  rw [decodeVarint2Env_eq_nil_of_some hdv hevs_v, M.stepEvents_nil]
  exact Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem e2u311_tightPoolAt_append_step {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {o₁ c₁ r₁ o₂ c₂ r₂ o₃ c₃ r₃ : Nat} {evs₁ evs₂ : List AllocEvent} (sm : State)
    (hevs₁ : SpqrTightEvs o₁ c₁ r₁ evs₁)
    (hevs₂ : SpqrTightEvs o₂ c₂ r₂ evs₂)
    (hO : o₁ + o₂ ≤ o₃) (hC : c₁ + c₂ ≤ c₃) (hR : Nat.max r₁ r₂ ≤ r₃) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) sm ⊢
      e2u311_tightPoolAt A lim st o₃ c₃ r₃ sm := by
  rw [← M.stepEvents_append evs₁ evs₂ st]
  exact Entails.sepExists_right (evs₁ ++ evs₂)
    (Entails.pure_right ((hevs₁.append hevs₂).mono hO hC hR) (Entails.refl _))

private theorem e2u311_vecU8ZeroCapAt_entails_vecU8CapAt (A : RustAlloc) (p : BitVec 64)
    (bound : Nat) (bs : List (BitVec 8)) :
    tlb_vecU8ZeroCapAt A p bs ⊢ vecU8CapAt A p bound bs := by
  unfold tlb_vecU8ZeroCapAt vecU8CapAt
  refine Entails.sepExists_elim fun ptr => ?_
  exact Entails.sepExists_right 0#64
    (Entails.sepExists_right ptr
      (Entails.pure_right bytesMergeCapOk_zero (Entails.refl _)))

private theorem e2u311_niche_none_entails_optAuthCapAt (A : RustAlloc) (a : BitVec 64)
    (bound : Nat) :
    ((a ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 8#64) 40) ⊢
      optProtoAuthenticatorCapAt A a bound none := by
  unfold optProtoAuthenticatorCapAt
  exact Entails.refl _

private def e2u311_ekSentDomLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (o c r : Nat) (s0 s : State)
    (Hmsg : SepProp) (bufRef slot ptr : BitVec 64) (bs cur : List (BitVec 8)) : SepProp :=
  e2u311_tightPoolAt A lim st o c r s ∗
    Hmsg ∗
    (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 112#64) 48 ∗
    ekSentSavedRegs s0.sp s0 ∗
    unchunkedMergeBelow s0.sp

private theorem e2u311_ekSentDomLoopPre_transport {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (o c r : Nat) (s0 : State)
    {s₁ s₂ : State} (hvm : VmPreserved s₁ s₂)
    (Hmsg : SepProp) (bufRef slot ptr : BitVec 64) (bs cur : List (BitVec 8)) :
    e2u311_ekSentDomLoopPre A lim st o c r s0 s₁ Hmsg bufRef slot ptr bs cur =
      e2u311_ekSentDomLoopPre A lim st o c r s0 s₂ Hmsg bufRef slot ptr bs cur := by
  unfold e2u311_ekSentDomLoopPre
  rw [e2u311_tightPoolAt_transport A lim st o c r hvm]

private noncomputable def e2u311_ekSentDomOwnSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Dom : UnchunkedEkSentCt1ReceivedMergeGhost → Prop)
    (maxOps cumCap maxReq : Nat) :
    Spec (UnchunkedEkSentCt1ReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      Dom x ∧
      FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)⌝ ∗
      tlb_ucEkSentCt1ReceivedZeroCapAt A.repAlloc x.msgPtr x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedOwnStack
  post := (unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv A lim
    (fun _ => SpqrTightEvs maxOps cumCap maxReq)
    (tlb_GuardedEnv Dom (SpqrTightEvs maxOps cumCap maxReq) UnchunkedEkSentCt1ReceivedMergeEnv)).post

private theorem e2u311_ekSent_ok_exit_dom_entails {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {Dom : UnchunkedEkSentCt1ReceivedMergeGhost → Prop}
    {maxOps cumCap maxReq : Nat}
    (x : UnchunkedEkSentCt1ReceivedMergeGhost) (hDom : Dom x)
    (s0 s sf : State) (m : V1State.Unchunked.EkSentCt1Received) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hsome : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps cumCap maxReq evs) :
    stackAt s0.sp unchunkedOwnStack ∗
      (protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (e2u311_ekSentDomOwnSpec A lim Dom maxOps cumCap maxReq).post (x, st) s0 sf := by
  dsimp only [e2u311_ekSentDomOwnSpec, unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv]
  rw [hsome, htr, hx0, ← A.pool_transport lim (M.stepEvents evs st) s sf hvm]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp unchunkedOwnStack ∗
      (protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) sf))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) sf ∗
        (stackAt s0.sp unchunkedOwnStack ∗
          (protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono
    (Entails.sepExists_right evs (Entails.pure_right (Or.inl ⟨hDom, hevs⟩) (Entails.refl _)))
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

private theorem e2u311_ekSent_exit_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Dom : UnchunkedEkSentCt1ReceivedMergeGhost → Prop}
    {maxOps cumCap maxReq : Nat}
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {after : List (BitVec 8)}
    (hDom : Dom x)
    (hsome : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, after))
    (_hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hafter_le : after.length ≤ x.bs.length)
    (hafter_suf : IsDropSuffix x.bs after)
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 after.length)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ekSentDomLoopPre A lim st maxOps cumCap maxReq s0 s
        (protoUnchunkedEkSentCt1ReceivedCapAt A.repAlloc x.msgPtr after.length m)
        x.bufRef x.slot x.ptr x.bs after)
      (WppPost (e2u311_ekSentDomOwnSpec A lim Dom maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - after.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : after.length = after.length)
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2u311_ekSentDomLoopPre, e2u311_tightPoolAt,
      sliceCursorAfter_eq_split hafter_le hafter_suf, sliceCursorAt, ekSentSavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm, arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepBudgetAux.stackAt_unchunkedMerge_epilogue s0.sp s0)
      (by unfold ekSentSavedRegs; sep_focus)
    have hcur_fold :
        (x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 after.length) ∗
          (x.ptr ↦ₛ x.bs.take (x.bs.length - after.length)) ∗ (curPtr ↦ₛ after) ⊢
        sliceCursorAfter x.slot x.ptr x.bs after := by
      rw [sliceCursorAfter_eq_split hafter_le hafter_suf, sliceCursorAt]
      exact Entails.of_eq (by dsimp only [curPtr]; sep_ac_rfl)
    apply SepWP.fold hcur_fold (by dsimp only [curPtr]; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx24, hx25, hx26, hx27, hx28, hvregs]⟩
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (e2u311_ekSent_ok_exit_dom_entails A lim st x hDom s0 s _ m after evs hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2u311_ekSent_decode_key_dom_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {Q : State → SepProp → Prop} {R Hmsg : SepProp}
    {o c r maxOps cumCap maxReq limit : Nat}
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {s0 s : State}
    {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hO : o ≤ maxOps) (hC : c ≤ cumCap) (hR : r ≤ maxReq)
    (hgt_lim : ¬ cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_ge : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag0 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_311).base + 204#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ekSentDomLoopPre A lim st o c r s0 s' Hmsg x.bufRef x.slot x.ptr x.bs rest)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ekSentDomLoopPre A lim st o c r s0 s Hmsg x.bufRef x.slot x.ptr x.bs cur)
      Q (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2u311_ekSentDomLoopPre, e2u311_tightPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, unchunkedMergeBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := (blkPl_311).base + 172#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2u311_stackAt_decodeVarint2_raw_eq,
              arm64_norm, wp_norm, hsp, hx19])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19],
        hcur_lt,
        e2u311_fitsEnv_step_tight hFit hevs (e2u311_decodeVarint2Env_tight_of_some hd)
          hO hC (Nat.max_le.mpr ⟨hR, Nat.zero_le _⟩)⟩)
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
    have hshr := key_shr32_of_lt hk_ge
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
    have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
      omega
    apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 204#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        e2u311_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (e2u311_tightPoolAt_nil_step (o := o) (c := c) (r := r) A lim st sm hd hevs hevs_v) (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [e2u311_tightPoolAt_transport A lim st o c r hvm2]
      refine SepWPpLscro.weaken_pre ?_
        (hcont _
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
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
      dsimp only [e2u311_ekSentDomLoopPre]; sep_entail

private theorem e2u311_ekSent_field1_epoch_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {Q : State → SepProp → Prop} {R Hrest : SepProp}
    {maxOps cumCap maxReq limit : Nat}
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {s0 s : State}
    {epoch : BitVec 64} {pre tail : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_tail : limit ≤ tail.length)
    (hbs_split : x.bs = pre ++ (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ekSentDomLoopPre A lim st 0 0 0 s0 s'
          (Hrest ∗ ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
          x.bufRef x.slot x.ptr x.bs tail)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ekSentDomLoopPre A lim st 0 0 0 s0 s
        (Hrest ∗ ((x.msgPtr + 0x60#64) ↦₆₄ 0#64))
        x.bufRef x.slot x.ptr x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ tail))
      Q (WppPanicFalse R) := by
  by_cases hv0 : (epoch == 0#64) = true
  · have hez : epoch = 0#64 := eq_of_beq hv0
    subst hez
    simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field, hv0, ↓reduceIte,
      List.nil_append] using hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
  · let rest := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint epoch ++ tail
    have hcur_eq : CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ tail =
        0x08#8 :: rest := by
      have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .varint = [0x08#8] := rfl
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field, hv0,
        Bool.false_eq_true, ↓reduceIte, hk, rest, List.cons_append, List.nil_append]
    rw [hcur_eq] at hbs_split ⊢
    have hcur_le : (0x08#8 :: rest).length ≤ x.bs.length := by
      rw [hbs_split, List.length_append]; omega
    have hcur_lt : (0x08#8 :: rest).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hcur_suf : IsDropSuffix x.bs (0x08#8 :: rest) := e2u311_isDropSuffix_of_append hbs_split
    have hpos_v : 0 < (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint epoch).length :=
      e2u311_proto_encodeVarint_pos epoch
    have hgt_lim : ¬ (0x08#8 :: rest).length ≤ limit := by
      dsimp only [rest]; rw [List.length_cons, List.length_append]; omega
    refine e2u311_ekSent_decode_key_dom_step hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hgt_lim hsp_align
      hcur_le hcur_lt hcur_suf (key := 8#64) (iwt := .varint)
      rfl (by decide) rfl (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    obtain ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest_le : rest.length ≤ x.bs.length := by
      simp only [hbs_split, rest, List.length_append, List.length_cons]; omega
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
    have hrest_suf : IsDropSuffix x.bs rest :=
      e2u311_isDropSuffix_of_append (pre := pre ++ [0x08#8])
        (by simp only [hbs_split, List.append_assoc, List.singleton_append])
    apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 340#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
      have hdv : decodeVarint rest = some (epoch, tail) :=
        e2u311_codec_decodeVarint_proto_encodeVarint epoch tail
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
      by_vm_steps
        (conv => arg 4; rw [e2u311_ekSentDomLoopPre, e2u311_tightPoolAt,
          sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_leaf s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          sepConj_pure_left_comm])
        apply SepWP.exists_elim; intro evs
        apply SepWP.pure_elim; intro hevs
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
        refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
          (ret_pc := (blkPl_311).base + 352#64) hVarintCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
              simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, A.pool_of_vmPreserved hvm_d,
                arm64_norm, wp_norm, hsp1, hx19_1, e2u311_stackAt_decodeVarint2_raw_eq]; try rfl)
          (And.intro hrest_lt
            (e2u311_fitsEnv_step_tight hFit hevs (e2u311_decodeVarint2Env_tight_of_some hdv)
              (Nat.zero_le _) (Nat.zero_le _)
              (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)))
          (by sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
          hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        have htail_le : tail.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
        apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 152#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
            e2u311_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
            sepConj_assoc, arm64_norm, wp_norm, hsp1])
          apply SepWP.exists_elim; intro evs_v
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
          apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf htail_le) (by sep_focus)
          apply SepWP.fold (e2u311_tightPoolAt_nil_step (o := 0) (c := 0) (r := 0) A lim st sm hdv hevs hevs_v) (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [e2u311_tightPoolAt_transport A lim st 0 0 0 hvm2]
          refine SepWPpLscro.weaken_pre ?_
            (hcont _
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr1])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm, hx21_m])
              (by simp only [arm64_norm, wp_norm, hx22_m])
              (by simp only [arm64_norm, wp_norm, hx23_m])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
          dsimp only [e2u311_ekSentDomLoopPre]; sep_entail

private theorem e2u311_ekSent_field2_auth_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {maxRoot maxMac authOps authCum authReq maxOps cumCap maxReq limit : Nat}
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (e2u311_authMergeTightSpecDomOf A lim (e2u311_AuthDomOf maxRoot maxMac)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    {Q : State → SepProp → Prop} {R Hrest : SepProp}
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {s0 s : State}
    {opt : Option ProtoAuthenticator} {pre tail : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hO : authOps ≤ maxOps) (hC : authCum ≤ cumCap) (hR : authReq ≤ maxReq)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_tail : limit ≤ tail.length)
    (hopt_valid : e2u311_ValidOptAuthPBOf maxRoot maxMac opt)
    (hbs_split : x.bs = pre ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 opt ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ekSentDomLoopPre A lim st authOps authCum authReq s0 s'
          (Hrest ∗ optProtoAuthenticatorCapAt A.repAlloc (x.msgPtr + 0x30#64) tail.length opt)
          x.bufRef x.slot x.ptr x.bs tail)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ekSentDomLoopPre A lim st 0 0 0 s0 s
        (Hrest ∗ (((x.msgPtr + 0x30#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (x.msgPtr + 0x30#64 + 8#64) 40))
        x.bufRef x.slot x.ptr x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 opt ++ tail))
      Q (WppPanicFalse R) := by
  cases opt with
  | none =>
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
    refine SepWPpLscro.weaken_pre ?_
      (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs)
    unfold e2u311_ekSentDomLoopPre
    exact sepConj_mono (e2u311_tightPoolAt_mono A lim st (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) s)
      (sepConj_mono
        (sepConj_mono_right (e2u311_niche_none_entails_optAuthCapAt A.repAlloc (x.msgPtr + 0x30#64) tail.length))
        (Entails.refl _))
  | some a =>
    let rest := tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) tail
    have hcur_eq :
        CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 (some a) ++ tail =
        0x12#8 :: rest := by
      have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := rfl
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk, rest, tlb_lenPrefixed,
        List.cons_append, List.nil_append, List.append_assoc]
    rw [hcur_eq] at hbs_split ⊢
    have hcur_le : (0x12#8 :: rest).length ≤ x.bs.length := by
      rw [hbs_split, List.length_append]; omega
    have hcur_lt : (0x12#8 :: rest).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hcur_suf : IsDropSuffix x.bs (0x12#8 :: rest) := e2u311_isDropSuffix_of_append hbs_split
    have hgt_lim : ¬ (0x12#8 :: rest).length ≤ limit := by
      dsimp only [rest, tlb_lenPrefixed]
      rw [List.length_cons, List.length_append, List.length_append]
      omega
    refine e2u311_ekSent_decode_key_dom_step hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hgt_lim hsp_align
      hcur_le hcur_lt hcur_suf (key := 18#64) (iwt := .lengthDelimited)
      rfl (by decide) rfl (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    obtain ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest_le : rest.length ≤ x.bs.length := by
      simp only [hbs_split, rest, List.length_append, List.length_cons]; omega
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
    have hrest_suf : IsDropSuffix x.bs rest :=
      e2u311_isDropSuffix_of_append (pre := pre ++ [0x12#8])
        (by simp only [hbs_split, List.append_assoc, List.singleton_append])
    apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 228#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
      rw [e2u311_ekSentDomLoopPre_transport A lim st 0 0 0 s0 hvm_d]
      have h56 : (x.msgPtr + 0x30#64) + 8#64 = x.msgPtr + 56#64 := by bv_lin
      have h64 : (x.msgPtr + 0x30#64) + 16#64 = x.msgPtr + 64#64 := by bv_lin
      have h72 : (x.msgPtr + 0x30#64) + 24#64 = x.msgPtr + 72#64 := by bv_lin
      have h80 : (x.msgPtr + 0x30#64) + 32#64 = x.msgPtr + 80#64 := by bv_lin
      have h88 : (x.msgPtr + 0x30#64) + 40#64 = x.msgPtr + 88#64 := by bv_lin
      have h48 : x.msgPtr + 0x30#64 = x.msgPtr + 48#64 := rfl
      have hdef_zcap := e2u311_default_auth_cells_entails_zeroCap A.repAlloc (x.msgPtr + 0x30#64)
      rw [h56, h64, h72, h80, h88] at hdef_zcap
      conv at hdef_zcap => arg 1; rw [h48]
      apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 252#64)
      by_vm_steps
        (conv => arg 4; rw [e2u311_ekSentDomLoopPre, memRegion_40_split_5_cells (x.msgPtr + 0x30#64),
          h56, h64, h72, h80, h88, h48])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v5
        apply SepWP.exists_elim; intro v4
        apply SepWP.exists_elim; intro v3
        apply SepWP.exists_elim; intro v2
        apply SepWP.exists_elim; intro v1
        wp_steps
        apply SepWP.fold hdef_zcap (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm_init => ?_⟩
        rw [e2u311_tightPoolAt_transport A lim st 0 0 0 hvm_init]
        let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
        let x_am : AuthMergeGhost :=
          ⟨.lengthDelimited, x.msgPtr + 0x30#64, default, x.bufRef, x.slot, restPtr, rest⟩
        have hDom_am : e2u311_AuthDomOf maxRoot maxMac x_am :=
          ⟨rfl, rfl, a, tail, hopt_valid a rfl, rfl⟩
        apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
        by_vm_steps
          (conv => arg 4; rw [e2u311_tightPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
            unchunkedMergeBelow_eq_authMergeStack s0.sp])
          (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
            sepConj_pure_left_comm])
          apply SepWP.exists_elim; intro evs
          apply SepWP.pure_elim; intro hevs
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_call => ?_⟩
          refine call_budget_lscro (x := (x_am, M.stepEvents evs st))
            (ret_pc := (blkPl_311).base + 264#64) hAuthTightCall
            (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
            (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
            (by simp only [arm64_norm, wp_norm])
            (by conv =>
                  lhs
                  dsimp only [e2u311_authMergeTightSpecDomOf, x_am]
                  rw [tlb_domHeap_of_dom hDom_am]
                  arg 2
                  simp only [A.pool_of_vmPreserved hvm_call, arm64_norm, wp_norm, hsp1])
            (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
              by simp only [arm64_norm, wp_norm, hx20_1],
              by simp only [arm64_norm, wp_norm, hx19_1],
              hrest_lt,
              e2u311_fitsEnv_step_tight hFit hevs
                (fun _ hge => tlb_guardedEnv_tight_of_dom hDom_am hge)
                (by omega) (by omega)
                (Nat.max_le.mpr ⟨Nat.zero_le _, hR⟩)⟩)
            (by sep_focus) ?_
          intro sm hpcm hrunm hspm hcsm
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
            hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
            at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
          have hrest_lt64 : rest.length < 2 ^ 64 :=
            Nat.lt_trans hrest_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
          have ⟨hraw_a, _, _⟩ := e2u311_lenPrefixed_sub_lt hrest_lt64
          have ham : (mergeMessage ProtoAuthenticator.mergeField
              (codecWireTypeToProto x_am.wt) x_am.msg x_am.bs 97).toOption = some (a, tail) := by
            dsimp only [x_am, codecWireTypeToProto]
            rw [e2u311_protoAuth_mergeMessage_roundtrip a tail 96 hraw_a]
            rfl
          have htail_le : tail.length ≤ rest.length := by
            dsimp only [rest, tlb_lenPrefixed]
            rw [List.length_append, List.length_append]; omega
          apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 152#64)
          by_vm_steps
            (conv => arg 4; simp only [e2u311_authMergeTightSpecDomOf, authMergeSpecOfEnv,
              ham, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro evs_am
            wp_focus_pure; intro htrm
            wp_focus_pure; intro hevs_am
            wp_focus_pure; intro hsm0
            (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1, ← unchunkedMergeBelow_eq_authMergeStack])
            apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf htail_le) (by sep_focus)
            apply SepWP.fold
              (e2u311_tightPoolAt_append_step (o₃ := authOps) (c₃ := authCum) (r₃ := authReq)
                A lim st sm hevs
                (tlb_guardedEnv_tight_of_dom hDom_am hevs_am)
                (by omega)
                (by omega)
                (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩))
              (by sep_focus)
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [e2u311_tightPoolAt_transport A lim st authOps authCum authReq hvm2]
            refine SepWPpLscro.weaken_pre ?_
              (hcont _
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr1])
                (by simp only [arm64_norm, wp_norm, hx19_m])
                (by simp only [arm64_norm, wp_norm, hx20_m])
                (by simp only [arm64_norm, wp_norm, hx21_m])
                (by simp only [arm64_norm, wp_norm, hx22_m])
                (by simp only [arm64_norm, wp_norm, hx23_m])
                ⟨by simp only [arm64_norm, wp_norm, hx24_m],
                 by simp only [arm64_norm, wp_norm, hx25_m],
                 by simp only [arm64_norm, wp_norm, hx26_m],
                 by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
            dsimp only [e2u311_ekSentDomLoopPre, optProtoAuthenticatorCapAt, x_am]; sep_entail

private theorem e2u311_ekSent_field3_dk_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {Q : State → SepProp → Prop} {R Hrest : SepProp}
    {o₁ c₁ r₁ o₂ c₂ r₂ maxDk maxOps cumCap maxReq limit : Nat}
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {s0 s : State}
    {dk pre tail : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hO1 : o₁ ≤ o₂) (hC1 : c₁ ≤ c₂) (hR1 : r₁ ≤ r₂)
    (hO2 : o₁ + 2 ≤ o₂)
    (hC2 : c₁ + 2 * spqrAllocTightCost (Nat.max 8 maxDk) ≤ c₂)
    (hR2 : Nat.max r₁ (Nat.max 8 maxDk) ≤ r₂)
    (hOmax : o₂ ≤ maxOps) (hCmax : c₂ ≤ cumCap) (hRmax : r₂ ≤ maxReq)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_tail : limit ≤ tail.length)
    (hdk_max : dk.length ≤ maxDk)
    (hbs_split : x.bs = pre ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 dk ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ekSentDomLoopPre A lim st o₂ c₂ r₂ s0 s'
          (Hrest ∗ vecU8CapAt A.repAlloc x.msgPtr tail.length dk)
          x.bufRef x.slot x.ptr x.bs tail)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ekSentDomLoopPre A lim st o₁ c₁ r₁ s0 s
        (Hrest ∗ tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [])
        x.bufRef x.slot x.ptr x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 dk ++ tail))
      Q (WppPanicFalse R) := by
  by_cases hdk0 : dk.isEmpty = true
  · have hdkn : dk = [] := List.isEmpty_iff.mp hdk0
    subst hdkn
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hdk0, ↓reduceIte,
      List.nil_append]
    refine SepWPpLscro.weaken_pre ?_
      (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs)
    unfold e2u311_ekSentDomLoopPre
    exact sepConj_mono (e2u311_tightPoolAt_mono A lim st hO1 hC1 hR1 s)
      (sepConj_mono
        (sepConj_mono_right (e2u311_vecU8ZeroCapAt_entails_vecU8CapAt A.repAlloc x.msgPtr tail.length []))
        (Entails.refl _))
  · let rest := tlb_lenPrefixed dk tail
    have hcur_eq : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 dk ++ tail =
        0x1a#8 :: rest := by
      have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] := rfl
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, hdk0, Bool.false_eq_true,
        ↓reduceIte, hk, rest, tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]
    rw [hcur_eq] at hbs_split ⊢
    have hcur_le : (0x1a#8 :: rest).length ≤ x.bs.length := by
      rw [hbs_split, List.length_append]; omega
    have hcur_lt : (0x1a#8 :: rest).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hcur_suf : IsDropSuffix x.bs (0x1a#8 :: rest) := e2u311_isDropSuffix_of_append hbs_split
    have hgt_lim : ¬ (0x1a#8 :: rest).length ≤ limit := by
      dsimp only [rest, tlb_lenPrefixed]
      rw [List.length_cons, List.length_append, List.length_append]
      omega
    refine e2u311_ekSent_decode_key_dom_step hVarintCall hFit
      (Nat.le_trans hO1 hOmax) (Nat.le_trans hC1 hCmax) (Nat.le_trans hR1 hRmax)
      hgt_lim hsp_align hcur_le hcur_lt hcur_suf (key := 26#64) (iwt := .lengthDelimited)
      rfl (by decide) rfl (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    obtain ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest_le : rest.length ≤ x.bs.length := by
      simp only [hbs_split, rest, List.length_append, List.length_cons]; omega
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
    have hrest_suf : IsDropSuffix x.bs rest :=
      e2u311_isDropSuffix_of_append (pre := pre ++ [0x1a#8])
        (by simp only [hbs_split, List.append_assoc, List.singleton_append])
    apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 372#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      have hdk_lt64 : dk.length < 2 ^ 64 := by
        have hlt64 : rest.length < 2 ^ 64 :=
          Nat.lt_trans hrest_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
        exact (e2u311_lenPrefixed_sub_lt hlt64).1
      have hmb : mergeBytes .lengthDelimited rest = some (dk, tail) :=
        e2u311_codec_mergeBytes_lenPrefixed dk tail hdk_lt64
      apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
      by_vm_steps
        (conv => arg 4; rw [e2u311_ekSentDomLoopPre, e2u311_tightPoolAt, tlb_vecU8ZeroCapAt,
          sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_bytesMerge3 s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro ptr1
        apply SepWP.exists_elim; intro evs
        wp_focus_pure; intro hevs
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_call => ?_⟩
        let x_bm : BytesMergeGhost :=
          ⟨.lengthDelimited, x.msgPtr, 0#64, ptr1, [], x.bufRef, x.slot, restPtr, rest⟩
        refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
          (ret_pc := (blkPl_311).base + 384#64) hBytesCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm]
                arg 2
                simp only [A.pool_of_vmPreserved hvm_call, A.pool_of_vmPreserved hvm_d,
                  arm64_norm, wp_norm, hsp1])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
            by simp only [arm64_norm, wp_norm, hx20_1],
            by simp only [arm64_norm, wp_norm, hx19_1],
            hrest_lt,
            bytesMergeCapOk_zero,
            e2u311_fitsEnv_step_tight hFit hevs
              (fun _ hbm => e2u311_bytesMerge_zeroCap_tight x_bm dk tail maxDk rfl rfl hmb hdk_max hbm)
              (Nat.le_trans hO2 hOmax) (Nat.le_trans hC2 hCmax) (Nat.le_trans hR2 hRmax)⟩)
          (by sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
          hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        have htail_le : tail.length ≤ rest.length := by
          dsimp only [rest, tlb_lenPrefixed]
          rw [List.length_append, List.length_append]; omega
        apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 152#64)
        by_vm_steps
          (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm, hmb,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_bm
          apply SepWP.exists_elim; intro cap1'
          apply SepWP.exists_elim; intro ptr1'
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_bm
          wp_focus_pure; intro hsm0
          wp_focus_pure; intro hcap1'
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
          apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf htail_le) (by sep_focus)
          have hdk_cap : vecU8At A.repAlloc x.msgPtr cap1' ptr1' dk ⊢
              vecU8CapAt A.repAlloc x.msgPtr tail.length dk := by
            unfold vecU8CapAt
            refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
            exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
          apply SepWP.fold hdk_cap (by sep_focus)
          apply SepWP.fold
            (e2u311_tightPoolAt_append_step A lim st sm hevs
              (e2u311_bytesMerge_zeroCap_tight x_bm dk tail maxDk rfl rfl hmb hdk_max hevs_bm)
              hO2 hC2 hR2)
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [e2u311_tightPoolAt_transport A lim st o₂ c₂ r₂ hvm2]
          refine SepWPpLscro.weaken_pre ?_
            (hcont _
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr1])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm, hx21_m])
              (by simp only [arm64_norm, wp_norm, hx22_m])
              (by simp only [arm64_norm, wp_norm, hx23_m])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
          dsimp only [e2u311_ekSentDomLoopPre]; sep_entail

private theorem e2u311_ekSent_field4_ct1_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {Q : State → SepProp → Prop} {R Hrest : SepProp}
    {o₁ c₁ r₁ maxCt1 maxOps cumCap maxReq limit : Nat}
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {s0 s : State}
    {ct1 pre tail : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hO1 : o₁ ≤ maxOps) (hC1 : c₁ ≤ cumCap) (hR1 : r₁ ≤ maxReq)
    (hO2 : o₁ + 2 ≤ maxOps)
    (hC2 : c₁ + 2 * spqrAllocTightCost (Nat.max 8 maxCt1) ≤ cumCap)
    (hR2 : Nat.max r₁ (Nat.max 8 maxCt1) ≤ maxReq)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_tail : limit ≤ tail.length)
    (hct1_max : ct1.length ≤ maxCt1)
    (hbs_split : x.bs = pre ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ct1 ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ekSentDomLoopPre A lim st maxOps cumCap maxReq s0 s'
          (Hrest ∗ vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) tail.length ct1)
          x.bufRef x.slot x.ptr x.bs tail)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ekSentDomLoopPre A lim st o₁ c₁ r₁ s0 s
        (Hrest ∗ tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [])
        x.bufRef x.slot x.ptr x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ct1 ++ tail))
      Q (WppPanicFalse R) := by
  by_cases hct10 : ct1.isEmpty = true
  · have hct1n : ct1 = [] := List.isEmpty_iff.mp hct10
    subst hct1n
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hct10, ↓reduceIte,
      List.nil_append]
    refine SepWPpLscro.weaken_pre ?_
      (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs)
    unfold e2u311_ekSentDomLoopPre
    exact sepConj_mono (e2u311_tightPoolAt_mono A lim st hO1 hC1 hR1 s)
      (sepConj_mono
        (sepConj_mono_right
          (e2u311_vecU8ZeroCapAt_entails_vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) tail.length []))
        (Entails.refl _))
  · let rest := tlb_lenPrefixed ct1 tail
    have hcur_eq : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ct1 ++ tail =
        0x22#8 :: rest := by
      have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] := rfl
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, hct10, Bool.false_eq_true,
        ↓reduceIte, hk, rest, tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]
    rw [hcur_eq] at hbs_split ⊢
    have hcur_le : (0x22#8 :: rest).length ≤ x.bs.length := by
      rw [hbs_split, List.length_append]; omega
    have hcur_lt : (0x22#8 :: rest).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hcur_suf : IsDropSuffix x.bs (0x22#8 :: rest) := e2u311_isDropSuffix_of_append hbs_split
    have hgt_lim : ¬ (0x22#8 :: rest).length ≤ limit := by
      dsimp only [rest, tlb_lenPrefixed]
      rw [List.length_cons, List.length_append, List.length_append]
      omega
    refine e2u311_ekSent_decode_key_dom_step hVarintCall hFit
      hO1 hC1 hR1 hgt_lim hsp_align hcur_le hcur_lt hcur_suf (key := 34#64) (iwt := .lengthDelimited)
      rfl (by decide) rfl (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    obtain ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest_le : rest.length ≤ x.bs.length := by
      simp only [hbs_split, rest, List.length_append, List.length_cons]; omega
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
    have hrest_suf : IsDropSuffix x.bs rest :=
      e2u311_isDropSuffix_of_append (pre := pre ++ [0x22#8])
        (by simp only [hbs_split, List.append_assoc, List.singleton_append])
    apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 292#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      have hct1_lt64 : ct1.length < 2 ^ 64 := by
        have hlt64 : rest.length < 2 ^ 64 :=
          Nat.lt_trans hrest_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
        exact (e2u311_lenPrefixed_sub_lt hlt64).1
      have hmb : mergeBytes .lengthDelimited rest = some (ct1, tail) :=
        e2u311_codec_mergeBytes_lenPrefixed ct1 tail hct1_lt64
      apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
      by_vm_steps
        (conv => arg 4; rw [e2u311_ekSentDomLoopPre, e2u311_tightPoolAt, tlb_vecU8ZeroCapAt,
          sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_bytesMerge3 s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro ptr2
        apply SepWP.exists_elim; intro evs
        wp_focus_pure; intro hevs
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_call => ?_⟩
        let x_bm : BytesMergeGhost :=
          ⟨.lengthDelimited, x.msgPtr + 0x18#64, 0#64, ptr2, [], x.bufRef, x.slot, restPtr, rest⟩
        refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
          (ret_pc := (blkPl_311).base + 304#64) hBytesCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm]
                arg 2
                simp only [A.pool_of_vmPreserved hvm_call, A.pool_of_vmPreserved hvm_d,
                  arm64_norm, wp_norm, hsp1])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
            by simp only [arm64_norm, wp_norm, hx20_1],
            by simp only [arm64_norm, wp_norm, hx19_1],
            hrest_lt,
            bytesMergeCapOk_zero,
            e2u311_fitsEnv_step_tight hFit hevs
              (fun _ hbm => e2u311_bytesMerge_zeroCap_tight x_bm ct1 tail maxCt1 rfl rfl hmb hct1_max hbm)
              hO2 hC2 hR2⟩)
          (by sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
          hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        have htail_le : tail.length ≤ rest.length := by
          dsimp only [rest, tlb_lenPrefixed]
          rw [List.length_append, List.length_append]; omega
        apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 152#64)
        by_vm_steps
          (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm, hmb,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_bm
          apply SepWP.exists_elim; intro cap2'
          apply SepWP.exists_elim; intro ptr2'
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_bm
          wp_focus_pure; intro hsm0
          wp_focus_pure; intro hcap2'
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
          apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf htail_le) (by sep_focus)
          have hct1_cap : vecU8At A.repAlloc (x.msgPtr + 0x18#64) cap2' ptr2' ct1 ⊢
              vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) tail.length ct1 := by
            unfold vecU8CapAt
            refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
            exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
          apply SepWP.fold hct1_cap (by sep_focus)
          apply SepWP.fold
            (e2u311_tightPoolAt_append_step A lim st sm hevs
              (e2u311_bytesMerge_zeroCap_tight x_bm ct1 tail maxCt1 rfl rfl hmb hct1_max hevs_bm)
              hO2 hC2 hR2)
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [e2u311_tightPoolAt_transport A lim st maxOps cumCap maxReq hvm2]
          refine SepWPpLscro.weaken_pre ?_
            (hcont _
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr1])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm, hx21_m])
              (by simp only [arm64_norm, wp_norm, hx22_m])
              (by simp only [arm64_norm, wp_norm, hx23_m])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
          dsimp only [e2u311_ekSentDomLoopPre, x_bm]; sep_entail

private theorem e2u311_ekSent_dom_own_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {maxRoot maxMac maxDk maxCt1 authOps authCum authReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 4 ≤ maxOps)
    (hCum : authCum + 2 * spqrAllocTightCost (Nat.max 8 maxDk) +
      2 * spqrAllocTightCost (Nat.max 8 maxCt1) ≤ cumCap)
    (hReq : Nat.max authReq (Nat.max (Nat.max 8 maxDk) (Nat.max 8 maxCt1)) ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (e2u311_authMergeTightSpecDomOf A lim (e2u311_AuthDomOf maxRoot maxMac)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)))) :
    subroutine_ok ((blkPC_311).rebase (blkPl_311).base H)
      (blkPl_311).base
      (withLsCodeRoLoaded lsmpl
        (e2u311_ekSentDomOwnSpec A lim
          (e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1)
          maxOps cumCap maxReq)) := by
  let Dom := e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2u311_ekSentDomOwnSpec
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2u311_ekSentDomOwnSpec A lim Dom maxOps cumCap maxReq) (x, st) R s0)
    (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  rintro ⟨h_1, h_2, h_3, hbs_lt, hDom, hFit⟩
  obtain ⟨hwt_p, hmsg_def, pb, after, hpb, hbs_eq⟩ := hDom
  have hwt_ld : x.wt = .lengthDelimited := e2u311_wt_eq_lengthDelimited hwt_p
  have hbs_lt64 : x.bs.length < 2 ^ 64 :=
    Nat.lt_trans hbs_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
  have hsome : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (pb, after) := by
    rw [hwt_p, hmsg_def, hbs_eq, e2u311_ekSentCt1Received_mergeMessage_roundtrip pb after
      (hbs_eq ▸ hbs_lt64)]
    rfl
  let raw := V1State.Unchunked.EkSentCt1Received.encodeRaw pb
  let rest0 := raw ++ after
  have hbs_raw : x.bs = CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
      (BitVec.ofNat 64 raw.length) ++ rest0 := by
    simp only [hbs_eq, tlb_lenPrefixed, raw, rest0, List.append_assoc]
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw.length, rest0) := by
    rw [hbs_raw]
    exact e2u311_codec_decodeVarint_proto_encodeVarint (BitVec.ofNat 64 raw.length) rest0
  have hraw_lt64 : raw.length < 2 ^ 64 :=
    (e2u311_lenPrefixed_sub_lt (hbs_eq ▸ hbs_lt64)).1
  have hlen_nat : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_lt64]
  have hge_len : ¬ rest0.length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hlen_nat]; dsimp only [rest0]; rw [List.length_append]; omega
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hule := ule_len_of_ge hge_len hrest0_lt
  have hsub := bv_len_sub_limit hge_len
  have hlim_raw : rest0.length - raw.length = after.length := by
    dsimp only [rest0]; rw [List.length_append]; omega
  have hlim_eq : rest0.length - (BitVec.ofNat 64 raw.length).toNat = after.length := by
    rw [hlen_nat]; exact hlim_raw
  have hsaved :
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        memRegion (s0.sp - 40#64) 8 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      ekSentSavedRegs s0.sp s0 := Entails.refl _
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [stackAt_unchunkedMerge s0.sp, unchunkedMergeBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v_lr
    apply SepWP.exists_elim; intro v_fp
    wp_steps
    apply SepWP.fold hsaved (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st))
      (ret_pc := (blkPl_311).base + 52#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2u311_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
      (by exact ⟨by simp only [arm64_norm, wp_norm, h_3],
        hbs_lt,
        by simpa only [AllocCostModel.stepEvents, List.foldl] using
             e2u311_fitsEnv_step_tight hFit (SpqrTightEvs.nil 0 0 0)
               (e2u311_decodeVarint2Env_tight_of_some hdv0)
               (Nat.zero_le _) (Nat.zero_le _)
               (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := (blkPl_311).base + 152#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2u311_stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (e2u311_tightPoolAt_nil_step (o := 0) (c := 0) (r := 0) A lim st sm hdv0 (SpqrTightEvs.nil 0 0 0) hevs_dv)
        (by simp only [M.stepEvents_nil]; sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [e2u311_tightPoolAt_transport A lim st 0 0 0 hvm2]
      let f1 := CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 pb.epoch
      let f2 := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 pb.auth
      let f3 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 pb.dk
      let f4 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 pb.ct1
      let p0 := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 raw.length)
      let cur4 := f4 ++ after
      let cur3 := f3 ++ cur4
      let cur2 := f2 ++ cur3
      have hrest0_eq : rest0 = f1 ++ cur2 := by
        dsimp only [rest0, raw, V1State.Unchunked.EkSentCt1Received.encodeRaw, f1, f2, f3, f4, cur2, cur3, cur4]
        simp only [List.append_assoc]
      let cDk := 2 * spqrAllocTightCost (Nat.max 8 maxDk)
      let cCt1 := 2 * spqrAllocTightCost (Nat.max 8 maxCt1)
      let rDk := Nat.max 8 maxDk
      let rCt1 := Nat.max 8 maxCt1
      have hCum' : authCum + cDk + cCt1 ≤ cumCap := hCum
      have hReq_auth : authReq ≤ maxReq := Nat.le_trans (Nat.le_max_left _ _) hReq
      have hReq_dk : rDk ≤ maxReq :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hReq
      have hReq_ct1 : rCt1 ≤ maxReq :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hReq
      refine SepWPpLscro.weaken_pre ?_
        (e2u311_ekSent_field1_epoch_dom hVarintCall
          (Hrest := tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
            tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
            (((x.msgPtr + 0x30#64) ↦₆₄ 0xffffffffffffffff#64) ∗
              memRegion (x.msgPtr + 0x30#64 + 8#64) 40))
          (limit := after.length) (epoch := pb.epoch) (pre := p0) (tail := cur2)
          hFit hsp_align hbs_lt
          (by dsimp only [cur2, cur3, cur4]; simp only [List.length_append]; omega)
          (by rw [hbs_raw, hrest0_eq])
          (fun s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 => ?_)
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hsm1, hsub, hlim_eq, hlim_raw])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
      · have hdef_zero :
            tlb_ucEkSentCt1ReceivedZeroCapAt A.repAlloc x.msgPtr default =
              tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
              (((x.msgPtr + 0x30#64) ↦₆₄ 0xffffffffffffffff#64) ∗
                memRegion (x.msgPtr + 0x30#64 + 8#64) 40) ∗
              ((x.msgPtr + 0x60#64) ↦₆₄ 0#64) := rfl
        rw [hmsg_def, hdef_zero]
        dsimp only [e2u311_ekSentDomLoopPre]
        rw [← hrest0_eq, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        exact Entails.of_eq (by sep_ac_rfl)
      · refine SepWPpLscro.weaken_pre ?_
          (e2u311_ekSent_field2_auth_dom hVarintCall hAuthTightCall
            (Hrest := tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
              ((x.msgPtr + 0x60#64) ↦₆₄ pb.epoch))
            (limit := after.length) (opt := pb.auth) (pre := p0 ++ f1) (tail := cur3)
            hFit (by omega) (by omega) hReq_auth hsp_align hbs_lt
            (by dsimp only [cur3, cur4]; simp only [List.length_append]; omega)
            hpb.1
            (by rw [hbs_raw, hrest0_eq]; dsimp only [p0, f1, f2, cur2]; simp only [List.append_assoc])
            (fun s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hcs2 => ?_)
            hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1)
        · dsimp only [e2u311_ekSentDomLoopPre, cur2]; sep_entail
        · refine SepWPpLscro.weaken_pre ?_
            (e2u311_ekSent_field3_dk_dom hVarintCall hBytesCall
              (Hrest := tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
                optProtoAuthenticatorCapAt A.repAlloc (x.msgPtr + 0x30#64) cur3.length pb.auth ∗
                ((x.msgPtr + 0x60#64) ↦₆₄ pb.epoch))
              (o₁ := authOps) (c₁ := authCum) (r₁ := authReq)
              (o₂ := authOps + 2) (c₂ := authCum + cDk) (r₂ := Nat.max authReq rDk)
              (maxDk := maxDk) (limit := after.length) (dk := pb.dk)
              (pre := p0 ++ f1 ++ f2) (tail := cur4)
              hFit (by omega) (by omega) (Nat.le_max_left _ _)
              (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
              (by omega) (by omega) (Nat.max_le.mpr ⟨hReq_auth, hReq_dk⟩)
              hsp_align hbs_lt
              (by dsimp only [cur4]; rw [List.length_append]; omega)
              hpb.2.1
              (by rw [hbs_raw, hrest0_eq]; dsimp only [p0, f1, f2, f3, cur2, cur3]; simp only [List.append_assoc])
              (fun s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs3 => ?_)
              hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hcs2)
          · dsimp only [e2u311_ekSentDomLoopPre, cur3]; sep_entail
          · refine SepWPpLscro.weaken_pre ?_
              (e2u311_ekSent_field4_ct1_dom hVarintCall hBytesCall
                (Hrest := vecU8CapAt A.repAlloc x.msgPtr cur4.length pb.dk ∗
                  optProtoAuthenticatorCapAt A.repAlloc (x.msgPtr + 0x30#64) cur3.length pb.auth ∗
                  ((x.msgPtr + 0x60#64) ↦₆₄ pb.epoch))
                (o₁ := authOps + 2) (c₁ := authCum + cDk) (r₁ := Nat.max authReq rDk)
                (maxCt1 := maxCt1) (limit := after.length) (ct1 := pb.ct1)
                (pre := p0 ++ f1 ++ f2 ++ f3) (tail := after)
                hFit (by omega) (by omega) (Nat.max_le.mpr ⟨hReq_auth, hReq_dk⟩)
                (by omega) hCum'
                (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hReq_auth, hReq_dk⟩, hReq_ct1⟩)
                hsp_align hbs_lt (Nat.le_refl _) hpb.2.2
                (by rw [hbs_raw, hrest0_eq]; dsimp only [p0, f1, f2, f3, f4, cur2, cur3, cur4]; simp only [List.append_assoc])
                (fun s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hcs4 => ?_)
                hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs3)
            · dsimp only [e2u311_ekSentDomLoopPre, cur4]; sep_entail
            · refine SepWPpLscro.weaken_pre ?_
                (e2u311_ekSent_exit_dom
                  (Dom := Dom) (m := pb) (after := after)
                  ⟨hwt_p, hmsg_def, pb, after, hpb, hbs_eq⟩ hsome hsp_align
                  (by rw [hbs_raw, hrest0_eq]; dsimp only [cur2, cur3, cur4]; simp only [List.length_append]; omega)
                  (e2u311_isDropSuffix_of_append (pre := p0 ++ f1 ++ f2 ++ f3 ++ f4)
                    (by rw [hbs_raw, hrest0_eq]; dsimp only [p0, f1, f2, f3, f4, cur2, cur3, cur4]; simp only [List.append_assoc]))
                  hpc4 hrun4 hsp4 htr4 hx21_4 hx22_4 hcs4)
              have hdk_m := vecU8CapAt_mono_u A.repAlloc x.msgPtr pb.dk
                (by dsimp only [cur4]; rw [List.length_append]; omega : after.length ≤ cur4.length)
              have hauth_m := optProtoAuthenticatorCapAt_mono A.repAlloc (x.msgPtr + 0x30#64) pb.auth
                (by dsimp only [cur3, cur4]; simp only [List.length_append]; omega : after.length ≤ cur3.length)
              dsimp only [e2u311_ekSentDomLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt]
              refine Entails.trans
                (sepConj_mono_right (sepConj_mono_left
                  (sepConj_mono_left (sepConj_mono hdk_m (sepConj_mono_left hauth_m)))))
                (Entails.of_eq (by sep_ac_rfl))

/-! ## 4d. Block `312` (`Ct1Sent::merge`) Canonical-`Dom` Tight Proofs -/

private def e2u311_ct1SentDomLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (o c r : Nat) (s0 s : State)
    (Hmsg : SepProp) (bufRef slot ptr : BitVec 64) (bs cur : List (BitVec 8)) : SepProp :=
  e2u311_tightPoolAt A lim st o c r s ∗
    Hmsg ∗
    (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 112#64) 48 ∗
    unchunkedSavedRegs s0.sp s0 ∗
    unchunkedMergeBelow s0.sp

private theorem e2u311_ct1SentDomLoopPre_transport {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (o c r : Nat) (s0 : State)
    {s₁ s₂ : State} (hvm : VmPreserved s₁ s₂)
    (Hmsg : SepProp) (bufRef slot ptr : BitVec 64) (bs cur : List (BitVec 8)) :
    e2u311_ct1SentDomLoopPre A lim st o c r s0 s₁ Hmsg bufRef slot ptr bs cur =
      e2u311_ct1SentDomLoopPre A lim st o c r s0 s₂ Hmsg bufRef slot ptr bs cur := by
  unfold e2u311_ct1SentDomLoopPre
  rw [e2u311_tightPoolAt_transport A lim st o c r hvm]

private noncomputable def e2u311_ct1SentDomOwnSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Dom : UnchunkedCt1SentMergeGhost → Prop)
    (maxOps cumCap maxReq : Nat) :
    Spec (UnchunkedCt1SentMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      Dom x ∧
      FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)⌝ ∗
      tlb_ucCt1SentZeroCapAt A.repAlloc x.msgPtr x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedOwnStack
  post := (unchunkedCt1SentMergeOwnSpecOfEnv A lim
    (fun _ => SpqrTightEvs maxOps cumCap maxReq)
    (tlb_GuardedEnv Dom (SpqrTightEvs maxOps cumCap maxReq) UnchunkedCt1SentMergeEnv)).post

private theorem e2u311_ct1Sent_ok_exit_dom_entails {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {Dom : UnchunkedCt1SentMergeGhost → Prop}
    {maxOps cumCap maxReq : Nat}
    (x : UnchunkedCt1SentMergeGhost) (hDom : Dom x)
    (s0 s sf : State) (m : V1State.Unchunked.Ct1Sent) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hsome : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps cumCap maxReq evs) :
    stackAt s0.sp unchunkedOwnStack ∗
      (protoUnchunkedCt1SentCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (e2u311_ct1SentDomOwnSpec A lim Dom maxOps cumCap maxReq).post (x, st) s0 sf := by
  dsimp only [e2u311_ct1SentDomOwnSpec, unchunkedCt1SentMergeOwnSpecOfEnv]
  rw [hsome, htr, hx0, ← A.pool_transport lim (M.stepEvents evs st) s sf hvm]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp unchunkedOwnStack ∗
      (protoUnchunkedCt1SentCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) sf))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) sf ∗
        (stackAt s0.sp unchunkedOwnStack ∗
          (protoUnchunkedCt1SentCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono
    (Entails.sepExists_right evs (Entails.pure_right (Or.inl ⟨hDom, hevs⟩) (Entails.refl _)))
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

private theorem e2u311_ct1Sent_exit_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {Dom : UnchunkedCt1SentMergeGhost → Prop}
    {maxOps cumCap maxReq : Nat}
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.Ct1Sent} {after : List (BitVec 8)}
    (hDom : Dom x)
    (hsome : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m, after))
    (_hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hafter_le : after.length ≤ x.bs.length)
    (hafter_suf : IsDropSuffix x.bs after)
    (hpc : s.pc = (blkPl_312).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 after.length)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ct1SentDomLoopPre A lim st maxOps cumCap maxReq s0 s
        (protoUnchunkedCt1SentCapAt A.repAlloc x.msgPtr after.length m)
        x.bufRef x.slot x.ptr x.bs after)
      (WppPost (e2u311_ct1SentDomOwnSpec A lim Dom maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - after.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : after.length = after.length)
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2u311_ct1SentDomLoopPre, e2u311_tightPoolAt,
      sliceCursorAfter_eq_split hafter_le hafter_suf, sliceCursorAt, unchunkedSavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm, arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold
      (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux.stackAt_unchunkedMerge_epilogue s0.sp s0)
      (by unfold unchunkedSavedRegs; sep_focus)
    have hcur_fold :
        (x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 after.length) ∗
          (x.ptr ↦ₛ x.bs.take (x.bs.length - after.length)) ∗ (curPtr ↦ₛ after) ⊢
        sliceCursorAfter x.slot x.ptr x.bs after := by
      rw [sliceCursorAfter_eq_split hafter_le hafter_suf, sliceCursorAt]
      exact Entails.of_eq (by dsimp only [curPtr]; sep_ac_rfl)
    apply SepWP.fold hcur_fold (by dsimp only [curPtr]; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx24, hx25, hx26, hx27, hx28, hvregs]⟩
    exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (e2u311_ct1Sent_ok_exit_dom_entails A lim st x hDom s0 s _ m after evs hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2u311_ct1Sent_decode_key_dom_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {Q : State → SepProp → Prop} {R Hmsg : SepProp}
    {o c r maxOps cumCap maxReq limit : Nat}
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {s0 s : State}
    {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hO : o ≤ maxOps) (hC : c ≤ cumCap) (hR : r ≤ maxReq)
    (hgt_lim : ¬ cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_ge : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag0 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_312).base + 204#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ct1SentDomLoopPre A lim st o c r s0 s' Hmsg x.bufRef x.slot x.ptr x.bs rest)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ct1SentDomLoopPre A lim st o c r s0 s Hmsg x.bufRef x.slot x.ptr x.bs cur)
      Q (WppPanicFalse R) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2u311_ct1SentDomLoopPre, e2u311_tightPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, unchunkedMergeBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := (blkPl_312).base + 172#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2u311_stackAt_decodeVarint2_raw_eq,
              arm64_norm, wp_norm, hsp, hx19])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19],
        hcur_lt,
        e2u311_fitsEnv_step_tight hFit hevs (e2u311_decodeVarint2Env_tight_of_some hd)
          hO hC (Nat.max_le.mpr ⟨hR, Nat.zero_le _⟩)⟩)
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
    have hshr := key_shr32_of_lt hk_ge
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
    have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
      omega
    apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 204#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        e2u311_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (e2u311_tightPoolAt_nil_step (o := o) (c := c) (r := r) A lim st sm hd hevs hevs_v) (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [e2u311_tightPoolAt_transport A lim st o c r hvm2]
      refine SepWPpLscro.weaken_pre ?_
        (hcont _
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
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
      dsimp only [e2u311_ct1SentDomLoopPre]; sep_entail

private theorem e2u311_ct1Sent_field1_epoch_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {Q : State → SepProp → Prop} {R Hrest : SepProp}
    {maxOps cumCap maxReq limit : Nat}
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {s0 s : State}
    {epoch : BitVec 64} {pre tail : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_tail : limit ≤ tail.length)
    (hbs_split : x.bs = pre ++ (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ct1SentDomLoopPre A lim st 0 0 0 s0 s'
          (Hrest ∗ ((x.msgPtr + 0x78#64) ↦₆₄ epoch))
          x.bufRef x.slot x.ptr x.bs tail)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ct1SentDomLoopPre A lim st 0 0 0 s0 s
        (Hrest ∗ ((x.msgPtr + 0x78#64) ↦₆₄ 0#64))
        x.bufRef x.slot x.ptr x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ tail))
      Q (WppPanicFalse R) := by
  by_cases hv0 : (epoch == 0#64) = true
  · have hez : epoch = 0#64 := eq_of_beq hv0
    subst hez
    simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field, hv0, ↓reduceIte,
      List.nil_append] using hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
  · let rest := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint epoch ++ tail
    have hcur_eq : CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ tail =
        0x08#8 :: rest := by
      have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .varint = [0x08#8] := rfl
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field, hv0,
        Bool.false_eq_true, ↓reduceIte, hk, rest, List.cons_append, List.nil_append]
    rw [hcur_eq] at hbs_split ⊢
    have hcur_le : (0x08#8 :: rest).length ≤ x.bs.length := by
      rw [hbs_split, List.length_append]; omega
    have hcur_lt : (0x08#8 :: rest).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hcur_suf : IsDropSuffix x.bs (0x08#8 :: rest) := e2u311_isDropSuffix_of_append hbs_split
    have hpos_v : 0 < (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint epoch).length :=
      e2u311_proto_encodeVarint_pos epoch
    have hgt_lim : ¬ (0x08#8 :: rest).length ≤ limit := by
      dsimp only [rest]; rw [List.length_cons, List.length_append]; omega
    refine e2u311_ct1Sent_decode_key_dom_step hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hgt_lim hsp_align
      hcur_le hcur_lt hcur_suf (key := 8#64) (iwt := .varint)
      rfl (by decide) rfl (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    obtain ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest_le : rest.length ≤ x.bs.length := by
      simp only [hbs_split, rest, List.length_append, List.length_cons]; omega
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
    have hrest_suf : IsDropSuffix x.bs rest :=
      e2u311_isDropSuffix_of_append (pre := pre ++ [0x08#8])
        (by simp only [hbs_split, List.append_assoc, List.singleton_append])
    apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 372#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
      have hdv : decodeVarint rest = some (epoch, tail) :=
        e2u311_codec_decodeVarint_proto_encodeVarint epoch tail
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
      by_vm_steps
        (conv => arg 4; rw [e2u311_ct1SentDomLoopPre, e2u311_tightPoolAt,
          sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_leaf s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          sepConj_pure_left_comm])
        apply SepWP.exists_elim; intro evs
        apply SepWP.pure_elim; intro hevs
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
        refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
          (ret_pc := (blkPl_312).base + 384#64) hVarintCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
              simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, A.pool_of_vmPreserved hvm_d,
                arm64_norm, wp_norm, hsp1, hx19_1, e2u311_stackAt_decodeVarint2_raw_eq]; try rfl)
          (And.intro hrest_lt
            (e2u311_fitsEnv_step_tight hFit hevs (e2u311_decodeVarint2Env_tight_of_some hdv)
              (Nat.zero_le _) (Nat.zero_le _)
              (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)))
          (by sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
          hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        have htail_le : tail.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
        apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 152#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
            e2u311_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
            sepConj_assoc, arm64_norm, wp_norm, hsp1])
          apply SepWP.exists_elim; intro evs_v
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
          apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf htail_le) (by sep_focus)
          apply SepWP.fold (e2u311_tightPoolAt_nil_step (o := 0) (c := 0) (r := 0) A lim st sm hdv hevs hevs_v) (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [e2u311_tightPoolAt_transport A lim st 0 0 0 hvm2]
          refine SepWPpLscro.weaken_pre ?_
            (hcont _
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr1])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm, hx21_m])
              (by simp only [arm64_norm, wp_norm, hx22_m])
              (by simp only [arm64_norm, wp_norm, hx23_m])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
          dsimp only [e2u311_ct1SentDomLoopPre]; sep_entail

private theorem e2u311_ct1Sent_field2_auth_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {maxRoot maxMac authOps authCum authReq maxOps cumCap maxReq limit : Nat}
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (e2u311_authMergeTightSpecDomOf A lim (e2u311_AuthDomOf maxRoot maxMac)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    {Q : State → SepProp → Prop} {R Hrest : SepProp}
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {s0 s : State}
    {opt : Option ProtoAuthenticator} {pre tail : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hO : authOps ≤ maxOps) (hC : authCum ≤ cumCap) (hR : authReq ≤ maxReq)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_tail : limit ≤ tail.length)
    (hopt_valid : e2u311_ValidOptAuthPBOf maxRoot maxMac opt)
    (hbs_split : x.bs = pre ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 opt ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ct1SentDomLoopPre A lim st authOps authCum authReq s0 s'
          (Hrest ∗ optProtoAuthenticatorCapAt A.repAlloc (x.msgPtr + 0x48#64) tail.length opt)
          x.bufRef x.slot x.ptr x.bs tail)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ct1SentDomLoopPre A lim st 0 0 0 s0 s
        (Hrest ∗ (((x.msgPtr + 0x48#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (x.msgPtr + 0x48#64 + 8#64) 40))
        x.bufRef x.slot x.ptr x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 opt ++ tail))
      Q (WppPanicFalse R) := by
  cases opt with
  | none =>
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
    refine SepWPpLscro.weaken_pre ?_
      (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs)
    unfold e2u311_ct1SentDomLoopPre
    exact sepConj_mono (e2u311_tightPoolAt_mono A lim st (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) s)
      (sepConj_mono
        (sepConj_mono_right (e2u311_niche_none_entails_optAuthCapAt A.repAlloc (x.msgPtr + 0x48#64) tail.length))
        (Entails.refl _))
  | some a =>
    let rest := tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) tail
    have hcur_eq :
        CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 (some a) ++ tail =
        0x12#8 :: rest := by
      have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := rfl
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk, rest, tlb_lenPrefixed,
        List.cons_append, List.nil_append, List.append_assoc]
    rw [hcur_eq] at hbs_split ⊢
    have hcur_le : (0x12#8 :: rest).length ≤ x.bs.length := by
      rw [hbs_split, List.length_append]; omega
    have hcur_lt : (0x12#8 :: rest).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hcur_suf : IsDropSuffix x.bs (0x12#8 :: rest) := e2u311_isDropSuffix_of_append hbs_split
    have hgt_lim : ¬ (0x12#8 :: rest).length ≤ limit := by
      dsimp only [rest, tlb_lenPrefixed]
      rw [List.length_cons, List.length_append, List.length_append]
      omega
    refine e2u311_ct1Sent_decode_key_dom_step hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hgt_lim hsp_align
      hcur_le hcur_lt hcur_suf (key := 18#64) (iwt := .lengthDelimited)
      rfl (by decide) rfl (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    obtain ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest_le : rest.length ≤ x.bs.length := by
      simp only [hbs_split, rest, List.length_append, List.length_cons]; omega
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
    have hrest_suf : IsDropSuffix x.bs rest :=
      e2u311_isDropSuffix_of_append (pre := pre ++ [0x12#8])
        (by simp only [hbs_split, List.append_assoc, List.singleton_append])
    apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 276#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
      rw [e2u311_ct1SentDomLoopPre_transport A lim st 0 0 0 s0 hvm_d]
      have h80 : (x.msgPtr + 0x48#64) + 8#64 = x.msgPtr + 80#64 := by bv_lin
      have h88 : (x.msgPtr + 0x48#64) + 16#64 = x.msgPtr + 88#64 := by bv_lin
      have h96 : (x.msgPtr + 0x48#64) + 24#64 = x.msgPtr + 96#64 := by bv_lin
      have h104 : (x.msgPtr + 0x48#64) + 32#64 = x.msgPtr + 104#64 := by bv_lin
      have h112 : (x.msgPtr + 0x48#64) + 40#64 = x.msgPtr + 112#64 := by bv_lin
      have h72 : x.msgPtr + 0x48#64 = x.msgPtr + 72#64 := rfl
      have hdef_zcap := e2u311_default_auth_cells_entails_zeroCap A.repAlloc (x.msgPtr + 0x48#64)
      rw [h80, h88, h96, h104, h112] at hdef_zcap
      conv at hdef_zcap => arg 1; rw [h72]
      apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 300#64)
      by_vm_steps
        (conv => arg 4; rw [e2u311_ct1SentDomLoopPre, memRegion_40_split_5_cells (x.msgPtr + 0x48#64),
          h80, h88, h96, h104, h112, h72])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v5
        apply SepWP.exists_elim; intro v4
        apply SepWP.exists_elim; intro v3
        apply SepWP.exists_elim; intro v2
        apply SepWP.exists_elim; intro v1
        wp_steps
        apply SepWP.fold hdef_zcap (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm_init => ?_⟩
        rw [e2u311_tightPoolAt_transport A lim st 0 0 0 hvm_init]
        let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
        let x_am : AuthMergeGhost :=
          ⟨.lengthDelimited, x.msgPtr + 0x48#64, default, x.bufRef, x.slot, restPtr, rest⟩
        have hDom_am : e2u311_AuthDomOf maxRoot maxMac x_am :=
          ⟨rfl, rfl, a, tail, hopt_valid a rfl, rfl⟩
        apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
        by_vm_steps
          (conv => arg 4; rw [e2u311_tightPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
            unchunkedMergeBelow_eq_authMergeStack s0.sp])
          (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
            sepConj_pure_left_comm])
          apply SepWP.exists_elim; intro evs
          apply SepWP.pure_elim; intro hevs
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_call => ?_⟩
          refine call_budget_lscro (x := (x_am, M.stepEvents evs st))
            (ret_pc := (blkPl_312).base + 312#64) hAuthTightCall
            (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
            (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
            (by simp only [arm64_norm, wp_norm])
            (by conv =>
                  lhs
                  dsimp only [e2u311_authMergeTightSpecDomOf, x_am]
                  rw [tlb_domHeap_of_dom hDom_am]
                  arg 2
                  simp only [A.pool_of_vmPreserved hvm_call, arm64_norm, wp_norm, hsp1])
            (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
              by simp only [arm64_norm, wp_norm, hx20_1],
              by simp only [arm64_norm, wp_norm, hx19_1],
              hrest_lt,
              e2u311_fitsEnv_step_tight hFit hevs
                (fun _ hge => tlb_guardedEnv_tight_of_dom hDom_am hge)
                (by omega) (by omega)
                (Nat.max_le.mpr ⟨Nat.zero_le _, hR⟩)⟩)
            (by sep_focus) ?_
          intro sm hpcm hrunm hspm hcsm
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
            hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
            at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
          have hrest_lt64 : rest.length < 2 ^ 64 :=
            Nat.lt_trans hrest_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
          have ⟨hraw_a, _, _⟩ := e2u311_lenPrefixed_sub_lt hrest_lt64
          have ham : (mergeMessage ProtoAuthenticator.mergeField
              (codecWireTypeToProto x_am.wt) x_am.msg x_am.bs 97).toOption = some (a, tail) := by
            dsimp only [x_am, codecWireTypeToProto]
            rw [e2u311_protoAuth_mergeMessage_roundtrip a tail 96 hraw_a]
            rfl
          have htail_le : tail.length ≤ rest.length := by
            dsimp only [rest, tlb_lenPrefixed]
            rw [List.length_append, List.length_append]; omega
          apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 152#64)
          by_vm_steps
            (conv => arg 4; simp only [e2u311_authMergeTightSpecDomOf, authMergeSpecOfEnv,
              ham, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro evs_am
            wp_focus_pure; intro htrm
            wp_focus_pure; intro hevs_am
            wp_focus_pure; intro hsm0
            (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1, ← unchunkedMergeBelow_eq_authMergeStack])
            apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf htail_le) (by sep_focus)
            apply SepWP.fold
              (e2u311_tightPoolAt_append_step (o₃ := authOps) (c₃ := authCum) (r₃ := authReq)
                A lim st sm hevs
                (tlb_guardedEnv_tight_of_dom hDom_am hevs_am)
                (by omega)
                (by omega)
                (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩))
              (by sep_focus)
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [e2u311_tightPoolAt_transport A lim st authOps authCum authReq hvm2]
            refine SepWPpLscro.weaken_pre ?_
              (hcont _
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr1])
                (by simp only [arm64_norm, wp_norm, hx19_m])
                (by simp only [arm64_norm, wp_norm, hx20_m])
                (by simp only [arm64_norm, wp_norm, hx21_m])
                (by simp only [arm64_norm, wp_norm, hx22_m])
                (by simp only [arm64_norm, wp_norm, hx23_m])
                ⟨by simp only [arm64_norm, wp_norm, hx24_m],
                 by simp only [arm64_norm, wp_norm, hx25_m],
                 by simp only [arm64_norm, wp_norm, hx26_m],
                 by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
            dsimp only [e2u311_ct1SentDomLoopPre, optProtoAuthenticatorCapAt, x_am]; sep_entail

private theorem e2u311_ct1Sent_field3_hdr_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {Q : State → SepProp → Prop} {R Hrest : SepProp}
    {o₁ c₁ r₁ o₂ c₂ r₂ maxHdr maxOps cumCap maxReq limit : Nat}
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {s0 s : State}
    {hdr pre tail : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hO1 : o₁ ≤ o₂) (hC1 : c₁ ≤ c₂) (hR1 : r₁ ≤ r₂)
    (hO2 : o₁ + 2 ≤ o₂)
    (hC2 : c₁ + 2 * spqrAllocTightCost (Nat.max 8 maxHdr) ≤ c₂)
    (hR2 : Nat.max r₁ (Nat.max 8 maxHdr) ≤ r₂)
    (hOmax : o₂ ≤ maxOps) (hCmax : c₂ ≤ cumCap) (hRmax : r₂ ≤ maxReq)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_tail : limit ≤ tail.length)
    (hhdr_max : hdr.length ≤ maxHdr)
    (hbs_split : x.bs = pre ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 hdr ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ct1SentDomLoopPre A lim st o₂ c₂ r₂ s0 s'
          (Hrest ∗ vecU8CapAt A.repAlloc x.msgPtr tail.length hdr)
          x.bufRef x.slot x.ptr x.bs tail)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ct1SentDomLoopPre A lim st o₁ c₁ r₁ s0 s
        (Hrest ∗ tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [])
        x.bufRef x.slot x.ptr x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 hdr ++ tail))
      Q (WppPanicFalse R) := by
  by_cases hhdr0 : hdr.isEmpty = true
  · have hhdrn : hdr = [] := List.isEmpty_iff.mp hhdr0
    subst hhdrn
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hhdr0, ↓reduceIte,
      List.nil_append]
    refine SepWPpLscro.weaken_pre ?_
      (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs)
    unfold e2u311_ct1SentDomLoopPre
    exact sepConj_mono (e2u311_tightPoolAt_mono A lim st hO1 hC1 hR1 s)
      (sepConj_mono
        (sepConj_mono_right (e2u311_vecU8ZeroCapAt_entails_vecU8CapAt A.repAlloc x.msgPtr tail.length []))
        (Entails.refl _))
  · let rest := tlb_lenPrefixed hdr tail
    have hcur_eq : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 hdr ++ tail =
        0x1a#8 :: rest := by
      have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] := rfl
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, hhdr0, Bool.false_eq_true,
        ↓reduceIte, hk, rest, tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]
    rw [hcur_eq] at hbs_split ⊢
    have hcur_le : (0x1a#8 :: rest).length ≤ x.bs.length := by
      rw [hbs_split, List.length_append]; omega
    have hcur_lt : (0x1a#8 :: rest).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hcur_suf : IsDropSuffix x.bs (0x1a#8 :: rest) := e2u311_isDropSuffix_of_append hbs_split
    have hgt_lim : ¬ (0x1a#8 :: rest).length ≤ limit := by
      dsimp only [rest, tlb_lenPrefixed]
      rw [List.length_cons, List.length_append, List.length_append]
      omega
    refine e2u311_ct1Sent_decode_key_dom_step hVarintCall hFit
      (Nat.le_trans hO1 hOmax) (Nat.le_trans hC1 hCmax) (Nat.le_trans hR1 hRmax)
      hgt_lim hsp_align hcur_le hcur_lt hcur_suf (key := 26#64) (iwt := .lengthDelimited)
      rfl (by decide) rfl (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    obtain ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest_le : rest.length ≤ x.bs.length := by
      simp only [hbs_split, rest, List.length_append, List.length_cons]; omega
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
    have hrest_suf : IsDropSuffix x.bs rest :=
      e2u311_isDropSuffix_of_append (pre := pre ++ [0x1a#8])
        (by simp only [hbs_split, List.append_assoc, List.singleton_append])
    apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 324#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      have hhdr_lt64 : hdr.length < 2 ^ 64 := by
        have hlt64 : rest.length < 2 ^ 64 :=
          Nat.lt_trans hrest_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
        exact (e2u311_lenPrefixed_sub_lt hlt64).1
      have hmb : mergeBytes .lengthDelimited rest = some (hdr, tail) :=
        e2u311_codec_mergeBytes_lenPrefixed hdr tail hhdr_lt64
      apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
      by_vm_steps
        (conv => arg 4; rw [e2u311_ct1SentDomLoopPre, e2u311_tightPoolAt, tlb_vecU8ZeroCapAt,
          sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_bytesMerge3 s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro ptr1
        apply SepWP.exists_elim; intro evs
        wp_focus_pure; intro hevs
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_call => ?_⟩
        let x_bm : BytesMergeGhost :=
          ⟨.lengthDelimited, x.msgPtr, 0#64, ptr1, [], x.bufRef, x.slot, restPtr, rest⟩
        refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
          (ret_pc := (blkPl_312).base + 336#64) hBytesCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm]
                arg 2
                simp only [A.pool_of_vmPreserved hvm_call, A.pool_of_vmPreserved hvm_d,
                  arm64_norm, wp_norm, hsp1])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
            by simp only [arm64_norm, wp_norm, hx20_1],
            by simp only [arm64_norm, wp_norm, hx19_1],
            hrest_lt,
            bytesMergeCapOk_zero,
            e2u311_fitsEnv_step_tight hFit hevs
              (fun _ hbm => e2u311_bytesMerge_zeroCap_tight x_bm hdr tail maxHdr rfl rfl hmb hhdr_max hbm)
              (Nat.le_trans hO2 hOmax) (Nat.le_trans hC2 hCmax) (Nat.le_trans hR2 hRmax)⟩)
          (by sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
          hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        have htail_le : tail.length ≤ rest.length := by
          dsimp only [rest, tlb_lenPrefixed]
          rw [List.length_append, List.length_append]; omega
        apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 152#64)
        by_vm_steps
          (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm, hmb,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_bm
          apply SepWP.exists_elim; intro cap1'
          apply SepWP.exists_elim; intro ptr1'
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_bm
          wp_focus_pure; intro hsm0
          wp_focus_pure; intro hcap1'
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
          apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf htail_le) (by sep_focus)
          have hhdr_cap : vecU8At A.repAlloc x.msgPtr cap1' ptr1' hdr ⊢
              vecU8CapAt A.repAlloc x.msgPtr tail.length hdr := by
            unfold vecU8CapAt
            refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
            exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
          apply SepWP.fold hhdr_cap (by sep_focus)
          apply SepWP.fold
            (e2u311_tightPoolAt_append_step A lim st sm hevs
              (e2u311_bytesMerge_zeroCap_tight x_bm hdr tail maxHdr rfl rfl hmb hhdr_max hevs_bm)
              hO2 hC2 hR2)
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [e2u311_tightPoolAt_transport A lim st o₂ c₂ r₂ hvm2]
          refine SepWPpLscro.weaken_pre ?_
            (hcont _
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr1])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm, hx21_m])
              (by simp only [arm64_norm, wp_norm, hx22_m])
              (by simp only [arm64_norm, wp_norm, hx23_m])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
          dsimp only [e2u311_ct1SentDomLoopPre]; sep_entail

private theorem e2u311_ct1Sent_field4_es_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {Q : State → SepProp → Prop} {R Hrest : SepProp}
    {o₁ c₁ r₁ o₂ c₂ r₂ maxEs maxOps cumCap maxReq limit : Nat}
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {s0 s : State}
    {es pre tail : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hO1 : o₁ ≤ o₂) (hC1 : c₁ ≤ c₂) (hR1 : r₁ ≤ r₂)
    (hO2 : o₁ + 2 ≤ o₂)
    (hC2 : c₁ + 2 * spqrAllocTightCost (Nat.max 8 maxEs) ≤ c₂)
    (hR2 : Nat.max r₁ (Nat.max 8 maxEs) ≤ r₂)
    (hOmax : o₂ ≤ maxOps) (hCmax : c₂ ≤ cumCap) (hRmax : r₂ ≤ maxReq)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_tail : limit ≤ tail.length)
    (hes_max : es.length ≤ maxEs)
    (hbs_split : x.bs = pre ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 es ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ct1SentDomLoopPre A lim st o₂ c₂ r₂ s0 s'
          (Hrest ∗ vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) tail.length es)
          x.bufRef x.slot x.ptr x.bs tail)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ct1SentDomLoopPre A lim st o₁ c₁ r₁ s0 s
        (Hrest ∗ tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [])
        x.bufRef x.slot x.ptr x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 es ++ tail))
      Q (WppPanicFalse R) := by
  by_cases hes0 : es.isEmpty = true
  · have hesn : es = [] := List.isEmpty_iff.mp hes0
    subst hesn
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hes0, ↓reduceIte,
      List.nil_append]
    refine SepWPpLscro.weaken_pre ?_
      (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs)
    unfold e2u311_ct1SentDomLoopPre
    exact sepConj_mono (e2u311_tightPoolAt_mono A lim st hO1 hC1 hR1 s)
      (sepConj_mono
        (sepConj_mono_right
          (e2u311_vecU8ZeroCapAt_entails_vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) tail.length []))
        (Entails.refl _))
  · let rest := tlb_lenPrefixed es tail
    have hcur_eq : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 es ++ tail =
        0x22#8 :: rest := by
      have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] := rfl
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, hes0, Bool.false_eq_true,
        ↓reduceIte, hk, rest, tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]
    rw [hcur_eq] at hbs_split ⊢
    have hcur_le : (0x22#8 :: rest).length ≤ x.bs.length := by
      rw [hbs_split, List.length_append]; omega
    have hcur_lt : (0x22#8 :: rest).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hcur_suf : IsDropSuffix x.bs (0x22#8 :: rest) := e2u311_isDropSuffix_of_append hbs_split
    have hgt_lim : ¬ (0x22#8 :: rest).length ≤ limit := by
      dsimp only [rest, tlb_lenPrefixed]
      rw [List.length_cons, List.length_append, List.length_append]
      omega
    refine e2u311_ct1Sent_decode_key_dom_step hVarintCall hFit
      (Nat.le_trans hO1 hOmax) (Nat.le_trans hC1 hCmax) (Nat.le_trans hR1 hRmax)
      hgt_lim hsp_align hcur_le hcur_lt hcur_suf (key := 34#64) (iwt := .lengthDelimited)
      rfl (by decide) rfl (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    obtain ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest_le : rest.length ≤ x.bs.length := by
      simp only [hbs_split, rest, List.length_append, List.length_cons]; omega
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
    have hrest_suf : IsDropSuffix x.bs rest :=
      e2u311_isDropSuffix_of_append (pre := pre ++ [0x22#8])
        (by simp only [hbs_split, List.append_assoc, List.singleton_append])
    apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 348#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      have hes_lt64 : es.length < 2 ^ 64 := by
        have hlt64 : rest.length < 2 ^ 64 :=
          Nat.lt_trans hrest_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
        exact (e2u311_lenPrefixed_sub_lt hlt64).1
      have hmb : mergeBytes .lengthDelimited rest = some (es, tail) :=
        e2u311_codec_mergeBytes_lenPrefixed es tail hes_lt64
      apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
      by_vm_steps
        (conv => arg 4; rw [e2u311_ct1SentDomLoopPre, e2u311_tightPoolAt, tlb_vecU8ZeroCapAt,
          sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_bytesMerge3 s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro ptr2
        apply SepWP.exists_elim; intro evs
        wp_focus_pure; intro hevs
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_call => ?_⟩
        let x_bm : BytesMergeGhost :=
          ⟨.lengthDelimited, x.msgPtr + 0x18#64, 0#64, ptr2, [], x.bufRef, x.slot, restPtr, rest⟩
        refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
          (ret_pc := (blkPl_312).base + 360#64) hBytesCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm]
                arg 2
                simp only [A.pool_of_vmPreserved hvm_call, A.pool_of_vmPreserved hvm_d,
                  arm64_norm, wp_norm, hsp1])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
            by simp only [arm64_norm, wp_norm, hx20_1],
            by simp only [arm64_norm, wp_norm, hx19_1],
            hrest_lt,
            bytesMergeCapOk_zero,
            e2u311_fitsEnv_step_tight hFit hevs
              (fun _ hbm => e2u311_bytesMerge_zeroCap_tight x_bm es tail maxEs rfl rfl hmb hes_max hbm)
              (Nat.le_trans hO2 hOmax) (Nat.le_trans hC2 hCmax) (Nat.le_trans hR2 hRmax)⟩)
          (by sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
          hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        have htail_le : tail.length ≤ rest.length := by
          dsimp only [rest, tlb_lenPrefixed]
          rw [List.length_append, List.length_append]; omega
        apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 152#64)
        by_vm_steps
          (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm, hmb,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_bm
          apply SepWP.exists_elim; intro cap2'
          apply SepWP.exists_elim; intro ptr2'
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_bm
          wp_focus_pure; intro hsm0
          wp_focus_pure; intro hcap2'
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
          apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf htail_le) (by sep_focus)
          have hes_cap : vecU8At A.repAlloc (x.msgPtr + 0x18#64) cap2' ptr2' es ⊢
              vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) tail.length es := by
            unfold vecU8CapAt
            refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
            exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
          apply SepWP.fold hes_cap (by sep_focus)
          apply SepWP.fold
            (e2u311_tightPoolAt_append_step A lim st sm hevs
              (e2u311_bytesMerge_zeroCap_tight x_bm es tail maxEs rfl rfl hmb hes_max hevs_bm)
              hO2 hC2 hR2)
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [e2u311_tightPoolAt_transport A lim st o₂ c₂ r₂ hvm2]
          refine SepWPpLscro.weaken_pre ?_
            (hcont _
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr1])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm, hx21_m])
              (by simp only [arm64_norm, wp_norm, hx22_m])
              (by simp only [arm64_norm, wp_norm, hx23_m])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
          dsimp only [e2u311_ct1SentDomLoopPre, x_bm]; sep_entail

private theorem e2u311_ct1Sent_field5_ct1_dom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {Q : State → SepProp → Prop} {R Hrest : SepProp}
    {o₁ c₁ r₁ maxCt1 maxOps cumCap maxReq limit : Nat}
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {s0 s : State}
    {ct1 pre tail : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hO1 : o₁ ≤ maxOps) (hC1 : c₁ ≤ cumCap) (hR1 : r₁ ≤ maxReq)
    (hO2 : o₁ + 2 ≤ maxOps)
    (hC2 : c₁ + 2 * spqrAllocTightCost (Nat.max 8 maxCt1) ≤ cumCap)
    (hR2 : Nat.max r₁ (Nat.max 8 maxCt1) ≤ maxReq)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_tail : limit ≤ tail.length)
    (hct1_max : ct1.length ≤ maxCt1)
    (hbs_split : x.bs = pre ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ct1 ++ tail))
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_312).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s'
        (e2u311_ct1SentDomLoopPre A lim st maxOps cumCap maxReq s0 s'
          (Hrest ∗ vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) tail.length ct1)
          x.bufRef x.slot x.ptr x.bs tail)
        Q (WppPanicFalse R))
    (hpc : s.pc = (blkPl_312).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
      (e2u311_ct1SentDomLoopPre A lim st o₁ c₁ r₁ s0 s
        (Hrest ∗ tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [])
        x.bufRef x.slot x.ptr x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ct1 ++ tail))
      Q (WppPanicFalse R) := by
  by_cases hct10 : ct1.isEmpty = true
  · have hct1n : ct1 = [] := List.isEmpty_iff.mp hct10
    subst hct1n
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hct10, ↓reduceIte,
      List.nil_append]
    refine SepWPpLscro.weaken_pre ?_
      (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs)
    unfold e2u311_ct1SentDomLoopPre
    exact sepConj_mono (e2u311_tightPoolAt_mono A lim st hO1 hC1 hR1 s)
      (sepConj_mono
        (sepConj_mono_right
          (e2u311_vecU8ZeroCapAt_entails_vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) tail.length []))
        (Entails.refl _))
  · let rest := tlb_lenPrefixed ct1 tail
    have hcur_eq : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ct1 ++ tail =
        0x2a#8 :: rest := by
      have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 5#32 .lengthDelimited = [0x2a#8] := rfl
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, hct10, Bool.false_eq_true,
        ↓reduceIte, hk, rest, tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]
    rw [hcur_eq] at hbs_split ⊢
    have hcur_le : (0x2a#8 :: rest).length ≤ x.bs.length := by
      rw [hbs_split, List.length_append]; omega
    have hcur_lt : (0x2a#8 :: rest).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hcur_suf : IsDropSuffix x.bs (0x2a#8 :: rest) := e2u311_isDropSuffix_of_append hbs_split
    have hgt_lim : ¬ (0x2a#8 :: rest).length ≤ limit := by
      dsimp only [rest, tlb_lenPrefixed]
      rw [List.length_cons, List.length_append, List.length_append]
      omega
    refine e2u311_ct1Sent_decode_key_dom_step hVarintCall hFit
      hO1 hC1 hR1 hgt_lim hsp_align hcur_le hcur_lt hcur_suf (key := 42#64) (iwt := .lengthDelimited)
      rfl (by decide) rfl (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1
    obtain ⟨hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest_le : rest.length ≤ x.bs.length := by
      simp only [hbs_split, rest, List.length_append, List.length_cons]; omega
    have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
    have hrest_suf : IsDropSuffix x.bs rest :=
      e2u311_isDropSuffix_of_append (pre := pre ++ [0x2a#8])
        (by simp only [hbs_split, List.append_assoc, List.singleton_append])
    apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 236#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      have hct1_lt64 : ct1.length < 2 ^ 64 := by
        have hlt64 : rest.length < 2 ^ 64 :=
          Nat.lt_trans hrest_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
        exact (e2u311_lenPrefixed_sub_lt hlt64).1
      have hmb : mergeBytes .lengthDelimited rest = some (ct1, tail) :=
        e2u311_codec_mergeBytes_lenPrefixed ct1 tail hct1_lt64
      apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
      by_vm_steps
        (conv => arg 4; rw [e2u311_ct1SentDomLoopPre, e2u311_tightPoolAt, tlb_vecU8ZeroCapAt,
          sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_bytesMerge3 s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro ptr3
        apply SepWP.exists_elim; intro evs
        wp_focus_pure; intro hevs
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_call => ?_⟩
        let x_bm : BytesMergeGhost :=
          ⟨.lengthDelimited, x.msgPtr + 0x30#64, 0#64, ptr3, [], x.bufRef, x.slot, restPtr, rest⟩
        refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
          (ret_pc := (blkPl_312).base + 248#64) hBytesCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm]
                arg 2
                simp only [A.pool_of_vmPreserved hvm_call, A.pool_of_vmPreserved hvm_d,
                  arm64_norm, wp_norm, hsp1])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
            by simp only [arm64_norm, wp_norm, hx20_1],
            by simp only [arm64_norm, wp_norm, hx19_1],
            hrest_lt,
            bytesMergeCapOk_zero,
            e2u311_fitsEnv_step_tight hFit hevs
              (fun _ hbm => e2u311_bytesMerge_zeroCap_tight x_bm ct1 tail maxCt1 rfl rfl hmb hct1_max hbm)
              hO2 hC2 hR2⟩)
          (by sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
          hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        have htail_le : tail.length ≤ rest.length := by
          dsimp only [rest, tlb_lenPrefixed]
          rw [List.length_append, List.length_append]; omega
        apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 152#64)
        by_vm_steps
          (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, BytesMerge3Env, x_bm, hmb,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_bm
          apply SepWP.exists_elim; intro cap3'
          apply SepWP.exists_elim; intro ptr3'
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_bm
          wp_focus_pure; intro hsm0
          wp_focus_pure; intro hcap3'
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
          apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf htail_le) (by sep_focus)
          have hct1_cap : vecU8At A.repAlloc (x.msgPtr + 0x30#64) cap3' ptr3' ct1 ⊢
              vecU8CapAt A.repAlloc (x.msgPtr + 0x30#64) tail.length ct1 := by
            unfold vecU8CapAt
            refine Entails.trans (Entails.pure_right hcap3' (Entails.refl _)) ?_
            exact Entails.sepExists_right cap3' (Entails.sepExists_right ptr3' (Entails.refl _))
          apply SepWP.fold hct1_cap (by sep_focus)
          apply SepWP.fold
            (e2u311_tightPoolAt_append_step A lim st sm hevs
              (e2u311_bytesMerge_zeroCap_tight x_bm ct1 tail maxCt1 rfl rfl hmb hct1_max hevs_bm)
              hO2 hC2 hR2)
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [e2u311_tightPoolAt_transport A lim st maxOps cumCap maxReq hvm2]
          refine SepWPpLscro.weaken_pre ?_
            (hcont _
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr1])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm, hx21_m])
              (by simp only [arm64_norm, wp_norm, hx22_m])
              (by simp only [arm64_norm, wp_norm, hx23_m])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
          dsimp only [e2u311_ct1SentDomLoopPre, x_bm]; sep_entail

private theorem e2u311_ct1Sent_dom_own_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {maxRoot maxMac maxHdr maxEs maxCt1 authOps authCum authReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 6 ≤ maxOps)
    (hCum : authCum + 2 * spqrAllocTightCost (Nat.max 8 maxHdr) +
      2 * spqrAllocTightCost (Nat.max 8 maxEs) +
      2 * spqrAllocTightCost (Nat.max 8 maxCt1) ≤ cumCap)
    (hReq : Nat.max authReq
      (Nat.max (Nat.max 8 maxHdr) (Nat.max (Nat.max 8 maxEs) (Nat.max 8 maxCt1))) ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (e2u311_authMergeTightSpecDomOf A lim (e2u311_AuthDomOf maxRoot maxMac)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)))) :
    subroutine_ok ((blkPC_312).rebase (blkPl_312).base H)
      (blkPl_312).base
      (withLsCodeRoLoaded lsmpl
        (e2u311_ct1SentDomOwnSpec A lim
          (e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1)
          maxOps cumCap maxReq)) := by
  let Dom := e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2u311_ct1SentDomOwnSpec
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2u311_ct1SentDomOwnSpec A lim Dom maxOps cumCap maxReq) (x, st) R s0)
    (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  rintro ⟨h_1, h_2, h_3, hbs_lt, hDom, hFit⟩
  obtain ⟨hwt_p, hmsg_def, pb, after, hpb, hbs_eq⟩ := hDom
  have hwt_ld : x.wt = .lengthDelimited := e2u311_wt_eq_lengthDelimited hwt_p
  have hbs_lt64 : x.bs.length < 2 ^ 64 :=
    Nat.lt_trans hbs_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
  have hsome : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (pb, after) := by
    rw [hwt_p, hmsg_def, hbs_eq, e2u311_ct1Sent_mergeMessage_roundtrip pb after
      (hbs_eq ▸ hbs_lt64)]
    rfl
  let raw := V1State.Unchunked.Ct1Sent.encodeRaw pb
  let rest0 := raw ++ after
  have hbs_raw : x.bs = CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
      (BitVec.ofNat 64 raw.length) ++ rest0 := by
    simp only [hbs_eq, tlb_lenPrefixed, raw, rest0, List.append_assoc]
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw.length, rest0) := by
    rw [hbs_raw]
    exact e2u311_codec_decodeVarint_proto_encodeVarint (BitVec.ofNat 64 raw.length) rest0
  have hraw_lt64 : raw.length < 2 ^ 64 :=
    (e2u311_lenPrefixed_sub_lt (hbs_eq ▸ hbs_lt64)).1
  have hlen_nat : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_lt64]
  have hge_len : ¬ rest0.length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hlen_nat]; dsimp only [rest0]; rw [List.length_append]; omega
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hule := ule_len_of_ge hge_len hrest0_lt
  have hsub := bv_len_sub_limit hge_len
  have hlim_raw : rest0.length - raw.length = after.length := by
    dsimp only [rest0]; rw [List.length_append]; omega
  have hlim_eq : rest0.length - (BitVec.ofNat 64 raw.length).toNat = after.length := by
    rw [hlen_nat]; exact hlim_raw
  have hsaved :
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        memRegion (s0.sp - 40#64) 8 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      unchunkedSavedRegs s0.sp s0 := Entails.refl _
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [stackAt_unchunkedMerge s0.sp, unchunkedMergeBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v_lr
    apply SepWP.exists_elim; intro v_fp
    wp_steps
    apply SepWP.fold hsaved (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st))
      (ret_pc := (blkPl_312).base + 52#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2u311_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
      (by exact ⟨by simp only [arm64_norm, wp_norm, h_3],
        hbs_lt,
        by simpa only [AllocCostModel.stepEvents, List.foldl] using
             e2u311_fitsEnv_step_tight hFit (SpqrTightEvs.nil 0 0 0)
               (e2u311_decodeVarint2Env_tight_of_some hdv0)
               (Nat.zero_le _) (Nat.zero_le _)
               (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩)⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := (blkPl_312).base + 152#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2u311_stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (e2u311_tightPoolAt_nil_step (o := 0) (c := 0) (r := 0) A lim st sm hdv0 (SpqrTightEvs.nil 0 0 0) hevs_dv)
        (by simp only [M.stepEvents_nil]; sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [e2u311_tightPoolAt_transport A lim st 0 0 0 hvm2]
      let f1 := CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 pb.epoch
      let f2 := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 pb.auth
      let f3 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 pb.hdr
      let f4 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 pb.es
      let f5 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 pb.ct1
      let p0 := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 raw.length)
      let cur5 := f5 ++ after
      let cur4 := f4 ++ cur5
      let cur3 := f3 ++ cur4
      let cur2 := f2 ++ cur3
      have hrest0_eq : rest0 = f1 ++ cur2 := by
        dsimp only [rest0, raw, V1State.Unchunked.Ct1Sent.encodeRaw, f1, f2, f3, f4, f5, cur2, cur3, cur4, cur5]
        simp only [List.append_assoc]
      let cHdr := 2 * spqrAllocTightCost (Nat.max 8 maxHdr)
      let cEs := 2 * spqrAllocTightCost (Nat.max 8 maxEs)
      let cCt1 := 2 * spqrAllocTightCost (Nat.max 8 maxCt1)
      let rHdr := Nat.max 8 maxHdr
      let rEs := Nat.max 8 maxEs
      let rCt1 := Nat.max 8 maxCt1
      have hCum' : authCum + cHdr + cEs + cCt1 ≤ cumCap := hCum
      have hReq_auth : authReq ≤ maxReq := Nat.le_trans (Nat.le_max_left _ _) hReq
      have hReq_hdr : rHdr ≤ maxReq :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hReq
      have hReq_es : rEs ≤ maxReq :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hReq
      have hReq_ct1 : rCt1 ≤ maxReq :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))) hReq
      refine SepWPpLscro.weaken_pre ?_
        (e2u311_ct1Sent_field1_epoch_dom hVarintCall
          (Hrest := tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
            tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
            tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
            (((x.msgPtr + 0x48#64) ↦₆₄ 0xffffffffffffffff#64) ∗
              memRegion (x.msgPtr + 0x48#64 + 8#64) 40))
          (limit := after.length) (epoch := pb.epoch) (pre := p0) (tail := cur2)
          hFit hsp_align hbs_lt
          (by dsimp only [cur2, cur3, cur4, cur5]; simp only [List.length_append]; omega)
          (by rw [hbs_raw, hrest0_eq])
          (fun s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 => ?_)
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hsm1, hsub, hlim_eq, hlim_raw])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
      · have hdef_zero :
            tlb_ucCt1SentZeroCapAt A.repAlloc x.msgPtr default =
              tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
              (((x.msgPtr + 0x48#64) ↦₆₄ 0xffffffffffffffff#64) ∗
                memRegion (x.msgPtr + 0x48#64 + 8#64) 40) ∗
              ((x.msgPtr + 0x78#64) ↦₆₄ 0#64) := rfl
        rw [hmsg_def, hdef_zero]
        dsimp only [e2u311_ct1SentDomLoopPre]
        rw [← hrest0_eq, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        exact Entails.of_eq (by sep_ac_rfl)
      · refine SepWPpLscro.weaken_pre ?_
          (e2u311_ct1Sent_field2_auth_dom hVarintCall hAuthTightCall
            (Hrest := tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
              ((x.msgPtr + 0x78#64) ↦₆₄ pb.epoch))
            (limit := after.length) (opt := pb.auth) (pre := p0 ++ f1) (tail := cur3)
            hFit (by omega) (by omega) hReq_auth hsp_align hbs_lt
            (by dsimp only [cur3, cur4, cur5]; simp only [List.length_append]; omega)
            hpb.1
            (by rw [hbs_raw, hrest0_eq]; dsimp only [p0, f1, f2, cur2]; simp only [List.append_assoc])
            (fun s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hcs2 => ?_)
            hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1)
        · dsimp only [e2u311_ct1SentDomLoopPre, cur2]; sep_entail
        · refine SepWPpLscro.weaken_pre ?_
            (e2u311_ct1Sent_field3_hdr_dom hVarintCall hBytesCall
              (Hrest := tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
                tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
                optProtoAuthenticatorCapAt A.repAlloc (x.msgPtr + 0x48#64) cur3.length pb.auth ∗
                ((x.msgPtr + 0x78#64) ↦₆₄ pb.epoch))
              (o₁ := authOps) (c₁ := authCum) (r₁ := authReq)
              (o₂ := authOps + 2) (c₂ := authCum + cHdr) (r₂ := Nat.max authReq rHdr)
              (maxHdr := maxHdr) (limit := after.length) (hdr := pb.hdr)
              (pre := p0 ++ f1 ++ f2) (tail := cur4)
              hFit (by omega) (by omega) (Nat.le_max_left _ _)
              (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
              (by omega) (by omega) (Nat.max_le.mpr ⟨hReq_auth, hReq_hdr⟩)
              hsp_align hbs_lt
              (by dsimp only [cur4, cur5]; simp only [List.length_append]; omega)
              hpb.2.1
              (by rw [hbs_raw, hrest0_eq]; dsimp only [p0, f1, f2, f3, cur2, cur3]; simp only [List.append_assoc])
              (fun s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs3 => ?_)
              hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hcs2)
          · dsimp only [e2u311_ct1SentDomLoopPre, cur3]; sep_entail
          · refine SepWPpLscro.weaken_pre ?_
              (e2u311_ct1Sent_field4_es_dom hVarintCall hBytesCall
                (Hrest := vecU8CapAt A.repAlloc x.msgPtr cur4.length pb.hdr ∗
                  tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
                  optProtoAuthenticatorCapAt A.repAlloc (x.msgPtr + 0x48#64) cur3.length pb.auth ∗
                  ((x.msgPtr + 0x78#64) ↦₆₄ pb.epoch))
                (o₁ := authOps + 2) (c₁ := authCum + cHdr) (r₁ := Nat.max authReq rHdr)
                (o₂ := authOps + 4) (c₂ := authCum + cHdr + cEs)
                (r₂ := Nat.max (Nat.max authReq rHdr) rEs)
                (maxEs := maxEs) (limit := after.length) (es := pb.es)
                (pre := p0 ++ f1 ++ f2 ++ f3) (tail := cur5)
                hFit (by omega) (by omega) (Nat.le_max_left _ _)
                (by omega) (Nat.le_refl _) (Nat.le_refl _)
                (by omega) (by omega)
                (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hReq_auth, hReq_hdr⟩, hReq_es⟩)
                hsp_align hbs_lt
                (by dsimp only [cur5]; rw [List.length_append]; omega)
                hpb.2.2.1
                (by rw [hbs_raw, hrest0_eq]; dsimp only [p0, f1, f2, f3, f4, cur2, cur3, cur4]; simp only [List.append_assoc])
                (fun s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hcs4 => ?_)
                hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs3)
            · dsimp only [e2u311_ct1SentDomLoopPre, cur4]; sep_entail
            · refine SepWPpLscro.weaken_pre ?_
                (e2u311_ct1Sent_field5_ct1_dom hVarintCall hBytesCall
                  (Hrest := vecU8CapAt A.repAlloc x.msgPtr cur4.length pb.hdr ∗
                    vecU8CapAt A.repAlloc (x.msgPtr + 0x18#64) cur5.length pb.es ∗
                    optProtoAuthenticatorCapAt A.repAlloc (x.msgPtr + 0x48#64) cur3.length pb.auth ∗
                    ((x.msgPtr + 0x78#64) ↦₆₄ pb.epoch))
                  (o₁ := authOps + 4) (c₁ := authCum + cHdr + cEs)
                  (r₁ := Nat.max (Nat.max authReq rHdr) rEs)
                  (maxCt1 := maxCt1) (limit := after.length) (ct1 := pb.ct1)
                  (pre := p0 ++ f1 ++ f2 ++ f3 ++ f4) (tail := after)
                  hFit (by omega) (by omega)
                  (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hReq_auth, hReq_hdr⟩, hReq_es⟩)
                  (by omega) hCum'
                  (Nat.max_le.mpr
                    ⟨Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hReq_auth, hReq_hdr⟩, hReq_es⟩, hReq_ct1⟩)
                  hsp_align hbs_lt (Nat.le_refl _) hpb.2.2.2
                  (by rw [hbs_raw, hrest0_eq]; dsimp only [p0, f1, f2, f3, f4, f5, cur2, cur3, cur4, cur5]; simp only [List.append_assoc])
                  (fun s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hcs5 => ?_)
                  hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hcs4)
              · dsimp only [e2u311_ct1SentDomLoopPre, cur5]; sep_entail
              · refine SepWPpLscro.weaken_pre ?_
                  (e2u311_ct1Sent_exit_dom
                    (Dom := Dom) (m := pb) (after := after)
                    ⟨hwt_p, hmsg_def, pb, after, hpb, hbs_eq⟩ hsome hsp_align
                    (by rw [hbs_raw, hrest0_eq]; dsimp only [cur2, cur3, cur4, cur5]; simp only [List.length_append]; omega)
                    (e2u311_isDropSuffix_of_append (pre := p0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5)
                      (by rw [hbs_raw, hrest0_eq]; dsimp only [p0, f1, f2, f3, f4, f5, cur2, cur3, cur4, cur5]; simp only [List.append_assoc]))
                    hpc5 hrun5 hsp5 htr5 hx21_5 hx22_5 hcs5)
                have hhdr_m := vecU8CapAt_mono_u A.repAlloc x.msgPtr pb.hdr
                  (by dsimp only [cur4, cur5]; simp only [List.length_append]; omega : after.length ≤ cur4.length)
                have hes_m := vecU8CapAt_mono_u A.repAlloc (x.msgPtr + 0x18#64) pb.es
                  (by dsimp only [cur5]; rw [List.length_append]; omega : after.length ≤ cur5.length)
                have hauth_m := optProtoAuthenticatorCapAt_mono A.repAlloc (x.msgPtr + 0x48#64) pb.auth
                  (by dsimp only [cur3, cur4, cur5]; simp only [List.length_append]; omega : after.length ≤ cur3.length)
                dsimp only [e2u311_ct1SentDomLoopPre, protoUnchunkedCt1SentCapAt]
                refine Entails.trans
                  (sepConj_mono_right (sepConj_mono_left
                    (sepConj_mono_left (sepConj_mono hhdr_m (sepConj_mono hes_m (sepConj_mono_left hauth_m))))))
                  (Entails.of_eq (by sep_ac_rfl))

/-! ## 5. Parametric Guarded-Tight Theorems for Blocks `311` and `312` -/

/-- Fully parametric Block `311` (`V1State.Unchunked.EkSentCt1Received::merge`) guarded-tight
contract on `(blkPC_311).rebase (blkPl_311).base H`: takes explicit per-field byte bounds
`(maxRoot, maxMac, maxDk, maxCt1)` and derives `(maxOps, cumCap, maxReq)` from
`bytesMergeEventsCore` (`2` non-free ops per `bytes` field `dk` and `ct1` + `authOps`). -/
theorem e2u311_unchunkedEkSentCt1Received_merge_blk_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {maxRoot maxMac maxDk maxCt1 authOps authCum authReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 4 ≤ maxOps)
    (hCum : authCum + 2 * spqrAllocTightCost (Nat.max 8 maxDk) +
      2 * spqrAllocTightCost (Nat.max 8 maxCt1) ≤ cumCap)
    (hReq : Nat.max authReq (Nat.max (Nat.max 8 maxDk) (Nat.max 8 maxCt1)) ≤ maxReq)
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (e2u311_authMergeTightSpecDomOf A lim (e2u311_AuthDomOf maxRoot maxMac)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)))) :
    subroutine_ok ((blkPC_311).rebase (blkPl_311).base H)
      (blkPl_311).base
      (withLsCodeRoLoaded lsmpl
        (e2u311_ucEkSentCt1ReceivedMergeTightSpecDomOf A lim
          (e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1)
          (tlb_GuardedEnv (e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1)
            (SpqrTightEvs maxOps cumCap maxReq) UnchunkedEkSentCt1ReceivedMergeEnv)
          (tlb_GuardedEnv (e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1)
            (SpqrTightEvs maxOps cumCap maxReq) UnchunkedEkSentCt1ReceivedMergeEnv))) := by
  have hKleene := unchunkedEkSentCt1ReceivedMerge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hDom : e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1 x.1
  · have hDomOwn := e2u311_ekSent_dom_own_ok hOps hCum hReq hVarintCall hBytesCall hAuthTightCall
    let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
    have hpre_dom : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl
          (e2u311_ekSentDomOwnSpec A lim
            (e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1)
            maxOps cumCap maxReq)).pre x s0 ∗ (R_extra ∗ R) := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, e2u311_ucEkSentCt1ReceivedMergeTightSpecDomOf,
        e2u311_ekSentDomOwnSpec, R_extra]
      rw [tlb_domHeap_of_dom hDom, stackAt_unchunkedMergeStack_eq_own s0.sp]
      simp only [sepConj_assoc]
      refine sepConj_mono ?_ (Entails.of_eq (by sep_ac_rfl))
      rw [← sepConj_emp ⌜_⌝]
      refine Entails.pure_left fun hp => ?_
      rw [← sepConj_emp ⌜_⌝]
      exact Entails.pure_right ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hDom,
        fun evs ht => hp.2.2.2.2 evs (Or.inl ⟨hDom, ht⟩)⟩ (Entails.refl emp)
    refine hDomOwn.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre_dom hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      have hpost_eq :
          (withLsCodeRoLoaded lsmpl
            (e2u311_ucEkSentCt1ReceivedMergeTightSpecDomOf A lim
              (e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1)
              (tlb_GuardedEnv (e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1)
                (SpqrTightEvs maxOps cumCap maxReq) UnchunkedEkSentCt1ReceivedMergeEnv)
              (tlb_GuardedEnv (e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1)
                (SpqrTightEvs maxOps cumCap maxReq) UnchunkedEkSentCt1ReceivedMergeEnv))).post x s0 sf ∗ R =
          (withLsCodeRoLoaded lsmpl
            (e2u311_ekSentDomOwnSpec A lim
              (e2u311_UcEkSentCt1ReceivedDomOf maxRoot maxMac maxDk maxCt1)
              maxOps cumCap maxReq)).post x s0 sf ∗ (R_extra ∗ R) := by
        have hbs_lt : x.1.bs.length < 2 ^ 63 := by
          have hp0 := hpre_dom
          dsimp only [withLsCodeRoLoaded, e2u311_ekSentDomOwnSpec] at hp0
          simp only [sepConj_assoc] at hp0
          rw [satisfies_pure_sepConj] at hp0
          exact hp0.1.2.2.2.1
        obtain ⟨hwt_p, hmsg_def, pb, after, _, hbs_eq⟩ := hDom
        have hbs_lt64 : x.1.bs.length < 2 ^ 64 :=
          Nat.lt_trans hbs_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
        have hsome : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
            (codecWireTypeToProto x.1.wt) x.1.msg x.1.bs 98).toOption = some (pb, after) := by
          rw [hwt_p, hmsg_def, hbs_eq, e2u311_ekSentCt1Received_mergeMessage_roundtrip pb after
            (hbs_eq ▸ hbs_lt64)]
          rfl
        dsimp only [withLsCodeRoLoaded, e2u311_ucEkSentCt1ReceivedMergeTightSpecDomOf,
          e2u311_ekSentDomOwnSpec, unchunkedEkSentCt1ReceivedMergeSpecOfEnv,
          unchunkedEkSentCt1ReceivedMergeOwnSpecOfEnv, R_extra,
          unchunkedEkSentCt1ReceivedPBCapAt, optAuthenticatorPBCapAt,
          protoUnchunkedEkSentCt1ReceivedCapAt, vecU8CapAt, optProtoAuthenticatorCapAt]
        rw [hsome, stackAt_unchunkedMergeStack_eq_own s0.sp]
        rcases hauth : pb.auth with _ | auth <;> simp only [hauth] <;> sep_ac_rfl
      rw [hpost_eq]
      exact hq
    · dsimp only [withLsCodeRoLoaded, e2u311_ekSentDomOwnSpec] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, e2u311_ekSentDomOwnSpec] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, e2u311_ekSentDomOwnSpec] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
  · have hpre_kl : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, e2u311_ucEkSentCt1ReceivedMergeTightSpecDomOf,
        unchunkedEkSentCt1ReceivedMergeSpec, unchunkedEkSentCt1ReceivedMergeSpecOfEnv]
      rw [tlb_domHeap_of_not_dom hDom]
      refine sepConj_mono_left (sepConj_mono_left ?_)
      refine Entails.pure_left fun hp =>
        Entails.pure_right ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
          tlb_fitsEnv_fallback_of_not_dom hDom hp.2.2.2.2⟩ (Entails.refl _)
    refine hKleene.mono_outcome x R s0 hpc hrun hpre_kl hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, Satisfies.mono ?_ hq⟩
      dsimp only [withLsCodeRoLoaded, e2u311_ucEkSentCt1ReceivedMergeTightSpecDomOf,
        unchunkedEkSentCt1ReceivedMergeSpec, unchunkedEkSentCt1ReceivedMergeSpecOfEnv]
      refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
      refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
      exact Entails.sepExists_right evs
        (Entails.pure_right (Or.inr ⟨hDom, unchunkedEkSentCt1ReceivedMergePostEnv_imp_pre hevs⟩)
          (Entails.refl _))
    · dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeSpec,
        unchunkedEkSentCt1ReceivedMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeSpec,
        unchunkedEkSentCt1ReceivedMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, unchunkedEkSentCt1ReceivedMergeSpec,
        unchunkedEkSentCt1ReceivedMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1

/-- Fully parametric Block `312` (`V1State.Unchunked.Ct1Sent::merge`) guarded-tight contract on
`(blkPC_312).rebase (blkPl_312).base H`: takes explicit per-field byte bounds
`(maxRoot, maxMac, maxHdr, maxEs, maxCt1)` and derives `(maxOps, cumCap, maxReq)` from
`bytesMergeEventsCore` (`2` non-free ops per `bytes` field `hdr`, `es`, `ct1` + `authOps`). -/
theorem e2u311_unchunkedCt1Sent_merge_blk_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {maxRoot maxMac maxHdr maxEs maxCt1 authOps authCum authReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 6 ≤ maxOps)
    (hCum : authCum + 2 * spqrAllocTightCost (Nat.max 8 maxHdr) +
      2 * spqrAllocTightCost (Nat.max 8 maxEs) +
      2 * spqrAllocTightCost (Nat.max 8 maxCt1) ≤ cumCap)
    (hReq : Nat.max authReq
      (Nat.max (Nat.max 8 maxHdr) (Nat.max (Nat.max 8 maxEs) (Nat.max 8 maxCt1))) ≤ maxReq)
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (e2u311_authMergeTightSpecDomOf A lim (e2u311_AuthDomOf maxRoot maxMac)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv (e2u311_AuthDomOf maxRoot maxMac)
            (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)))) :
    subroutine_ok ((blkPC_312).rebase (blkPl_312).base H)
      (blkPl_312).base
      (withLsCodeRoLoaded lsmpl
        (e2u311_ucCt1SentMergeTightSpecDomOf A lim
          (e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1)
          (tlb_GuardedEnv (e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1)
            (SpqrTightEvs maxOps cumCap maxReq) UnchunkedCt1SentMergeEnv)
          (tlb_GuardedEnv (e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1)
            (SpqrTightEvs maxOps cumCap maxReq) UnchunkedCt1SentMergeEnv))) := by
  have hKleene := unchunkedCt1SentMerge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hDom : e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1 x.1
  · have hBytesBudgetCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
        (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)) :=
      bytesMerge3RawSpec_eq_polyCommon A lim ▸ hBytesCall
    have hDomOwn := e2u311_ct1Sent_dom_own_ok hOps hCum hReq hVarintCall hBytesBudgetCall hAuthTightCall
    let R_extra : SepProp := memRegion (s0.sp - BitVec.ofNat 64 unchunkedMergeStack) 48
    have hpre_dom : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl
          (e2u311_ct1SentDomOwnSpec A lim
            (e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1)
            maxOps cumCap maxReq)).pre x s0 ∗ (R_extra ∗ R) := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, e2u311_ucCt1SentMergeTightSpecDomOf,
        e2u311_ct1SentDomOwnSpec, R_extra]
      rw [tlb_domHeap_of_dom hDom, stackAt_unchunkedMergeStack_eq_own s0.sp]
      simp only [sepConj_assoc]
      refine sepConj_mono ?_ (Entails.of_eq (by sep_ac_rfl))
      rw [← sepConj_emp ⌜_⌝]
      refine Entails.pure_left fun hp => ?_
      rw [← sepConj_emp ⌜_⌝]
      exact Entails.pure_right ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hDom,
        fun evs ht => hp.2.2.2.2 evs (Or.inl ⟨hDom, ht⟩)⟩ (Entails.refl emp)
    refine hDomOwn.mono_outcome x (R_extra ∗ R) s0 hpc hrun hpre_dom hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      have hpost_eq :
          (withLsCodeRoLoaded lsmpl
            (e2u311_ucCt1SentMergeTightSpecDomOf A lim
              (e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1)
              (tlb_GuardedEnv (e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1)
                (SpqrTightEvs maxOps cumCap maxReq) UnchunkedCt1SentMergeEnv)
              (tlb_GuardedEnv (e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1)
                (SpqrTightEvs maxOps cumCap maxReq) UnchunkedCt1SentMergeEnv))).post x s0 sf ∗ R =
          (withLsCodeRoLoaded lsmpl
            (e2u311_ct1SentDomOwnSpec A lim
              (e2u311_UcCt1SentDomOf maxRoot maxMac maxHdr maxEs maxCt1)
              maxOps cumCap maxReq)).post x s0 sf ∗ (R_extra ∗ R) := by
        have hbs_lt : x.1.bs.length < 2 ^ 63 := by
          have hp0 := hpre_dom
          dsimp only [withLsCodeRoLoaded, e2u311_ct1SentDomOwnSpec] at hp0
          simp only [sepConj_assoc] at hp0
          rw [satisfies_pure_sepConj] at hp0
          exact hp0.1.2.2.2.1
        obtain ⟨hwt_p, hmsg_def, pb, after, _, hbs_eq⟩ := hDom
        have hbs_lt64 : x.1.bs.length < 2 ^ 64 :=
          Nat.lt_trans hbs_lt (by decide : (2 ^ 63 : Nat) < 2 ^ 64)
        have hsome : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
            (codecWireTypeToProto x.1.wt) x.1.msg x.1.bs 98).toOption = some (pb, after) := by
          rw [hwt_p, hmsg_def, hbs_eq, e2u311_ct1Sent_mergeMessage_roundtrip pb after
            (hbs_eq ▸ hbs_lt64)]
          rfl
        dsimp only [withLsCodeRoLoaded, e2u311_ucCt1SentMergeTightSpecDomOf,
          e2u311_ct1SentDomOwnSpec, unchunkedCt1SentMergeSpecOfEnv,
          unchunkedCt1SentMergeOwnSpecOfEnv, R_extra,
          unchunkedCt1SentPBCapAt, optAuthenticatorPBCapAt,
          protoUnchunkedCt1SentCapAt, vecU8CapAt, optProtoAuthenticatorCapAt]
        rw [hsome, stackAt_unchunkedMergeStack_eq_own s0.sp]
        rcases hauth : pb.auth with _ | auth <;> simp only [hauth] <;> sep_ac_rfl
      rw [hpost_eq]
      exact hq
    · dsimp only [withLsCodeRoLoaded, e2u311_ct1SentDomOwnSpec] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, e2u311_ct1SentDomOwnSpec] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, e2u311_ct1SentDomOwnSpec] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
  · have hpre_kl : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, e2u311_ucCt1SentMergeTightSpecDomOf,
        unchunkedCt1SentMergeSpec, unchunkedCt1SentMergeSpecOfEnv]
      rw [tlb_domHeap_of_not_dom hDom]
      refine sepConj_mono_left (sepConj_mono_left ?_)
      refine Entails.pure_left fun hp =>
        Entails.pure_right ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
          tlb_fitsEnv_fallback_of_not_dom hDom hp.2.2.2.2⟩ (Entails.refl _)
    refine hKleene.mono_outcome x R s0 hpc hrun hpre_kl hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, Satisfies.mono ?_ hq⟩
      dsimp only [withLsCodeRoLoaded, e2u311_ucCt1SentMergeTightSpecDomOf,
        unchunkedCt1SentMergeSpec, unchunkedCt1SentMergeSpecOfEnv]
      refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
      refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
      exact Entails.sepExists_right evs
        (Entails.pure_right (Or.inr ⟨hDom, unchunkedCt1SentMergePostEnv_imp_pre hevs⟩)
          (Entails.refl _))
    · dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeSpec,
        unchunkedCt1SentMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeSpec,
        unchunkedCt1SentMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, unchunkedCt1SentMergeSpec,
        unchunkedCt1SentMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1

/-! ## 6. `libsignalSessionLib.blockProgram` Tight Contracts (`tlb_*PlacedTightOk*`) -/

/-- Guarded-tight contract `tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim maxOps ext` on Block `311` (`authOps + 4 ≤ maxOps`). -/
theorem e2u311_ucEkSentCt1Received_merge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {authOps maxOps : Nat}
    (hOps : authOps + 4 ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext) :
    tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim maxOps ext := by
  have hCum : 2952 + 2 * spqrAllocTightCost (Nat.max 8 2400) +
      2 * spqrAllocTightCost (Nat.max 8 960) ≤ 42108 := by decide
  have hok := e2u311_unchunkedEkSentCt1Received_merge_blk_tight_ok_of_contracts
    (H := Rust.withPanics ext)
    (maxRoot := 32) (maxMac := 32) (maxDk := 2400) (maxCt1 := 960)
    (authOps := authOps) (authCum := 2952) (authReq := 32)
    (maxOps := maxOps) (cumCap := 42108) (maxReq := 2560)
    hOps hCum (by decide)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_261).rebase (CryptoVerification.blkPl_261).base (fun _ => none))) hFrom)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase (CryptoVerification.RecordCodecs.Placed.blkPl_257).base (fun _ => none))) hPush)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_291).rebase (CryptoVerification.blkPl_291).base (fun _ => none))) hVarint)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_263).rebase (CryptoVerification.blkPl_263).base (fun _ => none))) hSkip)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_290).rebase (CryptoVerification.blkPl_290).base (fun _ => none))) hBytes)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase (CryptoVerification.blkPl_295).base (fun _ => none))) hAuthUntight)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase (CryptoVerification.blkPl_295).base (fun _ => none))) hAuthTight)
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_311).rebase (blkPl_311).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 311)] at hok
  exact hok

/-- Default `maxOps = 8` (`4 + 4`) specialization for Block `311`. -/
theorem e2u311_ucEkSentCt1Received_merge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim 4 ext) :
    tlb_UcEkSentCt1ReceivedMergePlacedTightOk A lim ext :=
  e2u311_ucEkSentCt1Received_merge_placed_tight_ok_of (Nat.le_refl 8)
    hFrom hPush hVarint hSkip hBytes hAuthUntight hAuthTight

/-- Guarded-tight contract `tlb_UcCt1SentMergePlacedTightOkOf A lim maxOps ext` on Block `312` (`authOps + 6 ≤ maxOps`). -/
theorem e2u311_ucCt1Sent_merge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {authOps maxOps : Nat}
    (hOps : authOps + 6 ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext) :
    tlb_UcCt1SentMergePlacedTightOkOf A lim maxOps ext := by
  have hCum : 2952 + 2 * spqrAllocTightCost (Nat.max 8 64) +
      2 * spqrAllocTightCost (Nat.max 8 2080) +
      2 * spqrAllocTightCost (Nat.max 8 960) ≤ 46102 := by decide
  have hok := e2u311_unchunkedCt1Sent_merge_blk_tight_ok_of_contracts
    (H := Rust.withPanics ext)
    (maxRoot := 32) (maxMac := 32) (maxHdr := 64) (maxEs := 2080) (maxCt1 := 960)
    (authOps := authOps) (authCum := 2952) (authReq := 32)
    (maxOps := maxOps) (cumCap := 46102) (maxReq := 2560)
    hOps hCum (by decide)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_261).rebase (CryptoVerification.blkPl_261).base (fun _ => none))) hFrom)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase (CryptoVerification.RecordCodecs.Placed.blkPl_257).base (fun _ => none))) hPush)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_291).rebase (CryptoVerification.blkPl_291).base (fun _ => none))) hVarint)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_263).rebase (CryptoVerification.blkPl_263).base (fun _ => none))) hSkip)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_290).rebase (CryptoVerification.blkPl_290).base (fun _ => none))) hBytes)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase (CryptoVerification.blkPl_295).base (fun _ => none))) hAuthUntight)
    (e2u311_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase (CryptoVerification.blkPl_295).base (fun _ => none))) hAuthTight)
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_312).rebase (blkPl_312).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 312)] at hok
  exact hok

/-- Default `maxOps = 10` (`4 + 6`) specialization for Block `312`. -/
theorem e2u311_ucCt1Sent_merge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim 4 ext) :
    tlb_UcCt1SentMergePlacedTightOk A lim ext :=
  e2u311_ucCt1Sent_merge_placed_tight_ok_of (Nat.le_refl 10)
    hFrom hPush hVarint hSkip hBytes hAuthUntight hAuthTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightU311PlacedBudgetR2
