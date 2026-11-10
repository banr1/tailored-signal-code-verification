/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Canonical Inner `Unchunked.HeaderSent` Tight Budget Proof for Block `304`

Proves the canonical inlined `V1State.Unchunked.HeaderSent` merge step inside
`Chunked.KeysSampled::merge` (Block `304`) within `authOps + 4` non-free operations and
`42,108` B (`Authenticator` `2,952` B + `ek` `19,578` B + `dk` `19,578` B, `maxReq ≤ 2,560` B).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalProtoCodec (decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeCapOk BytesMergeGhost IsDropSuffix bytesMergeCapOk_zero decodeVarint_suffix pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans ule_len_of_ge)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.SpqrV1.Prost.MessageMerge (ChunkedInl10CalleeSaved ChunkedKeysSampledMergeGhost SepWPpLscro bv64_add_zero bv64_sub_zero bv_len_sub_limit chunkedInlBelowStack chunkedInlBelow_authMerge chunkedInlBelow_authMerge_entails chunkedInlBelow_bytesMerge3 chunkedInlBelow_bytesMerge3_entails chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails chunkedInlSavedRegs10 chunkedKeysSampledMerge_fnOff cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto optHeaderSentPBCapAt unchunked4CapAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_304 blkPl_304)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialEncoderPBAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common (b304PoolAt b304PoolAt_eq_of_vmPreserved b304PoolAt_mono b304PoolAt_step b304PoolAt_step_nil b304_bytesMerge3Env_spqrTight_2560 b304_fitsEnv_decodeVarint2_of_some b304_fitsEnv_step_tight codec_decodeVarint_encodeVarint codec_decodeVarint_tlb_lenPrefixed codec_mergeBytes_encode encodeBytesField_tag3_of_ne encodeBytesField_tag4_of_ne encodeOptMessage_tag2_some encodeUint64Field_tag1_of_ne isDropSuffix_append_right isDropSuffix_cons_tail proto_mergeMessage_authenticator_canonical validUcHeaderSentPB_encodeRaw_len_le)

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304UcPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost memRegion_40_cells mergeBytes_length optAuthenticatorPBCapAt
   optAuthenticatorPBCapAt_mono)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthDom tlb_AuthGuardedEnvOf tlb_AuthTightEnvOf tlb_ValidAuthPB tlb_ValidUcHeaderSentPB
   tlb_authMergeTightSpecOfEnv tlb_authenticatorZeroCapAt tlb_domHeap_of_dom
   tlb_fitsEnv_guarded_of_dom tlb_guardedEnv_tight_of_dom tlb_lenPrefixed
   tlb_vecU8ZeroCapAt tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcBudgetAux
  (unchunked4CapAt_eq vecU8CapAt vecU8CapAt_mono')
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some sepWPpLscro_of_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedKeysSampledMerge_fnOff

@[local simp, local arm64_norm]
private theorem bv64_add48_add8 (a : BitVec 64) : a + 48#64 + 8#64 = a + 56#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add48_add16 (a : BitVec 64) : a + 48#64 + 16#64 = a + 64#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add48_add24 (a : BitVec 64) : a + 48#64 + 24#64 = a + 72#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add48_add32 (a : BitVec 64) : a + 48#64 + 32#64 = a + 80#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem bv64_add48_add40 (a : BitVec 64) : a + 48#64 + 40#64 = a + 88#64 := by bv_omega

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

/-! ## 1. Zero-Capacity Cell Folding Helpers -/

theorem cells_zero_entails_vecU8At_nil (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      vecU8At A a 0#64 1#64 [] := by
  unfold vecU8At vecHeader
  dsimp only [List.length_nil]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.le_refl,
    true_and, ↓reduceIte, sepConj_emp]
  have hp : (0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := ⟨by decide, by decide⟩
  exact Entails.trans (Entails.pure_right hp (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

private theorem memRegion_unchunked4_none_split_b304 (a : BitVec 64) :
    memRegion (a + 8#64) 96 =
      ∃∗ v96 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64,
      ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((a + 8#64) ↦₆₄ v8) ∗ ((a + 16#64) ↦₆₄ v16) ∗ ((a + 24#64) ↦₆₄ v24) ∗ ((a + 32#64) ↦₆₄ v32) ∗
        ((a + 40#64) ↦₆₄ v40) ∗ ((a + 48#64) ↦₆₄ v48) ∗ memRegion (a + 56#64) 40 ∗ ((a + 96#64) ↦₆₄ v96) := by
  have s1 := ProofLib.memRegion_split (a + 8#64) 8 88 (by decide)
  have s2 := ProofLib.memRegion_split (a + 16#64) 8 80 (by decide)
  have s3 := ProofLib.memRegion_split (a + 24#64) 8 72 (by decide)
  have s4 := ProofLib.memRegion_split (a + 32#64) 8 64 (by decide)
  have s5 := ProofLib.memRegion_split (a + 40#64) 8 56 (by decide)
  have s6 := ProofLib.memRegion_split (a + 48#64) 8 48 (by decide)
  have s7 := ProofLib.memRegion_split (a + 56#64) 40 8 (by decide)
  simp only [Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
    at s1 s2 s3 s4 s5 s6 s7
  rw [s1, s2, s3, s4, s5, s6, s7, ProofLib.memRegion_eight (a + 8#64), ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64), ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64),
    ProofLib.memRegion_eight (a + 48#64), ProofLib.memRegion_eight (a + 96#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem cells_zero_entails_uc_init (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 48#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 56#64) 40 ∗
      ((a + 96#64) ↦₆₄ 0#64) ⊢
      vecU8At A a 0#64 1#64 [] ∗
      vecU8At A (a + 0x18#64) 0#64 1#64 [] ∗
      optAuthenticatorPBCapAt A (a + 0x30#64) n none ∗
      ((a + 0x60#64) ↦₆₄ 0#64) := by
  dsimp only [optAuthenticatorPBCapAt, noneCap]
  have h1 := cells_zero_entails_vecU8At_nil A a
  have h2 := cells_zero_entails_vecU8At_nil A (a + 24#64)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  have h56 : a + 0x30#64 + 8#64 = a + 56#64 := by bv_omega
  rw [h32, h40] at h2
  rw [h56]
  change _ ⊢
    vecU8At A a 0#64 1#64 [] ∗
    vecU8At A (a + 24#64) 0#64 1#64 [] ∗
    (((a + 48#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 56#64) 40) ∗
    ((a + 96#64) ↦₆₄ 0#64)
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

private theorem cells_zero_entails_authZeroCapAt (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      tlb_authenticatorZeroCapAt A a default := by
  unfold tlb_authenticatorZeroCapAt
  have h1 := Entails.trans (cells_zero_entails_vecU8At_nil A a)
    (tlb_vecU8ZeroCapAt_of_ptr A a 1#64 [])
  have h2 := Entails.trans (cells_zero_entails_vecU8At_nil A (a + 24#64))
    (tlb_vecU8ZeroCapAt_of_ptr A (a + 24#64) 1#64 [])
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [h32, h40] at h2
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗ tlb_vecU8ZeroCapAt A (a + 24#64) []
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 h2)

private theorem vecU8At_entails_vecU8CapAt_b304 (A : RustAlloc) (a cap ptr : BitVec 64) (n : Nat)
    (bs : List (BitVec 8)) (hcap : BytesMergeCapOk cap n) :
    vecU8At A a cap ptr bs ⊢ vecU8CapAt A a n bs := by
  unfold vecU8CapAt
  refine Entails.trans (Entails.pure_right hcap (Entails.refl _)) ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

/-! ## 2. Parameterized Inner-Loop State & Key-Varint Step Helper -/

def b304UcPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s0 s : State) (x : ChunkedKeysSampledMergeGhost) (msgPart : SepProp)
    (cur : List (BitVec 8)) (ops cum : Nat) : SepProp :=
  msgPart ∗
  optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 104#64) none ∗
  stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
  memRegion (s0.sp - 128#64) 48 ∗
  chunkedInlSavedRegs10 s0.sp s0 ∗
  (x.bufRef ↦₆₄ x.slot) ∗
  sliceCursorAfter x.slot x.ptr x.bs cur ∗
  b304PoolAt A lim st ops cum s

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_304).base

private theorem b304_uc_step_key_varint [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {msgPart : SepProp} {cur afterKey : List (BitVec 8)}
    {key : BitVec 64} {outerLimit innerLimit ops cum : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, afterKey))
    (hcont : ∀ s1 : State,
      s1.pc = entry + 448#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 0#5) = 0#64 →
      s1.readReg64 (Reg.gpr 1#5) = key →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot → s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s1.readReg64 (Reg.gpr 23#5) = 1#64 → s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 25#5) = 8#64 → s1.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s1
        (b304UcPre A lim st s0 s1 x msgPart afterKey ops cum) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 428#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (b304UcPre A lim st s0 s x msgPart cur ops cum) Q (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hafter_le_cur : afterKey.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [b304UcPre, b304PoolAt, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 448#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19], hcur_lt, b304_fitsEnv_decodeVarint2_of_some hd⟩)
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 448#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hafter_le_cur) (by sep_focus)
      apply SepWP.fold
        (b304PoolAt_step_nil A lim st (LibsignalBinary.Heap.VmPreserved.refl sm) hevs
          (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← b304PoolAt_eq_of_vmPreserved hvm2]
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
        (P' := b304UcPre A lim st s0 _ x msgPart afterKey ops cum)
        (by dsimp only [b304UcPre]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hpcm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrunm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hspm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htrm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsm0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsm1])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26_m])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27_m],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28_m],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs_m]⟩

/-! ## 3. Canonical Steps for Fields `1..4` (`epoch`, `auth`, `ek`, `dk`) -/

private theorem b304_uc_field1_epoch [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {epoch : BitVec 64} {cur1 : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_cur1 : innerLimit ≤ cur1.length)
    (hcur0_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ cur1).length ≤ x.bs.length)
    (hcur0_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ cur1))
    (hcont : ∀ s' : State,
      s'.pc = entry + 428#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (b304UcPre A lim st s0 s' x
          (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
            vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
            optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) cur1.length none ∗
            ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
          cur1 0 0) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 428#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (b304UcPre A lim st s0 s x
        (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
          vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64)
            (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ cur1).length none ∗
          ((x.msgPtr + 0x60#64) ↦₆₄ 0#64))
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ cur1) 0 0) Q (WppPanicFalse R) := by
  by_cases hep : epoch = 0#64
  · subst hep
    have hf1 : CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 0#64 = [] := by decide
    rw [hf1, List.nil_append]
    exact hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  · have hcur0_eq := encodeUint64Field_tag1_of_ne epoch hep cur1
    rw [hcur0_eq] at hcur0_le hcur0_suf ⊢
    let afterKey := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint epoch ++ cur1
    have hgt_lim : ¬ (0x08#8 :: afterKey).length ≤ innerLimit := by
      dsimp only [afterKey]; simp only [List.length_cons, List.length_append]; omega
    have hcur0_lt : (0x08#8 :: afterKey).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur0_le hbs_lt
    have hk_eq : (0x08#8 :: afterKey) = CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x08#64 ++ afterKey := by
      have : CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x08#64 = [0x08#8] := by decide
      rw [this]; rfl
    have hd_key : decodeVarint (0x08#8 :: afterKey) = some (0x08#64, afterKey) := by
      rw [hk_eq]; exact codec_decodeVarint_encodeVarint 0x08#64 afterKey
    refine b304_uc_step_key_varint hVarintCall hgt_lim hsp_align hcur0_le hcur0_lt hcur0_suf hd_key
      ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hafter_le_cur0 : afterKey.length ≤ (0x08#8 :: afterKey).length := by simp
    have hafter_le : afterKey.length ≤ x.bs.length := Nat.le_trans hafter_le_cur0 hcur0_le
    have hafter_lt : afterKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hafter_le hbs_lt
    have hafter_suf : IsDropSuffix x.bs afterKey :=
      suffix_trans hcur0_le hcur0_suf hafter_le_cur0 (isDropSuffix_cons_tail 0x08#8 afterKey)
    have hd_val : decodeVarint afterKey = some (epoch, cur1) :=
      codec_decodeVarint_encodeVarint epoch cur1
    have hcur1_le_after : cur1.length ≤ afterKey.length := Nat.le_of_lt (decodeVarint_length hd_val)
    let afterPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - afterKey.length)
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [b304UcPre, b304PoolAt, sliceCursorAfter_eq_split hafter_le hafter_suf,
        chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, afterPtr, afterKey⟩, M.stepEvents evs st))
        (ret_pc := entry + 616#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx19_1], hafter_lt, b304_fitsEnv_decodeVarint2_of_some hd_val⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 428#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
          stackAt_decodeVarint2_raw_eq, hd_val, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_dv
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hafter_le hafter_suf hcur1_le_after) (by sep_focus)
        apply SepWP.fold
          (b304PoolAt_step_nil A lim st (LibsignalBinary.Heap.VmPreserved.refl sm) hevs
            (decodeVarint2Env_eq_nil_of_some hd_val hevs_dv))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← b304PoolAt_eq_of_vmPreserved hvm2]
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := b304UcPre A lim st s0 _ x
            (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
              vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
              optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) cur1.length none ∗
              ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
            cur1 0 0)
          (by dsimp only [b304UcPre, optAuthenticatorPBCapAt]; simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrunm])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hspm])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htrm, htr1])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27_m],
           by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28_m],
           by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem b304_uc_field2_auth [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hOps_uc : authOps + 4 ≤ maxOps)
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {epoch : BitVec 64} {auth : Option ProtoAuthenticator}
    {cur2 : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560))
    (hauth_valid : ∀ a, auth = some a → tlb_ValidAuthPB a)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_cur2 : innerLimit ≤ cur2.length)
    (hcur1_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32 auth ++ cur2).length ≤ x.bs.length)
    (hcur1_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32 auth ++ cur2))
    (hcont : ∀ s' : State,
      s'.pc = entry + 428#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (b304UcPre A lim st s0 s' x
          (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
            vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
            optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) cur2.length auth ∗
            ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
          cur2 authOps 2952) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 428#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (b304UcPre A lim st s0 s x
        (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
          vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64)
            (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32 auth ++ cur2).length none ∗
          ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32 auth ++ cur2) 0 0)
      Q (WppPanicFalse R) := by
  rcases auth with _ | a
  · dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
      (P' := b304UcPre A lim st s0 s x
        (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
          vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) cur2.length none ∗
          ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
        cur2 authOps 2952)
    · dsimp only [b304UcPre]
      have hm := b304PoolAt_mono A lim st (Nat.zero_le authOps) (by decide : 0 ≤ 2952) s
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm))))))
    · exact hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  · have ha : tlb_ValidAuthPB a := hauth_valid a rfl
    have hcur1_eq := encodeOptMessage_tag2_some CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw a cur2
    rw [hcur1_eq] at hcur1_le hcur1_suf ⊢
    let afterKey := tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw a) cur2
    have hgt_lim : ¬ (0x12#8 :: afterKey).length ≤ innerLimit := by
      dsimp only [afterKey, tlb_lenPrefixed]
      simp only [List.length_cons, List.length_append]
      omega
    have hcur1_lt : (0x12#8 :: afterKey).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur1_le hbs_lt
    have hk_eq : (0x12#8 :: afterKey) = CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x12#64 ++ afterKey := by
      have : CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x12#64 = [0x12#8] := by decide
      rw [this]; rfl
    have hd_key : decodeVarint (0x12#8 :: afterKey) = some (0x12#64, afterKey) := by
      rw [hk_eq]; exact codec_decodeVarint_encodeVarint 0x12#64 afterKey
    refine b304_uc_step_key_varint hVarintCall hgt_lim hsp_align hcur1_le hcur1_lt hcur1_suf hd_key
      ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hafter_le_cur1 : afterKey.length ≤ (0x12#8 :: afterKey).length := by simp
    have hafter_le : afterKey.length ≤ x.bs.length := Nat.le_trans hafter_le_cur1 hcur1_le
    have hafter_lt : afterKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hafter_le hbs_lt
    have hafter_suf : IsDropSuffix x.bs afterKey :=
      suffix_trans hcur1_le hcur1_suf hafter_le_cur1 (isDropSuffix_cons_tail 0x12#8 afterKey)
    have hcur2_le_after : cur2.length ≤ afterKey.length := by
      dsimp only [afterKey, tlb_lenPrefixed]; simp only [List.length_append]; omega
    let afterPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - afterKey.length)
    let x_auth : AuthMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr + 0x30#64, default, x.bufRef, x.slot, afterPtr, afterKey⟩
    have hAuthDom : tlb_AuthDom x_auth := ⟨rfl, rfl, a, cur2, ha, rfl⟩
    have hauth_res :
        (CryptoVerification.LibsignalSpqrV1.Proto.mergeMessage CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.mergeField (codecWireTypeToProto x_auth.wt)
          x_auth.msg x_auth.bs 97).toOption = some (a, cur2) :=
      proto_mergeMessage_authenticator_canonical a cur2 ha
    apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
    by_vm_steps
      (conv => arg 4; rw [b304UcPre, b304PoolAt, optAuthenticatorPBCapAt,
        memRegion_40_cells (x.msgPtr + 0x30#64), sliceCursorAfter_eq_split hafter_le hafter_suf,
        chunkedInlBelow_authMerge s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
      apply SepWP.exists_elim; intro evs; apply SepWP.exists_elim; intro w1
      apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
      apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.fold (cells_zero_entails_authZeroCapAt A.repAlloc (x.msgPtr + 0x30#64)) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_auth, M.stepEvents evs st))
        (ret_pc := entry + 540#64) hAuthTightCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [tlb_authMergeTightSpecOfEnv, x_auth]
              rw [tlb_domHeap_of_dom hAuthDom]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hafter_lt,
          tlb_fitsEnv_guarded_of_dom hAuthDom
            (b304_fitsEnv_step_tight hFit hevs (fun _ h => h)
              (by omega : 0 + authOps ≤ maxOps) (by decide : 0 + 2952 ≤ 384723) (by decide : 32 ≤ 2560))⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 428#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_authMergeTightSpecOfEnv, authMergeSpecOfEnv, x_auth,
          hauth_res, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_a
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_g
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        have hevs_a : SpqrTightEvs authOps 2952 32 evs_a :=
          tlb_guardedEnv_tight_of_dom hAuthDom hevs_g
        apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hafter_le hafter_suf hcur2_le_after) (by sep_focus)
        apply SepWP.fold
          (b304PoolAt_step A lim st (LibsignalBinary.Heap.VmPreserved.refl sm) hevs hevs_a (by decide : 32 ≤ 2560))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← b304PoolAt_eq_of_vmPreserved hvm2]
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := b304UcPre A lim st s0 _ x
            (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
              vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
              optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) cur2.length (some a) ∗
              ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
            cur2 authOps 2952)
          (by dsimp only [b304UcPre, optAuthenticatorPBCapAt]; simp only [Nat.zero_add, arm64_norm]; sep_entail)
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

private theorem b304_uc_field3_ek [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hOps_uc : authOps + 4 ≤ maxOps)
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {epoch : BitVec 64} {auth : Option ProtoAuthenticator}
    {ek cur3 : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560))
    (hek_len : ek.length ≤ 2560)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_cur3 : innerLimit ≤ cur3.length)
    (hcur2_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 ek ++ cur3).length ≤ x.bs.length)
    (hcur2_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 ek ++ cur3))
    (hcont : ∀ s' : State,
      s'.pc = entry + 428#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (b304UcPre A lim st s0 s' x
          (vecU8CapAt A.repAlloc x.msgPtr cur3.length ek ∗
            vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
            optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) cur3.length auth ∗
            ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
          cur3 (authOps + 2) 22530) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 428#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (b304UcPre A lim st s0 s x
        (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
          vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64)
            (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 ek ++ cur3).length auth ∗
          ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 ek ++ cur3) authOps 2952) Q (WppPanicFalse R) := by
  by_cases hek_nil : ek = []
  · subst hek_nil
    have hf3 : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 [] = [] := by decide
    rw [hf3, List.nil_append]
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
      (P' := b304UcPre A lim st s0 s x
        (vecU8CapAt A.repAlloc x.msgPtr cur3.length [] ∗
          vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) cur3.length auth ∗
          ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
        cur3 (authOps + 2) 22530)
    · dsimp only [b304UcPre]
      have hcap := vecU8At_entails_vecU8CapAt_b304 A.repAlloc x.msgPtr 0#64 1#64 cur3.length []
        bytesMergeCapOk_zero
      have hm := b304PoolAt_mono A lim st (by omega : authOps ≤ authOps + 2) (by decide : 2952 ≤ 22530) s
      exact sepConj_mono (sepConj_mono_left hcap)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm))))))
    · exact hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  · have hcur2_eq := encodeBytesField_tag3_of_ne ek cur3 hek_nil
    rw [hcur2_eq] at hcur2_le hcur2_suf ⊢
    let afterKey := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 ek.length) ++ ek ++ cur3
    have hgt_lim : ¬ (0x1a#8 :: afterKey).length ≤ innerLimit := by
      dsimp only [afterKey]; simp only [List.length_cons, List.length_append]; omega
    have hcur2_lt : (0x1a#8 :: afterKey).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur2_le hbs_lt
    have hk_eq : (0x1a#8 :: afterKey) = CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x1a#64 ++ afterKey := by
      have : CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x1a#64 = [0x1a#8] := by decide
      rw [this]; rfl
    have hd_key : decodeVarint (0x1a#8 :: afterKey) = some (0x1a#64, afterKey) := by
      rw [hk_eq]; exact codec_decodeVarint_encodeVarint 0x1a#64 afterKey
    refine b304_uc_step_key_varint hVarintCall hgt_lim hsp_align hcur2_le hcur2_lt hcur2_suf hd_key
      ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hafter_le_cur2 : afterKey.length ≤ (0x1a#8 :: afterKey).length := by simp
    have hafter_le : afterKey.length ≤ x.bs.length := Nat.le_trans hafter_le_cur2 hcur2_le
    have hafter_lt : afterKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hafter_le hbs_lt
    have hafter_suf : IsDropSuffix x.bs afterKey :=
      suffix_trans hcur2_le hcur2_suf hafter_le_cur2 (isDropSuffix_cons_tail 0x1a#8 afterKey)
    have hmb : mergeBytes .lengthDelimited afterKey = some (ek, cur3) :=
      codec_mergeBytes_encode ek cur3 (by omega)
    have hcur3_le_after : cur3.length ≤ afterKey.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcur3_le_cur2 : cur3.length ≤ (0x1a#8 :: afterKey).length :=
      Nat.le_trans hcur3_le_after hafter_le_cur2
    let afterPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - afterKey.length)
    let x_bm : BytesMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr, 0#64, 1#64, [], x.bufRef, x.slot, afterPtr, afterKey⟩
    apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
    by_vm_steps
      (conv => arg 4; rw [b304UcPre, b304PoolAt, sliceCursorAfter_eq_split hafter_le hafter_suf,
        chunkedInlBelow_bytesMerge3 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
        (ret_pc := entry + 416#64) hBytesCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [bytesMerge3RawBudgetSpec, x_bm]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hafter_lt,
          bytesMergeCapOk_zero,
          b304_fitsEnv_step_tight hFit hevs
            (fun _ hb => b304_bytesMerge3Env_spqrTight_2560 hmb hek_len hb)
            (by omega : authOps + 2 ≤ maxOps) (by decide : 2952 + 19578 ≤ 384723) (Nat.le_refl 2560)⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 428#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_b
        apply SepWP.exists_elim; intro cap1'
        apply SepWP.exists_elim; intro ptr1'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_b
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap1'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hafter_le hafter_suf hcur3_le_after) (by sep_focus)
        apply SepWP.fold (vecU8At_entails_vecU8CapAt_b304 A.repAlloc x.msgPtr cap1' ptr1' cur3.length ek hcap1') (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x30#64) auth hcur3_le_cur2) (by sep_focus)
        apply SepWP.fold
          (b304PoolAt_step A lim st (LibsignalBinary.Heap.VmPreserved.refl sm) hevs
            (b304_bytesMerge3Env_spqrTight_2560 hmb hek_len hevs_b) (Nat.le_refl 2560))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← b304PoolAt_eq_of_vmPreserved hvm2]
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := b304UcPre A lim st s0 _ x
            (vecU8CapAt A.repAlloc x.msgPtr cur3.length ek ∗
              vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
              optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) cur3.length auth ∗
              ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
            cur3 (authOps + 2) 22530)
          (by dsimp only [b304UcPre]; simp only [Nat.reduceAdd, arm64_norm]; sep_entail)
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

private theorem b304_uc_field4_dk [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hOps_uc : authOps + 4 ≤ maxOps)
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {epoch : BitVec 64} {auth : Option ProtoAuthenticator}
    {ek dk restAfterUc : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560))
    (hdk_len : dk.length ≤ 2560)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur3_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 dk ++ restAfterUc).length ≤ x.bs.length)
    (hcur3_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 dk ++ restAfterUc))
    (hcont : ∀ s' : State,
      s'.pc = entry + 428#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 restAfterUc.length →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (b304UcPre A lim st s0 s' x
          (unchunked4CapAt A.repAlloc x.msgPtr restAfterUc.length epoch auth ek dk)
          restAfterUc (authOps + 4) 42108) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 428#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 restAfterUc.length)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (b304UcPre A lim st s0 s x
        (vecU8CapAt A.repAlloc x.msgPtr
            (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 dk ++ restAfterUc).length ek ∗
          vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64)
            (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 dk ++ restAfterUc).length auth ∗
          ((x.msgPtr + 0x60#64) ↦₆₄ epoch))
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 dk ++ restAfterUc) (authOps + 2) 22530)
      Q (WppPanicFalse R) := by
  by_cases hdk_nil : dk = []
  · subst hdk_nil
    have hf4 : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 [] = [] := by decide
    rw [hf4, List.nil_append]
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
      (P' := b304UcPre A lim st s0 s x
        (unchunked4CapAt A.repAlloc x.msgPtr restAfterUc.length epoch auth ek [])
        restAfterUc (authOps + 4) 42108)
    · dsimp only [b304UcPre]
      rw [unchunked4CapAt_eq]
      have hcap := vecU8At_entails_vecU8CapAt_b304 A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64
        restAfterUc.length [] bytesMergeCapOk_zero
      have hm := b304PoolAt_mono A lim st (by omega : authOps + 2 ≤ authOps + 4)
        (by decide : 22530 ≤ 42108) s
      exact sepConj_mono (sepConj_mono_right (sepConj_mono_left hcap))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm))))))
    · exact hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  · have hcur3_eq := encodeBytesField_tag4_of_ne dk restAfterUc hdk_nil
    rw [hcur3_eq] at hcur3_le hcur3_suf ⊢
    let afterKey := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 dk.length) ++ dk ++ restAfterUc
    have hgt_lim : ¬ (0x22#8 :: afterKey).length ≤ restAfterUc.length := by
      dsimp only [afterKey]; simp only [List.length_cons, List.length_append]; omega
    have hcur3_lt : (0x22#8 :: afterKey).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur3_le hbs_lt
    have hk_eq : (0x22#8 :: afterKey) = CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x22#64 ++ afterKey := by
      have : CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x22#64 = [0x22#8] := by decide
      rw [this]; rfl
    have hd_key : decodeVarint (0x22#8 :: afterKey) = some (0x22#64, afterKey) := by
      rw [hk_eq]; exact codec_decodeVarint_encodeVarint 0x22#64 afterKey
    refine b304_uc_step_key_varint hVarintCall hgt_lim hsp_align hcur3_le hcur3_lt hcur3_suf hd_key
      ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hafter_le_cur3 : afterKey.length ≤ (0x22#8 :: afterKey).length := by simp
    have hafter_le : afterKey.length ≤ x.bs.length := Nat.le_trans hafter_le_cur3 hcur3_le
    have hafter_lt : afterKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hafter_le hbs_lt
    have hafter_suf : IsDropSuffix x.bs afterKey :=
      suffix_trans hcur3_le hcur3_suf hafter_le_cur3 (isDropSuffix_cons_tail 0x22#8 afterKey)
    have hmb : mergeBytes .lengthDelimited afterKey = some (dk, restAfterUc) :=
      codec_mergeBytes_encode dk restAfterUc (by omega)
    have hrest_le_after : restAfterUc.length ≤ afterKey.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hrest_le_cur3 : restAfterUc.length ≤ (0x22#8 :: afterKey).length :=
      Nat.le_trans hrest_le_after hafter_le_cur3
    let afterPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - afterKey.length)
    let x_bm : BytesMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr + 0x18#64, 0#64, 1#64, [], x.bufRef, x.slot, afterPtr, afterKey⟩
    apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
    by_vm_steps
      (conv => arg 4; rw [b304UcPre, b304PoolAt, sliceCursorAfter_eq_split hafter_le hafter_suf,
        chunkedInlBelow_bytesMerge3 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
        (ret_pc := entry + 576#64) hBytesCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [bytesMerge3RawBudgetSpec, x_bm]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hafter_lt,
          bytesMergeCapOk_zero,
          b304_fitsEnv_step_tight hFit hevs
            (fun _ hb => b304_bytesMerge3Env_spqrTight_2560 hmb hdk_len hb)
            (by omega : (authOps + 2) + 2 ≤ maxOps) (by decide : 22530 + 19578 ≤ 384723) (Nat.le_refl 2560)⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 428#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_b
        apply SepWP.exists_elim; intro cap2'
        apply SepWP.exists_elim; intro ptr2'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_b
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap2'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hafter_le hafter_suf hrest_le_after) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_mono' A.repAlloc x.msgPtr ek hrest_le_cur3) (by sep_focus)
        apply SepWP.fold
          (vecU8At_entails_vecU8CapAt_b304 A.repAlloc (x.msgPtr + 0x18#64) cap2' ptr2'
            restAfterUc.length dk hcap2') (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x30#64) auth hrest_le_cur3) (by sep_focus)
        apply SepWP.fold
          (b304PoolAt_step A lim st (LibsignalBinary.Heap.VmPreserved.refl sm) hevs
            (b304_bytesMerge3Env_spqrTight_2560 hmb hdk_len hevs_b) (Nat.le_refl 2560))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← b304PoolAt_eq_of_vmPreserved hvm2]
        have hadd_ops : (authOps + 2) + 2 = authOps + 4 := by omega
        rw [hadd_ops]
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := b304UcPre A lim st s0 _ x
            (unchunked4CapAt A.repAlloc x.msgPtr restAfterUc.length epoch auth ek dk)
            restAfterUc (authOps + 4) 42108)
          (by dsimp only [b304UcPre]; rw [unchunked4CapAt_eq]; simp only [Nat.reduceAdd, arm64_norm]; sep_entail)
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

/-! ## 4. Full Canonical Placed Outer-Tag-1 (`+300 → +168`) Theorem -/

theorem b304_uc_canonical_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hOps_uc : authOps + 4 ≤ maxOps)
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {u : CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent} {restAfterUc : List (BitVec 8)}
    {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560))
    (hu : tlb_ValidUcHeaderSentPB u)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : (tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw u) restAfterUc).length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs (tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw u) restAfterUc))
    (hcont : ∀ s' : State,
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (b304UcPre A lim st s0 s' x
          (optHeaderSentPBCapAt A.repAlloc x.msgPtr restAfterUc.length (some u))
          restAfterUc (authOps + 4) 42108) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 300#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (b304UcPre A lim st s0 s x
        (optHeaderSentPBCapAt A.repAlloc x.msgPtr
          (tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw u) restAfterUc).length none)
        (tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw u) restAfterUc) 0 0)
      Q (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let raw := CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw u
  let rest := tlb_lenPrefixed raw restAfterUc
  let cur0 := raw ++ restAfterUc
  have hraw_len_le : raw.length ≤ 3736 := validUcHeaderSentPB_encodeRaw_len_le hu
  have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
  have hdv0 : decodeVarint rest = some (BitVec.ofNat 64 raw.length, cur0) :=
    codec_decodeVarint_tlb_lenPrefixed raw restAfterUc
  have hcur0_le_rest : cur0.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hcur0_le : cur0.length ≤ x.bs.length := Nat.le_trans hcur0_le_rest hrest_le
  have hcur0_lt : cur0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur0_le hbs_lt
  have hcur0_suf : IsDropSuffix x.bs cur0 :=
    suffix_trans hrest_le hrest_suf hcur0_le_rest (decodeVarint_suffix hdv0)
  have hlen_toNat : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have hnlt_len : ¬ cur0.length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hlen_toNat]; dsimp only [cur0]; simp only [List.length_append]; omega
  have hule := ule_len_of_ge hnlt_len hcur0_lt
  have hsub := bv_len_sub_limit hnlt_len
  have hlim_eq : cur0.length - raw.length = restAfterUc.length := by
    dsimp only [cur0]; simp only [List.length_append]; omega
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [b304UcPre, b304PoolAt, optHeaderSentPBCapAt,
      memRegion_unchunked4_none_split_b304 x.msgPtr,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
    apply SepWP.exists_elim; intro evs; apply SepWP.exists_elim; intro v96
    apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40
    apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (cells_zero_entails_uc_init A.repAlloc x.msgPtr cur0.length) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
      (ret_pc := entry + 348#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19], hrest_lt, b304_fitsEnv_decodeVarint2_of_some hdv0⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 428#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hcur0_le_rest) (by sep_focus)
      apply SepWP.fold
        (b304PoolAt_step_nil A lim st (LibsignalBinary.Heap.VmPreserved.refl sm) hevs
          (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
        (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hcur0_le hcur0_suf, sliceCursorAt]; simp only [sepConj_assoc])
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hcur0_le hcur0_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← b304PoolAt_eq_of_vmPreserved hvm2]
      let f1 := CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 u.epoch
      let f2 := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage CryptoVerification.LibsignalSpqrV1.ProtoAuthenticator.encodeRaw 2#32 u.auth
      let f3 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 u.ek
      let f4 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 u.dk
      let cur3 := f4 ++ restAfterUc
      let cur2 := f3 ++ cur3
      let cur1 := f2 ++ cur2
      have hcur0_split : cur0 = f1 ++ cur1 := by
        dsimp only [cur0, raw, CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw, f1, f2, f3, f4, cur1, cur2, cur3]
        simp only [List.append_assoc]
      have hcur1_le_cur0 : cur1.length ≤ cur0.length := by
        rw [hcur0_split]; conv_rhs => rw [List.length_append]
        exact Nat.le_add_left cur1.length f1.length
      have hcur1_le : cur1.length ≤ x.bs.length := Nat.le_trans hcur1_le_cur0 hcur0_le
      have hcur1_suf : IsDropSuffix x.bs cur1 :=
        suffix_trans hcur0_le hcur0_suf hcur1_le_cur0 (by rw [hcur0_split]; exact isDropSuffix_append_right f1 cur1)
      have hcur2_le_cur1 : cur2.length ≤ cur1.length := by
        change cur2.length ≤ (f2 ++ cur2).length; conv_rhs => rw [List.length_append]
        exact Nat.le_add_left cur2.length f2.length
      have hcur2_le : cur2.length ≤ x.bs.length := Nat.le_trans hcur2_le_cur1 hcur1_le
      have hcur2_suf : IsDropSuffix x.bs cur2 :=
        suffix_trans hcur1_le hcur1_suf hcur2_le_cur1 (isDropSuffix_append_right f2 cur2)
      have hcur3_le_cur2 : cur3.length ≤ cur2.length := by
        change cur3.length ≤ (f3 ++ cur3).length; conv_rhs => rw [List.length_append]
        exact Nat.le_add_left cur3.length f3.length
      have hcur3_le : cur3.length ≤ x.bs.length := Nat.le_trans hcur3_le_cur2 hcur2_le
      have hcur3_suf : IsDropSuffix x.bs cur3 :=
        suffix_trans hcur2_le hcur2_suf hcur3_le_cur2 (isDropSuffix_append_right f3 cur3)
      have hend_le_cur3 : restAfterUc.length ≤ cur3.length := by
        change restAfterUc.length ≤ (f4 ++ restAfterUc).length; conv_rhs => rw [List.length_append]
        exact Nat.le_add_left restAfterUc.length f4.length
      have hend_le : restAfterUc.length ≤ x.bs.length := Nat.le_trans hend_le_cur3 hcur3_le
      have hend_suf : IsDropSuffix x.bs restAfterUc :=
        suffix_trans hcur3_le hcur3_suf hend_le_cur3 (isDropSuffix_append_right f4 restAfterUc)
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
        (P' := b304UcPre A lim st s0 _ x
          (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
            vecU8At A.repAlloc (x.msgPtr + 0x18#64) 0#64 1#64 [] ∗
            optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x30#64) (f1 ++ cur1).length none ∗
            ((x.msgPtr + 0x60#64) ↦₆₄ 0#64))
          (f1 ++ cur1) 0 0)
        (by rw [← hcur0_split]; dsimp only [b304UcPre, sliceCursorAfter]; sep_entail)
      refine b304_uc_field1_epoch (outerLimit := outerLimit) (innerLimit := restAfterUc.length)
        hVarintCall hsp_align hbs_lt
        (Nat.le_trans hend_le_cur3 (Nat.le_trans hcur3_le_cur2 hcur2_le_cur1))
        (by rw [← hcur0_split]; exact hcur0_le)
        (by rw [← hcur0_split]; exact hcur0_suf)
        (fun sA hpcA hrunA hspA htrA hx19A hx20A hx21A hx22A hx23A hx24A hx25A hx26A hcsA => ?_)
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm, hx21_m])
        (by simp only [arm64_norm, wp_norm, hx22_m])
        (by simp only [arm64_norm, wp_norm, hx23_m])
        (by simp only [arm64_norm, wp_norm, hx24_m])
        (by simp only [arm64_norm, wp_norm, hx25_m])
        (by simp only [arm64_norm, wp_norm, hsm1, hsub, hlen_toNat, hlim_eq])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      refine b304_uc_field2_auth hVarintCall hAuthTightCall hOps_uc hFit hu.1 hsp_align hbs_lt
        (Nat.le_trans hend_le_cur3 hcur3_le_cur2) hcur1_le hcur1_suf
        (fun sB hpcB hrunB hspB htrB hx19B hx20B hx21B hx22B hx23B hx24B hx25B hx26B hcsB => ?_)
        hpcA hrunA hspA htrA hx19A hx20A hx21A hx22A hx23A hx24A hx25A hx26A hcsA
      refine b304_uc_field3_ek hVarintCall hBytesCall hOps_uc hFit
        (by have := hu.2.1; omega) hsp_align hbs_lt hend_le_cur3 hcur2_le hcur2_suf
        (fun sC hpcC hrunC hspC htrC hx19C hx20C hx21C hx22C hx23C hx24C hx25C hx26C hcsC => ?_)
        hpcB hrunB hspB htrB hx19B hx20B hx21B hx22B hx23B hx24B hx25B hx26B hcsB
      refine b304_uc_field4_dk hVarintCall hBytesCall hOps_uc hFit
        (by have := hu.2.2; omega) hsp_align hbs_lt hcur3_le hcur3_suf
        (fun sD hpcD hrunD hspD htrD hx19D hx20D hx21D hx22D hx23D hx24D hx25D hx26D hcsD => ?_)
        hpcC hrunC hspC htrC hx19C hx20C hx21C hx22C hx23C hx24C hx25C hx26C hcsC
      obtain ⟨hx27D, hx28D, hvregsD⟩ := hcsD
      obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : restAfterUc.length = restAfterUc.length)
      apply sepWPpLscro_of_vm (mid := entry + 168#64)
      by_vm_steps
        (conv => arg 4; rw [b304UcPre, sliceCursorAfter_eq_split hend_le hend_suf, sliceCursorAt])
        (conv => arg 4; simp only [sepConj_assoc])
        wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hend_le hend_suf) (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := b304UcPre A lim st s0 _ x
            (optHeaderSentPBCapAt A.repAlloc x.msgPtr restAfterUc.length (some u))
            restAfterUc (authOps + 4) 42108)
          (by dsimp only [b304UcPre, optHeaderSentPBCapAt, sliceCursorAfter];
              rw [b304PoolAt_eq_of_vmPreserved hvm3]; simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunD])
          (by simp only [arm64_norm, wp_norm, hspD])
          (by simp only [arm64_norm, wp_norm, htrD])
          (by simp only [arm64_norm, wp_norm, hx19D])
          (by simp only [arm64_norm, wp_norm, hx20D])
          (by simp only [arm64_norm, wp_norm, hx21D])
          (by simp only [arm64_norm, wp_norm, hx22D])
          (by simp only [arm64_norm, wp_norm, hx23D])
          (by simp only [arm64_norm, wp_norm, hx24D])
          (by simp only [arm64_norm, wp_norm, hx25D])
          ⟨by simp only [arm64_norm, wp_norm, hx27D],
           by simp only [arm64_norm, wp_norm, hx28D],
           by simp only [arm64_norm, wp_norm, hvregsD]⟩

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304UcPlacedBudget
