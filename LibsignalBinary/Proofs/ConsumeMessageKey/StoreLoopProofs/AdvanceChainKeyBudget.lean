/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.AdvanceChainKey
public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DeriveSeed
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `AdvanceChainKey` Sub-Segment (Block 24)

Proves `AdvanceChainKeyPlacedSpec` and `AdvanceChainKeyPlacedRoSpec` under `RustCliAllocBudget M`
and `SeamBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.AdvanceChainKeyBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState hmacWith keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (ChainKey RatchetState)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded
  blkLib_eq_24 blkPC_24 blkPl_24 libsignalRoLoaded_of_keepsFrozen lsmpl
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (
  RatchetGhost chainKeyBytes ratchetAt
)
open CryptoVerification.SessionModel (chainStepN)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkDummyImg cmkEpiloguePC_placed cmkLoopFrame cmkLoopHeap
  cmkLoopHeap_placed cmkLoopHeap_placed_eq cmkLoopPC_placed cmkSavedRegs logFilterAddr
)
open CryptoVerification.LibsignalSession.StoreLoop (
  add_one_ne_zero_of_lt chainKeyBytes_pointsTo hmacWith_length
  keyToBytes32_bytesToKey32 keyToBytes32_length memRegion_32_eq_exists_words
  memRegion_one_eq_exists_pointsTo8 pack64 pointsTo64_4_entails_memRegion_32
  pointsTo8_eq_pointsToBytes_singleton pointsToBytes_32_eq_pointsTo64
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (hmacSpec)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  AdvanceChainKeyPlacedRoSpec AdvanceChainKeyPlacedSpec
  hmacAtStateSpec hmac_placed_ok_at_state hmac_placed_ro_ok_at_state
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

attribute [local irreducible] Program.fetch Program.externAt?

private theorem ratchetAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ratchetAt (A.atState lim st s) = ratchetAt A.repAlloc :=
  rfl

private theorem stackAt_7712_split_2048 (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 7712 =
      memRegion (sp0 - 8192#64) 5664 ∗ stackAt (sp0 - 480#64) 2048 := by
  simp only [stackAt]
  have h := memRegion_split (sp0 - 8192#64) 5664 2048 (by decide)
  have a1 : sp0 - 480#64 - 7712#64 = sp0 - 8192#64 := by bv_omega
  have a2 : sp0 - 8192#64 + 5664#64 = sp0 - 480#64 - 2048#64 := by bv_omega
  change memRegion (sp0 - 8192#64) 7712 =
    memRegion (sp0 - 8192#64) 5664 ∗ memRegion (sp0 - 8192#64 + 5664#64) 2048 at h
  rw [a2] at h
  change memRegion (sp0 - 480#64 - 7712#64) 7712 = _
  rw [a1]
  exact h

private theorem memRegion_256_advanceChainKey_split (sp0 : BitVec 64) :
    memRegion (sp0 - 352#64) 256 =
      ∃∗ b320 : BitVec 8,
        ((sp0 - 320#64) ↦₈ b320) ∗
        memRegion (sp0 - 319#64) 31 ∗
        memRegion (sp0 - 224#64) 32 ∗
        (memRegion (sp0 - 352#64) 32 ∗
         memRegion (sp0 - 288#64) 64 ∗
         memRegion (sp0 - 192#64) 96) := by
  rw [show (256 : Nat) = 32 + (1 + (31 + (64 + (32 + 96)))) from rfl,
      memRegion_split (sp0 - 352#64) 32 224 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64) 1 223 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64 + 1#64) 31 192 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64 + 1#64 + 31#64) 64 128 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64 + 1#64 + 31#64 + 64#64) 32 96 (by decide)]
  have ha1 : sp0 - 352#64 + 32#64 = sp0 - 320#64 := by bv_omega
  have ha2 : sp0 - 320#64 + 1#64 = sp0 - 319#64 := by bv_omega
  have ha3 : sp0 - 319#64 + 31#64 = sp0 - 288#64 := by bv_omega
  have ha4 : sp0 - 288#64 + 64#64 = sp0 - 224#64 := by bv_omega
  have ha5 : sp0 - 224#64 + 32#64 = sp0 - 192#64 := by bv_omega
  rw [ha1, ha2, ha3, ha4, ha5, memRegion_one_eq_exists_pointsTo8 (sp0 - 320#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext b320
  sep_ac_rfl

private def advanceChainKeyFrame (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (s0 : State) : SepProp :=
  ratchetAt A x.self G' st' ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  memRegion (s0.sp - 8192#64) 5664 ∗
  memRegion (s0.sp - 480#64) 112 ∗
  ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
  memRegion (s0.sp - 360#64) 4 ∗
  memRegion (s0.sp - 352#64) 32 ∗
  memRegion (s0.sp - 288#64) 64 ∗
  memRegion (s0.sp - 192#64) 96 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

private theorem cmkLoopHeap_advanceChainKey_split (A : RustAlloc) (img : Obj.Image)
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (st' : RatchetState)
    (ckc : ChainKey) (s0 : State) :
    cmkLoopHeap A img x G' st' ckc s0 =
      ∃∗ b320 : BitVec 8,
        ((s0.sp - 320#64) ↦₈ b320) ∗
        (memRegion (s0.sp - 224#64) 32 ∗
         (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
         stackAt (s0.sp - 480#64) 2048 ∗
         memRegion (s0.sp - 319#64) 31 ∗
         ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
         ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
         advanceChainKeyFrame A img x G' st' s0) := by
  unfold cmkLoopHeap cmkLoopFrame advanceChainKeyFrame
  rw [chainKeyBytes_pointsTo x.ckA ckc,
      stackAt_7712_split_2048 s0.sp,
      memRegion_256_advanceChainKey_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext b320
  sep_ac_rfl

private theorem advanceChainKeyPost_entails_cmkLoopHeap
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi : BitVec 64)
    (hq0_lo : q0_lo = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).take 8))
    (hq0_hi : q0_hi = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 8).take 8))
    (hq1_lo : q1_lo = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 16).take 8))
    (hq1_hi : q1_hi = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 24))
    (s0 : State) :
    (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
     (x.ckA ↦₆₄ q0_lo) ∗
     ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
     ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
     ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
     ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
     stackAt (s0.sp - 480#64) 2048 ∗
     advanceChainKeyFrame A img x G' st' s0) ⊢
      cmkLoopHeap A img x G' st' (chainStepN F 1 ckc) s0 := by
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hck'_key : keyToBytes32 (chainStepN F 1 ckc).key = bs := by
    change keyToBytes32 (bytesToKey32 bs) = bs
    exact keyToBytes32_bytesToKey32 bs hbs
  have hck'_idx : (chainStepN F 1 ckc).index = ckc.index + 1#32 := rfl
  have hckA_words :
      ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi)) =
      (x.ckA ↦ₛ bs) := by
    rw [hq0_lo, hq0_hi, hq1_lo, hq1_hi, ← pointsToBytes_32_eq_pointsTo64 x.ckA bs hbs]
  have hckA_full :
      ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
       ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) =
      (x.ckA ↦ₛ chainKeyBytes (chainStepN F 1 ckc)) := by
    rw [chainKeyBytes_pointsTo x.ckA (chainStepN F 1 ckc), hck'_key, hck'_idx, ← hckA_words]
    sep_ac_rfl
  have h224 := pointsTo64_4_entails_memRegion_32 (s0.sp - 224#64) q0_lo q0_hi q1_lo q1_hi
  have h320 := pointsTo64_4_entails_memRegion_32 (s0.sp - 320#64) q0_lo q0_hi q1_lo q1_hi
  have ha216 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_omega
  have ha208 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
  have ha200 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_omega
  have ha312 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_omega
  have ha304 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_omega
  have ha296 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_omega
  rw [ha216, ha208, ha200] at h224
  rw [ha312, ha304, ha296] at h320
  have h256 :
      (memRegion (s0.sp - 352#64) 32 ∗
       memRegion (s0.sp - 320#64) 32 ∗
       memRegion (s0.sp - 288#64) 64 ∗
       memRegion (s0.sp - 224#64) 32 ∗
       memRegion (s0.sp - 192#64) 96) =
      memRegion (s0.sp - 352#64) 256 := by
    have hb1 : s0.sp - 352#64 + 32#64 = s0.sp - 320#64 := by bv_omega
    have hb2 : s0.sp - 320#64 + 32#64 = s0.sp - 288#64 := by bv_omega
    have hb3 : s0.sp - 288#64 + 64#64 = s0.sp - 224#64 := by bv_omega
    have hb4 : s0.sp - 224#64 + 32#64 = s0.sp - 192#64 := by bv_omega
    rw [← hb4, ← memRegion_split (s0.sp - 224#64) 32 96 (by decide),
        ← hb3, ← memRegion_split (s0.sp - 288#64) 64 128 (by decide),
        ← hb2, ← memRegion_split (s0.sp - 320#64) 32 192 (by decide),
        ← hb1, ← memRegion_split (s0.sp - 352#64) 32 224 (by decide)]
  unfold cmkLoopHeap cmkLoopFrame advanceChainKeyFrame
  rw [stackAt_7712_split_2048 s0.sp]
  have hreord1 :
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
       (x.ckA ↦₆₄ q0_lo) ∗
       ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
       ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
       ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       (ratchetAt A x.self G' st' ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 8192#64) 5664 ∗
        memRegion (s0.sp - 480#64) 112 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        memRegion (s0.sp - 360#64) 4 ∗
        memRegion (s0.sp - 352#64) 32 ∗
        memRegion (s0.sp - 288#64) 64 ∗
        memRegion (s0.sp - 192#64) 96 ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 200#64) ↦₆₄ q1_hi)) ∗
       (((s0.sp - 320#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 296#64) ↦₆₄ q1_hi)) ∗
       ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗
       (ratchetAt A x.self G' st' ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        (memRegion (s0.sp - 8192#64) 5664 ∗ stackAt (s0.sp - 480#64) 2048) ∗
        memRegion (s0.sp - 480#64) 112 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        memRegion (s0.sp - 360#64) 4 ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        memRegion (s0.sp - 352#64) 32 ∗
        memRegion (s0.sp - 288#64) 64 ∗
        memRegion (s0.sp - 192#64) 96 ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) := by sep_ac_rfl
  rw [hreord1, hckA_full]
  refine Entails.trans (sepConj_mono h224 (sepConj_mono_left h320)) ?_
  rw [← h256]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem cmkLoopHeap_placed_transport [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) {s1 s2 : State}
    (hvm : VmPreserved s1 s2)
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState)
    (ckc : ChainKey) (s0 : State) :
    cmkLoopHeap_placed (A.atState lim st s1) x Gc stc ckc s0 ⊢
      cmkLoopHeap_placed (A.atState lim st s2) x Gc stc ckc s0 := by
  rw [cmkLoopHeap_placed_eq, cmkLoopHeap_placed_eq]
  unfold cmkLoopHeap
  rw [ratchetAt_atState, ratchetAt_atState,
      RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_pool]
  repeat apply sepConj_mono_right
  rw [A.pool_transport lim st s1 s2 hvm]
  exact Entails.refl _

private theorem advanceChainKey_preHmac_placed_wp [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (b320 : BitVec 8) (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (blkPl_24).base + 1140#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) s
      ((s0.sp - 320#64) ↦₈ b320)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ((s0.sp - 320#64) ↦₈ 2#8) ∗ R) ∧
        VmPreserved s sf ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x0 = s0.sp - 224#64 ∧
        sf.readReg64 .x1 = x.ckA ∧
        sf.readReg64 .x2 = 32#64 ∧
        sf.readReg64 .x3 = s0.sp - 320#64 ∧
        sf.readReg64 .x4 = 1#64 ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.readReg64 .x30 = (blkPl_24).base + 1172#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  apply sepWP_seg_ls_vm
    (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 (mid := lsmpl.base 73)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨fun _ hm => hm, hvm, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.spAligned, wp_norm, arm64_norm, *]

private theorem advanceChainKey_hmac_placed_wp [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    (H : String → Option (State → State))
    (xg : ConsumeMessageKeyGhost) (ckc : ChainKey) (s0 s : State)
    (hhmac : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s))
    (hstat : s.status = .Running)
    (hpc : s.pc = lsmpl.base 73)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = s0.sp - 224#64)
    (hx1 : s.readReg64 .x1 = xg.ckA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hx3 : s.readReg64 .x3 = s0.sp - 320#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = xg.ckA)
    (hx22 : s.readReg64 .x22 = xg.theirA)
    (hx23 : s.readReg64 .x23 = xg.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx30 : s.readReg64 .x30 = (blkPl_24).base + 1172#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1172#64) s
      (memRegion (s0.sp - 224#64) 32 ∗
       (xg.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
       stackAt (s0.sp - 480#64) 2048)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [2#8]) ∗
             (xg.ckA ↦ₛ keyToBytes32 ckc.key) ∗
             ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
             stackAt (s0.sp - 480#64) 2048) ∗ R) ∧
        VmPreserved s sf ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = xg.ckA ∧
        sf.readReg64 .x22 = xg.theirA ∧
        sf.readReg64 .x23 = xg.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  dsimp only [hmacAtStateSpec, hmacSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.hmacSpec] at hhmac
  wp_call hhmac (s0.sp - 224#64, xg.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [2#8])
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨?_, ‹VmPreserved s sf›, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R hm
    have hsp_sf0 : s.sp = s0.sp - 480#64 := hsp
    rw [hsp_sf0, pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 2#8] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  all_goals simp only [State.spAligned, wp_norm, arm64_norm, *]

private theorem advanceChainKey_postHmac_placed_wp [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3 : BitVec 64)
    (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (blkPl_24).base + 1172#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlt : ckc.index < x.counter) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H)
      (if (ckc.index + 1#32) < x.counter
       then (blkPl_24).base + 820#64
       else (blkPl_24).base + 1244#64)
      s
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ t0) ∗
       ((s0.sp - 312#64) ↦₆₄ t1) ∗
       ((s0.sp - 304#64) ↦₆₄ t2) ∗
       ((s0.sp - 296#64) ↦₆₄ t3) ∗
       (x.ckA ↦₆₄ k0) ∗
       ((x.ckA + 8#64) ↦₆₄ k1) ∗
       ((x.ckA + 16#64) ↦₆₄ k2) ∗
       ((x.ckA + 24#64) ↦₆₄ k3) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index))
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
             ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
             ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
             (x.ckA ↦₆₄ q0_lo) ∗
             ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
             ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
             ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
             ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗ R) ∧
        VmPreserved s sf ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x26 = x.theirA ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x28 = (ckc.index + 1#32).zeroExtend 64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hne0 : ckc.index + 1#32 ≠ 0#32 := add_one_ne_zero_of_lt hlt
  let tgt : BitVec 64 :=
    if (ckc.index + 1#32) < x.counter
    then (blkPl_24).base + 820#64
    else (blkPl_24).base + 1244#64
  change SepWP ((blkPC_24).rebase (blkPl_24).base H) tgt s _ _
  apply sepWP_seg_ls_vm
    (Q := (blkPC_24).rebase (blkPl_24).base (hooksException H))
    blkLib_eq_24 (mid := tgt)
  intro _m_strip
  wp_steps
  wp_if hloop
  · have hlt' : ckc.index + 1#32 < x.counter := BitVec.ult_iff_lt.mp hloop
    simp only [tgt, hlt', ↓reduceIte]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨?_, hvm, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro R hm; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    all_goals simp only [State.spAligned, wp_norm, arm64_norm, *]
  · have hnlt' : ¬ (ckc.index + 1#32 < x.counter) := mt BitVec.ult_iff_lt.mpr hloop
    simp only [tgt, hnlt', ↓reduceIte]
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm := _hnsp.toVmPreserved (by wp_norm_lhs)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      ⟨?_, hvm, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro R hm; exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    all_goals simp only [State.spAligned, wp_norm, arm64_norm, *]

private theorem advanceChainKey_placed_ok_of_hmac [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State))
    {Inv : Memory → Prop}
    (hinv_kf : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    (hhmac_at : ∀ {s1 : State}, Inv s1.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s1))
    (x : ConsumeMessageKeyGhost) (st_init stD : M.σ)
    (remPost : List LibsignalBinary.Heap.AllocEvent → Prop)
    (G' : RatchetGhost) (st' : RatchetState)
    (ckc : ChainKey) (R : SepProp) (s0 sD : State)
    (hlt : ckc.index < x.counter)
    (hD : DefsBudget.AdvanceChainKeyState_placed A lim x st_init stD remPost G' st' ckc R s0 sD)
    (hL : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sD.mem)
    (hinv : Inv sD.mem) :
    let ck' := chainStepN F 1 ckc
    let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
    ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' ∧
      LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget.CmkLoopState_placed
        A lim x st_init stD remPost G' st' ck' R nextPC s0 s' := by
  dsimp only
  rcases hD with
    ⟨hsb, hpc,
     ⟨hstat, hsp, hsp0_align, _hsp_align, hx29, htr, hcl, hvregs⟩,
     ⟨hx19, hx21, hx22, hx23, hx27⟩,
     hmem⟩
  let A0 : RustAlloc := A.atState lim stD sD
  change sD.mem ⊨ cmkLoopHeap_placed A0 x G' st' ckc s0 ∗ R at hmem
  have hpc' : sD.pc = (blkPl_24).base + 1140#64 := hpc
  rw [cmkLoopHeap_placed_eq, cmkLoopHeap_advanceChainKey_split A0 cmkDummyImg x G' st' ckc s0] at hmem
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨b320, hmem⟩
  rw [sepConj_assoc] at hmem
  let R1 : SepProp :=
    (memRegion (s0.sp - 224#64) 32 ∗
     (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
     stackAt (s0.sp - 480#64) 2048 ∗
     memRegion (s0.sp - 319#64) 31 ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
     advanceChainKeyFrame A0 cmkDummyImg x G' st' s0) ∗ R
  rcases (advanceChainKey_preHmac_placed_wp H x b320 s0 sD hstat hpc' hsp hsp0_align
      hx19 hx21 hx22 hx23 hx27 hx29 ⟨htr, hvregs⟩).elim hmem hL with
    ⟨s1, hsteps1, ⟨_hpc1, hstat1, P_f1, hm1, hpost1, hvm1,
      hsp1, _hsp1_align, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1,
      hx19_1, hx21_1, hx22_1, hx23_1, hx27_1, hx29_1, hx30_1⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem1 := hpost1 R1 hm1
  rw [pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 2#8] at hmem1
  have hreord1 :
      (((s0.sp - 320#64) ↦ₛ [2#8]) ∗ R1) =
      ((memRegion (s0.sp - 224#64) 32 ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
        stackAt (s0.sp - 480#64) 2048) ∗
       (memRegion (s0.sp - 319#64) 31 ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
        advanceChainKeyFrame A0 cmkDummyImg x G' st' s0 ∗ R)) := by
    dsimp +zetaDelta only [R1]
    sep_ac_rfl
  rw [hreord1] at hmem1
  let R2 : SepProp :=
    memRegion (s0.sp - 319#64) 31 ∗
    ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
    ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
    advanceChainKeyFrame A0 cmkDummyImg x G' st' s0 ∗ R
  have hinv1 : Inv s1.mem := hinv_kf _ _ hinv hsteps1.keepsFrozen
  have hL1 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s1.mem := hsteps1.codeLoaded hL
  rcases (advanceChainKey_hmac_placed_wp F H (xg := x) ckc s0 s1 (hhmac_at hinv1) hstat1 _hpc1 hsp1 hsp0_align
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx21_1 hx22_1 hx23_1 hx27_1 hx29_1 hx30_1
      htr1).elim hmem1 hL1 with
    ⟨s2, hsteps2, ⟨_hpc2, hstat2, P_f2, hm2, hpost2, hvm2,
      hsp2, _hsp2_align, htr2, hx19_2, hx21_2, hx22_2, hx23_2, hx27_2, hx29_2⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem2 := hpost2 R2 hm2
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  have h320_combine :
      (((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31) ⊢
        memRegion (s0.sp - 320#64) 32 := by
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion (s0.sp - 320#64) [2#8])) ?_
    have ha319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_omega
    change (memRegion (s0.sp - 320#64) 1 ∗ memRegion (s0.sp - 319#64) 31) ⊢ _
    rw [← ha319, ← memRegion_split (s0.sp - 320#64) 1 31 (by decide)]
    exact Entails.refl _
  have hreord2 :
      ((((s0.sp - 224#64) ↦ₛ bs) ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
        stackAt (s0.sp - 480#64) 2048) ∗ R2) =
      ((((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31) ∗
       ((s0.sp - 224#64) ↦ₛ bs) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       advanceChainKeyFrame A0 cmkDummyImg x G' st' s0 ∗ R) := by
    dsimp +zetaDelta only [R2]
    sep_ac_rfl
  rw [hreord2] at hmem2
  have hmem2' := Satisfies.mono (sepConj_mono_left h320_combine) hmem2
  rw [memRegion_32_eq_exists_words (s0.sp - 320#64),
      pointsToBytes_32_eq_pointsTo64 (s0.sp - 224#64) bs hbs,
      pointsToBytes_32_eq_pointsTo64 x.ckA (keyToBytes32 ckc.key) hkey_len] at hmem2'
  have ha216 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_omega
  have ha208 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
  have ha200 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_omega
  have ha312 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_omega
  have ha304 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_omega
  have ha296 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_omega
  rw [ha216, ha208, ha200, ha312, ha304, ha296] at hmem2'
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem2'
  rcases hmem2' with ⟨t0, t1, t2, t3, hmem2'⟩
  let q0_lo := pack64 (bs.take 8)
  let q0_hi := pack64 ((bs.drop 8).take 8)
  let q1_lo := pack64 ((bs.drop 16).take 8)
  let q1_hi := pack64 (bs.drop 24)
  let k0 := pack64 ((keyToBytes32 ckc.key).take 8)
  let k1 := pack64 (((keyToBytes32 ckc.key).drop 8).take 8)
  let k2 := pack64 (((keyToBytes32 ckc.key).drop 16).take 8)
  let k3 := pack64 ((keyToBytes32 ckc.key).drop 24)
  have hreord3 :
      ((((s0.sp - 320#64) ↦₆₄ t0) ∗ ((s0.sp - 312#64) ↦₆₄ t1) ∗
        ((s0.sp - 304#64) ↦₆₄ t2) ∗ ((s0.sp - 296#64) ↦₆₄ t3)) ∗
       (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 200#64) ↦₆₄ q1_hi)) ∗
       ((x.ckA ↦₆₄ k0) ∗ ((x.ckA + 8#64) ↦₆₄ k1) ∗
        ((x.ckA + 16#64) ↦₆₄ k2) ∗ ((x.ckA + 24#64) ↦₆₄ k3)) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       advanceChainKeyFrame A0 cmkDummyImg x G' st' s0 ∗ R) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ t0) ∗
        ((s0.sp - 312#64) ↦₆₄ t1) ∗
        ((s0.sp - 304#64) ↦₆₄ t2) ∗
        ((s0.sp - 296#64) ↦₆₄ t3) ∗
        (x.ckA ↦₆₄ k0) ∗
        ((x.ckA + 8#64) ↦₆₄ k1) ∗
        ((x.ckA + 16#64) ↦₆₄ k2) ∗
        ((x.ckA + 24#64) ↦₆₄ k3) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index)) ∗
       (stackAt (s0.sp - 480#64) 2048 ∗ advanceChainKeyFrame A0 cmkDummyImg x G' st' s0 ∗ R)) := by
    sep_ac_rfl
  rw [hreord3] at hmem2'
  let R3 : SepProp := stackAt (s0.sp - 480#64) 2048 ∗ advanceChainKeyFrame A0 cmkDummyImg x G' st' s0 ∗ R
  have hL2 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s2.mem := hsteps2.codeLoaded hL1
  rcases (advanceChainKey_postHmac_placed_wp H x ckc q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3
      s0 s2 hstat2 _hpc2 hsp2 hsp0_align hx19_2 hx21_2 hx22_2 hx23_2 hx27_2 hx29_2
      htr2 hlt).elim hmem2' hL2 with
    ⟨s', hsteps3, ⟨hpc'', hstat', P_f3, hm3, hpost3, hvm3,
      hsp', hsp'_align, htr', hx19', hx21', hx23', hx26', hx27', hx28', hx29'⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem3 := hpost3 R3 hm3
  have hreord4 :
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
        (x.ckA ↦₆₄ q0_lo) ∗
        ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
        ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗ R3) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
        (x.ckA ↦₆₄ q0_lo) ∗
        ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
        ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
        stackAt (s0.sp - 480#64) 2048 ∗
        advanceChainKeyFrame A0 cmkDummyImg x G' st' s0) ∗ R) := by
    dsimp +zetaDelta only [R3]
    sep_ac_rfl
  rw [hreord4] at hmem3
  have hmem_A0 := Satisfies.mono
    (sepConj_mono_left
      (advanceChainKeyPost_entails_cmkLoopHeap F A0 cmkDummyImg x G' st' ckc q0_lo q0_hi q1_lo q1_hi rfl rfl rfl rfl s0))
    hmem3
  rw [← cmkLoopHeap_placed_eq] at hmem_A0
  have hvm_all : VmPreserved sD s' := (hvm1.trans hvm2).trans hvm3
  have hmem_final : s'.mem ⊨ cmkLoopHeap_placed (A.atState lim stD s') x G' st' (chainStepN F 1 ckc) s0 ∗ R :=
    Satisfies.mono (sepConj_mono_left (cmkLoopHeap_placed_transport A lim stD hvm_all x G' st' (chainStepN F 1 ckc) s0))
      hmem_A0
  have hsteps_all : Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' :=
    (hsteps1.trans hsteps2).trans hsteps3
  refine ⟨s', hsteps_all, hsb, ?_⟩
  refine ⟨hpc'',
    ⟨hstat', hsp', hsp0_align, hsp'_align, hx29', htr'.1,
     hcl.of_keepsFrozen hsteps_all.keepsFrozen, htr'.2⟩,
    ⟨hx21', hx23', hx26', hx27', hx28'⟩,
    fun _ => hx19',
    hmem_final⟩

theorem advanceChainKey_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    AdvanceChainKeyPlacedSpec F A lim H := by
  intro hHmac x st_init stD remPost G' st' ckc R s0 sD hlt hD hL
  let ⟨_, _, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hD
  exact advanceChainKey_placed_ok_of_hmac F A lim H
    (Inv := LibsignalCodeLoaded lsmpl)
    (fun _ _ h hkf => h.of_keepsFrozen hkf)
    (fun h => hmac_placed_ok_at_state hHmac h)
    x st_init stD remPost G' st' ckc R s0 sD hlt hD hL hcl

theorem advanceChainKey_placed_ro_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : String → Option (State → State)) :
    AdvanceChainKeyPlacedRoSpec F A lim H := by
  intro hHmac x st_init stD remPost G' st' ckc R s0 sD hlt hD hL hro
  let ⟨_, _, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hD
  exact advanceChainKey_placed_ok_of_hmac F A lim H
    (Inv := fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hr hkf⟩)
    (fun ⟨hc, hr⟩ => hmac_placed_ro_ok_at_state hHmac hc hr)
    x st_init stD remPost G' st' ckc R s0 sD hlt hD hL ⟨hcl, hro⟩

end LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.AdvanceChainKeyBudget
