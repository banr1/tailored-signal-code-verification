/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `prost::encoding::bytes::encode_repeated [local#2]`

Proves `[LibsignalPlacement]` `RustCliAllocBudget`-threaded contracts (`encodeRepeated59DetSpecOf`,
`encodeRepeatedSpec`, `encodeRepeatedSpecX`) for `encode_repeated::<Vec<u8>, Vec<u8>> [local#2]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2Budget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   fitsEvents_append rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl lsρ withLsCodeLoaded ls_subroutine_ok_of_block
   blkPC_289 blkPl_289 lsProg_289)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeBytesField)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap doReserveStack doReserveStackX sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustNoAllocShimSym spqrRustAllocSym spqrRustReallocSym
   spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Varint
  (EncodeRepeatedGhost encodeRepeatedBytes encodeRepeatedBytes_nil encodeRepeatedBytes_cons
   encodeBytesField_some_eq encodeKey_lengthDelimited_eq encodeBytesField_some_length
   repeatedBytesElemAt repeatedBytesSliceAt repeatedBytesSliceAt_nil repeatedBytesSliceAt_cons
   encodeRepeatedStackOf len_beq_zero_false setup_x20_eq latch_beq_zero_true
   base_add16_sub8 base_add16_sub8_add8 base_add16_add24
   elem_len_ult_spare_iff elem_len_after_reserve_not_ult
   vecU8At_expose_slice vecU8At_pack_slice stackAt_encodeRepeated
   vecU8At_eq_header_rest vecU8At_of_header_rest
   EncRepeatedCalleeSavedPlaced withEncRepeatedCSPlaced subroutine_ok_withEncRepeatedCS_placed
   encodeVarint_length_bounds)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents noAllocShimSpec framelessMemcpyBudgetSpec framelessMemcpySpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushBytesEvents encodeVarintEvents)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (do_reserve_7_placed_ok do_reserve_7_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (reserveStep reserveStep_of_spare reserveStep_of_need_doReserveEvents
   pushBytesStep pushBytesStep_snd_eq encodeRepeatedElemStep encodeRepeatedStep
   sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeRepeatedElemStep_fst_ge encodeRepeatedEvents EncodeRepeatedEnv encodeRepeatedEnv_events
   encodeVarintDetSpecOf encodeRepeatedSpecOf encodeRepeatedSpec encodeRepeatedSpecX
   encodeRepeated59DetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommonBudget
  (step_memcpy_call_gen_placed step_encode_varint_det_call_gen_placed
   step_do_reserve7_call_gen_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
  (encode_varint4_det_placed_ok encode_varint4_det_placed_ok_x)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
  CryptoVerification.LibsignalProtoCodec.encodeVarint encodeBytesField encodeRepeatedBytes
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Hook and Arithmetic Helpers -/

private theorem sessionMemcpyRegionBudget_of_framelessMemcpy {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr framelessMemcpyBudgetSpec) :
    subroutine_ok P addr sessionMemcpyRegionBudgetSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [framelessMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
    sessionMemcpyRegionSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hq.1.2.2, ⟨hq.1.1, hq.1.2.1⟩, hq.2⟩

private theorem setup_x24_59 {n : Nat} (hlt : n < 2 ^ 59) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 (2 * n)) <<< 3 =
      BitVec.ofNat 64 (24 * n) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2n : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3n : (BitVec.ofNat 64 (3 * n)).toNat = 3 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h24n : (BitVec.ofNat 64 (24 * n)).toNat = 24 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : BitVec.ofNat 64 n + BitVec.ofNat 64 (2 * n) = BitVec.ofNat 64 (3 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hn, h2n, h3n, Nat.mod_eq_of_lt (by omega)]; omega
  rw [h2]; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, h3n, h24n, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

private theorem latch_sub24_59 (k : Nat) (hk : k + 1 < 2 ^ 59) :
    BitVec.ofNat 64 (24 * (k + 1)) - 24#64 = BitVec.ofNat 64 (24 * k) := by
  have hk_toNat : (BitVec.ofNat 64 (24 * (k + 1))).toNat = 24 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hk0_toNat : (BitVec.ofNat 64 (24 * k)).toNat = 24 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hle : (24#64 : BitVec 64) ≤ BitVec.ofNat 64 (24 * (k + 1)) := by
    rw [BitVec.le_def, hk_toNat]; change 24 ≤ 24 * (k + 1); omega
  rw [BitVec.toNat_sub_of_le hle, hk_toNat, hk0_toNat]
  change 24 * (k + 1) - 24 = 24 * k; omega

/-! ## Placed Copy, Element Iteration, Latch, and Loop Steppers -/

theorem step_copy_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (hmemcpy : subroutine_ok (lsProg_289 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v cap ptr elemPtr sp keyVal remBytes curBase16 : BitVec 64)
    (bs2 elemBs : List (BitVec 8)) (curSt : M.σ)
    (hle : bs2.length + elemBs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0) (hne : elemBs ≠ [])
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_289).base + 56#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = keyVal)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 elemBs.length)
    (hx22 : s.readReg64 .x22 = elemPtr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs2.length)
    (hx24 : s.readReg64 .x24 = remBytes) (hx25 : s.readReg64 .x25 = curBase16)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs2 ∗ (elemPtr ↦ₛ elemBs) ∗ A.pool lim curSt s) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_289).base + 84#64 → sm.status = .Running → sm.sp = sp - 80#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = remBytes → sm.readReg64 .x25 = curBase16 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_289 H) ret sm
        ((vecU8At A.repAlloc v cap ptr (bs2 ++ elemBs) ∗ (elemPtr ↦ₛ elemBs) ∗
          A.pool lim curSt sm) ∗ F) Q Qp) :
    SepWPp (lsProg_289 H) ret s P Q Qp := by
  subst hP
  have hpos : 0 < elemBs.length := List.length_pos_of_ne_nil hne
  rw [vecU8At_expose_slice A.repAlloc v cap ptr bs2 elemBs.length hle hcap hptr hpos]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsρ spqrMemcpySym)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], fun hvm0 _ => ?_⟩
    rw [← A.pool_of_vmPreserved hvm0]
    have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_memcpy_call_gen_placed A lim hmemcpy
      (ptr + BitVec.ofNat 64 bs2.length) elemPtr sp ((blkPl_289).base + bv% (76)) elemBs curSt
      (F := (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs2) ∗
        memRegion (ptr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 elemBs.length)
          (cap.toNat - bs2.length - elemBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by sep_ac_rfl) ?_
    intro sm hpcm1 hrunm1 hspm1 htrm1 hcsm1 hcs_s0 _
    rcases hcsm1 with ⟨hx19m, hx20m, hx21m, _, hx23m, hx24m, hx25m, _⟩
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_289).base + bv% (84))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm1 _ => ?_⟩
      rw [← A.pool_of_vmPreserved hvm1]
      refine SepWPp.weaken_pre ?_
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_s0.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self])))
      rw [← vecU8At_pack_slice A.repAlloc v cap ptr bs2 elemBs hle hcap hptr hne]
      exact Entails.of_eq (by sep_ac_rfl)

theorem step_iter_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    {s0 s : State}
    (henc : subroutine_ok (lsProg_289 H) (lsmpl.base 292)
      (withEncRepeatedCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_289 H) (lsmpl.base 320)
      (withEncRepeatedCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_289 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (tag : Nat) (v curCap curPtr curBase elemPtr sp remBytes : BitVec 64)
    (curBs elemBs : List (BitVec 8)) (curSt : M.σ)
    (hfit : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
      curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62)
    (hfits_elem : FitsEvents M lim curSt
      (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_289).base + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = remBytes) (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesElemAt curBase elemPtr elemBs ∗
      vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_289).base + 84#64 → sm.status = .Running → sm.sp = sp - 80#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x24 = remBytes → sm.readReg64 .x25 = curBase + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).1 →
      SepWPp (lsProg_289 H) ret sm
        ((repeatedBytesElemAt curBase elemPtr elemBs ∗
          vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeBytesField tag (some elemBs)) ∗
          A.pool lim (M.stepEvents (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 curSt) sm ∗
          stackAt (sp - 80#64) (48 + resStack)) ∗ F) Q Qp) :
    SepWPp (lsProg_289 H) ret s P Q Qp := by
  subst hP
  have hlen_ef := encodeBytesField_some_length tag elemBs
  have hkey_eq := encodeKey_lengthDelimited_eq tag
  have hkey_bounds := encodeVarint_length_bounds (BitVec.ofNat 64 (tag * 8 + 2))
  have hlen_bounds := encodeVarint_length_bounds (BitVec.ofNat 64 elemBs.length)
  let s1 := pushBytesStep (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length curCap.toNat curBs.length
  let s2 := pushBytesStep (encodeVarint (BitVec.ofNat 64 elemBs.length)).length s1.1
    (curBs.length + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length)
  let s3 := reserveStep s2.1
    (curBs.length + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length +
      (encodeVarint (BitVec.ofNat 64 elemBs.length)).length) elemBs.length
  have helem_step_eq : encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs =
      (s3.1, s1.2 ++ s2.2 ++ s3.2) := rfl
  rw [helem_step_eq, List.append_assoc, fitsEvents_append] at hfits_elem
  rcases hfits_elem with ⟨hfits1, hfits23⟩
  rw [fitsEvents_append] at hfits23
  rcases hfits23 with ⟨hfits2, hfits3⟩
  have hfit1 : curBs.length + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62 := by
    rw [← hkey_eq]
    rcases hfit with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hfits_call1 : FitsEvents M lim curSt
      (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 (tag * 8 + 2)) v curCap curPtr curBs)) := by
    rw [encodeVarintEvents, ← pushBytesStep_snd_eq]; exact hfits1
  have hb8 := base_add16_sub8 curBase
  have hb16 := base_add16_sub8_add8 curBase
  rw [repeatedBytesElemAt]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 292)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], fun hvm0 _ => ?_⟩
    rw [← A.pool_of_vmPreserved hvm0]
    refine step_encode_varint_det_call_gen_placed A lim henc
      (BitVec.ofNat 64 (tag * 8 + 2)) v curCap curPtr sp ((blkPl_289).base + bv% (112)) curBs curSt hfit1 hfits_call1
      (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
        (elemPtr ↦ₛ elemBs) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by sep_ac_rfl) ?_
    intro st_s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcsm1 hcs1 hge1 hpres1 hcap1_det
    rcases hcsm1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, hx25_1, _⟩
    have hfit2 : (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length +
        (encodeVarint (BitVec.ofNat 64 elemBs.length)).length ≤ cap1.toNat ∨
        (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length + 10 < 2 ^ 62 := by
      rw [List.length_append, ← hkey_eq]
      rcases hfit with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hfits_call2 : FitsEvents M lim (M.stepEvents s1.2 curSt)
        (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 elemBs.length) v cap1 ptr1
          (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))))) := by
      rw [encodeVarintEvents, ← pushBytesStep_snd_eq, hcap1_det, List.length_append]
      exact hfits2
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 292)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm1 _ => ?_⟩
      rw [← A.pool_of_vmPreserved hvm1]
      refine step_encode_varint_det_call_gen_placed A lim henc
        (BitVec.ofNat 64 elemBs.length) v cap1 ptr1 sp ((blkPl_289).base + bv% (124))
        (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))) (M.stepEvents s1.2 curSt) hfit2 hfits_call2
        (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
          (elemPtr ↦ₛ elemBs) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro st_s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcsm2 hcs2 hge2 hpres2 hcap2_det
      rcases hcsm2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, hx24_2, hx25_2, _⟩
      have hs2_eq : pushBytesStep (encodeVarint (BitVec.ofNat 64 elemBs.length)).length cap1.toNat
          (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length = s2 := by
        rw [hcap1_det, List.length_append]
      rw [hs2_eq] at hcap2_det ⊢
      set bs2 := curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2)) ++
        encodeVarint (BitVec.ofNat 64 elemBs.length) with hbs2_def
      have hs3_eq : reserveStep cap2.toNat bs2.length elemBs.length = s3 := by
        rw [hcap2_det]; simp only [hbs2_def, List.length_append]; rfl
      clear hcap1_det hcap2_det hs2_eq
      have hbs_final : bs2 ++ elemBs = curBs ++ encodeBytesField tag (some elemBs) := by
        simp only [hbs2_def, ← hkey_eq, encodeBytesField_some_eq, List.append_assoc]
      have hbs2_len : bs2.length + elemBs.length =
          curBs.length + (encodeBytesField tag (some elemBs)).length := by
        rw [← List.length_append, hbs_final, List.length_append]
      clear_value bs2; clear hbs2_def
      rw [vecU8At_eq_header_rest A.repAlloc v cap2 ptr2 bs2]
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hbs2_le, hcap2_lt, hptr2_ne⟩ => ?_
      have helem_lt : elemBs.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
      by_cases hneed : cap2.toNat < bs2.length + elemBs.length
      · have hfit3 : bs2.length + elemBs.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
        have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 elemBs.length) = true :=
          (elem_len_ult_spare_iff hbs2_le hcap2_lt helem_lt).mpr hneed
        have hne : elemBs ≠ [] := by intro h; subst h; simp at hneed; omega
        obtain ⟨hnot_ult, hnew_ge, hnew_cap, hnew_bound⟩ := elem_len_after_reserve_not_ult hfit3 hneed
        have hs3_res : s3 = (reserveCap cap2.toNat bs2.length elemBs.length,
            doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 elemBs.length)) := by
          rw [← hs3_eq]
          exact reserveStep_of_need_doReserveEvents v cap2 ptr2 bs2 elemBs.length (by omega)
        have hfits_res : FitsEvents M lim (M.stepEvents s2.2 (M.stepEvents s1.2 curSt))
            (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 elemBs.length)) := by
          simpa [hs3_res] using hfits3
        apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 320)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [← A.pool_of_vmPreserved hvm2]
          have hx1_toNat : (BitVec.ofNat 64 bs2.length).toNat = bs2.length := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          refine step_do_reserve7_call_gen_placed hres A lim hdoReserve
            v cap2 ptr2 sp ((blkPl_289).base + bv% (176)) bs2 elemBs.length
            (M.stepEvents s2.2 (M.stepEvents s1.2 curSt)) hnew_bound hfits_res
            (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗
              (elemPtr ↦ₛ elemBs) ∗ F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs2.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
            (by rw [← vecU8At_of_header_rest A.repAlloc v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne]; sep_ac_rfl) ?_
          intro st_s3 newPtr hpc3 hrun3 hsp3 htr3 hcsm3 hcs3
          rcases hcsm3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, _, hx24_3, hx25_3, _⟩
          rw [vecU8At_eq_header_rest A.repAlloc v
            (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr bs2]
          simp only [sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨hnew_le, hnew_lt63, hnew_ptr⟩ => ?_
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_289).base + bv% (56))
          by_vm_steps
            wp_steps
            refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              ⟨by simp only [arm64_norm, *], fun hvm3 _ => ?_⟩
            rw [← A.pool_of_vmPreserved hvm3]
            have hst_all : M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 elemBs.length))
                (M.stepEvents s2.2 (M.stepEvents s1.2 curSt)) =
                M.stepEvents (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 curSt := by
              rw [helem_step_eq, List.append_assoc, M.stepEvents_append, M.stepEvents_append, hs3_res]
            rw [hst_all]
            refine step_copy_placed A lim H hmemcpy v
              (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr elemPtr sp
              (BitVec.ofNat 64 (tag * 8 + 2)) remBytes (curBase + 16#64) bs2 elemBs
              (M.stepEvents (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 curSt)
              hnew_ge hnew_lt63 hnew_ptr hne
              (F := stackAt (sp - 80#64) (48 + resStack) ∗
                ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗ F)
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hcs3.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
              (by rw [← vecU8At_of_header_rest A.repAlloc v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr bs2 hnew_le hnew_lt63 hnew_ptr]; sep_ac_rfl) ?_
            intro st_s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
            have hnewCap_det : (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)).toNat =
                (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).1 := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), helem_step_eq, hs3_res]
            refine SepWPp.weaken_pre ?_
              (hnext st_s4 (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr
                hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
                (by rw [hnewCap_det]; exact encodeRepeatedElemStep_fst_ge tag curCap.toNat curBs.length elemBs)
                (fun h => absurd h (by omega)) hnewCap_det)
            rw [hbs_final, repeatedBytesElemAt]
            exact Entails.of_eq (by sep_ac_rfl)
      · have hle2 : bs2.length + elemBs.length ≤ cap2.toNat := by omega
        have hs3_spare : s3 = (cap2.toNat, []) := by
          rw [← hs3_eq]; exact reserveStep_of_spare hle2
        have hst_all : M.stepEvents s2.2 (M.stepEvents s1.2 curSt) =
            M.stepEvents (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 curSt := by
          rw [helem_step_eq, hs3_spare, List.append_nil, M.stepEvents_append]
        have hcap2_elem : cap2.toNat =
            (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).1 := by
          rw [helem_step_eq, hs3_spare]
        have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 elemBs.length) = false := by
          rw [Bool.eq_false_iff]; intro h
          exact hneed ((elem_len_ult_spare_iff hbs2_le hcap2_lt helem_lt).mp h)
        have hpres_all : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat →
            cap2 = curCap ∧ ptr2 = curPtr := by
          intro hfit_cap
          have h1 : curBs.length + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length ≤ curCap.toNat := by
            rw [← hkey_eq]; omega
          obtain ⟨hc1, hp1⟩ := hpres1 h1
          have h2 : (curBs ++ encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length +
              (encodeVarint (BitVec.ofNat 64 elemBs.length)).length ≤ cap1.toNat := by
            rw [hc1, List.length_append, ← hkey_eq]; omega
          obtain ⟨hc2, hp2⟩ := hpres2 h2
          exact ⟨hc2.trans hc1, hp2.trans hp1⟩
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_289).base + bv% (144))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv2 => ?_⟩
          rw [← A.pool_of_vmPreserved hvm2, hst_all]
          by_cases helem : elemBs = []
          · subst helem
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_289).base + bv% (84))
            by_vm_steps
              wp_steps
              refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                ⟨by simp only [arm64_norm, *], fun hvm3 hinv3 => ?_⟩
              rw [← A.pool_of_vmPreserved hvm3]
              refine SepWPp.weaken_pre ?_
                (hnext _ cap2 ptr2
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                    (by simp only [arm64_norm]) (hinv2.trans hinv3))
                  (by omega) hpres_all hcap2_elem)
              have hbs_nil : bs2 = curBs ++ encodeBytesField tag (some []) := by simpa using hbs_final
              rw [← hbs_nil, ← vecU8At_of_header_rest A.repAlloc v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne,
                repeatedBytesElemAt]
              exact Entails.of_eq (by sep_ac_rfl)
          · have hcbnz : (BitVec.ofNat 64 elemBs.length == 0#64) = false :=
              len_beq_zero_false (List.length_pos_of_ne_nil helem) helem_lt
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_289).base + bv% (56))
            by_vm_steps
              wp_steps
              refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                ⟨by simp only [arm64_norm, *], fun hvm3 hinv3 => ?_⟩
              rw [← A.pool_of_vmPreserved hvm3]
              refine step_copy_placed A lim H hmemcpy v cap2 ptr2 elemPtr sp
                (BitVec.ofNat 64 (tag * 8 + 2)) remBytes (curBase + 16#64) bs2 elemBs
                (M.stepEvents (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 curSt)
                hle2 hcap2_lt hptr2_ne helem
                (F := stackAt (sp - 80#64) (48 + resStack) ∗
                  ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ BitVec.ofNat 64 elemBs.length) ∗ F)
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) (hinv2.trans hinv3))
                (by rw [← vecU8At_of_header_rest A.repAlloc v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne]; sep_ac_rfl) ?_
              intro st_s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
              refine SepWPp.weaken_pre ?_
                (hnext st_s4 cap2 ptr2 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
                  (by omega) hpres_all hcap2_elem)
              rw [hbs_final, repeatedBytesElemAt]
              exact Entails.of_eq (by sep_ac_rfl)

theorem step_latch_zero_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (sp curBase : BitVec 64) (curSt : M.σ)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_289).base + 84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * 1))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = A.pool lim curSt s ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_289).base + 228#64 → sm.status = .Running → sm.sp = sp - 80#64 →
      sm.trace = s0.trace → EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_289 H) ret sm (A.pool lim curSt sm ∗ F) Q Qp) :
    SepWPp (lsProg_289 H) ret s P Q Qp := by
  subst hP
  have hbeq := latch_beq_zero_true
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_289).base + bv% (228))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], fun hvm0 _ => ?_⟩
    rw [← A.pool_of_vmPreserved hvm0]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_latch_succ_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (v keyVal sp curBase : BitVec 64) (k : Nat) (curSt : M.σ)
    (_hpos : 0 < k) (hlt : k + 1 < 2 ^ 59)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_289).base + 84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = A.pool lim curSt s ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_289).base + 96#64 → sm.status = .Running → sm.sp = sp - 80#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = BitVec.ofNat 64 (24 * k) →
      sm.readReg64 .x25 = (curBase + 24#64) + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_289 H) ret sm (A.pool lim curSt sm ∗ F) Q Qp) :
    SepWPp (lsProg_289 H) ret s P Q Qp := by
  subst hP
  have hbeq : (BitVec.ofNat 64 (24 * (k + 1)) == 24#64) = false := by
    rw [beq_eq_false_iff_ne]; intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change 24 * (k + 1) = 24 at ht; omega
  have hx24_next := latch_sub24_59 k hlt
  have hx25_next := base_add16_add24 curBase
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_289).base + bv% (96))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], fun hvm0 _ => ?_⟩
    rw [← A.pool_of_vmPreserved hvm0]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_loop_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    {s0 : State}
    (henc : subroutine_ok (lsProg_289 H) (lsmpl.base 292)
      (withEncRepeatedCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_289 H) (lsmpl.base 320)
      (withEncRepeatedCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_289 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (tag : Nat) (v sp : BitVec 64) (elems : List (BitVec 64 × List (BitVec 8)))
    (hne : elems ≠ []) (helem_cnt : elems.length < 2 ^ 59)
    (curBase curCap curPtr : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit : curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat ∨
      curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).2)
    {s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_289).base + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * elems.length))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesSliceAt curBase elems ∗
      vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_289).base + 228#64 → sm.status = .Running → sm.sp = sp - 80#64 →
      sm.trace = s0.trace → EncRepeatedCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeRepeatedBytes tag (elems.map Prod.snd)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat =
        (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).1 →
      SepWPp (lsProg_289 H) ret sm
        ((repeatedBytesSliceAt curBase elems ∗
          vecU8At A.repAlloc v nextCap nextPtr
            (curBs ++ encodeRepeatedBytes tag (elems.map Prod.snd)) ∗
          A.pool lim (M.stepEvents
            (encodeRepeatedStep tag curCap.toNat curBs.length (elems.map Prod.snd)).2 curSt) sm ∗
          stackAt (sp - 80#64) (48 + resStack)) ∗ F) Q Qp) :
    SepWPp (lsProg_289 H) ret s P Q Qp := by
  induction elems generalizing curBase curCap curPtr curBs curSt s P F with
  | nil => exact False.elim (hne rfl)
  | cons head rest ih =>
    rcases head with ⟨elemPtr, elemBs⟩
    subst hP
    let se := encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs
    let sr := encodeRepeatedStep tag se.1
      (curBs.length + (encodeBytesField tag (some elemBs)).length) (rest.map Prod.snd)
    have hstep_cons : encodeRepeatedStep tag curCap.toNat curBs.length
        (((elemPtr, elemBs) :: rest).map Prod.snd) = (sr.1, se.2 ++ sr.2) := rfl
    rw [hstep_cons, fitsEvents_append] at hfits
    rcases hfits with ⟨hfits_head, hfits_rest0⟩
    simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit
    have hfit_head : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
        curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62 := by
      rcases hfit with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    refine step_iter_placed hres A lim H henc hdoReserve hmemcpy tag v curCap curPtr curBase elemPtr sp
      (BitVec.ofNat 64 (24 * (rest.length + 1))) curBs elemBs curSt hfit_head hfits_head
      (F := repeatedBytesSliceAt (curBase + 24#64) rest ∗ F)
      hpc hrun hsp halign htr hx19 hx20 hx24 hx25 hcs
      (by rw [repeatedBytesSliceAt_cons]; sep_ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 hge1 hpres1 hcap1_det
    cases rest with
    | nil =>
      simp only [List.length_nil, Nat.zero_add] at hx24_1
      refine step_latch_zero_placed A lim H sp curBase (M.stepEvents se.2 curSt)
        (F := repeatedBytesElemAt curBase elemPtr elemBs ∗
          vecU8At A.repAlloc v cap1 ptr1 (curBs ++ encodeBytesField tag (some elemBs)) ∗
          stackAt (sp - 80#64) (48 + resStack) ∗
          repeatedBytesSliceAt (curBase + 24#64) [] ∗ F)
        hpc1 hrun1 hsp1 htr1 hx24_1 hx25_1 hcs1 (by sep_ac_rfl) ?_
      intro s2 hpc2 hrun2 hsp2 htr2 hcs2
      have hsr_nil : sr = (se.1, []) := rfl
      have hstep_nil_snd : (encodeRepeatedStep tag curCap.toNat curBs.length
          (((elemPtr, elemBs) :: []).map Prod.snd)).2 = se.2 := by
        rw [hstep_cons, hsr_nil, List.append_nil]
      have hcap1_nil : cap1.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length
          (((elemPtr, elemBs) :: []).map Prod.snd)).1 := by
        rw [hcap1_det, hstep_cons, hsr_nil]
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap1 ptr1 hpc2 hrun2 hsp2 htr2 hcs2 hge1 (by simpa using hpres1) hcap1_nil)
      rw [hstep_nil_snd]
      simp only [repeatedBytesSliceAt_cons, repeatedBytesSliceAt_nil, List.map_cons, List.map_nil,
        encodeRepeatedBytes_cons, encodeRepeatedBytes_nil, List.append_nil]
      exact Entails.of_eq (by sep_ac_rfl)
    | cons nextHead rest' =>
      have hrest_ne : nextHead :: rest' ≠ [] := List.cons_ne_nil _ _
      have hrest_pos : 0 < (nextHead :: rest').length := List.length_pos_of_ne_nil hrest_ne
      have helem_cnt' : (nextHead :: rest').length + 1 < 2 ^ 59 := helem_cnt
      set tail := nextHead :: rest'
      refine step_latch_succ_placed A lim H v (BitVec.ofNat 64 (tag * 8 + 2)) sp curBase
        tail.length (M.stepEvents se.2 curSt) hrest_pos helem_cnt'
        (F := repeatedBytesElemAt curBase elemPtr elemBs ∗
          vecU8At A.repAlloc v cap1 ptr1 (curBs ++ encodeBytesField tag (some elemBs)) ∗
          stackAt (sp - 80#64) (48 + resStack) ∗
          repeatedBytesSliceAt (curBase + 24#64) tail ∗ F)
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx24_1 hx25_1 hcs1 (by sep_ac_rfl) ?_
      intro s1' hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1'
      have hfit_rest : (curBs ++ encodeBytesField tag (some elemBs)).length +
          (encodeRepeatedBytes tag (tail.map Prod.snd)).length ≤ cap1.toNat ∨
          (curBs ++ encodeBytesField tag (some elemBs)).length +
            (encodeRepeatedBytes tag (tail.map Prod.snd)).length + 10 < 2 ^ 62 := by
        rw [List.length_append]
        rcases hfit with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have hsr_eq : encodeRepeatedStep tag cap1.toNat
          (curBs ++ encodeBytesField tag (some elemBs)).length (tail.map Prod.snd) = sr := by
        rw [hcap1_det, List.length_append]
      have hfits_rest : FitsEvents M lim (M.stepEvents se.2 curSt)
          (encodeRepeatedStep tag cap1.toNat
            (curBs ++ encodeBytesField tag (some elemBs)).length (tail.map Prod.snd)).2 := by
        rw [hsr_eq]; exact hfits_rest0
      refine ih hrest_ne (by omega) (curBase + 24#64) cap1 ptr1
        (curBs ++ encodeBytesField tag (some elemBs)) (M.stepEvents se.2 curSt)
        hfit_rest hfits_rest
        (F := repeatedBytesElemAt curBase elemPtr elemBs ∗ F)
        hpc1' hrun1' hsp1' htr1' hx19_1' hx20_1' hx24_1' hx25_1' hcs1'
        (by sep_ac_rfl) ?_
      intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 hge2 hpres2 hcap2_det
      rw [hsr_eq] at hcap2_det ⊢
      have hpres_all : curBs.length +
          (encodeRepeatedBytes tag (((elemPtr, elemBs) :: tail).map Prod.snd)).length ≤
          curCap.toNat → cap2 = curCap ∧ ptr2 = curPtr := by
        intro hfit_cap
        simp only [List.map_cons, encodeRepeatedBytes_cons, List.length_append] at hfit_cap
        obtain ⟨hc1, hp1⟩ := hpres1 (by omega)
        have h2 : (curBs ++ encodeBytesField tag (some elemBs)).length +
            (encodeRepeatedBytes tag (tail.map Prod.snd)).length ≤ cap1.toNat := by
          rw [hc1, List.length_append]; omega
        obtain ⟨hc2, hp2⟩ := hpres2 h2
        exact ⟨hc2.trans hc1, hp2.trans hp1⟩
      have hcap2_cons : cap2.toNat = (encodeRepeatedStep tag curCap.toNat curBs.length
          (((elemPtr, elemBs) :: tail).map Prod.snd)).1 := by
        rw [hstep_cons]; exact hcap2_det
      refine SepWPp.weaken_pre ?_
        (hnext s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs2 (by omega) hpres_all hcap2_cons)
      have hst_cons : M.stepEvents sr.2 (M.stepEvents se.2 curSt) =
          M.stepEvents (encodeRepeatedStep tag curCap.toNat curBs.length
            (((elemPtr, elemBs) :: tail).map Prod.snd)).2 curSt := by
        rw [hstep_cons, M.stepEvents_append]
      clear_value tail
      rw [hst_cons, repeatedBytesSliceAt_cons, List.map_cons, encodeRepeatedBytes_cons,
        ← List.append_assoc]
      exact Entails.of_eq (by sep_ac_rfl)

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

theorem encode_repeated_2_59_det_gen_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 80 < 2 ^ 64) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : EncodeRepeatedGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    (henc : subroutine_ok (lsProg_289 H) (lsmpl.base 292)
      (withEncRepeatedCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_289 H) (lsmpl.base 320)
      (withEncRepeatedCSPlaced s0 (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_289 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hpc : s0.pc = (blkPl_289).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeRepeated59DetSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (halign : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_289 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) →
            (s'.mem ⊨ (encodeRepeated59DetSpecOf resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (encodeRepeated59DetSpecOf resStack A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have hloop := step_loop_placed hres A lim H henc hdoReserve hmemcpy
  refine ⟨(encodeRepeated59DetSpecOf resStack A lim).pre (x, st0) s0, hpre, ?_⟩
  dsimp only [encodeRepeated59DetSpecOf, encodeRepeatedSpecOf]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, htag1, htag2, helem_cnt, hfit, hfits0⟩ => ?_
  have hfits_ev : FitsEvents M lim st0 (encodeRepeatedEvents x) := FitsEnv.eq_iff.mp hfits0
  rcases x with ⟨tag, base, elems, v, cap, ptr, bs⟩
  dsimp only at hx0 hx1 hx2 hx3 htag1 htag2 helem_cnt hfit hfits_ev ⊢
  cases elems with
  | nil =>
    apply sepWPp_of_sepWP_cs_vm_placed (mid := s0.readReg64 .lr)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine ⟨?_, by simp only [arm64_norm, *],
        by simp only [CalleeSavedPreserved, arm64_norm, *, and_self]⟩
      intro hPR
      let xNil := EncodeRepeatedGhost.mk tag base [] v cap ptr bs
      have hp1 : (cap.toNat ≤ cap.toNat ∧
          (bs.length + (encodeRepeatedBytes tag (([] : List (BitVec 64 × List (BitVec 8))).map Prod.snd)).length ≤ cap.toNat →
            cap = cap ∧ ptr = ptr) ∧
          cap.toNat = (encodeRepeatedStep tag cap.toNat bs.length (([] : List (BitVec 64 × List (BitVec 8))).map Prod.snd)).1) = True :=
        eq_true ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩, rfl⟩
      have hp2 : EncodeRepeatedEnv xNil [] = True :=
        eq_true (encodeRepeatedEnv_events xNil)
      simp only [sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨[], cap, ptr, by simp only [arm64_norm, *], ?_⟩
      rw [hp1, hp2, pure_true, emp_sepConj, emp_sepConj, M.stepEvents_nil]
      simpa only [List.map_nil, encodeRepeatedBytes_nil, List.append_nil, sepConj_assoc] using hPR
  | cons head rest =>
    have hne : head :: rest ≠ [] := List.cons_ne_nil _ _
    have hpos : 0 < (head :: rest).length := List.length_pos_of_ne_nil hne
    have hcbz : (BitVec.ofNat 64 (head :: rest).length == 0#64) = false :=
      len_beq_zero_false hpos (by omega)
    have hx24_setup := setup_x24_59 helem_cnt
    have hx0' : BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 32 tag := hx0
    rw [stackAt_encodeRepeated hres s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 =>
      SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
      SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 =>
      SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
      SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 => ?_
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_289).base + bv% (96))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_pro hinv_pro => ?_⟩
      rw [← A.pool_of_vmPreserved hvm_pro]
      have hx20_setup := setup_x20_eq htag2
      set savedCells : SepProp :=
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ v3) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) with hsaved_def
      clear_value savedCells
      have halign64 : s0.sp &&& 15#64 = 0#64 := by
        simpa only [State.spAligned, beq_iff_eq] using halign
      refine hloop tag v s0.sp (head :: rest) hne helem_cnt base cap ptr bs st0 hfit hfits_ev
        (F := savedCells)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign64
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ((EncRepeatedCalleeSavedPlaced.refl s0).step (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv_pro)
        (by sep_ac_rfl) ?_
      intro sm cap' ptr' hpcm hrunm hspm htrm hcsm hge hpres hcap_det
      rcases hcsm with ⟨hx26m, hx27m, hx28m, hvregsm, _⟩
      rw [hsaved_def]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := s0.readReg64 .lr)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm_epi _ => ?_⟩
        rw [← A.pool_of_vmPreserved hvm_epi]
        apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        refine ⟨?_, by simp only [arm64_norm, *],
          by simp only [CalleeSavedPreserved, arm64_norm, *]⟩
        intro hPR
        let xCons := EncodeRepeatedGhost.mk tag base (head :: rest) v cap ptr bs
        have hp1 : (cap.toNat ≤ cap'.toNat ∧
            (bs.length + (encodeRepeatedBytes tag ((head :: rest).map Prod.snd)).length ≤ cap.toNat →
              cap' = cap ∧ ptr' = ptr) ∧
            cap'.toNat = (encodeRepeatedStep tag cap.toNat bs.length ((head :: rest).map Prod.snd)).1) = True :=
          eq_true ⟨hge, hpres, hcap_det⟩
        have hp2 : EncodeRepeatedEnv xCons (encodeRepeatedEvents xCons) = True :=
          eq_true (encodeRepeatedEnv_events xCons)
        simp only [satisfies_sepExists, satisfies_pure_sepConj]
        refine ⟨s0.readReg64 (Reg.gpr 29#5), s0.readReg64 (Reg.gpr 30#5),
          s0.readReg64 (Reg.gpr 25#5), v3, s0.readReg64 (Reg.gpr 24#5),
          s0.readReg64 (Reg.gpr 23#5), s0.readReg64 (Reg.gpr 22#5),
          s0.readReg64 (Reg.gpr 21#5), s0.readReg64 (Reg.gpr 20#5),
          s0.readReg64 (Reg.gpr 19#5), encodeRepeatedEvents xCons, cap', ptr',
          by simp only [arm64_norm, *], ?_⟩
        rw [hp1, hp2, pure_true, emp_sepConj, emp_sepConj]
        convert hPR using 1; sep_ac_rfl

theorem encode_repeated_2_59_det_placed_ok_of_callees [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok (lsProg_289 H) (lsmpl.base 292)
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_289 H) (lsmpl.base 320)
      (withLsCodeLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_289 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_289 H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp
  intro (x, st0) R s0 hpc hrun hpre halign
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encode_repeated_2_59_det_gen_placed_ok hres
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 henc0)
    (subroutine_ok_withEncRepeatedCS_placed s0 hcl0 hdoReserve0)
    hmemcpy hpc hrun hpre halign
  exact ⟨P, R, hP, hwp⟩

theorem encode_repeated_2_59_det_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_289).rebase (blkPl_289).base H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf doReserveStack A lim)) :=
  encode_repeated_2_59_det_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_289 H)
      (encode_varint4_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_289 H)
      (do_reserve_7_placed_ok h_panic hshim halloc hrealloc))
    (sessionMemcpyRegionBudget_of_framelessMemcpy (spqr_hook_ok_of_mem hmc))

theorem encode_repeated_2_59_det_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_289).rebase (blkPl_289).base H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeated59DetSpecOf doReserveStackX A lim)) :=
  encode_repeated_2_59_det_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_289 H)
      (encode_varint4_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_289 H)
      (do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc))
    (sessionMemcpyRegionBudget_of_framelessMemcpy (spqr_hook_ok_of_mem hmc))

theorem encode_repeated_2_placed_ok_of_callees [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (henc0 : subroutine_ok (lsProg_289 H) (lsmpl.base 292)
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_289 H) (lsmpl.base 320)
      (withLsCodeLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_289 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_289 H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hsp =>
    (encode_repeated_2_59_det_placed_ok_of_callees hres henc0 hdoReserve0 hmemcpy).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨hpre.1, ?_⟩
  have hpre2 := hpre.2
  simp only [encodeRepeatedSpecOf, encodeRepeated59DetSpecOf, sepConj_assoc,
    satisfies_pure_sepConj] at hpre2 ⊢
  rcases hpre2 with ⟨⟨hw0, hx1, hx2, hx3, ht1, ht2, hcnt, hfit, hfits⟩, hm⟩
  exact ⟨⟨hw0, hx1, hx2, hx3, ht1, ht2, by omega, hfit, hfits⟩, hm⟩

theorem encode_repeated_2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_289).rebase (blkPl_289).base H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpec A lim)) :=
  encode_repeated_2_placed_ok_of_callees (resStack := doReserveStack) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_289 H)
      (encode_varint4_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_289 H)
      (do_reserve_7_placed_ok h_panic hshim halloc hrealloc))
    (sessionMemcpyRegionBudget_of_framelessMemcpy (spqr_hook_ok_of_mem hmc))

theorem encode_repeated_2_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H spqrMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_289).rebase (blkPl_289).base H) (blkPl_289).base
      (withLsCodeLoaded lsmpl (encodeRepeatedSpecX A lim)) :=
  encode_repeated_2_placed_ok_of_callees (resStack := doReserveStackX) (by decide)
    (ls_subroutine_ok_of_block (callerProg := lsProg_289 H)
      (encode_varint4_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_289 H)
      (do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc))
    (sessionMemcpyRegionBudget_of_framelessMemcpy (spqr_hook_ok_of_mem hmc))

end LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2Budget
