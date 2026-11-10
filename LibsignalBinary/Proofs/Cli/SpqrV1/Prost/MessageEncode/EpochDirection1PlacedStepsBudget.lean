/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Stages 1–3 (`+0..+328`) of `encode<EpochDirection> [local#3]` (Block `457`)

Proves budget-threaded `SepWPp` stage lemmas (`step_hdr_1_placed`, `step_ctr_1_placed`,
`step_next_1_placed`) on CLI Block `457` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1PlacedStepsBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement lsMemcpySym lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPl_460)
open CryptoVerification.Cli.SpqrV1.Varint.Placed (blkPl_451)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_457 blkPl_457_ρ lsProg_457)
open CryptoVerification.RustHeap (vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (WireType encodeKey)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost vecU8At_eq_header_sep_buf)
open CryptoVerification.SpqrV1.Varint
  (elem_len_after_reserve_not_ult elem_len_ult_spare_iff vecU8At_expose_slice vecU8At_pack_slice)
open CryptoVerification.SpqrV1.ProtoRepr (epochDirectionPBEncodedLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero ofNat_countLeadingZeros_32
   ofNat_countLeadingZeros_64 ofNat_length_beq_zero_of_lt ule_self_64 ule_zero_64
   ult_self_64 ult_zero_64 zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Auth (authEncodeStackOf)
open LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget (sepWPp_extract_vecU8At_bounds)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (AuthEncodeCalleeSavedPlaced bs0_append_epochDirectionHeaderBytes
   bs_append_epochDirectionCtrBytes_of_ne_zero bs_append_epochDirectionCtrBytes_of_zero
   bs_append_epochDirectionNextBytes_of_empty bs_append_epochDirectionNextBytes_of_ne_empty
   cap_toNat_eq_of_beq encodeVarint_epochDirection_tag_eq_proto epochDirectionCtrBytes
   epochDirectionCtrBytes_len_of_ne_zero epochDirectionElemsAt epochDirectionHeaderBytes
   epochDirectionHeaderBytes_len_bounds epochDirectionNextBytes
   epochDirectionNextBytes_len_of_ne_empty epochDirectionSavedFrame lt_cap_toNat_of_beq_false
   reserveCap_one_bounds withAuthEncodeCSPlaced zext64_orr_1_32 zext64_trunc32_orr_1
   zext64_trunc32_orr_100000001)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget (encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (VecU8EncodeEnv VecU8ReserveChain)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
  (step_ed_do_reserve2_call_placed step_ed_encode_varint_det_call_placed
   step_ed_memcpy_call_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirectionBasePlacedBudget
  (step_epochDir_len_placed step_epochDir_prologue_placed
   step_epochDir_push_ctr_tag_placed step_epochDir_push_next_tag_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1PlacedBudgetAux
  (fitsEvents_and_step_of_chain fitsEvents_encodeVarint_of_env sepWP_done_tpidr_placed
   sepWPp_of_sepWP_cs_placed_vm vecU8ReserveChain_doReserve vecU8ReserveChain_encodeVarint)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem bv_pc_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_omega
private theorem bv_bl_target (a b k : BitVec 64) : a + k + (b - a - k) = b := by bv_omega
private theorem lsmpl_base_451 [LibsignalPlacement] : lsmpl.base 451 = (blkPl_451).base := rfl
private theorem lsmpl_base_460 [LibsignalPlacement] : lsmpl.base 460 = (blkPl_460).base := rfl
private theorem lsmpl_rho_memcpy [LibsignalPlacement] : lsmpl.ρ "memcpy" = lsρ lsMemcpySym := rfl
private theorem blkPl_457_memcpy [LibsignalPlacement] :
    (blkPl_457).ρ "memcpy" = lsρ lsMemcpySym := rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit bv_pc_add_sub_cancel bv_bl_target BitVec.toNat_zero
  blkPl_457_ρ lsmpl_base_451 lsmpl_base_460 lsmpl_rho_memcpy blkPl_457_memcpy
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero ule_zero_64 ult_zero_64
  ule_self_64 ult_self_64 zext64_trunc32_orr_1 zext64_trunc32_orr_100000001 zext64_orr_1_32

/-! ## Block `457` Budget-Threaded Step Lemmas (`+0 .. +328`) -/

/-- Step 1 for `encode<EpochDirection> [local#3]` (`+0 .. +172`, Block `457`). -/
theorem step_hdr_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_457 H) (blkPl_451).base
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (tag : BitVec 32) (v cap0 ptr0 dirA nextPtr prevPtr sp : BitVec 64)
    (bs0 : List (BitVec 8)) (d : EpochDirectionPB) (st0 : M.σ) (finalLen : Nat)
    (hnext_lt : d.next.length < 2 ^ 63) (hprev_lt : d.prev.length < 2 ^ 63)
    (hlen_fit : epochDirectionPBEncodedLen d < 2 ^ 64)
    (hfit : bs0.length + (epochDirectionHeaderBytes tag d).length ≤ cap0.toNat ∨
      bs0.length + (epochDirectionHeaderBytes tag d).length + 10 < 2 ^ 62)
    (hle_fin : bs0.length + (epochDirectionHeaderBytes tag d).length ≤ finalLen)
    (hEnv0 : FitsEnv M lim st0 (VecU8EncodeEnv cap0.toNat finalLen))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = tag) (hx1 : s.readReg64 .x1 = dirA) (hx2 : s.readReg64 .x2 = v)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (vecU8At A.repAlloc v cap0 ptr0 bs0 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool lim st0 s ∗ stackAt sp (authEncodeStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_457).base + 172#64 → sm.status = .Running → sm.sp = sp - 64#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x21 = dirA →
      sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = d.ctr.zeroExtend 64 → AuthEncodeCalleeSavedPlaced s0 sm →
      cap0.toNat ≤ cap1.toNat →
      (bs0.length + (epochDirectionHeaderBytes tag d).length ≤ cap0.toNat →
        cap1 = cap0 ∧ ptr1 = ptr0) →
      VecU8ReserveChain cap0.toNat cap1.toNat finalLen evs →
      FitsEnv M lim (M.stepEvents evs st0) (VecU8EncodeEnv cap1.toNat finalLen) →
      SepWPp (lsProg_457 H) ret sm
        ((vecU8At A.repAlloc v cap1 ptr1 (bs0 ++ epochDirectionHeaderBytes tag d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗
          A.pool lim (M.stepEvents evs st0) sm ∗ stackAt (sp - 64#64) (48 + resStack) ∗
          epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
            (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  have hhdr_bds := epochDirectionHeaderBytes_len_bounds tag d
  let S := epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
    (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
  refine step_epochDir_prologue_placed hres H tag dirA v sp
    (F := vecU8At A.repAlloc v cap0 ptr0 bs0 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool lim st0 s ∗ F)
    hhs0 hpc hrun hsp halign htr hw0 hx1 hx2 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx21_1 hcs1 hvmp01
  rw [← A.pool_of_vmPreserved hvmp01]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1 hinv1
    rw [← A.pool_of_vmPreserved hvmp1]
    let tagVal := (((tag <<< 3) ||| (WireType.lengthDelimited).toU32).zeroExtend 64)
    have htag_eq : encodeVarint tagVal = encodeKey tag .lengthDelimited :=
      encodeVarint_epochDirection_tag_eq_proto tag
    have hvarint1_fit : bs0.length + (encodeVarint tagVal).length ≤ cap0.toNat ∨
        bs0.length + 10 < 2 ^ 62 := by
      rw [htag_eq]; rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
    have hle_v1 : bs0.length + (encodeVarint tagVal).length ≤ finalLen := by
      rw [htag_eq]; omega
    refine step_ed_encode_varint_det_call_placed A lim henc tagVal
      v cap0 ptr0 sp ((blkPl_457).base + 44#64) bs0 st0 hvarint1_fit
      (fitsEvents_encodeVarint_of_env hEnv0 hle_v1)
      (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ S ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by dsimp only [tagVal]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
      (by dsimp only [S]; sep_ac_rfl) ?_
    intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge01 hpres01 hdet01
    let evs01 := encodeVarintEvents (EncodeVarintGhost.mk tagVal v cap0 ptr0 bs0)
    have hchain01 := vecU8ReserveChain_encodeVarint (v := v) (curPtr := ptr0) hle_v1 hdet01
    have hEnv01 := (fitsEvents_and_step_of_chain hEnv0 hchain01).2
    rw [htag_eq] at hpres01
    have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = dirA := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
    refine step_epochDir_len_placed H v dirA nextPtr prevPtr sp d hnext_lt hprev_lt hlen_fit
      (F := vecU8At A.repAlloc v cap01 ptr01 (bs0 ++ encodeKey tag .lengthDelimited) ∗
        A.pool lim (M.stepEvents evs01 st0) s2 ∗ stackAt (sp - 64#64) (48 + resStack) ∗ S ∗ F)
      hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hcs2 (by dsimp only [evs01]; rw [htag_eq]; sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hcs3 hvmp23
    rw [← A.pool_of_vmPreserved hvmp23]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp3 hinv3
      rw [← A.pool_of_vmPreserved hvmp3]
      let lenVal := BitVec.ofNat 64 (epochDirectionPBEncodedLen d)
      let bs01 := bs0 ++ encodeKey tag .lengthDelimited
      have hhdr_eq : bs01.length + (encodeVarint lenVal).length =
          bs0.length + (epochDirectionHeaderBytes tag d).length := by
        dsimp only [bs01, lenVal]; rw [List.length_append, hhdr_bds.1]; omega
      have hvarint2_fit : bs01.length + (encodeVarint lenVal).length ≤ cap01.toNat ∨
          bs01.length + 10 < 2 ^ 62 := by
        rw [hhdr_eq]; dsimp only [bs01]; rw [List.length_append]
        rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
      have hle_v2 : bs01.length + (encodeVarint lenVal).length ≤ finalLen := by
        rw [hhdr_eq]; exact hle_fin
      refine step_ed_encode_varint_det_call_placed A lim henc lenVal
        v cap01 ptr01 sp ((blkPl_457).base + 172#64) bs01 (M.stepEvents evs01 st0)
        hvarint2_fit (fitsEvents_encodeVarint_of_env hEnv01 hle_v2)
        (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ S ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by dsimp only [lenVal]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
          (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
        (by dsimp only [bs01]; sep_ac_rfl) ?_
      intro s4 cap1 ptr1 hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1 hdet1
      let evs12 := encodeVarintEvents (EncodeVarintGhost.mk lenVal v cap01 ptr01 bs01)
      have hchain12 := vecU8ReserveChain_encodeVarint (v := v) (curPtr := ptr01) hle_v2 hdet1
      have hEnv1 := (fitsEvents_and_step_of_chain hEnv01 hchain12).2
      rw [← M.stepEvents_append] at hEnv1
      rw [hhdr_eq] at hpres1
      have hpres_all : bs0.length + (epochDirectionHeaderBytes tag d).length ≤ cap0.toNat →
          cap1 = cap0 ∧ ptr1 = ptr0 := by
        intro hle0
        obtain ⟨hc01, hp01⟩ := hpres01 (by omega)
        obtain ⟨hc1, hp1⟩ := hpres1 (by rw [hc01]; exact hle0)
        exact ⟨hc1.trans hc01, hp1.trans hp01⟩
      refine SepWPp.weaken_pre
        (by
          dsimp only [S, bs01, lenVal, evs12]
          rw [bs0_append_epochDirectionHeaderBytes bs0 tag d, ← M.stepEvents_append]
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext s4 cap1 ptr1 (evs01 ++ evs12) hpc4 hrun4 hsp4 htr4
          (by rw [hcs34.1]; simp only [arm64_norm, *])
          (by rw [hcs34.2.1]; simp only [arm64_norm, *])
          (by rw [hcs34.2.2.1]; simp only [arm64_norm, *])
          (by rw [hcs34.2.2.2.1]; simp only [arm64_norm, *])
          (by rw [hcs34.2.2.2.2.1]; simp only [arm64_norm, *])
          hcs4 (Nat.le_trans hge01 hge1) hpres_all
          (hchain01.trans (Nat.le_refl _) hchain12) hEnv1)))

private theorem step_ctr_from_192_1_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_457 H) (blkPl_451).base
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (v curCap curPtr dirA sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (curSt : M.σ) (finalLen : Nat)
    (hctr_ne : (d.ctr == 0#32) = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (epochDirectionCtrBytes d).length ≤ curCap.toNat ∨
      bs1.length + (epochDirectionCtrBytes d).length + 10 < 2 ^ 62)
    (hle_fin : bs1.length + (epochDirectionCtrBytes d).length ≤ finalLen)
    (hEnv : FitsEnv M lim curSt (VecU8EncodeEnv curCap.toNat finalLen))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 192#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs1 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_457).base + 224#64 → sm.status = .Running → sm.sp = sp - 64#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x21 = dirA →
      sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionCtrBytes d).length ≤ curCap.toNat →
        cap2 = curCap ∧ ptr2 = curPtr) →
      VecU8ReserveChain curCap.toNat cap2.toNat finalLen evs →
      FitsEnv M lim (M.stepEvents evs curSt) (VecU8EncodeEnv cap2.toNat finalLen) →
      SepWPp (lsProg_457 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ epochDirectionCtrBytes d) ∗
          A.pool lim (M.stepEvents evs curSt) sm ∗
          stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  obtain ⟨hctr_len, _⟩ := epochDirectionCtrBytes_len_of_ne_zero d hctr_ne
  refine step_epochDir_push_ctr_tag_placed A.repAlloc H v curCap curPtr dirA sp bs1 d hlt
    (F := A.pool lim curSt s ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hvmp01
  rw [← A.pool_of_vmPreserved hvmp01]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1 hinv1
    rw [← A.pool_of_vmPreserved hvmp1]
    have hctr_eq : (bs1 ++ [0x08#8]).length + (encodeVarint (d.ctr.zeroExtend 64)).length =
        bs1.length + (epochDirectionCtrBytes d).length := by
      rw [List.length_append, List.length_singleton, hctr_len]; omega
    have hvarint_fit : (bs1 ++ [0x08#8]).length +
          (encodeVarint (d.ctr.zeroExtend 64)).length ≤ curCap.toNat ∨
        (bs1 ++ [0x08#8]).length + 10 < 2 ^ 62 := by
      rw [hctr_eq, List.length_append, List.length_singleton]
      rcases hfit with h | h; exact Or.inl h; exact Or.inr (by omega)
    have hle_v : (bs1 ++ [0x08#8]).length + (encodeVarint (d.ctr.zeroExtend 64)).length ≤
        finalLen := by rw [hctr_eq]; exact hle_fin
    refine step_ed_encode_varint_det_call_placed A lim henc
      (d.ctr.zeroExtend 64) v curCap curPtr sp ((blkPl_457).base + 224#64)
      (bs1 ++ [0x08#8]) curSt hvarint_fit (fitsEvents_encodeVarint_of_env hEnv hle_v) (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
      (by sep_ac_rfl) ?_
    intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2 hdet2
    have hchain := vecU8ReserveChain_encodeVarint (v := v) (curPtr := curPtr) hle_v hdet2
    have hEnv2 := (fitsEvents_and_step_of_chain hEnv hchain).2
    rw [hctr_eq] at hpres2
    refine SepWPp.weaken_pre
      (by rw [bs_append_epochDirectionCtrBytes_of_ne_zero bs1 d hctr_ne]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext s2 cap2 ptr2 _ hpc2 hrun2 hsp2 htr2
        (by rw [hcs12.1]; simp only [arm64_norm, *])
        (by rw [hcs12.2.1]; simp only [arm64_norm, *])
        (by rw [hcs12.2.2.1]; simp only [arm64_norm, *])
        (by rw [hcs12.2.2.2.1]; simp only [arm64_norm, *])
        hcs2 hge2 hpres2 hchain hEnv2))

/-- Step 2 for `encode<EpochDirection> [local#3]` (`+172 .. +224`, Block `457`). -/
theorem step_ctr_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_457 H) (blkPl_451).base
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_457 H) (blkPl_460).base
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (v cap1 ptr1 dirA sp : BitVec 64) (bs1 : List (BitVec 8)) (d : EpochDirectionPB)
    (curSt : M.σ) (finalLen : Nat)
    (hfit : bs1.length + (epochDirectionCtrBytes d).length ≤ cap1.toNat ∨
      bs1.length + (epochDirectionCtrBytes d).length + 10 < 2 ^ 62)
    (hle_fin : bs1.length + (epochDirectionCtrBytes d).length ≤ finalLen)
    (hEnv : FitsEnv M lim curSt (VecU8EncodeEnv cap1.toNat finalLen))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 172#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v cap1 ptr1 bs1 ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_457).base + 224#64 → sm.status = .Running → sm.sp = sp - 64#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x21 = dirA →
      sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      AuthEncodeCalleeSavedPlaced s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionCtrBytes d).length ≤ cap1.toNat →
        cap2 = cap1 ∧ ptr2 = ptr1) →
      VecU8ReserveChain cap1.toNat cap2.toNat finalLen evs →
      FitsEnv M lim (M.stepEvents evs curSt) (VecU8EncodeEnv cap2.toNat finalLen) →
      SepWPp (lsProg_457 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ epochDirectionCtrBytes d) ∗
          A.pool lim (M.stepEvents evs curSt) sm ∗
          stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  have hstep192 := step_ctr_from_192_1_placed A lim H henc
  subst hP
  cases hctr : (d.ctr == 0#32)
  · obtain ⟨hctr_len, hctr_ge2⟩ := epochDirectionCtrBytes_len_of_ne_zero d hctr
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1)
      (bs := bs1) (F := A.pool lim curSt s ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by sep_ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1, vecHeader]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_460).base)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0
        rw [← A.pool_of_vmPreserved hvmp0]
        have hcap_eq : cap1.toNat = bs1.length :=
          cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1)) hcap1
        have hfit2 : bs1.length + (epochDirectionCtrBytes d).length + 10 < 2 ^ 62 := by
          rcases hfit with h | h <;> omega
        obtain ⟨_, hbound1, _, _⟩ := reserveCap_one_bounds hcap_eq (by omega)
        have hchain_res := vecU8ReserveChain_doReserve v cap1 ptr1 bs1 1 finalLen
          (by omega) (by omega) hbound1
        obtain ⟨hfits_res, hEnv_res⟩ := fitsEvents_and_step_of_chain hEnv hchain_res
        refine step_ed_do_reserve2_call_placed hres A lim hdoReserve v cap1 ptr1 sp
          ((blkPl_457).base + 508#64) bs1 1 curSt hbound1 hfits_res (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
        intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
        let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
        let evs_res := doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs1, vecHeader]
        apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 192#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          intro hvmp1 hinv1
          rw [← A.pool_of_vmPreserved hvmp1]
          exact hstep192 v newCap1 newPtr1 dirA sp bs1 d (M.stepEvents evs_res curSt) finalLen
            hctr (by dsimp only [newCap1]; omega) (Or.inr hfit2) hle_fin hEnv_res (F := F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *])
            (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
            (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
            (fun sm cap2 ptr2 evs2 hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hcsm
                hge2 _ hchain2 hEnv2 => by
              rw [← M.stepEvents_append] at hEnv2
              exact SepWPp.weaken_pre
                (by rw [← M.stepEvents_append]; exact Entails.of_eq (by sep_ac_rfl))
                (hnext sm cap2 ptr2 (evs_res ++ evs2) hpcm hrunm hspm htrm hx19m hx20m hx21m
                  hx22m hcsm (Nat.le_trans (by dsimp only [newCap1]; omega) hge2)
                  (fun h => absurd h (by omega))
                  (hchain_res.trans (Nat.le_refl _) hchain2) hEnv2))))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat := lt_cap_toNat_of_beq_false hcap1_le hcap1_f
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 192#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0
        rw [← A.pool_of_vmPreserved hvmp0]
        exact hstep192 v cap1 ptr1 dirA sp bs1 d curSt finalLen hctr hlt1 hfit hle_fin hEnv
          (F := F) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) hnext)
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 224#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0
      refine SepWPp.weaken_pre
        (by
          rw [← A.pool_of_vmPreserved hvmp0, ← M.stepEvents_nil curSt,
            bs_append_epochDirectionCtrBytes_of_zero bs1 d hctr]
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ cap1 ptr1 [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (.nil _ _) hEnv))

private theorem step_next_from_300_1_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_457 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs2 : List (BitVec 8))
    (d : EpochDirectionPB) (curSt : M.σ)
    (hnext_ne : d.next.isEmpty = false) (hle : bs2.length + d.next.length ≤ curCap.toNat)
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 300#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = nextPtr) (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 bs2.length)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs2 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool lim curSt s) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_457).base + 328#64 → sm.status = .Running → sm.sp = sp - 64#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x21 = dirA →
      AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp (lsProg_457 H) ret sm
        ((vecU8At A.repAlloc v curCap curPtr (bs2 ++ d.next) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool lim curSt sm) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  subst hP
  have hnext_ne_nil : d.next ≠ [] := List.isEmpty_eq_false_iff.mp hnext_ne
  have hnext_pos : 0 < d.next.length := List.length_pos_of_ne_nil hnext_ne_nil
  refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := curCap) (ptr := curPtr)
    (bs := bs2) (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool lim curSt s ∗ F)
    (by sep_ac_rfl) fun _ hcap_lt hptr_ne => ?_
  rw [vecU8At_expose_slice A.repAlloc v curCap curPtr bs2 d.next.length hle hcap_lt hptr_ne
    hnext_pos, epochDirectionElemsAt]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := lsρ lsMemcpySym)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1 hinv1
    rw [← A.pool_of_vmPreserved hvmp1]
    refine step_ed_memcpy_call_placed hmemcpy (curPtr + BitVec.ofNat 64 bs2.length) nextPtr sp
      ((blkPl_457).base + 320#64) d.next
      (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.live curPtr curCap.toNat 1 ∗ (curPtr ↦ₛ bs2) ∗
        memRegion (curPtr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 d.next.length)
          (curCap.toNat - bs2.length - d.next.length) ∗
        ((dirA + 8#64) ↦₆₄ nextPtr) ∗ ((dirA + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
        ((dirA + 32#64) ↦₆₄ prevPtr) ∗ ((dirA + 40#64) ↦₆₄ BitVec.ofNat 64 d.prev.length) ∗
        (prevPtr ↦ₛ d.prev) ∗ ((dirA + 48#64) ↦₃₂ d.ctr) ∗ A.pool lim curSt _ ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
      (by sep_ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1 hvmpm
    rw [← A.pool_of_vmPreserved hvmpm]
    have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by
      rw [hcs01.2.1]; simp only [arm64_norm, *]
    have hx21_1 : s1.readReg64 .x21 = dirA := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
    have hx22_1 : s1.readReg64 .x22 = BitVec.ofNat 64 d.next.length := by
      rw [hcs01.2.2.2.1]; simp only [arm64_norm, *]
    have hx24_1 : s1.readReg64 .x24 = BitVec.ofNat 64 bs2.length := by
      rw [hcs01.2.2.2.2.2.1]; simp only [arm64_norm, *]
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 328#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp2 hinv2
      refine SepWPp.weaken_pre ?_
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2))
      rw [← A.pool_of_vmPreserved hvmp2,
        ← vecU8At_pack_slice A.repAlloc v curCap curPtr bs2 d.next hle hcap_lt hptr_ne hnext_ne_nil,
        epochDirectionElemsAt]
      exact Entails.of_eq (by sep_ac_rfl)))

private theorem step_next_from_248_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 : State}
    (henc : subroutine_ok (lsProg_457 H) (blkPl_451).base
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_457 H) (blkPl_460).base
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_457 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v curCap curPtr dirA nextPtr prevPtr sp : BitVec 64) (bs1 : List (BitVec 8))
    (d : EpochDirectionPB) (curSt : M.σ) (finalLen : Nat)
    (hnext_ne : d.next.isEmpty = false) (hlt : bs1.length < curCap.toNat)
    (hfit : bs1.length + (epochDirectionNextBytes d).length ≤ curCap.toNat ∨
      bs1.length + (epochDirectionNextBytes d).length + 10 < 2 ^ 62)
    (hle_fin : bs1.length + (epochDirectionNextBytes d).length ≤ finalLen)
    (hEnv : FitsEnv M lim curSt (VecU8EncodeEnv curCap.toNat finalLen))
    {s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 248#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs1.length) (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length) (hx21 : s.readReg64 .x21 = dirA)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length) (hx23 : s.readReg64 .x23 = nextPtr)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr bs1 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool lim curSt s ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_457).base + 328#64 → sm.status = .Running → sm.sp = sp - 64#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x21 = dirA →
      AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionNextBytes d).length ≤ curCap.toNat →
        cap2 = curCap ∧ ptr2 = curPtr) →
      VecU8ReserveChain curCap.toNat cap2.toNat finalLen evs →
      FitsEnv M lim (M.stepEvents evs curSt) (VecU8EncodeEnv cap2.toNat finalLen) →
      SepWPp (lsProg_457 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ epochDirectionNextBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗
          A.pool lim (M.stepEvents evs curSt) sm ∗
          stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  have hstep300 := step_next_from_300_1_placed A lim H hmemcpy
  have hnext_len := epochDirectionNextBytes_len_of_ne_empty d hnext_ne
  refine step_epochDir_push_next_tag_placed A.repAlloc H v curCap curPtr dirA nextPtr sp bs1 d
    hlt (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ A.pool lim curSt s ∗
      stackAt (sp - 64#64) (48 + resStack) ∗ F)
    hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hcs1 hvmp01
  rw [← A.pool_of_vmPreserved hvmp01]
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1 hinv1
    rw [← A.pool_of_vmPreserved hvmp1]
    have hvarint_fit : (bs1 ++ [0x12#8]).length +
        (encodeVarint (BitVec.ofNat 64 d.next.length)).length ≤ curCap.toNat ∨
        (bs1 ++ [0x12#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
    have hle_v : (bs1 ++ [0x12#8]).length +
        (encodeVarint (BitVec.ofNat 64 d.next.length)).length ≤ finalLen := by
      rw [List.length_append, List.length_singleton]; omega
    refine step_ed_encode_varint_det_call_placed A lim henc
      (BitVec.ofNat 64 d.next.length) v curCap curPtr sp ((blkPl_457).base + 280#64)
      (bs1 ++ [0x12#8]) curSt hvarint_fit (fitsEvents_encodeVarint_of_env hEnv hle_v)
      (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
      (by sep_ac_rfl) ?_
    intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge2 hpres2 hdet2
    let evs_v := encodeVarintEvents
      (EncodeVarintGhost.mk (BitVec.ofNat 64 d.next.length) v curCap curPtr (bs1 ++ [0x12#8]))
    have hchain_v := vecU8ReserveChain_encodeVarint (v := v) (curPtr := curPtr) hle_v hdet2
    have hEnv_v := (fitsEvents_and_step_of_chain hEnv hchain_v).2
    let bs2 := (bs1 ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 d.next.length)
    have hbs2_len : bs2.length + d.next.length = bs1.length + (epochDirectionNextBytes d).length := by
      dsimp only [bs2]; rw [List.length_append, List.length_append, List.length_singleton, hnext_len]
      omega
    have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by
      rw [hcs12.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = dirA := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 d.next.length := by
      rw [hcs12.2.2.2.1]; simp only [arm64_norm, *]
    have hx23_2 : s2.readReg64 .x23 = nextPtr := by rw [hcs12.2.2.2.2.1]; simp only [arm64_norm, *]
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap2) (ptr := ptr2)
      (bs := bs2) (F := A.pool lim (M.stepEvents evs_v curSt) s2 ∗
        stackAt (sp - 64#64) (48 + resStack) ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
      (by dsimp only [bs2, evs_v]; sep_ac_rfl) fun hle2 hcap2_lt _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap2 ptr2 bs2, vecHeader]
    have hnext_lt63 : d.next.length < 2 ^ 63 := by rcases hfit with h | h <;> omega
    by_cases hneed : cap2.toNat < bs2.length + d.next.length
    · have hfit_next : bs2.length + d.next.length < 2 ^ 62 := by rcases hfit with h | h <;> omega
      have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.next.length) = true :=
        (elem_len_ult_spare_iff hle2 hcap2_lt hnext_lt63).mpr hneed
      obtain ⟨hnot_ult, hle3, hge3, hbound_next⟩ := elem_len_after_reserve_not_ult hfit_next hneed
      have hchain_r := vecU8ReserveChain_doReserve v cap2 ptr2 bs2 d.next.length finalLen
        (by omega) (by omega) hbound_next
      obtain ⟨hfits_r, hEnv_r⟩ := fitsEvents_and_step_of_chain hEnv_v hchain_r
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_460).base)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp2 hinv2
        rw [← A.pool_of_vmPreserved hvmp2]
        refine step_ed_do_reserve2_call_placed hres A lim hdoReserve v cap2 ptr2 sp
          ((blkPl_457).base + 552#64) bs2 d.next.length (M.stepEvents evs_v curSt)
          hbound_next hfits_r (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
          (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl) ?_
        intro s3 ptr3 hpc3 hrun3 hsp3 htr3 hcs23 hcs3
        let cap3 := BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length d.next.length)
        let evs_r := doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 d.next.length)
        change (BitVec.ofNat 64 d.next.length).ule (cap3 - BitVec.ofNat 64 bs2.length) = true
          at hnot_ult
        have hx19_3 : s3.readReg64 .x19 = v := by rw [hcs23.1]; simp only [arm64_norm, *]
        have hx20_3 : s3.readReg64 .x20 = BitVec.ofNat 64 d.prev.length := by
          rw [hcs23.2.1]; simp only [arm64_norm, *]
        have hx21_3 : s3.readReg64 .x21 = dirA := by rw [hcs23.2.2.1]; simp only [arm64_norm, *]
        have hx22_3 : s3.readReg64 .x22 = BitVec.ofNat 64 d.next.length := by
          rw [hcs23.2.2.2.1]; simp only [arm64_norm, *]
        have hx23_3 : s3.readReg64 .x23 = nextPtr := by
          rw [hcs23.2.2.2.2.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v cap3 ptr3 bs2, vecHeader]
        apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 300#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          intro hvmp3 hinv3
          rw [← M.stepEvents_append] at hEnv_r
          rw [← A.pool_of_vmPreserved hvmp3, ← M.stepEvents_append]
          exact hstep300 v cap3 ptr3 dirA nextPtr prevPtr sp bs2 d
            (M.stepEvents (evs_v ++ evs_r) curSt) hnext_ne hle3
            (F := stackAt (sp - 64#64) (48 + resStack) ∗ F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcs3.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv3)
            (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
            (fun sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm =>
              SepWPp.weaken_pre
                (by
                  dsimp only [bs2]
                  rw [bs_append_epochDirectionNextBytes_of_ne_empty bs1 d hnext_ne]
                  exact Entails.of_eq (by sep_ac_rfl))
                (hnext sm cap3 ptr3 (evs_v ++ evs_r) hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
                  (Nat.le_trans hge2 hge3) (fun h => absurd h (by omega))
                  (hchain_v.trans (Nat.le_refl _) hchain_r) hEnv_r))))
    · have hle_fast : bs2.length + d.next.length ≤ cap2.toNat := by omega
      have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 d.next.length) = false :=
        Bool.eq_false_iff.mpr fun h => hneed ((elem_len_ult_spare_iff hle2 hcap2_lt hnext_lt63).mp h)
      have hpres_all : bs1.length + (epochDirectionNextBytes d).length ≤ curCap.toNat →
          cap2 = curCap ∧ ptr2 = curPtr := by
        intro hfit_cap; apply hpres2; rw [List.length_append, List.length_singleton]; omega
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 300#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp2 hinv2
        rw [← A.pool_of_vmPreserved hvmp2]
        exact hstep300 v cap2 ptr2 dirA nextPtr prevPtr sp bs2 d
          (M.stepEvents evs_v curSt) hnext_ne hle_fast
          (F := stackAt (sp - 64#64) (48 + resStack) ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv2)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
          (fun sm hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm =>
            SepWPp.weaken_pre
              (by
                dsimp only [bs2]
                rw [bs_append_epochDirectionNextBytes_of_ne_empty bs1 d hnext_ne]
                exact Entails.of_eq (by sep_ac_rfl))
              (hnext sm cap2 ptr2 evs_v hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
                hge2 hpres_all hchain_v hEnv_v))))

/-- Step 3 for `encode<EpochDirection> [local#3]` (`+224 .. +328`, Block `457`). -/
theorem step_next_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (henc : subroutine_ok (lsProg_457 H) (blkPl_451).base
      (withAuthEncodeCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_457 H) (blkPl_460).base
      (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_457 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v cap1 ptr1 dirA nextPtr prevPtr sp : BitVec 64)
    (bs1 : List (BitVec 8)) (d : EpochDirectionPB) (curSt : M.σ) (finalLen : Nat)
    (hnext_lt : d.next.length < 2 ^ 63)
    (hfit : bs1.length + (epochDirectionNextBytes d).length ≤ cap1.toNat ∨
      bs1.length + (epochDirectionNextBytes d).length + 10 < 2 ^ 62)
    (hle_fin : bs1.length + (epochDirectionNextBytes d).length ≤ finalLen)
    (hEnv : FitsEnv M lim curSt (VecU8EncodeEnv cap1.toNat finalLen))
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_457).base + 224#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v cap1 ptr1 bs1 ∗ epochDirectionElemsAt dirA nextPtr prevPtr d ∗
      A.pool lim curSt s ∗ stackAt (sp - 64#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_457).base + 328#64 → sm.status = .Running → sm.sp = sp - 64#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x21 = dirA →
      AuthEncodeCalleeSavedPlaced s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (epochDirectionNextBytes d).length ≤ cap1.toNat →
        cap2 = cap1 ∧ ptr2 = ptr1) →
      VecU8ReserveChain cap1.toNat cap2.toNat finalLen evs →
      FitsEnv M lim (M.stepEvents evs curSt) (VecU8EncodeEnv cap2.toNat finalLen) →
      SepWPp (lsProg_457 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ epochDirectionNextBytes d) ∗
          epochDirectionElemsAt dirA nextPtr prevPtr d ∗
          A.pool lim (M.stepEvents evs curSt) sm ∗
          stackAt (sp - 64#64) (48 + resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_457 H) ret s P Q Qp oom := by
  have hstep248 := step_next_from_248_1_placed hres A lim H henc hdoReserve hmemcpy
  subst hP
  have ⟨hnext_beq, _⟩ := ofNat_length_beq_zero_of_lt (bs := d.next) (by omega)
  cases hn : d.next.isEmpty
  · have hnext_len := epochDirectionNextBytes_len_of_ne_empty d hn
    refine sepWPp_extract_vecU8At_bounds (A := A.repAlloc) (v := v) (cap := cap1) (ptr := ptr1)
      (bs := bs1) (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗
        A.pool lim curSt s ∗ stackAt (sp - 64#64) (48 + resStack) ∗ F)
      (by sep_ac_rfl) fun hcap1_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v cap1 ptr1 bs1, vecHeader, epochDirectionElemsAt]
    by_cases hcap1 : cap1 == BitVec.ofNat 64 bs1.length
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_460).base)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0
        rw [← A.pool_of_vmPreserved hvmp0]
        have hcap_eq : cap1.toNat = bs1.length :=
          cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap1_le (BitVec.isLt cap1)) hcap1
        have hfit2 : bs1.length + (epochDirectionNextBytes d).length + 10 < 2 ^ 62 := by
          rcases hfit with h | h <;> omega
        obtain ⟨_, hbound1, _, _⟩ := reserveCap_one_bounds hcap_eq (by omega)
        have hchain_res := vecU8ReserveChain_doReserve v cap1 ptr1 bs1 1 finalLen
          (by omega) (by omega) hbound1
        obtain ⟨hfits_res, hEnv_res⟩ := fitsEvents_and_step_of_chain hEnv hchain_res
        refine step_ed_do_reserve2_call_placed hres A lim hdoReserve v cap1 ptr1 sp
          ((blkPl_457).base + 528#64) bs1 1 curSt hbound1 hfits_res
          (F := epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try sep_ac_rfl)
          ?_
        intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
        let newCap1 := BitVec.ofNat 64 (reserveCap cap1.toNat bs1.length 1)
        let evs_res := doReserveEvents (DoReserveCall.mk v cap1 ptr1 bs1 1)
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 bs1, vecHeader]
        apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 248#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          intro hvmp1 hinv1
          rw [← A.pool_of_vmPreserved hvmp1]
          exact hstep248 v newCap1 newPtr1 dirA nextPtr prevPtr sp bs1 d
            (M.stepEvents evs_res curSt) finalLen hn (by dsimp only [newCap1]; omega) (Or.inr hfit2)
            hle_fin hEnv_res (F := F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.1]; simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]; rw [hcs01.2.2.2.2.1]; simp only [arm64_norm, *])
            (hcs1.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
              (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv1)
            (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; try sep_ac_rfl)
            (fun sm cap2 ptr2 evs2 hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
                hge2 _ hchain2 hEnv2 => by
              rw [← M.stepEvents_append] at hEnv2
              exact SepWPp.weaken_pre
                (by rw [← M.stepEvents_append]; exact Entails.of_eq (by sep_ac_rfl))
                (hnext sm cap2 ptr2 (evs_res ++ evs2) hpcm hrunm hspm htrm hx19m hx20m hx21m hcsm
                  (Nat.le_trans (by dsimp only [newCap1]; omega) hge2) (fun h => absurd h (by omega))
                  (hchain_res.trans (Nat.le_refl _) hchain2) hEnv2))))
    · have hcap1_f : (cap1 == BitVec.ofNat 64 bs1.length) = false := Bool.eq_false_iff.mpr hcap1
      have hlt1 : bs1.length < cap1.toNat := lt_cap_toNat_of_beq_false hcap1_le hcap1_f
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 248#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0
        rw [← A.pool_of_vmPreserved hvmp0]
        exact hstep248 v cap1 ptr1 dirA nextPtr prevPtr sp bs1 d curSt finalLen hn hlt1 hfit
          hle_fin hEnv (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) halign (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader, epochDirectionElemsAt]; try sep_ac_rfl)
          hnext)
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_457).base + 328#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0
      refine SepWPp.weaken_pre
        (by
          rw [← A.pool_of_vmPreserved hvmp0, ← M.stepEvents_nil curSt,
            bs_append_epochDirectionNextBytes_of_empty bs1 d hn]
          exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ cap1 ptr1 [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
            (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv0)
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (.nil _ _) hEnv))

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EpochDirection1PlacedStepsBudget
