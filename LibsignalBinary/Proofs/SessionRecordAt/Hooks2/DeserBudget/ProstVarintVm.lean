/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean -- shake: keep
public meta import ProofLib -- shake: keep
public meta import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsW
public import LibsignalBinary.Proofs.TripleRatchet.Bytes.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Slow
import LibsignalBinary.Proofs.VarintBridge

/-!
# `VmPreserved` Contracts for `bytes` and `prost` Varint Leaves

Proves relocatable `[LibsignalPlacement]` total-correctness (`onPanic := ⌜False⌝`,
`onOom := ⌜False⌝`) contracts carrying `VmPreserved s0 sf` for heap-free leaves on valid inputs:
`bytes::bytes::static_drop` (Block `224`), `Bytes::from(Vec<u8>)` (Block `250`),
`decode_varint_slow` (Block `293`), `decode_varint_slice` (Block `76`), and `int32::merge`
(Block `8`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstVarintVm

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg LibsignalCodeLoaded
  withLsCodeLoaded withLsCl lsmpl
  blkPC_224 blkPl_224 blkPC_250 blkPl_250 blkPC_293 blkPl_293
  blkPC_76 blkPl_76 blkPC_8 blkPl_8
)
open CryptoVerification.RustHeap (RustAlloc vecU8At vecHeader)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarintAux mergeUint32)
open CryptoVerification.LibsignalTripleRatchet (
  varintSlow varintSlowAux
  bytesStaticDropSpec bytesFromVecPlacedSpec bytesPlacedAt bytesHeader bytesBoxU8Buf
  bytesPlacedVtable staticVtablePlacedAddr staticVtableSym
  promotableOddVtablePlacedAddr promotableOddVtableName
  promotableEvenVtablePlacedAddr promotableEvenVtableName
  bytesPtr bytesData bytesFromVecStack
  memRegion_32_eq_pointsTo64 stackAt_48_eq_cells getLsbD_zero_iff not_getLsbD_zero_iff
  ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.VarintBridge (
  decodeVarintAux_suffix decodeVarint_eq_varintSlow
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  DecodeVarintSlowGhost DecodeVarintSliceGhost Int32MergeGhost
  sliceCursorAt sliceCursorAfter VarintSlicePre varintSliceResultAt
  stackAt_varintSlowGen memRegion_24_cells stackAt_decodeVarintSliceGen
  stackAt_int32MergeGen memRegion_48_slice sliceOk_entails_memRegion48 stackAt_sliceGen_eq_slowGen
  vAcc1 vAcc2 vAcc3 vAcc4 vAcc5 vAcc6 vAcc7 vAcc8 vAcc9 vAcc10
  vAcc1_eq vAcc2_eq vAcc3_eq vAcc4_eq vAcc5_eq vAcc6_eq vAcc7_eq vAcc8_eq vAcc9_eq
  part0_2 part0_3 part0_4 part1_2 part1_3 part1_4
  hw_part0_eq hw_part01_eq
  varintSliceResultAt_1 varintSliceResultAt_2 varintSliceResultAt_3 varintSliceResultAt_4
  varintSliceResultAt_5 varintSliceResultAt_6 varintSliceResultAt_7 varintSliceResultAt_8
  varintSliceResultAt_9 varintSliceResultAt_10
  getLsbD_7_of_le getLsbD_7_of_gt signExtend64_getLsbD_63_of_le signExtend64_getLsbD_63_of_gt
  eq_ofNat_of_toNat_eq exists_cons_of_all_gt pointsToBytes_split_last
  ule_11_of_ge ule_11_of_lt
  ovf_byte2 ovf_byte3 ovf_byte6 ovf_byte7 ovf_byte10
  toNat_le_0x7f_iff two_le_toNat_iff byte9_ule_of_lt
  mergeUint32_ne_varint wt_beq_zero_of_varint cbz_len_cons_false mergeUint32_varint_1
  len_cons_sub_one ult_10_of_ge_11 ult_10_of_lt_11 len_ult_consumed_false bv_len_sub_consumed
)
open CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits (
  getLsbD_7_beq_of_le getLsbD_7_beq_of_gt
  signExtend64_getLsbD_63_beq_of_le signExtend64_getLsbD_63_beq_of_gt
  ovf_byte4_zext ovf_byte8_zext
)
open CryptoVerification.LibsignalTripleRatchet.Prost.X (
  decodeErrorHookStackW decodeVarintSliceStackW int32MergeStackW
)
open Proofs.libsignal.Hooks2 (subroutine_ok_withLsCodeLoaded_map')
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  withVmPreserved trapHooks sepWP_seq_vmPreserved
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget (
  sepWP_ret_vmPreserved
)

set_option maxRecDepth 2000000

private theorem vmPreserved_writeReg64_setPC {s : State} {r : Reg} {v pc' : BitVec 64} :
    VmPreserved s ((s.writeReg64 r v).setPC pc') := by
  cases s; cases r <;> exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local simp, local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

macro "wp_steps_vm_to " mid:term " as " hvm:ident : tactic =>
  `(tactic| (
    apply sepWP_seq_vmPreserved (mid := $mid)
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro $hvm:ident))

macro "wp_done_vm" : tactic =>
  `(tactic| (
    refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
      ⟨by simp only [wp_norm, arm64_norm], fun _hvm => ?_⟩
    wp_done))

macro "wp_done_vm_from " hprev:term : tactic =>
  `(tactic| (
    refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
      ⟨by simp only [wp_norm, arm64_norm], fun _hvm2 => ?_⟩
    have _hvm := ($hprev).trans _hvm2
    wp_done))

/-! ## 1. `bytes::bytes::static_drop` (Block `224`) & `Bytes::from(Vec<u8>)` (Block `250`) -/

/-- Block `224` (`bytes::bytes::static_drop`) meets `withVmPreserved bytesStaticDropSpec`. -/
theorem bytesStaticDrop_vmPreserved_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_224).rebase (blkPl_224).base H) (blkPl_224).base
      (withVmPreserved bytesStaticDropSpec) := by
  unfold withVmPreserved bytesStaticDropSpec
  wp_init x s0
  wp_steps_to_tgt_vm_s as _hvm
  wp_done

/-- Caller-block-polymorphic `withLsCl` form of `bytesStaticDrop_vmPreserved_placed_ok`. -/
theorem bytesStaticDrop_vmPreserved_placed_ok_cl [LibsignalPlacement] {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 224)
      (withLsCl lsmpl (withVmPreserved bytesStaticDropSpec)) :=
  ls_subroutine_ok_cl_of_callee (j := 224)
    (CryptoVerification.subroutine_ok_withLsCodeLoaded_of_plain
      (bytesStaticDrop_vmPreserved_placed_ok H))

set_option maxHeartbeats 1600000 in
/-- Block `250` (`<Bytes as From<Vec<u8>>>::from`) meets `withVmPreserved (bytesFromVecPlacedSpec A)`
on `cap.toNat = bs.length` (`onPanic := ⌜False⌝`, `onOom := ⌜False⌝`). -/
theorem bytesFromVec_vmPreserved_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_250).rebase (blkPl_250).base H) (blkPl_250).base
      (withVmPreserved (bytesFromVecPlacedSpec A)) := by
  unfold withVmPreserved bytesFromVecPlacedSpec vecU8At vecHeader bytesPlacedAt bytesHeader
    bytesBoxU8Buf bytesFromVecStack
  simp only [memRegion_32_eq_pointsTo64, stackAt_48_eq_cells]
  cells_unfold
  wp_init x s0
  obtain ⟨v, out, cap, ptr, bs⟩ := x
  dsimp only at *
  have hcap_eq : BitVec.ofNat 64 bs.length = cap := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ‹cap.toNat = bs.length›]
  have hif : (if cap = 0 then emp
      else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (if bs = [] then emp else A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs)) := by
    rw [‹cap.toNat = bs.length›]
    by_cases hbs : bs = []
    · subst hbs
      have hc0 : cap = 0 := by rw [← hcap_eq]; rfl
      simp [hc0]
    · have hc0 : cap ≠ 0 := by
        intro hc
        have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
        have h0 : cap.toNat = 0 := by simp [hc]
        omega
      simp only [hbs, hc0, ↓reduceIte, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  rw [hif, hcap_eq]
  by_cases hlen0 : cap = 0#64
  · have hbs_len0 : bs.length = 0 := by
      rw [← ‹cap.toNat = bs.length›, hlen0]; rfl
    subst hlen0
    wp_steps_vm_to ((blkPl_250).base + 176#64) as hvm1
    wp_step
    wp_steps_to_tgt_vm_s as hvm2
    have _hvm := hvm1.trans (vmPreserved_writeReg64_setPC.trans hvm2)
    simp only [bytesPlacedVtable, staticVtablePlacedAddr, staticVtableSym,
      hbs_len0, bytesPtr, bytesData, ite_true]
    wp_done
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hlen0
    have hbs_len_ne : bs.length ≠ 0 := by
      intro h0
      apply hlen0
      rw [← hcap_eq, h0]
    by_cases hodd : ptr.getLsbD 0 = true
    · have hodd64 : (ptr &&& 1#64) ≠ 0#64 := getLsbD_zero_iff.mp hodd
      wp_steps_vm_to ((blkPl_250).base + 204#64) as hvm1
      wp_step
      wp_steps_to_tgt_vm_s as hvm2
      have _hvm := hvm1.trans (vmPreserved_writeReg64_setPC.trans hvm2)
      simp only [bytesPlacedVtable, promotableOddVtablePlacedAddr, promotableOddVtableName,
        hbs_len_ne, hodd64, bytesPtr, bytesData, ite_false]
      wp_done
    · have hodd_f : ptr.getLsbD 0 = false := Bool.eq_false_iff.mpr hodd
      have heven : (ptr &&& 1#64) = 0#64 := not_getLsbD_zero_iff.mp hodd
      wp_steps_vm_to ((blkPl_250).base + 60#64) as hvm1
      wp_step
      wp_steps_to_tgt_vm_s as hvm2
      have _hvm := hvm1.trans (vmPreserved_writeReg64_setPC.trans hvm2)
      simp only [bytesPlacedVtable, promotableEvenVtablePlacedAddr, promotableEvenVtableName,
        hbs_len_ne, heven, bytesPtr, bytesData, ite_false, ite_true]
      wp_done

/-- Caller-block-polymorphic `withLsCl` form of `bytesFromVec_vmPreserved_placed_ok`. -/
theorem bytesFromVec_vmPreserved_placed_ok_cl [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsmpl.base 250)
      (withLsCl lsmpl (withVmPreserved (bytesFromVecPlacedSpec A))) :=
  ls_subroutine_ok_cl_of_callee (j := 250)
    (CryptoVerification.subroutine_ok_withLsCodeLoaded_of_plain
      (bytesFromVec_vmPreserved_placed_ok H))

/-! ## 2. `decode_varint_slow::<&mut &[u8]>` on `some` (Block `293`) -/

/-- Heap-pool-free total-correctness `VmPreserved` contract for `decode_varint_slow` (Block `293`)
in `varintSlow` cursor form at stack size `stackSz = 0x40 + errStack`. -/
def decodeVarintSlowSomeWithStackSpec (stackSz : Nat) :
    Spec ((BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) × BitVec 64 × Nat) where
  pre := fun ((slotA, slot, ptr, bs), v, k) s =>
    ⌜s.readReg64 .x0 = slotA ∧ bs.length < 2 ^ 64 ∧ varintSlow bs = some (v, k)⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ stackAt s.sp stackSz
  post := fun ((slotA, slot, ptr, bs), v, k) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)) ∗
      (ptr ↦ₛ bs) ∗ stackAt s0.sp stackSz

/-- Heap-pool-free total-correctness `VmPreserved` contract for `decode_varint_slow` (Block `293`)
in `decodeVarint` + `sliceCursorAt` form at `0x40 + errStack`. -/
def decodeVarintSlowSomeSpecGen (errStack : Nat) :
    Spec (DecodeVarintSlowGhost × BitVec 64 × List (BitVec 8)) where
  pre := fun (x, v, rest) s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧ decodeVarint x.bs = some (v, rest)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗ stackAt s.sp (0x40 + errStack)
  post := fun (x, v, rest) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗ stackAt s0.sp (0x40 + errStack)

/-- `decodeVarintSlowSomeSpecGen` specialized to `decodeErrorHookStackW`. -/
abbrev decodeVarintSlowSomeSpecW : Spec (DecodeVarintSlowGhost × BitVec 64 × List (BitVec 8)) :=
  decodeVarintSlowSomeSpecGen decodeErrorHookStackW

section VarintSlowSome

open CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow (
  StateAt CalleeSaved19_28 ofNat_ne_ofNat ofNat_sub_ofNat_of_le pointsToBytes_extract_at
  zeroExtend64_and_127 signExtend64_shiftLeft_63 byte9_hi_of_lt
  varintSlow_1 varintSlow_2 varintSlow_3 varintSlow_4 varintSlow_5
  varintSlow_6 varintSlow_7 varintSlow_8 varintSlow_9 varintSlow_10
  varintSlow_none_1 varintSlow_none_2 varintSlow_none_3 varintSlow_none_4 varintSlow_none_5
  varintSlow_none_6 varintSlow_none_7 varintSlow_none_8 varintSlow_none_9
  varintSlow_none_10_gt varintSlow_none_10_ovf
)

set_option maxHeartbeats 6400000 in
/-- Block `293` (`prost::encoding::varint::decode_varint_slow::<&mut &[u8]>`) meets
`decodeVarintSlowSomeWithStackSpec (0x40 + errStack)` with `onPanic := ⌜False⌝` and
`onOom := ⌜False⌝`. -/
theorem decode_varint_slow_some_withStack_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks} {errStack : Nat}
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H) (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSomeWithStackSpec (0x40 + errStack))) := by
  unfold withLsCodeLoaded decodeVarintSlowSomeWithStackSpec
  simp only [stackAt_varintSlowGen herr_stk, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init xtuple s0
  obtain ⟨⟨slotA, slot, ptr, bs⟩, v_out, k_out⟩ := xtuple
  dsimp only at *
  have h : bs.length < 2 ^ 64 := ‹_›
  have hvs : varintSlow bs = some (v_out, k_out) := ‹_›
  have hok : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s ((blkPl_293).base + bv% (52)) →
      VmPreserved s0 s →
      s.readReg64 (Reg.gpr 1#5) = v →
      SepWP ((blkPC_293).rebase (blkPl_293).base H) (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗
          stackAt (s0.sp - 64#64) errStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ R) →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v_out ∧
                    sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
                    slotA ↦₆₄ slot ∗
                    slot ↦₆₄ (ptr + BitVec.ofNat 64 k_out) ∗
                    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k_out) ∗
                    ptr ↦ₛ bs ∗
                    stackAt (s0.sp - 64#64) errStack ∗
                    memRegion (s0.sp - 56#64) 40 ∗
                    (s0.sp - 64#64) ↦₆₄ x_2 ∗
                    (s0.sp - 16#64) ↦₆₄ x_1 ∗
                    (s0.sp - 8#64) ↦₆₄ x) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
    intro s v k hsome ⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ hvm_s hx1
    have hvk : (v, k) = (v_out, k_out) := Option.some.inj (hsome.symm.trans hvs)
    rcases Prod.mk.inj hvk with ⟨rfl, rfl⟩
    wp_steps_to_tgt_vm_s as hvm_end
    have _hvm := hvm_s.trans hvm_end
    wp_done
  have hok9 : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s ((blkPl_293).base + bv% (432)) →
      VmPreserved s0 s →
      s.readReg64 (Reg.gpr 1#5) = v →
      SepWP ((blkPC_293).rebase (blkPl_293).base H) (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗
          stackAt (s0.sp - 64#64) errStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ R) →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v_out ∧
                    sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
                    slotA ↦₆₄ slot ∗
                    slot ↦₆₄ (ptr + BitVec.ofNat 64 k_out) ∗
                    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k_out) ∗
                    ptr ↦ₛ bs ∗
                    stackAt (s0.sp - 64#64) errStack ∗
                    memRegion (s0.sp - 56#64) 40 ∗
                    (s0.sp - 64#64) ↦₆₄ x_2 ∗
                    (s0.sp - 16#64) ↦₆₄ x_1 ∗
                    (s0.sp - 8#64) ↦₆₄ x) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
    intro s v k hsome ⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ hvm_s hx1
    have hvk : (v, k) = (v_out, k_out) := Option.some.inj (hsome.symm.trans hvs)
    rcases Prod.mk.inj hvk with ⟨rfl, rfl⟩
    wp_steps_to_tgt_vm_s as hvm_end
    have _hvm := hvm_s.trans hvm_end
    wp_done
  wp_steps_lscl_vm_s ((blkPl_293).base + bv% (20)) as hvm20 hinv20
  have hbs0 : bs ≠ [] := by rintro rfl; simp [varintSlow, varintSlowAux] at hvs
  obtain ⟨b0, bs1, hcons0'⟩ := List.exists_cons_of_ne_nil hbs0
  have hcons0 : ([] : List (BitVec 8)) ++ b0 :: bs1 = bs := hcons0'.symm
  clear hcons0' hbs0
  have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
    ofNat_ne_ofNat (by rw [← hcons0]; simp) h (by decide)
  have hpts0 : (ptr ↦ₛ bs) = (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ bs1) := by
    rw [← hcons0, List.nil_append, pointsToBytes_cons]
  conv => arg 4; rw [hpts0]
  wp_steps_lscl_vm_s ((blkPl_293).base + bv% (48)) as hvm48' hinv48
  have hvm48 := hvm20.trans hvm48'
  conv => arg 4; rw [← hpts0, ofNat_sub_ofNat_of_le (k := 1) (by rw [← hcons0]; simp) h]
  by_cases hb0 : b0 ≤ 0x7f#8
  · have hbit0 := getLsbD_7_of_le hb0
    wp_steps_lscl_vm_s ((blkPl_293).base + bv% (52)) as hvm52' _hinv52
    apply hok (vAcc1 b0) 1 (by rw [← hcons0]; exact varintSlow_1 b0 bs1 hb0)
      ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
      (hvm48.trans hvm52')
      (by simp only [arm64_norm, vAcc1, zeroExtend64_and_127])
  · have hbit0 := getLsbD_7_of_gt hb0
    wp_steps_lscl_vm_s ((blkPl_293).base + bv% (68)) as hvm68' hinv68
    have hvm68 := hvm48.trans hvm68'
    have hbs1 : bs1 ≠ [] := by
      rintro rfl
      have hnone : varintSlow bs = none := by rw [← hcons0]; exact varintSlow_none_1 b0 hb0
      rw [hvs] at hnone; cases hnone
    obtain ⟨b1, bs2, hcons1'⟩ := List.exists_cons_of_ne_nil hbs1
    have hcons1 : [b0] ++ b1 :: bs2 = bs := by rw [← hcons0, hcons1']; rfl
    clear hcons1' hbs1 hcons0
    have hlen_ne1 : BitVec.ofNat 64 bs.length ≠ 1#64 :=
      ofNat_ne_ofNat (by rw [← hcons1]; simp) h (by decide)
    have hpts1 := pointsToBytes_extract_at ptr bs [b0] bs2 b1 1 hcons1 rfl
    conv => arg 4; rw [hpts1]
    wp_steps_lscl_vm_s ((blkPl_293).base + bv% (136)) as hvm136' hinv136
    have hvm136 := hvm68.trans hvm136'
    conv => arg 4; rw [← hpts1, ofNat_sub_ofNat_of_le (k := 2) (by rw [← hcons1]; simp) h]
    by_cases hb1 : b1 ≤ 0x7f#8
    · have hbit1 := getLsbD_7_of_le hb1
      wp_steps_lscl_vm_s ((blkPl_293).base + bv% (52)) as hvm52' _hinv52
      apply hok (vAcc2 b0 b1) 2 (by rw [← hcons1]; exact varintSlow_2 b0 b1 bs2 hb0 hb1)
        ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
          by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
        (hvm136.trans hvm52')
        (by simp only [arm64_norm, vAcc2, vAcc1, zeroExtend64_and_127])
    · have hbit1 := getLsbD_7_of_gt hb1
      wp_steps_lscl_vm_s ((blkPl_293).base + bv% (140)) as hvm140' hinv140
      have hvm140 := hvm136.trans hvm140'
      have hbs2 : bs2 ≠ [] := by
        rintro rfl
        have hnone : varintSlow bs = none := by rw [← hcons1]; exact varintSlow_none_2 b0 b1 hb0 hb1
        rw [hvs] at hnone; cases hnone
      obtain ⟨b2, bs3, hcons2'⟩ := List.exists_cons_of_ne_nil hbs2
      have hcons2 : [b0, b1] ++ b2 :: bs3 = bs := by rw [← hcons1, hcons2']; rfl
      clear hcons2' hbs2 hcons1
      have hlen_ne2 : BitVec.ofNat 64 bs.length ≠ 2#64 :=
        ofNat_ne_ofNat (by rw [← hcons2]; simp) h (by decide)
      have hpts2 := pointsToBytes_extract_at ptr bs [b0, b1] bs3 b2 2 hcons2 rfl
      conv => arg 4; rw [hpts2]
      wp_steps_lscl_vm_s ((blkPl_293).base + bv% (172)) as hvm172' hinv172
      have hvm172 := hvm140.trans hvm172'
      conv => arg 4; rw [← hpts2, ofNat_sub_ofNat_of_le (k := 3) (by rw [← hcons2]; simp) h]
      by_cases hb2 : b2 ≤ 0x7f#8
      · have hbit2 := getLsbD_7_of_le hb2
        wp_steps_lscl_vm_s ((blkPl_293).base + bv% (52)) as hvm52' _hinv52
        apply hok (vAcc3 b0 b1 b2) 3 (by rw [← hcons2]; exact varintSlow_3 b0 b1 b2 bs3 hb0 hb1 hb2)
          ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
            by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
          (hvm172.trans hvm52')
          (by simp only [arm64_norm, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127])
      · have hbit2 := getLsbD_7_of_gt hb2
        wp_steps_lscl_vm_s ((blkPl_293).base + bv% (176)) as hvm176' hinv176
        have hvm176 := hvm172.trans hvm176'
        have hbs3 : bs3 ≠ [] := by
          rintro rfl
          have hnone : varintSlow bs = none := by rw [← hcons2]; exact varintSlow_none_3 b0 b1 b2 hb0 hb1 hb2
          rw [hvs] at hnone; cases hnone
        obtain ⟨b3, bs4, hcons3'⟩ := List.exists_cons_of_ne_nil hbs3
        have hcons3 : [b0, b1, b2] ++ b3 :: bs4 = bs := by rw [← hcons2, hcons3']; rfl
        clear hcons3' hbs3 hcons2
        have hlen_ne3 : BitVec.ofNat 64 bs.length ≠ 3#64 :=
          ofNat_ne_ofNat (by rw [← hcons3]; simp) h (by decide)
        have hpts3 := pointsToBytes_extract_at ptr bs [b0, b1, b2] bs4 b3 3 hcons3 rfl
        conv => arg 4; rw [hpts3]
        wp_steps_lscl_vm_s ((blkPl_293).base + bv% (208)) as hvm208' hinv208
        have hvm208 := hvm176.trans hvm208'
        conv => arg 4; rw [← hpts3, ofNat_sub_ofNat_of_le (k := 4) (by rw [← hcons3]; simp) h]
        by_cases hb3 : b3 ≤ 0x7f#8
        · have hbit3 := getLsbD_7_of_le hb3
          wp_steps_lscl_vm_s ((blkPl_293).base + bv% (52)) as hvm52' _hinv52
          apply hok (vAcc4 b0 b1 b2 b3) 4 (by rw [← hcons3]; exact varintSlow_4 b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3)
            ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
              by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
            (hvm208.trans hvm52')
            (by simp only [arm64_norm, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127])
        · have hbit3 := getLsbD_7_of_gt hb3
          wp_steps_lscl_vm_s ((blkPl_293).base + bv% (212)) as hvm212' hinv212
          have hvm212 := hvm208.trans hvm212'
          have hbs4 : bs4 ≠ [] := by
            rintro rfl
            have hnone : varintSlow bs = none := by rw [← hcons3]; exact varintSlow_none_4 b0 b1 b2 b3 hb0 hb1 hb2 hb3
            rw [hvs] at hnone; cases hnone
          obtain ⟨b4, bs5, hcons4'⟩ := List.exists_cons_of_ne_nil hbs4
          have hcons4 : [b0, b1, b2, b3] ++ b4 :: bs5 = bs := by rw [← hcons3, hcons4']; rfl
          clear hcons4' hbs4 hcons3
          have hlen_ne4 : BitVec.ofNat 64 bs.length ≠ 4#64 :=
            ofNat_ne_ofNat (by rw [← hcons4]; simp) h (by decide)
          have hpts4 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3] bs5 b4 4 hcons4 rfl
          conv => arg 4; rw [hpts4]
          wp_steps_lscl_vm_s ((blkPl_293).base + bv% (244)) as hvm244' hinv244
          have hvm244 := hvm212.trans hvm244'
          conv => arg 4; rw [← hpts4, ofNat_sub_ofNat_of_le (k := 5) (by rw [← hcons4]; simp) h]
          by_cases hb4 : b4 ≤ 0x7f#8
          · have hbit4 := getLsbD_7_of_le hb4
            wp_steps_lscl_vm_s ((blkPl_293).base + bv% (52)) as hvm52' _hinv52
            apply hok (vAcc5 b0 b1 b2 b3 b4) 5 (by rw [← hcons4]; exact varintSlow_5 b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4)
              ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
              (hvm244.trans hvm52')
              (by simp only [arm64_norm, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127])
          · have hbit4 := getLsbD_7_of_gt hb4
            wp_steps_lscl_vm_s ((blkPl_293).base + bv% (248)) as hvm248' hinv248
            have hvm248 := hvm244.trans hvm248'
            have hbs5 : bs5 ≠ [] := by
              rintro rfl
              have hnone : varintSlow bs = none := by rw [← hcons4]; exact varintSlow_none_5 b0 b1 b2 b3 b4 hb0 hb1 hb2 hb3 hb4
              rw [hvs] at hnone; cases hnone
            obtain ⟨b5, bs6, hcons5'⟩ := List.exists_cons_of_ne_nil hbs5
            have hcons5 : [b0, b1, b2, b3, b4] ++ b5 :: bs6 = bs := by rw [← hcons4, hcons5']; rfl
            clear hcons5' hbs5 hcons4
            have hlen_ne5 : BitVec.ofNat 64 bs.length ≠ 5#64 :=
              ofNat_ne_ofNat (by rw [← hcons5]; simp) h (by decide)
            have hpts5 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4] bs6 b5 5 hcons5 rfl
            conv => arg 4; rw [hpts5]
            wp_steps_lscl_vm_s ((blkPl_293).base + bv% (280)) as hvm280' hinv280
            have hvm280 := hvm248.trans hvm280'
            conv => arg 4; rw [← hpts5, ofNat_sub_ofNat_of_le (k := 6) (by rw [← hcons5]; simp) h]
            by_cases hb5 : b5 ≤ 0x7f#8
            · have hbit5 := getLsbD_7_of_le hb5
              wp_steps_lscl_vm_s ((blkPl_293).base + bv% (52)) as hvm52' _hinv52
              apply hok (vAcc6 b0 b1 b2 b3 b4 b5) 6 (by rw [← hcons5]; exact varintSlow_6 b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5)
                ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                  by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                (hvm280.trans hvm52')
                (by simp only [arm64_norm, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127])
            · have hbit5 := getLsbD_7_of_gt hb5
              wp_steps_lscl_vm_s ((blkPl_293).base + bv% (284)) as hvm284' hinv284
              have hvm284 := hvm280.trans hvm284'
              have hbs6 : bs6 ≠ [] := by
                rintro rfl
                have hnone : varintSlow bs = none := by rw [← hcons5]; exact varintSlow_none_6 b0 b1 b2 b3 b4 b5 hb0 hb1 hb2 hb3 hb4 hb5
                rw [hvs] at hnone; cases hnone
              obtain ⟨b6, bs7, hcons6'⟩ := List.exists_cons_of_ne_nil hbs6
              have hcons6 : [b0, b1, b2, b3, b4, b5] ++ b6 :: bs7 = bs := by rw [← hcons5, hcons6']; rfl
              clear hcons6' hbs6 hcons5
              have hlen_ne6 : BitVec.ofNat 64 bs.length ≠ 6#64 :=
                ofNat_ne_ofNat (by rw [← hcons6]; simp) h (by decide)
              have hpts6 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5] bs7 b6 6 hcons6 rfl
              conv => arg 4; rw [hpts6]
              wp_steps_lscl_vm_s ((blkPl_293).base + bv% (316)) as hvm316' hinv316
              have hvm316 := hvm284.trans hvm316'
              conv => arg 4; rw [← hpts6, ofNat_sub_ofNat_of_le (k := 7) (by rw [← hcons6]; simp) h]
              by_cases hb6 : b6 ≤ 0x7f#8
              · have hbit6 := getLsbD_7_of_le hb6
                wp_steps_lscl_vm_s ((blkPl_293).base + bv% (52)) as hvm52' _hinv52
                apply hok (vAcc7 b0 b1 b2 b3 b4 b5 b6) 7 (by rw [← hcons6]; exact varintSlow_7 b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6)
                  ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                    by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                  (hvm316.trans hvm52')
                  (by simp only [arm64_norm, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127])
              · have hbit6 := getLsbD_7_of_gt hb6
                wp_steps_lscl_vm_s ((blkPl_293).base + bv% (320)) as hvm320' hinv320
                have hvm320 := hvm316.trans hvm320'
                have hbs7 : bs7 ≠ [] := by
                  rintro rfl
                  have hnone : varintSlow bs = none := by rw [← hcons6]; exact varintSlow_none_7 b0 b1 b2 b3 b4 b5 b6 hb0 hb1 hb2 hb3 hb4 hb5 hb6
                  rw [hvs] at hnone; cases hnone
                obtain ⟨b7, bs8, hcons7'⟩ := List.exists_cons_of_ne_nil hbs7
                have hcons7 : [b0, b1, b2, b3, b4, b5, b6] ++ b7 :: bs8 = bs := by rw [← hcons6, hcons7']; rfl
                clear hcons7' hbs7 hcons6
                have hlen_ne7 : BitVec.ofNat 64 bs.length ≠ 7#64 :=
                  ofNat_ne_ofNat (by rw [← hcons7]; simp) h (by decide)
                have hpts7 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6] bs8 b7 7 hcons7 rfl
                conv => arg 4; rw [hpts7]
                wp_steps_lscl_vm_s ((blkPl_293).base + bv% (352)) as hvm352' hinv352
                have hvm352 := hvm320.trans hvm352'
                conv => arg 4; rw [← hpts7, ofNat_sub_ofNat_of_le (k := 8) (by rw [← hcons7]; simp) h]
                by_cases hb7 : b7 ≤ 0x7f#8
                · have hbit7 := getLsbD_7_of_le hb7
                  wp_steps_lscl_vm_s ((blkPl_293).base + bv% (52)) as hvm52' _hinv52
                  apply hok (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7) 8 (by rw [← hcons7]; exact varintSlow_8 b0 b1 b2 b3 b4 b5 b6 b7 bs8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
                    ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                      by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                    (hvm352.trans hvm52')
                    (by simp only [arm64_norm, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127])
                · have hbit7 := getLsbD_7_of_gt hb7
                  wp_steps_lscl_vm_s ((blkPl_293).base + bv% (356)) as hvm356' hinv356
                  have hvm356 := hvm352.trans hvm356'
                  have hbs8 : bs8 ≠ [] := by
                    rintro rfl
                    have hnone : varintSlow bs = none := by rw [← hcons7]; exact varintSlow_none_8 b0 b1 b2 b3 b4 b5 b6 b7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
                    rw [hvs] at hnone; cases hnone
                  obtain ⟨b8, bs9, hcons8'⟩ := List.exists_cons_of_ne_nil hbs8
                  have hcons8 : [b0, b1, b2, b3, b4, b5, b6, b7] ++ b8 :: bs9 = bs := by rw [← hcons7, hcons8']; rfl
                  clear hcons8' hbs8 hcons7
                  have hlen_ne8 : BitVec.ofNat 64 bs.length ≠ 8#64 :=
                    ofNat_ne_ofNat (by rw [← hcons8]; simp) h (by decide)
                  have hpts8 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7] bs9 b8 8 hcons8 rfl
                  conv => arg 4; rw [hpts8]
                  wp_steps_lscl_vm_s ((blkPl_293).base + bv% (388)) as hvm388' hinv388
                  have hvm388 := hvm356.trans hvm388'
                  conv => arg 4; rw [← hpts8, ofNat_sub_ofNat_of_le (k := 9) (by rw [← hcons8]; simp) h]
                  by_cases hb8 : b8 ≤ 0x7f#8
                  · have hbit8 := getLsbD_7_of_le hb8
                    wp_steps_lscl_vm_s ((blkPl_293).base + bv% (52)) as hvm52' _hinv52
                    apply hok (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8) 9 (by rw [← hcons8]; exact varintSlow_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                      ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                        by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                      (hvm388.trans hvm52')
                      (by simp only [arm64_norm, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127])
                  · have hbit8 := getLsbD_7_of_gt hb8
                    wp_steps_lscl_vm_s ((blkPl_293).base + bv% (392)) as hvm392' hinv392
                    have hvm392 := hvm388.trans hvm392'
                    have hbs9 : bs9 ≠ [] := by
                      rintro rfl
                      have hnone : varintSlow bs = none := by rw [← hcons8]; exact varintSlow_none_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
                      rw [hvs] at hnone; cases hnone
                    obtain ⟨b9, bs10, hcons9'⟩ := List.exists_cons_of_ne_nil hbs9
                    have hcons9 : [b0, b1, b2, b3, b4, b5, b6, b7, b8] ++ b9 :: bs10 = bs := by rw [← hcons8, hcons9']; rfl
                    clear hcons9' hbs9 hcons8
                    have hlen_ne9 : BitVec.ofNat 64 bs.length ≠ 9#64 :=
                      ofNat_ne_ofNat (by rw [← hcons9]; simp) h (by decide)
                    have hpts9 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7, b8] bs10 b9 9 hcons9 rfl
                    conv => arg 4; rw [hpts9]
                    wp_steps_lscl_vm_s ((blkPl_293).base + bv% (416)) as hvm416' hinv416
                    have hvm416 := hvm392.trans hvm416'
                    conv => arg 4; rw [← hpts9, ofNat_sub_ofNat_of_le (k := 10) (by rw [← hcons9]; simp) h]
                    have hb9 : b9 ≤ 0x7f#8 := by
                      by_contra hgt9
                      have hnone : varintSlow bs = none := by
                        rw [← hcons9]; exact varintSlow_none_10_gt b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hgt9
                      rw [hvs] at hnone; cases hnone
                    have hbit9 := signExtend64_getLsbD_63_of_le hb9
                    wp_steps_lscl_vm_s ((blkPl_293).base + bv% (424)) as hvm424' _hinv424
                    have hvm424 := hvm416.trans hvm424'
                    have hb9_ovf : ¬ 2#8 ≤ b9 := by
                      intro hge9
                      have hnone : varintSlow bs = none := by
                        rw [← hcons9]; exact varintSlow_none_10_ovf b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hge9
                      rw [hvs] at hnone; cases hnone
                    have hovf := byte9_hi_of_lt hb9 hb9_ovf
                    wp_steps_lscl_vm_s ((blkPl_293).base + bv% (432)) as hvm432' _hinv432
                    apply hok9 (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 10
                      (by rw [← hcons9]; exact varintSlow_10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9_ovf)
                      ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                        by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                      (hvm424.trans hvm432')
                      (by simp only [arm64_norm, vAcc10, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127, signExtend64_shiftLeft_63])

end VarintSlowSome

/-- Caller-block-polymorphic `withLsCl` form of `decode_varint_slow_some_withStack_placed_ok`. -/
theorem decode_varint_slow_some_withStack_placed_ok_cl [LibsignalPlacement]
    {H : LibsignalHooks} {errStack : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok callerProg (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSomeWithStackSpec (0x40 + errStack))) :=
  ls_subroutine_ok_cl_of_callee (j := 293)
    (decode_varint_slow_some_withStack_placed_ok herr_stk)

/-- Block `293` meets `decodeVarintSlowSomeSpecGen errStack` (`decodeVarint` + `sliceCursorAt` form). -/
theorem decode_varint_slow_some_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks} {errStack : Nat}
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H) (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSomeSpecGen errStack)) := by
  refine subroutine_ok_withLsCodeLoaded_map'
    (decode_varint_slow_some_withStack_placed_ok (H := H) herr_stk)
    (fun ⟨x, v, rest⟩ R s0 hpre => ?_)
  dsimp only [decodeVarintSlowSomeSpecGen, sliceCursorAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hbs, hdec⟩, hmem⟩
  have hvs : varintSlow x.bs = some (v, x.bs.length - rest.length) := by
    rw [decodeVarint_eq_varintSlow x.bs, hdec]; rfl
  refine ⟨((x.bufRef, x.slot, x.ptr, x.bs), v, x.bs.length - rest.length), R, ?_, ?_⟩
  · dsimp only [decodeVarintSlowSomeWithStackSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, by omega, hvs⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  · intro sf hpost
    dsimp only [decodeVarintSlowSomeWithStackSpec, decodeVarintSlowSomeSpecGen, sliceCursorAfter] at hpost ⊢
    obtain ⟨k, _, _, hrest_eq⟩ := decodeVarintAux_suffix x.bs 0 0#64 v rest hdec
    have hlen_sub : x.bs.length - (x.bs.length - rest.length) = rest.length := by
      rw [hrest_eq, List.length_drop]; omega
    rw [hlen_sub] at hpost
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

/-- Caller-block-polymorphic `withLsCl` form of `decode_varint_slow_some_placed_ok`. -/
theorem decode_varint_slow_some_placed_ok_cl [LibsignalPlacement]
    {H : LibsignalHooks} {errStack : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok callerProg (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSomeSpecGen errStack)) :=
  ls_subroutine_ok_cl_of_callee (j := 293) (decode_varint_slow_some_placed_ok herr_stk)

/-! ## 3. `decode_varint_slice` on `some` (Block `76`) -/

private def dummyAlloc : RustAlloc where
  pool := emp
  live _ _ _ := emp

/-- Heap-pool-free total-correctness `VmPreserved` contract for `decode_varint_slice` (Block `76`)
on `decodeVarint x.bs = some (v, rest)` at `0x50 + errStack`. -/
def decodeVarintSliceSomeSpecGen (errStack : Nat) :
    Spec (DecodeVarintSliceGhost × BitVec 64 × List (BitVec 8)) where
  pre := fun (x, v, rest) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ptr ∧
      (s.readReg64 .x2).toNat = x.bs.length ∧ x.bs.length < 2 ^ 63 ∧
      VarintSlicePre x.bs ∧ decodeVarint x.bs = some (v, rest)⌝ ∗
      memRegion x.ret 24 ∗ (x.ptr ↦ₛ x.bs) ∗ stackAt s.sp (0x50 + errStack)
  post := fun (x, v, rest) s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (x.ret ↦₆₄ 0#64) ∗ ((x.ret + 8#64) ↦₆₄ v) ∗
      ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 (x.bs.length - rest.length)) ∗
      (x.ptr ↦ₛ x.bs) ∗ stackAt s0.sp (0x50 + errStack)

/-- `decodeVarintSliceSomeSpecGen` specialized to `decodeErrorHookStackW`. -/
abbrev decodeVarintSliceSomeSpecW :
    Spec (DecodeVarintSliceGhost × BitVec 64 × List (BitVec 8)) :=
  decodeVarintSliceSomeSpecGen decodeErrorHookStackW

private theorem varintSliceSome_eq_resultAt (A : RustAlloc) (ret v : BitVec 64)
    (bs rest : List (BitVec 8)) {Q : SepProp} (h : decodeVarint bs = some (v, rest)) :
    (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ v) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (bs.length - rest.length)) ∗ Q =
    varintSliceResultAt A ret bs (decodeVarint bs) ∗ Q := by
  rw [h]; dsimp only [varintSliceResultAt]; sep_ac_rfl

open Lean Elab Tactic Meta in
local elab "wp_ret8_bv_bits " retStx:term:max ppSpace targetVal:term : tactic => do
  let g ← getMainGoal
  g.withContext do
    let addr ← elabTerm (← `($retStx + 8#64)) none
    let rhs ← elabTerm targetVal none
    let ty ← instantiateMVars (← g.getType)
    let pExpr := ty.getArg! 3
    let some sub := pExpr.find? fun e =>
        e.isAppOfArity ``Arm64.pointsTo64 2 && e.getArg! 0 == addr
      | throwError "wp_ret8_bv_bits: no (ret + 8#64) ↦₆₄ _ found in spatial context"
    let rhsCell ← mkAppM ``Arm64.pointsTo64 #[addr, rhs]
    let cellEqTy ← mkEq sub rhsCell
    let prfMVar ← mkFreshExprMVar cellEqTy
    let gs ← getGoals
    let mut toClear : Array FVarId := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let u := decl.userName
        if u != `b0 && u != `b1 && u != `b2 && u != `b3 && u != `b4 &&
           u != `b5 && u != `b6 && u != `b7 && u != `b8 && u != `b9 &&
           u != `hb0 && u != `hb1 && u != `hb2 && u != `hb3 && u != `hb4 &&
           u != `hb5 && u != `hb6 && u != `hb7 && u != `hb8 && u != `hb9 &&
           u != `ret then
          toClear := toClear.push decl.fvarId
    let mId ← prfMVar.mvarId!.tryClearMany toClear
    setGoals [mId]
    let hb0 := mkIdent `hb0
    let hb1 := mkIdent `hb1
    let hb2 := mkIdent `hb2
    let hb3 := mkIdent `hb3
    let hb4 := mkIdent `hb4
    let hb5 := mkIdent `hb5
    let hb6 := mkIdent `hb6
    let hb7 := mkIdent `hb7
    let hb8 := mkIdent `hb8
    evalTactic (← `(tactic| (
      apply pointsTo64_congr_val
      first
      | (rw [hw_part01_eq $hb0:ident $hb1:ident $hb2:ident $hb3:ident
               $hb4:ident $hb5:ident $hb6:ident $hb7:ident]
         clear $hb0:ident $hb1:ident $hb2:ident $hb3:ident
               $hb4:ident $hb5:ident $hb6:ident $hb7:ident
         try (rw [vAcc10]; refine congrArg₂ (· ||| ·) ?_ (by clear $hb8:ident; bv_bits))
         rw [vAcc9_eq]
         bv_bits)
      | (rw [hw_part0_eq $hb0:ident $hb1:ident $hb2:ident $hb3:ident]
         clear $hb0:ident $hb1:ident $hb2:ident $hb3:ident
         simp only [vAcc8_eq, vAcc7_eq, vAcc6_eq, vAcc5_eq, part1_4, part1_3, part1_2]
         bv_bits)
      | (simp only [vAcc4_eq, vAcc3_eq, vAcc2_eq, vAcc1_eq, part0_4, part0_3, part0_2]
         bv_bits))))
    setGoals gs
    let g' ← g.assert `hret8_val cellEqTy (← instantiateMVars prfMVar)
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    let hId := mkIdent `hret8_val
    evalTactic (← `(tactic| (rw [$hId:ident]; clear $hId:ident)))

set_option maxHeartbeats 6400000 in
/-- Block `76` (`prost::encoding::varint::decode_varint_slice`) meets
`decodeVarintSliceSomeSpecGen errStack` with `onPanic := ⌜False⌝` and `onOom := ⌜False⌝`. -/
theorem decode_varint_slice_some_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks} {errStack : Nat}
    (herr : 0x50 + errStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok ((blkPC_76).rebase (blkPl_76).base H) (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSomeSpecGen errStack)) := by
  unfold withLsCodeLoaded decodeVarintSliceSomeSpecGen
  simp only [memRegion_24_cells, stackAt_decodeVarintSliceGen herr, sepExists_sepConj_left,
    sepExists_sepConj_right]
  wp_init xtuple s0
  obtain ⟨⟨ret, ptr, bs⟩, v_out, rest_out⟩ := xtuple
  dsimp only at *
  have h : VarintSlicePre bs := ‹_›
  have h_4 : bs.length < 2 ^ 63 := ‹_›
  have hsome : decodeVarint bs = some (v_out, rest_out) := ‹_›
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := by
    apply eq_ofNat_of_toNat_eq; assumption
  obtain ⟨b0, bs1, rfl⟩ := exists_cons_of_all_gt (pre := []) h (by simp) (by rintro _ ⟨⟩)
  have hnone : decodeVarint (b0 :: bs1) ≠ none := by rw [hsome]; simp
  wp_steps_lscl_vm_s ((blkPl_76).base + bv% (16)) as hvm1 hcl1
  suffices hjoin : ∀ (m : Memory),
      VmPreserved s0
        ((((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
            (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
          (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC ((blkPl_76).base + bv% (36))).setMem m) →
      LibsignalCodeLoaded lsmpl m →
      SepWP ((blkPC_76).rebase (blkPl_76).base H) (s0.readReg64 Reg.lr)
        ((((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
            (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
          (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC ((blkPl_76).base + bv% (36))).setMem m)
        (ret ↦₆₄ v_stk_6 ∗ (ret + 8#64) ↦₆₄ v_stk_5 ∗ (ret + 16#64) ↦₆₄ v_stk_4 ∗
          (ptr ↦₈ b0 ∗ (ptr + 1#64) ↦ₛ bs1) ∗
          stackAt (s0.sp - 80#64) errStack ∗ memRegion (s0.sp - 80#64) 8 ∗
          memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ v_stk_3 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗ (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ R) →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
                  ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
                    varintSliceResultAt dummyAlloc ret (b0 :: bs1) (decodeVarint (b0 :: bs1)) ∗
                    ptr ↦ₛ (b0 :: bs1) ∗
                    stackAt (s0.sp - 80#64) errStack ∗ memRegion (s0.sp - 80#64) 8 ∗
                    memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ x_3 ∗
                    (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗ (s0.sp - 8#64) ↦₆₄ x) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) by
    conv =>
      arg 5; intro sf P_f; arg 1; intro hm
      simp only [varintSliceSome_eq_resultAt dummyAlloc ret v_out (b0 :: bs1) rest_out hsome]
    by_cases h11 : 11 ≤ (b0 :: bs1).length
    · have hule11 := ule_11_of_ge h11 h_4
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps_lscl_vm_s ((blkPl_76).base + bv% (36)) as hvm2 hcl2
      exact hjoin _ (hvm1.trans hvm2) hcl2
    · rcases h with h11' | ⟨hne, hlast⟩
      · exact (h11 h11').elim
      · have hule11 := ule_11_of_lt h11 h_4
        have hbit_last := getLsbD_7_beq_of_le hlast
        conv => arg 4; rw [pointsToBytes_split_last ptr (b0 :: bs1) hne h_4]
        wp_steps_lscl_vm_s ((blkPl_76).base + bv% (32)) as hvm2 hcl2
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne h_4, pointsToBytes_cons]
        wp_steps_lscl_vm_s ((blkPl_76).base + bv% (36)) as hvm3 hcl3
        exact hjoin _ (hvm1.trans (hvm2.trans hvm3)) hcl3
  intro m hvm_join _hcl_join
  apply sepWP_ret_vmPreserved
  by_vm_steps_withSvc (
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := signExtend64_getLsbD_63_beq_of_le hb0
      rw [varintSliceResultAt_1 dummyAlloc ret b0 bs1 hb0]
      wp_steps
      wp_ret8_bv_bits ret (vAcc1 b0)
      conv => arg 4; simp only [← pointsToBytes_cons]
      wp_done_vm_from hvm_join
    · have hbit0 := signExtend64_getLsbD_63_beq_of_gt hb0
      obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) h (by simp)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps 7
      by_cases hb1 : b1 ≤ 0x7f#8
      · have hbit1 := getLsbD_7_beq_of_le hb1
        rw [varintSliceResultAt_2 dummyAlloc ret b0 b1 bs2 hb0 hb1]
        wp_steps
        wp_ret8_bv_bits ret (vAcc2 b0 b1)
        conv => arg 4; simp only [← pointsToBytes_cons]
        wp_done_vm_from hvm_join
      · have hbit1 := getLsbD_7_beq_of_gt hb1
        have hovf2 := ovf_byte2 hb0 hb1
        obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) h (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, not_false_eq_true, and_self])
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps 7
        by_cases hb2 : b2 ≤ 0x7f#8
        · have hbit2 := getLsbD_7_beq_of_le hb2
        
          rw [varintSliceResultAt_3 dummyAlloc ret b0 b1 b2 bs3 hb0 hb1 hb2]
          wp_steps
          wp_ret8_bv_bits ret (vAcc3 b0 b1 b2)
          conv => arg 4; simp only [← pointsToBytes_cons]
          wp_done_vm_from hvm_join
        · have hbit2 := getLsbD_7_beq_of_gt hb2
          have hovf3 := ovf_byte3 hb0 hb1 hb2
          obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) h (by simp)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              hb0, hb1, hb2, not_false_eq_true, and_self])
          conv => arg 4; rw [pointsToBytes_cons]
          wp_steps 7
          by_cases hb3 : b3 ≤ 0x7f#8
          · have hbit3 := getLsbD_7_beq_of_le hb3
            rw [varintSliceResultAt_4 dummyAlloc ret b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3]
            wp_steps
            wp_ret8_bv_bits ret (vAcc4 b0 b1 b2 b3)
            conv => arg 4; simp only [← pointsToBytes_cons]
            wp_done_vm_from hvm_join
          · have hbit3 := getLsbD_7_beq_of_gt hb3
            have hovf4 := ovf_byte4_zext hb0 hb1 hb2 hb3
            obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) h (by simp)
              (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps 7
            by_cases hb4 : b4 ≤ 0x7f#8
            · have hbit4 := getLsbD_7_beq_of_le hb4
              rw [varintSliceResultAt_5 dummyAlloc ret b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4]
              wp_steps
              wp_ret8_bv_bits ret (vAcc5 b0 b1 b2 b3 b4)
              conv => arg 4; simp only [← pointsToBytes_cons]
              wp_done_vm_from hvm_join
            · have hbit4 := getLsbD_7_beq_of_gt hb4
              obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) h (by simp)
                (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                  hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
              conv => arg 4; rw [pointsToBytes_cons]
              wp_steps 5
              by_cases hb5 : b5 ≤ 0x7f#8
              · have hbit5 := getLsbD_7_beq_of_le hb5
                rw [varintSliceResultAt_6 dummyAlloc ret b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5]
                wp_steps
                wp_ret8_bv_bits ret (vAcc6 b0 b1 b2 b3 b4 b5)
                conv => arg 4; simp only [← pointsToBytes_cons]
                wp_done_vm_from hvm_join
              · have hbit5 := getLsbD_7_beq_of_gt hb5
                have hovf6 := ovf_byte6 hb4 hb5
                obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) h
                  (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                    forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
                    and_self])
                conv => arg 4; rw [pointsToBytes_cons]
                wp_steps 7
                by_cases hb6 : b6 ≤ 0x7f#8
                · have hbit6 := getLsbD_7_beq_of_le hb6
                  rw [varintSliceResultAt_7 dummyAlloc ret b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6]
                  wp_steps
                  wp_ret8_bv_bits ret (vAcc7 b0 b1 b2 b3 b4 b5 b6)
                  conv => arg 4; simp only [← pointsToBytes_cons]
                  wp_done_vm_from hvm_join
                · have hbit6 := getLsbD_7_beq_of_gt hb6
                  have hovf7 := ovf_byte7 hb4 hb5 hb6
                  obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
                    (pre := [b0, b1, b2, b3, b4, b5, b6]) h (by simp)
                    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                      forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
                  conv => arg 4; rw [pointsToBytes_cons]
                  wp_steps 7
                  by_cases hb7 : b7 ≤ 0x7f#8
                  · have hbit7 := getLsbD_7_beq_of_le hb7
                    rw [varintSliceResultAt_8 dummyAlloc ret b0 b1 b2 b3 b4 b5 b6 b7 bs8
                      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
                    wp_steps
                    wp_ret8_bv_bits ret (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7)
                    conv => arg 4; simp only [← pointsToBytes_cons]
                    wp_done_vm_from hvm_join
                  · have hbit7 := getLsbD_7_beq_of_gt hb7
                    have hovf8 := ovf_byte8_zext hb4 hb5 hb6 hb7
                    obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
                      (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) h (by simp)
                      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                        forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
                        and_self])
                    conv => arg 4; rw [pointsToBytes_cons]
                    wp_steps 7
                    by_cases hb8 : b8 ≤ 0x7f#8
                    · have hbit8 := signExtend64_getLsbD_63_beq_of_le hb8
                      rw [varintSliceResultAt_9 dummyAlloc ret b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done_vm_from hvm_join
                    · have hbit8 := signExtend64_getLsbD_63_beq_of_gt hb8
                      obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
                        (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) h (by simp)
                        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                          forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, not_false_eq_true,
                          and_self])
                      have hb9 : ¬ 2#8 ≤ b9 := by
                        intro hge
                        apply hnone
                        rw [decodeVarint]; iterate 10 rw [decodeVarintAux]
                        by_cases hb9_le : b9 ≤ 0x7f#8 <;>
                          simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5,
                            hb6, hb7, hb8, hb9_le, hge]
                      have hb9_ule := byte9_ule_of_lt hb9
                      have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                      conv => arg 4; rw [pointsToBytes_cons]
                      rw [varintSliceResultAt_10 dummyAlloc ret b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done_vm_from hvm_join)

/-- Caller-block-polymorphic `withLsCl` form of `decode_varint_slice_some_placed_ok`. -/
theorem decode_varint_slice_some_placed_ok_cl [LibsignalPlacement]
    {H : LibsignalHooks} {errStack : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (herr : 0x50 + errStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok callerProg (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSomeSpecGen errStack)) :=
  ls_subroutine_ok_cl_of_callee (j := 76) (decode_varint_slice_some_placed_ok herr)

/-! ## 4. `prost::encoding::int32::merge::<&mut &[u8]>` on `some` (Block `8`) -/

/-- Heap-pool-free total-correctness `VmPreserved` contract for `int32::merge` (Block `8`)
on `mergeUint32 x.wt x.bs = some (v, rest)` at `0x50 + (0x50 + errStack)`. -/
def int32MergeSomeSpecGen (errStack : Nat) :
    Spec (Int32MergeGhost × BitVec 32 × List (BitVec 8)) where
  pre := fun (x, v, rest) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧ mergeUint32 x.wt x.bs = some (v, rest)⌝ ∗
      memRegion x.valPtr 4 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      stackAt s.sp (0x50 + (0x50 + errStack))
  post := fun (x, v, rest) s0 sf =>
    ⌜sf.readReg64 .x0 = 0#64 ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (x.valPtr ↦₃₂ v) ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
      stackAt s0.sp (0x50 + (0x50 + errStack))

/-- `int32MergeSomeSpecGen` specialized to `decodeErrorHookStackW` (`int32MergeStackW`). -/
abbrev int32MergeSomeSpecW : Spec (Int32MergeGhost × BitVec 32 × List (BitVec 8)) :=
  int32MergeSomeSpecGen decodeErrorHookStackW

set_option maxHeartbeats 1600000 in
/-- Block `8` (`prost::encoding::int32::merge::<&mut &[u8]>`) meets
`int32MergeSomeSpecGen errStack` with `onPanic := ⌜False⌝` and `onOom := ⌜False⌝`. -/
theorem int32_merge_some_placed_ok [LibsignalPlacement]
    {H : LibsignalHooks} {errStack : Nat}
    (herr : 0x50 + (0x50 + errStack) ≤ 2 ^ 64 := by decide) :
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H) (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSomeSpecGen errStack)) := by
  have herrSlice : 0x50 + errStack ≤ 2 ^ 64 := by omega
  have herrSlow : 0x40 + errStack ≤ 2 ^ 64 := by omega
  unfold withLsCodeLoaded int32MergeSomeSpecGen
  simp only [sliceCursorAt, stackAt_int32MergeGen herr, sepExists_sepConj_left,
    sepExists_sepConj_right]
  wp_init xtuple s0
  obtain ⟨⟨wt, valPtr, bufRef, slot, ptr, bs⟩, v_out, rest_out⟩ := xtuple
  dsimp only at *
  have hSlice_cl := decode_varint_slice_some_placed_ok_cl
    (callerProg := (blkPC_8).rebase (blkPl_8).base H) herrSlice
  have hSlow_cl := decode_varint_slow_some_placed_ok_cl
    (callerProg := (blkPC_8).rebase (blkPl_8).base H) herrSlow
  have h_1 : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 wt.toNat := ‹_›
  have h : bs.length < 2 ^ 63 := ‹_›
  have hm : mergeUint32 wt bs = some (v_out, rest_out) := ‹_›
  have hwt : wt = .varint := by
    by_contra hne
    rw [mergeUint32_ne_varint bs hne] at hm
    cases hm
  subst hwt
  have hwt_br := wt_beq_zero_of_varint h_1
  cases bs with
  | nil =>
    simp [mergeUint32, decodeVarint, decodeVarintAux] at hm
  | cons b0 bs1 =>
    have hcbz := cbz_len_cons_false h
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := signExtend64_getLsbD_63_of_le hb0
      rw [mergeUint32_varint_1 bs1 hb0] at hm
      injection hm with hm_eq
      rcases Prod.mk.inj hm_eq with ⟨rfl, rfl⟩
      conv => arg 4; rw [pointsToBytes_cons, ProofLib.memRegion_four valPtr]
      simp only [sepExists_sepConj_left]
      apply SepWP.exists_elim; intro v_val
      apply sepWP_ret_vmPreserved
      by_vm_steps_withSvc (
        wp_steps
        conv => arg 4; rw [len_cons_sub_one b0 bs1, ← pointsToBytes_cons]
        simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left]
        wp_done_vm)
    · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
      have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      obtain ⟨v64, hd⟩ : ∃ v64 : BitVec 64,
          decodeVarint (b0 :: bs1) = some (v64, rest_out) ∧ v_out = v64.setWidth 32 := by
        cases hdec : decodeVarint (b0 :: bs1) with
        | none => simp [mergeUint32, hdec] at hm
        | some p =>
          rcases p with ⟨v64, rest'⟩
          simp [mergeUint32, hdec] at hm
          exact ⟨v64, by rw [hm.2], hm.1.symm⟩
      rcases hd with ⟨hd, rfl⟩
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps_lscl_vm_s ((blkPl_8).base + bv% (144)) as hvm1 hcl1
      by_cases h11 : 11 ≤ (b0 :: bs1).length
      · have hhi := ult_10_of_ge_11 h11 h
        have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
        conv => arg 4; rw [memRegion_48_slice s0.sp]
        wp_steps_lscl_vm_s (lsmpl.base 76) as hvm2 hcl2
        have hSlice_call := lscall_of_withLsCl hSlice_cl hcl2
        wp_call hSlice_call (⟨s0.sp - 80#64, ptr, b0 :: bs1⟩, v64, rest_out)
        have hcc := len_ult_consumed_false (rest := rest_out) h
        have hsub_len := bv_len_sub_consumed hd
        conv => arg 4; rw [ProofLib.memRegion_four valPtr]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sliceCursorAfter]
        apply SepWP.exists_elim; intro v_val
        wp_steps_to_tgt_vm_s as hvm3
        have _hvm := hvm1.trans (hvm2.trans (‹VmPreserved _ _›.trans hvm3))
        apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v64
          (BitVec.ofNat 64 ((b0 :: bs1).length - rest_out.length))) (by sep_focus)
        wp_done
      · have hhi := ult_10_of_lt_11 h11 h
        have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        conv => arg 4; rw [← pointsToBytes_cons, pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        wp_steps_lscl_vm_s ((blkPl_8).base + bv% (156)) as hvm2 hcl2
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
        by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
        · have hbit_last := getLsbD_7_of_le hlast
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
          conv => arg 4; rw [pointsToBytes_cons, memRegion_48_slice s0.sp]
          wp_steps_lscl_vm_s (lsmpl.base 76) as hvm3 hcl3
          have hSlice_call := lscall_of_withLsCl hSlice_cl hcl3
          wp_call hSlice_call (⟨s0.sp - 80#64, ptr, b0 :: bs1⟩, v64, rest_out)
          have hcc := len_ult_consumed_false (rest := rest_out) h
          have hsub_len := bv_len_sub_consumed hd
          conv => arg 4; rw [ProofLib.memRegion_four valPtr]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sliceCursorAfter]
          apply SepWP.exists_elim; intro v_val
          wp_steps_to_tgt_vm_s as hvm4
          have _hvm := hvm1.trans (hvm2.trans (hvm3.trans (‹VmPreserved _ _›.trans hvm4)))
          apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v64
            (BitVec.ofNat 64 ((b0 :: bs1).length - rest_out.length))) (by sep_focus)
          wp_done
        · have hbit_last := getLsbD_7_of_gt hlast
          wp_steps_lscl_vm_s (lsmpl.base 293) as hvm3 hcl3
          conv => arg 4; rw [stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)]
          apply SepWP.fold (show (slot ↦₆₄ ptr) ∗
              ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: bs1).length) ∗
              (ptr ↦ₛ (b0 :: bs1)) ⊢
              sliceCursorAt slot ptr (b0 :: bs1) from by
            unfold sliceCursorAt; exact Entails.of_eq (by sep_ac_rfl))
            (by sep_focus)
          have hSlow_call := lscall_of_withLsCl hSlow_cl hcl3
          wp_call hSlow_call (⟨bufRef, slot, ptr, b0 :: bs1⟩, v64, rest_out)
          apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)).symm)
            (by sep_focus)
          conv => arg 4; rw [ProofLib.memRegion_four valPtr]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro v_val
          wp_steps_to_tgt_vm_s as hvm4
          have _hvm := hvm1.trans (hvm2.trans (hvm3.trans (‹VmPreserved _ _›.trans hvm4)))
          wp_done

/-- Caller-block-polymorphic `withLsCl` form of `int32_merge_some_placed_ok`. -/
theorem int32_merge_some_placed_ok_cl [LibsignalPlacement]
    {H : LibsignalHooks} {errStack : Nat}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (herr : 0x50 + (0x50 + errStack) ≤ 2 ^ 64 := by decide) :
    subroutine_ok callerProg (lsmpl.base 8)
      (withLsCl lsmpl (int32MergeSomeSpecGen errStack)) :=
  ls_subroutine_ok_cl_of_callee (j := 8) (int32_merge_some_placed_ok herr)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstVarintVm
