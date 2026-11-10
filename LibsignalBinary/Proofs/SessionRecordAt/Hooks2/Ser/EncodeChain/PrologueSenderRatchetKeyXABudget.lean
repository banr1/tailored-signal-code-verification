/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Base
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXA
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `encode::<Chain, Vec<u8>>` Segments 0 and 1 (`+0` → `+176`)

Verifies relocatable Segment 0 (prologue, outer tag, `Chain::encoded_len`, and length varint,
`+0 → +68`) and Segment 1 (`sender_ratchet_key`, `+68 → +176`, cold `1676..1744`) in Block `12`
under `RustCliAllocBudget M` and `EncRawSegEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXABudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded
  ls_subroutine_ok_of_block lsρ lsMemcpySym
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalProtoCodec (encodeKey encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  EncodeVarintGhost vecU8Buf encodeVarint_length_bounds
  vecU8Buf_eq_open_one vecU8Buf_snoc_eq
  cap_beq_len_false cap_eq_ofNat_len bv_len_add_one
)
open CryptoVerification.E2E.Record (lenField bytesField)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_88 lsProg_88)
open CryptoVerification.E2E.Record.Serialization (
  ChainLenGhost chainLenStack EncodeChainGhost encChainMem protoChainAt
  stackAt_encodeChainStackX_split
  encChainSubStackX encChainSubRestX stackAt_sub_to_chainLenX
  encChainSavedRegs sp_sub_96_aligned trVRegs_of_call trVRegs_trans
  bv_add_neg96 encChain_tag_orr_eq encChain_encodeKey_eq encChain_encodeKey_len
  encChainMem_len_lt bytesField_nonempty_eq bv_ofNat_beq_zero_false
  vecU8At_eq_cells_buf vecU8Buf_eq_open_bytes vecReadRest bv_len_add_slice
  spare_ult_iff ule_of_ult_false
)
open Proofs.libsignal.Hooks2 (
  SepWPpLsCl sepWPpLsCl_extract_vecU8Buf_bounds
)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  chainLenSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget (
  EncRawSegEnv encRawSegEnv_nil encRawSegEnv_append
  fitsEnv_encRawSeg_left fitsEnv_encRawSeg_right
  fitsEnv_doReserve_of_encRawSeg fitsEnv_encodeVarint_of_encRawSeg
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeChainStackX SerContractsXPlaced encodeChainSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  EncodeVarintPlacedOkX DoReservePlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_of_sepWP_vm sepWPpLsCl_call_lscl_noPanic
  fitsEnv_encRawSeg_of_encodeChainEnv encRawSegEnv_doReserve encRawSegEnv_of_encodeVarintEnv
  step_encChain_encodeVarint_placed_x step_encChain_reserve1_placed_x
  step_encChain_reserveSlice_placed_x step_encChain_memcpy_placed_x
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_add_neg96

/-- Step a `bl <Chain as Message>::encoded_len` (`lsmpl.base 88`) call inside `encode::<Chain>`,
    transporting `A.pool lim st s` to `A.pool lim st sm` across `VmPreserved`. -/
theorem step_encChain_chainLen_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A.repAlloc)))
    (sp0 ret_pc : BitVec 64) (st : M.σ)
    {x : EncodeChainGhost}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 88)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = x.a)
    (hlen : (encChainMem x.gc).length < 2 ^ 32)
    (hP : P = (protoChainAt A.repAlloc x.gc x.a ∗ A.pool lim st s ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State),
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encChainMem x.gc).length →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((protoChainAt A.repAlloc x.gc x.a ∗ A.pool lim st sm ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  have hchain' : subroutine_ok (lsProg_12 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A.repAlloc)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hchain
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPpLsCl_call_lscl_noPanic (x := ChainLenGhost.mk x.a x.gc)
    (F := A.pool lim st s ∗ encChainSubRestX (sp0 - 96#64) chainLenStack ∗ F)
    hchain' hpc hrun hsp_aligned hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_chainLenX (sp0 - 96#64)] at hm
    simp only [chainLenSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [chainLenSpec, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨hx0m, htrm, hvm⟩ => ?_
    have hGoalEq :
        (protoChainAt A.repAlloc x.gc x.a ∗ stackAt (sp0 - 96#64) chainLenStack ∗
          A.pool lim st s ∗ encChainSubRestX (sp0 - 96#64) chainLenStack ∗ F) =
        ((protoChainAt A.repAlloc x.gc x.a ∗ A.pool lim st sm ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [stackAt_sub_to_chainLenX (sp0 - 96#64), ← A.pool_of_vmPreserved hvm]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm hvm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m

theorem step_encChain_prologue_placed_x [LibsignalPlacement]
    (H : LibsignalHooks)
    (tag : Nat) (a v sp0 w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : BitVec 64)
    (htag : tag = 6 ∨ tag = 7)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
      ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
      ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
      ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
      ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = lsmpl.base 10 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (blkPl_12).base + 52#64 →
      sm.readReg64 .x0 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm (encChainSavedRegs sp0 s ∗ F) Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have horr := encChain_tag_orr_eq htag
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
  have hSavedEq :
      (((sp0 - 96#64) ↦₆₄ s.readReg64 (Reg.gpr 29#5)) ∗
        ((sp0 - 88#64) ↦₆₄ s.readReg64 (Reg.gpr 30#5)) ∗
        ((sp0 - 80#64) ↦₆₄ s.readReg64 (Reg.gpr 28#5)) ∗
        ((sp0 - 72#64) ↦₆₄ s.readReg64 (Reg.gpr 27#5)) ∗
        ((sp0 - 64#64) ↦₆₄ s.readReg64 (Reg.gpr 26#5)) ∗
        ((sp0 - 56#64) ↦₆₄ s.readReg64 (Reg.gpr 25#5)) ∗
        ((sp0 - 48#64) ↦₆₄ s.readReg64 (Reg.gpr 24#5)) ∗
        ((sp0 - 40#64) ↦₆₄ s.readReg64 (Reg.gpr 23#5)) ∗
        ((sp0 - 32#64) ↦₆₄ s.readReg64 (Reg.gpr 22#5)) ∗
        ((sp0 - 24#64) ↦₆₄ s.readReg64 (Reg.gpr 21#5)) ∗
        ((sp0 - 16#64) ↦₆₄ s.readReg64 (Reg.gpr 20#5)) ∗
        ((sp0 - 8#64) ↦₆₄ s.readReg64 (Reg.gpr 19#5))) ∗ F =
      encChainSavedRegs sp0 s ∗ F := rfl
  rw [hSavedEq]
  exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by rcases htag with rfl | rfl <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])

theorem step_encChain_to_chainLen_placed_x [LibsignalPlacement]
    (H : LibsignalHooks) (a v : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 52#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = lsmpl.base 88 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (blkPl_12).base + 60#64 →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm P Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 88)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
  exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_to_lenVarint_placed_x [LibsignalPlacement]
    (H : LibsignalHooks) (a v lenVal : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 60#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = lenVal)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = lsmpl.base 10 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (blkPl_12).base + 68#64 →
      sm.readReg64 .x0 = lenVal →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm P Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
  by_vm_steps
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
  exact hnext _ hvm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])

/-- Combined Segment 0 (`+0 → +68`) parameterized directly by `EncRawSegEnv` on the header prefix
    `encodeKey x.tag .lengthDelimited ++ encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)`. -/
theorem step_encChain_seg0_raw_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A.repAlloc)))
    (x : EncodeChainGhost) (st : M.σ)
    (htag : x.tag = 6 ∨ x.tag = 7)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv x.bs.length
        (encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length))
    {ret : BitVec 64} {s0 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_12).base)
    (hrun : s0.status = .Running)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = BitVec.ofNat 64 x.tag)
    (hx1 : s0.readReg64 .x1 = x.a)
    (hx2 : s0.readReg64 .x2 = x.v)
    (hP : P = (protoChainAt A.repAlloc x.gc x.a ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s0 ∗ stackAt s0.sp encodeChainStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 68#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = x.v →
      sm.readReg64 .x20 = x.a →
      EncRawSegEnv x.bs.length
        (encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc x.v cap1 ptr1
          (x.bs ++ encodeKey x.tag .lengthDelimited ++
            encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
          protoChainAt A.repAlloc x.gc x.a ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (s0.sp - 96#64) encChainSubStackX ∗
          encChainSavedRegs s0.sp s0) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s0 P Q Qp := by
  subst hP
  have hkey_eq := encChain_encodeKey_eq htag
  have hkey_len := encChain_encodeKey_len htag
  have hev_tag_len : (encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))).length = 1 := by
    rw [hkey_eq]; exact hkey_len
  have hhdr_len :
      (encodeKey x.tag .lengthDelimited ++
        encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length =
      1 + (encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length := by
    rw [List.length_append, hkey_len]
  have ⟨_, hvar_le⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 (encChainMem x.gc).length)
  have hfit12 : FitsEnv M lim st
      (EncRawSegEnv x.bs.length
        (1 + (encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length)) := by
    rw [← hhdr_len]; exact hfit
  rw [stackAt_encodeChainStackX_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPpLsCl.exists_elim fun w96 => SepWPpLsCl.exists_elim fun w88 =>
    SepWPpLsCl.exists_elim fun w80 => SepWPpLsCl.exists_elim fun w72 =>
    SepWPpLsCl.exists_elim fun w64 => SepWPpLsCl.exists_elim fun w56 =>
    SepWPpLsCl.exists_elim fun w48 => SepWPpLsCl.exists_elim fun w40 =>
    SepWPpLsCl.exists_elim fun w32 => SepWPpLsCl.exists_elim fun w24 =>
    SepWPpLsCl.exists_elim fun w16 => SepWPpLsCl.exists_elim fun w8 => ?_
  refine step_encChain_prologue_placed_x H x.tag x.a x.v s0.sp
    w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 htag
    (F := protoChainAt A.repAlloc x.gc x.a ∗ vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s0 ∗ stackAt (s0.sp - 96#64) encChainSubStackX ∗ F)
    hpc hrun rfl halign hx0 hx1 hx2 (by sep_ac_rfl) ?_
  intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx19_1 hx20_1
  rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
  have hfit_ev1 := fitsEnv_encodeVarint_of_encRawSeg
    (x := EncodeVarintGhost.mk (BitVec.ofNat 64 (x.tag * 8 + 2)) x.v x.cap x.ptr x.bs)
    (by dsimp; omega) (by dsimp; omega)
    (by simp only [lenField, List.length_append] at hlen; omega)
    (fitsEnv_encRawSeg_left hfit12)
  refine step_encChain_encodeVarint_placed_x A lim H hEV
    (BitVec.ofNat 64 (x.tag * 8 + 2)) x.v x.cap x.ptr s0.sp
    ((blkPl_12).base + 52#64) x.bs st
    (by simp only [lenField, List.length_append] at hlen; omega)
    hfit_ev1
    (F := protoChainAt A.repAlloc x.gc x.a ∗ encChainSavedRegs s0.sp s0 ∗ F)
    hpc1 hrun1 hsp1 halign htr1 hlr1 hx0_1 hx1_1 (by sep_ac_rfl) ?_
  intro s2 cap0 ptr0 evs1 hpc2 hrun2 hsp2 htr2 hcs2 hevs1 _ _
  have hevs1' : EncRawSegEnv x.bs.length 1 evs1 :=
    encRawSegEnv_of_encodeVarintEnv (by dsimp; omega) (by dsimp; omega)
      (by simp only [lenField, List.length_append] at hlen; omega) hevs1
  have hfit2 := fitsEnv_encRawSeg_right hfit12 hevs1'
  have hx19_2 : s2.readReg64 .x19 = x.v := hcs2.1.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = x.a := hcs2.2.1.trans hx20_1
  refine step_encChain_to_chainLen_placed_x H x.a x.v
    hpc2 hrun2 hx19_2 hx20_2 ?_
  intro s3 hvm3 hpc3 hrun3 hsp3 htr3 hlr3 hx0_3 hx19_3 hx20_3
  rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents evs1 st) hvm3]
  refine step_encChain_chainLen_placed_x A lim H hchain s0.sp
    ((blkPl_12).base + 60#64) (M.stepEvents evs1 st)
    (x := x)
    (F := vecU8At A.repAlloc x.v cap0 ptr0 (x.bs ++ encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))) ∗
      encChainSavedRegs s0.sp s0 ∗ F)
    hpc3 hrun3 (hsp3.trans hsp2) halign (trVRegs_trans htr3 htr2) hlr3 hx0_3 (encChainMem_len_lt hlen)
    (by sep_ac_rfl) ?_
  intro s4 _ hpc4 hrun4 hsp4 htr4 hcs4 hx0_4
  have hx19_4 : s4.readReg64 .x19 = x.v := hcs4.1.trans hx19_3
  have hx20_4 : s4.readReg64 .x20 = x.a := hcs4.2.1.trans hx20_3
  rw [hkey_eq]
  refine step_encChain_to_lenVarint_placed_x H x.a x.v
    (BitVec.ofNat 64 (encChainMem x.gc).length)
    hpc4 hrun4 hx0_4 hx19_4 hx20_4 ?_
  intro s5 hvm5 hpc5 hrun5 hsp5 htr5 hlr5 hx0_5 hx1_5 hx19_5 hx20_5
  rw [← A.pool_of_vmPreserved (lim := lim) (st := M.stepEvents evs1 st) hvm5]
  have hfit_ev2 := fitsEnv_encodeVarint_of_encRawSeg
    (x := EncodeVarintGhost.mk (BitVec.ofNat 64 (encChainMem x.gc).length)
      x.v cap0 ptr0 (x.bs ++ encodeKey x.tag .lengthDelimited))
    (Nat.le_refl _)
    (by dsimp; rw [List.length_append, hkey_len])
    (by simp only [lenField, List.length_append, hkey_len] at hlen ⊢; omega)
    hfit2
  refine step_encChain_encodeVarint_placed_x A lim H hEV
    (BitVec.ofNat 64 (encChainMem x.gc).length) x.v cap0 ptr0 s0.sp
    ((blkPl_12).base + 68#64)
    (x.bs ++ encodeKey x.tag .lengthDelimited) (M.stepEvents evs1 st)
    (by simp only [lenField, List.length_append, hkey_len] at hlen ⊢; omega)
    hfit_ev2
    (F := protoChainAt A.repAlloc x.gc x.a ∗ encChainSavedRegs s0.sp s0 ∗ F)
    hpc5 hrun5 (hsp5.trans hsp4) halign (trVRegs_trans htr5 htr4) hlr5 hx0_5 hx1_5
    (by sep_ac_rfl) ?_
  intro s6 cap1 ptr1 evs2 hpc6 hrun6 hsp6 htr6 hcs6 hevs2 _ _
  have hevs2' : EncRawSegEnv (x.bs.length + 1)
      (encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length evs2 :=
    encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
      (by dsimp; rw [List.length_append, hkey_len])
      (by simp only [lenField, List.length_append, hkey_len] at hlen ⊢; omega) hevs2
  have hevs12 : EncRawSegEnv x.bs.length
      (encodeKey x.tag .lengthDelimited ++
        encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length
      (evs1 ++ evs2) := by
    rw [hhdr_len]
    exact encRawSegEnv_append hevs1' hevs2'
  have hx19_6 : s6.readReg64 .x19 = x.v := hcs6.1.trans hx19_5
  have hx20_6 : s6.readReg64 .x20 = x.a := hcs6.2.1.trans hx20_5
  rw [← M.stepEvents_append]
  have hGoalEq :
      ((vecU8At A.repAlloc x.v cap1 ptr1
        ((x.bs ++ encodeKey x.tag .lengthDelimited) ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        A.pool lim (M.stepEvents (evs1 ++ evs2) st) s6 ∗
        stackAt (s0.sp - 96#64) encChainSubStackX) ∗
        protoChainAt A.repAlloc x.gc x.a ∗ encChainSavedRegs s0.sp s0 ∗ F) =
      ((vecU8At A.repAlloc x.v cap1 ptr1
        (x.bs ++ encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        protoChainAt A.repAlloc x.gc x.a ∗
        A.pool lim (M.stepEvents (evs1 ++ evs2) st) s6 ∗
        stackAt (s0.sp - 96#64) encChainSubStackX ∗
        encChainSavedRegs s0.sp s0) ∗ F) := by sep_ac_rfl
  rw [hGoalEq]
  exact hnext s6 cap1 ptr1 (evs1 ++ evs2) hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hevs12

/-- Combined Segment 0 (`+0 → +68`) starting from `(encodeChainSpecX M A lim).pre (x, st) s0`. -/
theorem step_encChain_seg0_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A.repAlloc)))
    {x : EncodeChainGhost} {st : M.σ}
    {ret : BitVec 64} {s0 : State} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_12).base)
    (hrun : s0.status = .Running)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 68#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = x.v →
      sm.readReg64 .x20 = x.a →
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 →
      EncRawSegEnv x.bs.length
        (encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length evs →
      FitsEnv M lim (M.stepEvents evs st)
        (EncRawSegEnv
          (x.bs.length +
            (encodeKey x.tag .lengthDelimited ++
              encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length)
          (encChainMem x.gc).length) →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        (vecU8At A.repAlloc x.v cap1 ptr1
          (x.bs ++ encodeKey x.tag .lengthDelimited ++
            encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
          protoChainAt A.repAlloc x.gc x.a ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (s0.sp - 96#64) encChainSubStackX ∗
          encChainSavedRegs s0.sp s0)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s0
      ((encodeChainSpecX M A lim).pre (x, st) s0) Q Qp := by
  dsimp only [encodeChainSpecX]
  refine SepWPpLsCl.pure_elim fun ⟨hx0, hx1, hx2, htag, hlen, hfit_chain⟩ => ?_
  have hlf_len :
      (lenField x.tag (encChainMem x.gc)).length =
      (encodeKey x.tag .lengthDelimited ++
        encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length +
        (encChainMem x.gc).length := by
    simp only [lenField, List.length_append]
  have hfit_all : FitsEnv M lim st
      (EncRawSegEnv x.bs.length
        ((encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length +
          (encChainMem x.gc).length)) := by
    rw [← hlf_len]
    exact fitsEnv_encRawSeg_of_encodeChainEnv x hfit_chain
  refine step_encChain_seg0_raw_placed_x A lim H hEV hchain x st htag hlen
    (fitsEnv_encRawSeg_left hfit_all)
    (F := emp) hpc hrun halign hx0 hx1 hx2
    (by simp only [sepConj_emp]) ?_
  intro sm cap1 ptr1 evs hpcm hrunm hspm htrm hx19m hx20m hevs
  simp only [sepConj_emp]
  exact hnext sm cap1 ptr1 evs hpcm hrunm hspm htrm hx19m hx20m hlen hevs
    (fitsEnv_encRawSeg_right hfit_all hevs)

/-- Segment 1 tag + length varint (`+68 → +128`, cold `1676..1704`): `sender_ratchet_key`. -/
theorem step_encChain_seg1_tag_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a curCap curPtr srkPtr sp0 : BitVec 64) (curBs srkBs : List (BitVec 8))
    (st : M.σ)
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    (hfit : FitsEnv M lim st
      (EncRawSegEnv curBs.length (1 + (encodeVarint (BitVec.ofNat 64 srkBs.length)).length)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 128#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length →
      sm.readReg64 .x22 = srkPtr →
      EncRawSegEnv curBs.length (1 + (encodeVarint (BitVec.ofNat 64 srkBs.length)).length) evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have ⟨_, hvar_le⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 srkBs.length)
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hle _ _ => ?_
  have hsrk_nz := bv_ofNat_beq_zero_false hsrk_pos hsrk_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x0a#8
    have hfit_ev := fitsEnv_encodeVarint_of_encRawSeg
      (x := EncodeVarintGhost.mk (BitVec.ofNat 64 srkBs.length) v curCap curPtr (curBs ++ [0x0a#8]))
      (by dsimp; omega)
      (by dsimp; rw [List.length_append, List.length_singleton]; omega)
      (by omega) hfit
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs 0x0a#8 hlt,
      ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    refine step_encChain_encodeVarint_placed_x A lim H hEV
      (BitVec.ofNat 64 srkBs.length) v curCap curPtr sp0 ((blkPl_12).base + bv% (128))
      (curBs ++ [0x0a#8]) st
      (by simp only [List.length_append, List.length_singleton]; omega)
      hfit_ev (s0 := s0)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
    intro sm cap2 ptr2 evs hpcm hrunm hspm htrm hcsm hevs _ _
    refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
      (hnext sm cap2 ptr2 evs hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (encRawSegEnv_of_encodeVarintEnv (by dsimp; omega)
          (by dsimp; rw [List.length_append, List.length_singleton]; omega) (by omega) hevs))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hfit_dr : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v curCap curPtr curBs 1)) :=
      fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
        (fitsEnv_encRawSeg_left hfit)
    have hevs1 : EncRawSegEnv curBs.length 1 (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) :=
      encRawSegEnv_doReserve (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
    have hfit2 := fitsEnv_encRawSeg_right hfit hevs1
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_reserve1_placed_x A lim H hDR v curCap curPtr sp0
      ((blkPl_12).base + bv% (1696)) curBs st hcap_eq (by omega) hfit_dr (s0 := s0)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt _
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = srkPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x0a#8
    have hfit_ev := fitsEnv_encodeVarint_of_encRawSeg
      (x := EncodeVarintGhost.mk (BitVec.ofNat 64 srkBs.length) v newCap p' (curBs ++ [0x0a#8]))
      (Nat.le_refl _)
      (by dsimp only; rw [List.length_append, List.length_singleton])
      (by dsimp only; omega) hfit2
    rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPpLsCl.exists_elim fun y => ?_
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 10)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs 0x0a#8 hnew_gt,
      ← A.pool_of_vmPreserved (lim := lim)
        (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st) hvm2]
    refine step_encChain_encodeVarint_placed_x A lim H hEV
      (BitVec.ofNat 64 srkBs.length) v newCap p' sp0 ((blkPl_12).base + bv% (128))
      (curBs ++ [0x0a#8])
      (M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) st)
      (by simp only [List.length_append, List.length_singleton]; omega)
      hfit_ev (s0 := s0)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; sep_ac_rfl) ?_
    intro sm cap2 ptr2 evs2 hpcm hrunm hspm htrm hcsm hevs2 _ _
    have hevs2' : EncRawSegEnv (curBs.length + 1)
        (encodeVarint (BitVec.ofNat 64 srkBs.length)).length evs2 :=
      encRawSegEnv_of_encodeVarintEnv (Nat.le_refl _)
        (by dsimp; rw [List.length_append, List.length_singleton]) (by omega) hevs2
    rw [← M.stepEvents_append]
    refine SepWPpLsCl.congr_pre (by sep_ac_rfl)
      (hnext sm cap2 ptr2
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1) ++ evs2)
        hpcm hrunm hspm htrm
        (hcsm.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
        (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
        (encRawSegEnv_append hevs1 hevs2'))

/-- Segment 1 payload copy (`+128 → +176`, cold `1704..1744`): reserve & `memcpy` `srkBs`. -/
theorem step_encChain_seg1_copy_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a cap2 ptr2 srkCap srkPtr sp0 : BitVec 64) (bsMid srkBs : List (BitVec 8))
    (st : M.σ)
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv bsMid.length srkBs.length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 srkBs.length)
    (hx22 : s.readReg64 .x22 = srkPtr)
    (hP : P = ((v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A.repAlloc cap2 ptr2 bsMid ∗
      vecU8Buf A.repAlloc srkCap srkPtr srkBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      EncRawSegEnv bsMid.length srkBs.length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap3 ptr3 (bsMid ++ srkBs) ∗
          vecU8Buf A.repAlloc srkCap srkPtr srkBs ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A.repAlloc srkCap srkPtr srkBs ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hle2 _ _ => ?_
  refine sepWPpLsCl_extract_vecU8Buf_bounds (A := A.repAlloc) (cap := srkCap) (ptr := srkPtr) (bs := srkBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A.repAlloc cap2 ptr2 bsMid ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX ∗ F)
    (hP := by sep_ac_rfl) fun hsrk_le _ _ => ?_
  have hlen_add := bv_len_add_slice bsMid srkBs
  by_cases hspare : bsMid.length + srkBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).2.mpr hspare
    apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [vecU8Buf_eq_open_bytes A.repAlloc srkCap srkPtr srkBs hsrk_pos hsrk_le,
      ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_memcpy_placed_x A lim H hC cap2 ptr2 srkPtr sp0
      ((blkPl_12).base + bv% (168)) bsMid srkBs st hsrk_pos hspare (by omega) (s0 := s0)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A.repAlloc srkCap srkPtr srkBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sm _ hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (176))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm2]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ cap2 ptr2 [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (encRawSegEnv_nil bsMid.length srkBs.length))
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A.repAlloc srkCap srkPtr srkBs hsrk_pos hsrk_le]
    sep_ac_rfl
  · have hrem : cap2.toNat - bsMid.length < srkBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).1.mpr hrem
    have hfit_dr : FitsEnv M lim st
        (DoReserveEnv (DoReserveCall.mk v cap2 ptr2 bsMid srkBs.length)) :=
      fitsEnv_doReserve_of_encRawSeg (by omega) (by dsimp; omega) (by dsimp; omega) (by omega) hfit
    have hevs_dr : EncRawSegEnv bsMid.length srkBs.length
        (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid srkBs.length)) :=
      encRawSegEnv_doReserve (by omega) (by dsimp; omega) (by dsimp; omega) (by omega)
    apply sepWPpLsCl_of_sepWP_vm (mid := lsmpl.base 13)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm1]
    refine step_encChain_reserveSlice_placed_x A lim H hDR v cap2 ptr2 sp0
      ((blkPl_12).base + bv% (1728)) bsMid srkBs.length st hle2 hrem (by omega) (by omega) hfit_dr
      (s0 := s0)
      (F := vecU8Buf A.repAlloc srkCap srkPtr srkBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_ge hult_false _
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = srkPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPpLsCl_of_sepWP_vm (mid := lsρ lsMemcpySym)
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
    rw [vecU8Buf_eq_open_bytes A.repAlloc srkCap srkPtr srkBs hsrk_pos hsrk_le,
      ← A.pool_of_vmPreserved (lim := lim)
        (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid srkBs.length)) st)
        hvm2]
    refine step_encChain_memcpy_placed_x A lim H hC newCap p' srkPtr sp0
      ((blkPl_12).base + bv% (168)) bsMid srkBs
      (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid srkBs.length)) st)
      hsrk_pos hnew_ge (by omega) (s0 := s0)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A.repAlloc srkCap srkPtr srkBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl) ?_
    intro sm _ hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (176))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm3 => ?_⟩
    rw [← A.pool_of_vmPreserved (lim := lim)
      (st := M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid srkBs.length)) st)
      hvm3]
    refine SepWPpLsCl.congr_pre ?_
      (hnext _ newCap p' (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bsMid srkBs.length))
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hevs_dr)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A.repAlloc srkCap srkPtr srkBs hsrk_pos hsrk_le]
    sep_ac_rfl

/-- Combined Segment 1 (`+68 → +176`): `sender_ratchet_key: Vec<u8>`. -/
theorem step_encChain_seg1_placed_x [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks)
    (hC : SerContractsXPlaced M A lim H)
    (hEV : EncodeVarintPlacedOkX M A lim H)
    (hDR : DoReservePlacedOkX M A lim H)
    (v a curCap curPtr sp0 : BitVec 64) (srk : VecGhost) (curBs : List (BitVec 8))
    (st : M.σ)
    (hbound : curBs.length + (bytesField 1 srk.bytes).length < 2 ^ 32)
    (hfit : FitsEnv M lim st (EncRawSegEnv curBs.length (bytesField 1 srk.bytes).length))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ vecGhostAt A.repAlloc srk a ∗
      A.pool lim st s ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = (blkPl_12).base + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      EncRawSegEnv curBs.length (bytesField 1 srk.bytes).length evs →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A.repAlloc v cap' ptr' (curBs ++ bytesField 1 srk.bytes) ∗
          vecGhostAt A.repAlloc srk a ∗
          A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  subst hP
  by_cases hnil : srk.bytes = []
  · unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A.repAlloc a srk.cap srk.ptr srk.bytes]
    have hlen0 : BitVec.ofNat 64 srk.bytes.length = 0#64 := by simp [hnil]
    apply sepWPpLsCl_of_sepWP_vm (mid := (blkPl_12).base + bv% (176))
    by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    have hbf0 : curBs ++ bytesField 1 srk.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_eq_cells_buf A.repAlloc a srk.cap srk.ptr srk.bytes, ← hbf0,
      ← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    exact hnext _ curCap curPtr [] (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (encRawSegEnv_nil curBs.length (bytesField 1 srk.bytes).length)
  · have hsrk_pos : 0 < srk.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length) ++ srk.bytes =
        bytesField 1 srk.bytes :=
      bytesField_nonempty_eq 1 0x0a#8 srk.bytes hnil (by decide +kernel)
    have hbf_len :
        (bytesField 1 srk.bytes).length =
        (1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length) + srk.bytes.length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 srk.bytes.length)
    have hfit12 : FitsEnv M lim st
        (EncRawSegEnv curBs.length
          ((1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length) + srk.bytes.length)) := by
      rw [← hbf_len]; exact hfit
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A.repAlloc v curCap curPtr curBs,
        vecU8At_eq_cells_buf A.repAlloc a srk.cap srk.ptr srk.bytes]
    refine step_encChain_seg1_tag_placed_x A lim H hEV hDR
      v a curCap curPtr srk.ptr sp0 curBs srk.bytes st
      hsrk_pos (by omega) (by omega)
      (fitsEnv_encRawSeg_left hfit12)
      (F := (a ↦₆₄ srk.cap) ∗ vecU8Buf A.repAlloc srk.cap srk.ptr srk.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by sep_ac_rfl) ?_
    intro s1 cap2 ptr2 evs1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hevs1
    have hfit2 := fitsEnv_encRawSeg_right hfit12 hevs1
    have hbsMid_len :
        ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length =
        curBs.length + (1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length) := by
      rw [List.length_append, List.length_append, List.length_singleton, Nat.add_assoc]
    rw [vecU8At_eq_cells_buf A.repAlloc v cap2 ptr2
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length))]
    refine step_encChain_seg1_copy_placed_x A lim H hC hDR
      v a cap2 ptr2 srk.cap srk.ptr sp0
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) srk.bytes
      (M.stepEvents evs1 st)
      hsrk_pos (by omega) (by rw [hbsMid_len]; omega)
      (hbsMid_len ▸ hfit2)
      (F := (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by sep_ac_rfl) ?_
    intro s2 cap3 ptr3 evs2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hevs2
    have hevs2' : EncRawSegEnv
        (curBs.length + (1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length))
        srk.bytes.length evs2 := by
      rw [hbsMid_len] at hevs2; exact hevs2
    have hevs12 : EncRawSegEnv curBs.length (bytesField 1 srk.bytes).length (evs1 ++ evs2) := by
      rw [hbf_len]
      exact encRawSegEnv_append hevs1 hevs2'
    have hlist : ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes =
        curBs ++ bytesField 1 srk.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    rw [← M.stepEvents_append]
    refine SepWPpLsCl.congr_pre ?_
      (hnext s2 cap3 ptr3 (evs1 ++ evs2) hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hevs12)
    unfold vecGhostAt
    rw [hlist, vecU8At_eq_cells_buf A.repAlloc a srk.cap srk.ptr srk.bytes]
    sep_ac_rfl

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.PrologueSenderRatchetKeyXABudget
