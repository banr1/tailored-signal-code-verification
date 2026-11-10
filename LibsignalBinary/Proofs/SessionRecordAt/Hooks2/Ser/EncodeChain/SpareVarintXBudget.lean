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
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintStagesBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Spare-Capacity `encode_varint` and Block `12` Zero-Allocation Callee Steppers

Verifies `encode_varint` (Block `10`) against `encodeVarintPreallocSpecX A` for an arbitrary
`A : RustAlloc` when `x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat` (taking no
`do_reserve_and_handle` branch), and derives zero-allocation Block `12` callee steppers threading
`VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareVarintXBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded withLsCl
  extract_withLsCodeLoaded ls_subroutine_ok_of_block lsMemcpySym lsρ
  blkPC_10 blkPl_10
)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack doReserveStackX sessionMemcpySpec
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  EncodeVarintGhost encodeVarintStackX vecU8Buf vecU8At_eq_header_sep_buf
  vecU8Buf_eq_open_one vecU8Buf_snoc_eq cap_beq_len_false bv_len_add_one
  sepWPp_extract_vecU8Buf_le sp_sub_48_aligned varintContByte
  contByte9_contByte_eq contByte9_shr63_eq shr63_ult_128
  encodeVarintAux_of_ult encodeVarintAux_of_not_ult
  encodeVarint_exit_bs encodeVarint_step_bs
  EncVarintCalleeSavedPlaced stackAt_encodeVarint_gen_eq
)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm (ushr_ushr_7)
open CryptoVerification.E2E.Record.Placed (lsProg_12 blkPl_88 lsProg_88)
open CryptoVerification.E2E.Record.Serialization (
  ChainLenGhost chainLenStack EncodeChainGhost encChainMem protoChainAt
  encChainSubStackX encChainSubRestX sp_sub_96_aligned
  stackAt_sub_to_chainLenX stackAt_sub_to_encodeVarintX stackAt_sub_to_memcpyX
  vecSliceRest vecU8Buf_eq_open_slice vecU8Buf_append_slice_eq
  trVRegs_of_call
)
open Proofs.libsignal.Hooks2 (SepWPpLsCl)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (chainLenSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (
  sepWPp_of_sepWP_cs_placed_vm sepWPp_of_sepWP_vm
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.BaseXBudget (
  sepWPpLsCl_call_lscl_noPanic sepWPpLsCl_call_withLsCl_noPanic
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Spare-capacity length bounds and `encodeVarintPreallocSpecX` -/

theorem encodeVarintAux_pos (fuel : Nat) (v : BitVec 64) :
    1 ≤ (encodeVarintAux (fuel + 1) v).length := by
  cases h : v.ult 128#64
  · rw [encodeVarintAux_of_not_ult h, List.length_cons]
    omega
  · rw [encodeVarintAux_of_ult h]
    simp

theorem spare_lt_of_aux {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64} {cap : Nat}
    (hle : curBs.length + (encodeVarintAux (fuel + 1) v).length ≤ cap) :
    curBs.length < cap := by
  have := encodeVarintAux_pos fuel v
  omega

theorem spare_step_of_not_ult {curBs : List (BitVec 8)} {fuel : Nat} {v nextV : BitVec 64}
    {byte : BitVec 8} {cap : Nat}
    (hle : curBs.length + (encodeVarintAux (fuel + 1) v).length ≤ cap)
    (h : v.ult 128#64 = false) (hshift : v >>> 7 = nextV) :
    (curBs ++ [byte]).length + (encodeVarintAux fuel nextV).length ≤ cap := by
  rw [encodeVarintAux_of_not_ult h, hshift, List.length_cons] at hle
  rw [List.length_append, List.length_singleton]
  omega

theorem encodeVarint_exit_bs_s9 {v : BitVec 64} {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux 1 (v >>> 63) = rhs)
    (h : (v >>> 56).ult 128#64 = false) :
    bs ++ [(1#64 : BitVec 64).setWidth 8] = rhs := by
  have h1 : (1#64 : BitVec 64) = v >>> 63 := contByte9_shr63_eq v h
  rw [h1, ← encodeVarintAux_of_ult (shr63_ult_128 v), hcur]

def encodeVarintPreallocSpecOf (resStack : Nat) (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp (0x30 + resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗
      stackAt s0.sp (0x30 + resStack)

abbrev encodeVarintPreallocSpecX (A : RustAlloc) : Spec EncodeVarintGhost :=
  encodeVarintPreallocSpecOf doReserveStackX A

/-! ## Block `10` stage lemmas over `A : RustAlloc` -/

theorem step_encVarint_prologue_prealloc [LibsignalPlacement]
    (H : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_10).base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (if val.ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 32#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s.trace →
      sm.readReg64 .x0 = val → sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 bs.length → sm.readReg64 .x9 = cap →
      EncVarintCalleeSavedPlaced s sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) ret s P Q Qp := by
  subst hP
  apply sepWPp_of_sepWP_cs_placed_vm
    (mid := if val.ult 128#64 then (blkPl_10).base + bv% (512) else (blkPl_10).base + bv% (32))
  by_vm_steps
    wp_steps
    refine SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
    exact hnext _ hvm (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self])

theorem step_encVarint_final_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (lastVal v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 512#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sf : State,
      VmPreserved s0 sf →
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      Q sf (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
        vecU8Buf A curCap curPtr (curBs ++ [lastVal.setWidth 8]) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        stackAt (sp - 48#64) resStack) ∗ F)) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm_end => ?_⟩
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (BitVec.zeroExtend 8 lastVal) hlt]
    exact hnext _ (hvm.trans hvm_end)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by encodedLen_cc_close)

theorem step_encVarint_exit_prealloc [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (x : EncodeVarintGhost) (lastVal v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlt : curBs.length < x.cap.toNat)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 512#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 48#64) (halign : s0.sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = x.v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = x.cap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A x.cap x.ptr curBs ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      stackAt (s0.sp - 48#64) resStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintPreallocSpecOf resStack A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  refine step_encVarint_final_prealloc (F := emp) A H lastVal x.v x.cap x.ptr s0.sp v48 v40
    curBs hlt hvm hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro sf hvmf _ _ hspf htrf hcsf
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp, hbs] at hm_f
  simp only [encodeVarintPreallocSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, ⟨htrf, hvmf⟩, ?_⟩
  convert hm_f using 1
  sep_ac_rfl

theorem step_encVarint_s1_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 32#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (if (val >>> 7).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 136#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 7).ult 128#64 then val >>> 7 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x9 = curCap → sm.readReg64 .x10 = curPtr →
      EncVarintCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte val]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 7).ult 128#64 = true ∨ (val >>> 7).ult 128#64 = false := by
    cases (val >>> 7).ult 128#64 <;> simp
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte val)
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  rcases hcond_or with hcond | hcond
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (136))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_encVarint_s2_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 136#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (if (val >>> 14).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 252#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 14).ult 128#64 then val >>> 14 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x9 = curCap → sm.readReg64 .x10 = curPtr →
      EncVarintCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 7)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 14).ult 128#64 = true ∨ (val >>> 14).ult 128#64 = false := by
    cases (val >>> 14).ult 128#64 <;> simp
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  rcases hcond_or with hcond | hcond
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (252))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_encVarint_s3_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 252#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (if (val >>> 21).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 360#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 21).ult 128#64 then val >>> 21 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x9 = curCap → sm.readReg64 .x12 = val >>> 28 →
      EncVarintCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 14)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 21).ult 128#64 = true ∨ (val >>> 21).ult 128#64 = false := by
    cases (val >>> 21).ult 128#64 <;> simp
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  rcases hcond_or with hcond | hcond
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (360))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_encVarint_s4_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 360#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (if (val >>> 28).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 476#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 28).ult 128#64 then val >>> 28 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x9 = curCap → sm.readReg64 .x10 = curPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 28 →
      EncVarintCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 21)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 28).ult 128#64 = true ∨ (val >>> 28).ult 128#64 = false := by
    cases (val >>> 28).ult 128#64 <;> simp
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 21))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  rcases hcond_or with hcond | hcond
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (476))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 21)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_encVarint_s5_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 476#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (if (val >>> 35).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 668#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 35).ult 128#64 then val >>> 35 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x9 = curCap → sm.readReg64 .x10 = curPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 42 →
      EncVarintCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 28)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 35).ult 128#64 = true ∨ (val >>> 35).ult 128#64 = false := by
    cases (val >>> 35).ult 128#64 <;> simp
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 28))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  rcases hcond_or with hcond | hcond
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (668))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 28)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_encVarint_s6_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 668#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 42) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (if (val >>> 42).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 704#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 42).ult 128#64 then val >>> 42 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x9 = curCap → sm.readReg64 .x11 = val >>> 49 →
      sm.readReg64 .x12 = val >>> 42 →
      EncVarintCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 35)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 42).ult 128#64 = true ∨ (val >>> 42).ult 128#64 = false := by
    cases (val >>> 42).ult 128#64 <;> simp
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 35))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  rcases hcond_or with hcond | hcond
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (704))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 35)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_encVarint_s7_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 704#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx11 : s.readReg64 .x11 = val >>> 49) (hx12 : s.readReg64 .x12 = val >>> 42)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (if (val >>> 49).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 740#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 49).ult 128#64 then val >>> 49 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x9 = curCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = val >>> 49 → sm.readReg64 .x12 = curPtr →
      EncVarintCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 42)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 49).ult 128#64 = true ∨ (val >>> 49).ult 128#64 = false := by
    cases (val >>> 49).ult 128#64 <;> simp
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 42))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  rcases hcond_or with hcond | hcond
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (740))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 42)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_encVarint_s8_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx11 : s.readReg64 .x11 = val >>> 49)
    (hx12 : s.readReg64 .x12 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (if (val >>> 56).ult 128#64 then (blkPl_10).base + 512#64 else (blkPl_10).base + 984#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 56).ult 128#64 then val >>> 56 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x9 = curCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x12 = curPtr →
      EncVarintCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 49)]) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 56).ult 128#64 = true ∨ (val >>> 56).ult 128#64 = false := by
    cases (val >>> 56).ult 128#64 <;> simp
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 49))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  rcases hcond_or with hcond | hcond
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
  · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (984))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
      rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 49)) hlt]
      exact hnext _ (hvm.trans hvm_s)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))

theorem step_encVarint_s9_prealloc [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (val v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8))
    (hnot_ult : (val >>> 56).ult 128#64 = false)
    (hlt : curBs.length < curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hvm : VmPreserved s0 s)
    (hpc : s.pc = (blkPl_10).base + 984#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx12 : s.readReg64 .x12 = curPtr)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s0 sm →
      sm.pc = (blkPl_10).base + 512#64 →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = 1#64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length →
      sm.readReg64 .x9 = curCap →
      EncVarintCalleeSavedPlaced s0 sm →
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 56)]) ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hbyte := contByte9_contByte_eq val hnot_ult
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 56))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_10).base + bv% (512))
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], fun hvm_s _ => ?_⟩
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 56)) hlt]
    exact hnext _ (hvm.trans hvm_s)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))

/-! ## Spare-capacity `encode_varint` verification -/

theorem encodeVarint_prealloc_gen_placed_ok [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (R : SepProp) (s0 : State)
    (hpc0 : s0.pc = (blkPl_10).base)
    (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintPreallocSpecOf resStack A).pre x s0 ∗ R)
    (hsp0 : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp ((blkPC_10).rebase (blkPl_10).base H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintPreallocSpecOf resStack A).post x s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧
          CalleeSavedPreserved s0 s')
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (encodeVarintPreallocSpecOf resStack A).onPanic x s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp0; exact hsp0
  simp only [encodeVarintPreallocSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v48, v40, v32, v24, v16, v8, ⟨hx0, hx1, hspare0⟩, hpre⟩
  refine ⟨((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗
      (vecU8Buf A x.cap x.ptr x.bs ∗ stackAt (s0.sp - 48#64) resStack),
    ?_, ?_⟩
  · convert hpre using 1; sep_ac_rfl
  refine step_encVarint_prologue_prealloc H x.val x.v x.cap x.ptr s0.sp
    v48 v40 v32 v24 v16 v8 x.bs hpc0 hrun0 rfl halign hx0 hx1 rfl ?_
  intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hle0 : x.bs.length + (encodeVarintAux 10 x.val).length ≤ x.cap.toNat := hspare0
  have hbs0 : x.bs ++ encodeVarintAux 10 x.val = x.bs ++ encodeVarint x.val := rfl
  cases hult0 : x.val.ult 128#64
  · simp only [hult0, ↓reduceIte, Bool.false_eq_true] at hpc1
    have hbs1 := encodeVarint_step_bs hbs0 hult0 rfl
    have hle1 := spare_step_of_not_ult (byte := varintContByte x.val) hle0 hult0 rfl
    refine step_encVarint_s1_prealloc (F := FSave) A H
      x.val x.v x.cap x.ptr s0.sp v48 v40 x.bs (spare_lt_of_aux hle0)
      hvm1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by dsimp [FSave]; sep_ac_rfl) ?_
    intro s2 hvm2 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2
    cases hult1 : (x.val >>> 7).ult 128#64
    · simp only [hult1, ↓reduceIte, Bool.false_eq_true] at hpc2 hx0_2
      have hbs2 := encodeVarint_step_bs (nextV := x.val >>> 14) hbs1 hult1 (ushr_ushr_7 x.val 7 14)
      have hle2 := spare_step_of_not_ult (byte := varintContByte (x.val >>> 7)) hle1 hult1 (ushr_ushr_7 x.val 7 14)
      refine step_encVarint_s2_prealloc (F := FSave) A H
        x.val x.v x.cap x.ptr s0.sp v48 v40 _ (spare_lt_of_aux hle1)
        hvm2 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 rfl ?_
      intro s3 hvm3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3
      cases hult2 : (x.val >>> 14).ult 128#64
      · simp only [hult2, ↓reduceIte, Bool.false_eq_true] at hpc3 hx0_3
        have hbs3 := encodeVarint_step_bs (nextV := x.val >>> 21) hbs2 hult2 (ushr_ushr_7 x.val 14 21)
        have hle3 := spare_step_of_not_ult (byte := varintContByte (x.val >>> 14)) hle2 hult2 (ushr_ushr_7 x.val 14 21)
        refine step_encVarint_s3_prealloc (F := FSave) A H
          x.val x.v x.cap x.ptr s0.sp v48 v40 _ (spare_lt_of_aux hle2)
          hvm3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 rfl ?_
        intro s4 hvm4 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4
        cases hult3 : (x.val >>> 21).ult 128#64
        · simp only [hult3, ↓reduceIte, Bool.false_eq_true] at hpc4 hx0_4
          have hbs4 := encodeVarint_step_bs (nextV := x.val >>> 28) hbs3 hult3 (ushr_ushr_7 x.val 21 28)
          have hle4 := spare_step_of_not_ult (byte := varintContByte (x.val >>> 21)) hle3 hult3 (ushr_ushr_7 x.val 21 28)
          refine step_encVarint_s4_prealloc (F := FSave) A H
            x.val x.v x.cap x.ptr s0.sp v48 v40 _ (spare_lt_of_aux hle3)
            hvm4 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 rfl ?_
          intro s5 hvm5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5
          cases hult4 : (x.val >>> 28).ult 128#64
          · simp only [hult4, ↓reduceIte, Bool.false_eq_true] at hpc5 hx0_5
            have hbs5 := encodeVarint_step_bs (nextV := x.val >>> 35) hbs4 hult4 (ushr_ushr_7 x.val 28 35)
            have hle5 := spare_step_of_not_ult (byte := varintContByte (x.val >>> 28)) hle4 hult4 (ushr_ushr_7 x.val 28 35)
            refine step_encVarint_s5_prealloc (F := FSave) A H
              x.val x.v x.cap x.ptr s0.sp v48 v40 _ (spare_lt_of_aux hle4)
              hvm5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 rfl ?_
            intro s6 hvm6 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6 hx0_6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              have hle6 := spare_step_of_not_ult (byte := varintContByte (x.val >>> 35)) hle5 hult5 (ushr_ushr_7 x.val 35 42)
              refine step_encVarint_s6_prealloc (F := FSave) A H
                x.val x.v x.cap x.ptr s0.sp v48 v40 _ (spare_lt_of_aux hle5)
                hvm6 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6 rfl ?_
              intro s7 hvm7 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7 hx0_7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                have hle7 := spare_step_of_not_ult (byte := varintContByte (x.val >>> 42)) hle6 hult6 (ushr_ushr_7 x.val 42 49)
                refine step_encVarint_s7_prealloc (F := FSave) A H
                  x.val x.v x.cap x.ptr s0.sp v48 v40 _ (spare_lt_of_aux hle6)
                  hvm7 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7 rfl ?_
                intro s8 hvm8 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8 hx0_8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  have hle8 := spare_step_of_not_ult (byte := varintContByte (x.val >>> 49)) hle7 hult7 (ushr_ushr_7 x.val 49 56)
                  refine step_encVarint_s8_prealloc (F := FSave) A H
                    x.val x.v x.cap x.ptr s0.sp v48 v40 _ (spare_lt_of_aux hle7)
                    hvm8 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl ?_
                  intro s9 hvm9 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9 hx0_9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    have hle9 := spare_step_of_not_ult (byte := varintContByte (x.val >>> 56)) hle8 hult8 (ushr_ushr_7 x.val 56 63)
                    refine step_encVarint_s9_prealloc
                      (F := ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗ FSave)
                      A H x.val x.v x.cap x.ptr s0.sp _ hult8 (spare_lt_of_aux hle8)
                      hvm9 hpc9 hrun9 hsp9 htr9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9 (by sep_ac_rfl) ?_
                    intro s10 hvm10 hpc10 hrun10 hsp10 htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10
                    exact step_encVarint_exit_prealloc hres A H x 1#64 v48 v40 _
                      (encodeVarint_exit_bs_s9 hbs9 hult8) (spare_lt_of_aux hle9)
                      hvm10 hpc10 hrun10 hsp10 halign htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10
                      (by dsimp [FSave]; sep_ac_rfl)
                  · simp only [hult8, ↓reduceIte] at hpc9 hx0_9
                    exact step_encVarint_exit_prealloc hres A H x (x.val >>> 56) v48 v40 _
                      (encodeVarint_exit_bs hbs8 hult8) (spare_lt_of_aux hle8)
                      hvm9 hpc9 hrun9 hsp9 halign htr9 hx0_9 hx1_9 hx8_9 hx9_9 hcs9 rfl
                · simp only [hult7, ↓reduceIte] at hpc8 hx0_8
                  exact step_encVarint_exit_prealloc hres A H x (x.val >>> 49) v48 v40 _
                    (encodeVarint_exit_bs hbs7 hult7) (spare_lt_of_aux hle7)
                    hvm8 hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hcs8 rfl
              · simp only [hult6, ↓reduceIte] at hpc7 hx0_7
                exact step_encVarint_exit_prealloc hres A H x (x.val >>> 42) v48 v40 _
                  (encodeVarint_exit_bs hbs6 hult6) (spare_lt_of_aux hle6)
                  hvm7 hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hcs7 rfl
            · simp only [hult5, ↓reduceIte] at hpc6 hx0_6
              exact step_encVarint_exit_prealloc hres A H x (x.val >>> 35) v48 v40 _
                (encodeVarint_exit_bs hbs5 hult5) (spare_lt_of_aux hle5)
                hvm6 hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hcs6 rfl
          · simp only [hult4, ↓reduceIte] at hpc5 hx0_5
            exact step_encVarint_exit_prealloc hres A H x (x.val >>> 28) v48 v40 _
              (encodeVarint_exit_bs hbs4 hult4) (spare_lt_of_aux hle4)
              hvm5 hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hcs5 rfl
        · simp only [hult3, ↓reduceIte] at hpc4 hx0_4
          exact step_encVarint_exit_prealloc hres A H x (x.val >>> 21) v48 v40 _
            (encodeVarint_exit_bs hbs3 hult3) (spare_lt_of_aux hle3)
            hvm4 hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hcs4 rfl
      · simp only [hult2, ↓reduceIte] at hpc3 hx0_3
        exact step_encVarint_exit_prealloc hres A H x (x.val >>> 14) v48 v40 _
          (encodeVarint_exit_bs hbs2 hult2) (spare_lt_of_aux hle2)
          hvm3 hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hcs3 rfl
    · simp only [hult1, ↓reduceIte] at hpc2 hx0_2
      exact step_encVarint_exit_prealloc hres A H x (x.val >>> 7) v48 v40 _
        (encodeVarint_exit_bs hbs1 hult1) (spare_lt_of_aux hle1)
        hvm2 hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hcs2 rfl
  · simp only [hult0, ↓reduceIte] at hpc1
    exact step_encVarint_exit_prealloc hres A H x x.val v48 v40 x.bs
      (encodeVarint_exit_bs hbs0 hult0) (spare_lt_of_aux hle0)
      hvm1 hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by sep_ac_rfl)

/-- Relocatable `encode_varint` (Block `10`) satisfies `encodeVarintPreallocSpecX A` for any
`A : RustAlloc` when the destination buffer has spare capacity. -/
theorem encode_varint_prealloc_placed_ok_x [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_10).rebase (blkPl_10).base H)
      (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintPreallocSpecX A)) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  obtain ⟨_, hpre⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨P, hP, hwp⟩ := encodeVarint_prealloc_gen_placed_ok A H (resStack := doReserveStackX)
    (by decide) x R s0 hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

/-! ## Block `12` zero-allocation callee steppers -/

theorem step_encChain_encodeVarint_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (val v curCap curPtr sp0 ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hspare : curBs.length + (encodeVarint val).length ≤ curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8At A v curCap curPtr (curBs ++ encodeVarint val) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  have hEV' : subroutine_ok (lsProg_12 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintPreallocSpecX A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) (encode_varint_prealloc_placed_ok_x A H)
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  have hstk_eq : (0x30 + doReserveStackX : Nat) = encodeVarintStackX := rfl
  refine sepWPpLsCl_call_lscl_noPanic (x := EncodeVarintGhost.mk val v curCap curPtr curBs)
    (F := encChainSubRestX (sp0 - 96#64) encodeVarintStackX ∗ F)
    hEV' hpc hrun hsp_aligned hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarintX (sp0 - 96#64)] at hm
    simp only [encodeVarintPreallocSpecX, encodeVarintPreallocSpecOf, hstk_eq,
      hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hspare⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintPreallocSpecX, encodeVarintPreallocSpecOf, hstk_eq,
      hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun ⟨htrm, hvm⟩ => ?_
    have hGoalEq :
        (vecU8At A v curCap curPtr (curBs ++ encodeVarint val) ∗
          stackAt (sp0 - 96#64) encodeVarintStackX ∗
          encChainSubRestX (sp0 - 96#64) encodeVarintStackX ∗ F) =
        ((vecU8At A v curCap curPtr (curBs ++ encodeVarint val) ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [stackAt_sub_to_encodeVarintX (sp0 - 96#64)]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm hvm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm

theorem step_encChain_chainLen_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (sp0 ret_pc : BitVec 64)
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
    (hP : P = (protoChainAt A x.gc x.a ∗
      stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encChainMem x.gc).length →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((protoChainAt A x.gc x.a ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  have hchain' : subroutine_ok (lsProg_12 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hchain
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPpLsCl_call_lscl_noPanic (x := ChainLenGhost.mk x.a x.gc)
    (F := encChainSubRestX (sp0 - 96#64) chainLenStack ∗ F)
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
        (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) chainLenStack ∗
          encChainSubRestX (sp0 - 96#64) chainLenStack ∗ F) =
        ((protoChainAt A x.gc x.a ∗
          stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [stackAt_sub_to_chainLenX (sp0 - 96#64)]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm hvm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m

theorem step_encChain_memcpy_prealloc_x [LibsignalPlacement]
    (A : RustAlloc) (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (curCap curPtr srcPtr sp0 ret_pc : BitVec 64) (curBs sliceBs : List (BitVec 8))
    (hpos : 0 < sliceBs.length)
    (hle : curBs.length + sliceBs.length ≤ curCap.toNat)
    (hslice_lt : sliceBs.length < 2 ^ 32)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = curPtr + BitVec.ofNat 64 curBs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 sliceBs.length)
    (hP : P = (vecU8Buf A curCap curPtr curBs ∗
      (srcPtr ↦ₛ sliceBs) ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      SepWPpLsCl lsmpl (lsProg_12 H) ret sm
        ((vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F)
        Q Qp) :
    SepWPpLsCl lsmpl (lsProg_12 H) ret s P Q Qp := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  have hx2_toNat : (s.readReg64 .x2).toNat = sliceBs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPpLsCl_call_withLsCl_noPanic (x := (curPtr + BitVec.ofNat 64 curBs.length, srcPtr, sliceBs))
    (F := vecSliceRest A curCap curPtr curBs sliceBs.length ∗
      encChainSubRestX (sp0 - 96#64) extHookStack ∗ F)
    hmc hpc hrun hsp_aligned hlr ?_ ?_
  · intro R' hm
    rw [hP, vecU8Buf_eq_open_slice A curCap curPtr curBs sliceBs.length hpos hle,
      stackAt_sub_to_memcpyX (sp0 - 96#64)] at hm
    simp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, libcMemcpySpec, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_toNat⟩, ?_⟩
    convert hm using 1; sep_ac_rfl
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, hsp, sepConj_assoc]
    refine SepWPpLsCl.pure_elim fun hvm => ?_
    refine SepWPpLsCl.pure_elim fun ⟨_, htrm⟩ => ?_
    have hGoalEq :
        (((curPtr + BitVec.ofNat 64 curBs.length) ↦ₛ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗
          stackAt (sp0 - 96#64) extHookStack ∗
          vecSliceRest A curCap curPtr curBs sliceBs.length ∗
          encChainSubRestX (sp0 - 96#64) extHookStack ∗ F) =
        ((vecU8Buf A curCap curPtr (curBs ++ sliceBs) ∗
          (srcPtr ↦ₛ sliceBs) ∗ stackAt (sp0 - 96#64) encChainSubStackX) ∗ F) := by
      rw [stackAt_sub_to_memcpyX (sp0 - 96#64),
        ← vecU8Buf_append_slice_eq A curCap curPtr curBs sliceBs hpos hle]
      sep_ac_rfl
    rw [hGoalEq]
    exact hnext sm hvm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareVarintXBudget
