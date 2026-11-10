/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BaseBudgetAux

/-!
# Budget-Threaded Relocatable Base Step Lemmas for `spqr::encode_varint` (`Block 326`)

Proves budget-threaded exit blocks (`exit0`..`exit3`, `exit_328`, `exit_396`, `exit9`) and
continuation-byte stages 1..2 (`s1`, `s2`) for `spqr::encode_varint` (`Block 326`, 164 insns),
re-exporting prologue, tail, and `grow_one` helpers from `BaseBudgetAux`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BaseBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (growOneU8Events)
open CryptoVerification
  (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost bv_len_add_one cap_eq_ofNat_len
   sepWPp_extract_vecU8Buf_le varintContByte vecU8Buf
   vecU8Buf_eq_open_one vecU8Buf_snoc_eq zext8_zext64_trunc32)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Top.EncodeVarint
  (SpqrEncVarintCalleeSavedPlaced len_beq_cap_false origLen_add_step)
open CryptoVerification.SpqrV1.Top.Placed
  (blkPC_326 blkPl_326)
open scoped CryptoVerification.SpqrV1.Top.EncodeVarint
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (sepWPp_of_sepWP_cs_placed_vm)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
  (growOneU8ByteStep spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget
  (GrowOneU8StepOkExt)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BaseBudgetAux
  (SpqrVecPushBudgetInv growOneU8ByteStep_of_eq growOneU8ByteStep_of_lt
   grow_frame_budget_reassoc step_growOneU8_placed_call
   step_spqrEncVarint_placed_prologue step_spqrEncVarint_placed_tail)

export LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BaseBudgetAux
  (SpqrVecPushBudgetInv step_growOneU8_placed_call
   step_spqrEncVarint_placed_prologue step_spqrEncVarint_placed_tail)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Exit Blocks (`+44`, `+112`, `+184`, `+256`, `+328`, `+396`, `+640`) -/

/-- Stage 0 exit (`+44..+64`): sets `x21 = x22`, checks `x22 == curCap`, and
branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit0 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [x.val.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 420#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt x.val curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 412#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt x.val curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Stage 1 exit (`+112..+132`): shifts `x20 := x20 >>> 7`, checks `x21 == curCap`,
and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit1 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [(x.val >>> 7).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 420#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt (x.val >>> 7) curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 412#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt (x.val >>> 7) curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Stage 2 exit (`+184..+204`): shifts `x20 := x20 >>> 14`, checks `x21 == curCap`,
and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit2 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [(x.val >>> 14).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 184#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 420#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt (x.val >>> 14) curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 412#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt (x.val >>> 14) curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Stage 3 exit (`+256..+276`): shifts `x20 := x20 >>> 21`, checks `x21 == curCap`,
and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit3 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [(x.val >>> 21).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = x.val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 420#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt (x.val >>> 21) curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 412#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt (x.val >>> 21) curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Shared exit at `+328..+348` (used by Stages 4, 6, 8):
moves `w20 := w23`, checks `x21 == curCap`, and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit_328 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (lastVal curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 328#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hx23 : s.readReg64 .x23 = lastVal)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 420#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt lastVal curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 412#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt lastVal curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Shared exit at `+396..+412` (used by Stages 5 and 7):
moves `w20 := w24`, checks `x21 == curCap`, and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit_396 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (lastVal curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 396#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hx24 : s.readReg64 .x24 = lastVal)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 420#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt lastVal curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 412#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt lastVal curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [zext8_zext64_trunc32, arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-- Stage 9 exit (`+640..+656`): checks `x21 == curCap` with `x20 = 1#64`
and branches to `step_spqrEncVarint_placed_tail`. -/
theorem step_spqrEncVarint_placed_exit9 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (curCap curPtr v56 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : SpqrVecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [(1#64 : BitVec 64).setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v) (hx20 : s.readReg64 .x20 = 1#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length) (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack) ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (spqrEncodeVarintSpecX A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 80#64) extHookStack ∗
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 420#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt 1#64 curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 412#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      exact step_spqrEncVarint_placed_tail A lim abs hgrow x st0 curSt 1#64 curCap curPtr v56 curBs
        hinv hbs hlen_lt
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self])) rfl

/-! ## 2. Continuation-Byte Stages 1..2 -/

/-- Stage 1 (`+64..+112`): appends `varintContByte val` and branches on
`(val >>> 7).ult 128#64` to `+112` (`exit1`) or `+132` (Stage 2). -/
theorem step_spqrEncVarint_placed_s1 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (val v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_grow : curCap.toNat = curBs.length → FitsEvents M lim curSt (growOneU8Events curCap))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 64#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 curBs.length)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 7).ult 128#64 then
        (blkPl_326).base + 112#64
      else
        (blkPl_326).base + 132#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x22 = BitVec.ofNat 64 curBs.length →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap = (growOneU8ByteStep curCap curBs.length).1 →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte val]) ∗
          A.pool lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) extHookStack) ∗ F)
        Q Qp) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 7).ult 128#64 = true ∨ (val >>> 7).ult 128#64 = false := by
    cases (val >>> 7).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte val)
    have hstep_lt := growOneU8ByteStep_of_lt hlt
    have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 112#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte val) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 132#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte val) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hstep_eq := growOneU8ByteStep_of_eq hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 619)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_growOneU8_placed_call A lim abs hgrow v curCap curPtr sp
        ((blkPl_326).base + 88#64) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_grow hcap_eq)
        (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m _ hx22m hx23m _ _ hcsm hnew_gt hnew_ge hnew_eq
      have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
      have hx22m' : sm.readReg64 .x22 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
      have hx23m' : BitVec.zeroExtend 8 (sm.readReg64 .x23) = varintContByte val := by
        rw [hx23m]; simp only [arm64_norm, *]
      have hlen1 := bv_len_add_one curBs (varintContByte val)
      have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt =
          M.stepEvents (growOneU8Events curCap) curSt := by
        rw [hstep_eq]
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 112#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte val) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 132#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte val) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])

/-- Stage 2 (`+132..+184`): appends `varintContByte (val >>> 7)` and branches on
`(val >>> 14).ult 128#64` to `+184` (`exit2`) or `+204` (Stage 3). -/
theorem step_spqrEncVarint_placed_s2 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (horig : origLen + 1#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_grow : curCap.toNat = curBs.length → FitsEvents M lim curSt (growOneU8Events curCap))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 132#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 14).ult 128#64 then
        (blkPl_326).base + 184#64
      else
        (blkPl_326).base + 204#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x22 = origLen →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap = (growOneU8ByteStep curCap curBs.length).1 →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 7)]) ∗
          A.pool lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) extHookStack) ∗ F)
        Q Qp) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 14).ult 128#64 = true ∨ (val >>> 14).ult 128#64 = false := by
    cases (val >>> 14).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 7)) 1#64 2#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    have hstep_lt := growOneU8ByteStep_of_lt hlt
    have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 184#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 7)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 204#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 7)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hstep_eq := growOneU8ByteStep_of_eq hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 619)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_growOneU8_placed_call A lim abs hgrow v curCap curPtr sp
        ((blkPl_326).base + 160#64) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_grow hcap_eq)
        (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hx23m _ _ hcsm hnew_gt hnew_ge hnew_eq
      have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
      have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
      have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
      have hx23m' : BitVec.zeroExtend 8 (sm.readReg64 .x23) = varintContByte (val >>> 7) := by
        rw [hx23m]; simp only [arm64_norm, *]
      have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt =
          M.stepEvents (growOneU8Events curCap) curSt := by
        rw [hstep_eq]
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 184#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 7)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 204#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 7)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])

end LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BaseBudget
