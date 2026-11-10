/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `prost::encoding::varint::encode_varint [local#4]`

Proves `[LibsignalPlacement]` continuation-byte stages 4..8 and top-level
`RustCliAllocBudget`-threaded contracts (`encodeVarintDetSpec*`, `encodeVarintFitSpec*`,
`encodeVarintSpec*`) on `lsProg_292 H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded ls_subroutine_ok_of_block
   blkPC_292 blkPl_292 lsProg_292)
open CryptoVerification.RustHeap (vecU8At vecHeader)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStack doReserveStackX)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost VecReserveInv vecU8Buf vecU8At_eq_header_sep_buf vecU8Buf_eq_open_one
   vecU8Buf_snoc_eq cap_beq_len_false cap_eq_ofNat_len bv_len_add_one sepWPp_extract_vecU8Buf_le
   varintContByte EncVarintCalleeSavedPlaced stackAt_encodeVarint_gen_eq
   encodeVarint_step_bs encodeVarint_exit_bs)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  (zext64_trunc32_orr_mask ushr_ushr_7)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustNoAllocShimSym spqrRustAllocSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.Varint
  (encodeVarint_length_bounds stage_len_lt_of_step stage_len_lt_of_exit encodeVarint_exit_bs_s9)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushByteStep pushBytesEvents encodeVarintEvents encodeVarintEnv_events)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (pushByteStep_of_lt VecPushBudgetInv sepWPp_of_sepWP_cs_placed_vm
   doReserveSpecWithPlaced encodeVarintSpecOf final_frame_reassoc stage_frame_reassoc)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (do_reserve_7_placed_ok do_reserve_7_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserveSpecOf doReserve7_with_placed_of_ok step_doReserve_call_gen_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
  (encodeVarintFitSpecOf encodeVarintFitSpec encodeVarintFitSpecX
   EncodeVarint4FitPlacedOk EncodeVarint4FitPlacedOkX
   step_encVarint4_prologue_placed step_encVarint4_final_placed step_encVarint4_exit_placed
   step_encVarint4_s1_placed step_encVarint4_s2_placed step_encVarint4_s3_placed
   step_encVarint4_s9_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (pushBytesStep encodeVarintDetSpecOf encodeVarintDetSpec encodeVarintDetSpecX
   subroutine_ok_withLsCodeLoaded_encodeVarintFit_of_det)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Deterministic Capacity Step Helpers -/

def encodeVarintSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) :=
  encodeVarintSpecOf doReserveStack A lim

def encodeVarintSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (EncodeVarintGhost × M.σ) :=
  encodeVarintSpecOf doReserveStackX A lim

/-- Deterministic post-capacity invariant across remaining byte pushes of `encode_varint`. -/
def VecCapStepInv (x : EncodeVarintGhost) (curCap : BitVec 64)
    (curBs : List (BitVec 8)) (remLen : Nat) : Prop :=
  (pushBytesStep (encodeVarint x.val).length x.cap.toNat x.bs.length).1 =
    (pushBytesStep remLen curCap.toNat curBs.length).1

private theorem VecCapStepInv.init (x : EncodeVarintGhost) :
    VecCapStepInv x x.cap x.bs (encodeVarint x.val).length :=
  rfl

private theorem VecCapStepInv.of_rem_eq {x : EncodeVarintGhost} {curCap : BitVec 64}
    {curBs : List (BitVec 8)} {n1 n2 : Nat}
    (h : VecCapStepInv x curCap curBs n1) (hn : n1 = n2) :
    VecCapStepInv x curCap curBs n2 :=
  hn ▸ h

private theorem VecCapStepInv.step {x : EncodeVarintGhost} {curCap nextCap : BitVec 64}
    {curBs : List (BitVec 8)} {byte : BitVec 8} {rem : Nat}
    (h : VecCapStepInv x curCap curBs (rem + 1))
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecCapStepInv x nextCap (curBs ++ [byte]) rem := by
  have hlen : (curBs ++ [byte]).length = curBs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  unfold VecCapStepInv at h ⊢
  rw [h, pushBytesStep, hcap_step, hlen]

private theorem rem_len_step {α : Type} {curBs rhs L1 L2 : List α} {b : α}
    (h1 : curBs ++ L1 = rhs) (h2 : (curBs ++ [b]) ++ L2 = rhs) :
    L1.length = L2.length + 1 := by
  have hlen := congrArg List.length (h1.trans h2.symm)
  simp only [List.length_append, List.length_singleton] at hlen
  omega

private theorem rem_len_exit {α : Type} {curBs rhs L : List α} {b : α}
    (h1 : curBs ++ L = rhs) (h2 : curBs ++ [b] = rhs) :
    L.length = 1 := by
  have hlen := congrArg List.length (h1.trans h2.symm)
  simp only [List.length_append, List.length_singleton] at hlen
  omega

theorem step_encVarint4_det_exit_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A lim))
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (lastVal curCap curPtr v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hcap_inv : VecCapStepInv x curCap curBs 1)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 512#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 48#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = x.v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 48#64) resStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintDetSpecOf resStack A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  refine step_encVarint4_final_placed (F := emp) A lim H hdoReserve lastVal x.v curCap curPtr s0.sp v48 v40
    curBs curSt hlen_lt (fun hcap_eq => hinv.fits_reserve x.v hcap_eq)
    hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro sf cap' ptr' hpcf hrunf hspf htrf hcsf hge hpres hcap_step
  have hinv' := hinv.step (byte := lastVal.setWidth 8) hge hpres hcap_step
  have hcap_inv' := hcap_inv.step (byte := lastVal.setWidth 8) hcap_step
  have hcap_det : cap'.toNat = (pushBytesStep (encodeVarint x.val).length x.cap.toNat x.bs.length).1 := by
    simpa [VecCapStepInv, pushBytesStep] using hcap_inv'.symm
  have hres' := hinv'.res; rw [hbs] at hres'; have ⟨hcap_le, hcap_pres⟩ := hres'.finish
  have hev_eq : M.stepEvents (encodeVarintEvents x) st0 =
      M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt := by
    simpa [pushBytesEvents] using hinv'.events_eq
  refine ⟨?_, hspf, hcsf⟩; intro hm_f
  rw [sepConj_emp, hbs, ← hev_eq] at hm_f
  simp only [encodeVarintDetSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, encodeVarintEvents x, cap', ptr',
    htrf, ⟨hcap_le, hcap_pres, hcap_det⟩, ?_⟩
  rw [eq_true (encodeVarintEnv_events x), pure_true]
  convert hm_f using 1; sep_ac_rfl

/-! ## Placed Continuation-Byte Stages 4..8 -/

theorem step_encVarint4_s4_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 360#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 28).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 476#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 28).ult 128#64 then val >>> 28 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 28 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 21)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 28).ult 128#64 = true ∨ (val >>> 28).ult 128#64 = false := by
    cases (val >>> 28).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 21))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 21)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (476))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 21)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 320)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_292).base + bv% (440)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 =
          BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 21)) |||
            4294967168#64 := by simp only [arm64_norm, *]; simp
      have hx20m' : sm.readReg64 .x20 = val >>> 28 := by simp only [arm64_norm, *]
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 21))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 21)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (476))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 21)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint4_s5_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 476#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 28) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 35).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 668#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 35).ult 128#64 then val >>> 35 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr →
      sm.readReg64 .x11 = val >>> 35 → sm.readReg64 .x12 = val >>> 42 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 28)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 35).ult 128#64 = true ∨ (val >>> 35).ult 128#64 = false := by
    cases (val >>> 35).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 28))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 28)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (668))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 28)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 320)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_292).base + bv% (632)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 =
          BitVec.zeroExtend 64 (BitVec.truncate 32 (val >>> 28)) ||| 4294967168#64 := by
        simp only [arm64_norm, zext64_trunc32_orr_mask, *]
      have hx20m' : sm.readReg64 .x20 = val >>> 35 := by simp only [arm64_norm, *]
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 28))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 28)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (668))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 28)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint4_s6_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 668#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hx11 : s.readReg64 .x11 = val >>> 35)
    (hx12 : s.readReg64 .x12 = val >>> 42) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 42).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 704#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 42).ult 128#64 then val >>> 42 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x11 = val >>> 49 → sm.readReg64 .x12 = val >>> 42 →
      EncVarintCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 35)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 42).ult 128#64 = true ∨ (val >>> 42).ult 128#64 = false := by
    cases (val >>> 42).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 35))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 35)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (704))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 35)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 320)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_292).base + bv% (808)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 =
          BitVec.zeroExtend 64 (BitVec.truncate 32 (val >>> 35)) ||| 4294967168#64 := by
        simp only [arm64_norm, zext64_trunc32_orr_mask, *]
      have hx20m' : sm.readReg64 .x20 = val >>> 42 := by simp only [arm64_norm, *]
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 35))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 35)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (704))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 35)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint4_s7_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 704#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx11 : s.readReg64 .x11 = val >>> 49) (hx12 : s.readReg64 .x12 = val >>> 42)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 49).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 740#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 49).ult 128#64 then val >>> 49 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 →
      sm.readReg64 .x11 = val >>> 49 → sm.readReg64 .x12 = nextPtr → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 42)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 42)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 49).ult 128#64 = true ∨ (val >>> 49).ult 128#64 = false := by
    cases (val >>> 49).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 42))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 42)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (740))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 42)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 320)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_292).base + bv% (880)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 =
          BitVec.zeroExtend 64 (BitVec.truncate 32 (val >>> 42)) ||| 4294967168#64 := by
        simp only [arm64_norm, zext64_trunc32_orr_mask, *]
      have hx20m' : sm.readReg64 .x20 = val >>> 49 := by simp only [arm64_norm, *]
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 42))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 42)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (740))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 42)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint4_s8_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_292).base + 740#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx11 : s.readReg64 .x11 = val >>> 49)
    (hx12 : s.readReg64 .x12 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 56).ult 128#64 then (blkPl_292).base + 512#64 else (blkPl_292).base + 984#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 56).ult 128#64 then val >>> 56 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = val >>> 56 → sm.readReg64 .x12 = nextPtr →
      EncVarintCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 49)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 49)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (lsProg_292 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 56).ult 128#64 = true ∨ (val >>> 56).ult 128#64 = false := by
    cases (val >>> 56).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 49))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 49)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (984))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 49)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 320)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm _ => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_292).base + bv% (952)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 =
          BitVec.zeroExtend 64 (BitVec.truncate 32 (val >>> 49)) ||| 4294967168#64 := by
        simp only [arm64_norm, zext64_trunc32_orr_mask, *]
      have hx20m' : sm.readReg64 .x20 = val >>> 56 := by simp only [arm64_norm, *]
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 49))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (512))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 49)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_292).base + bv% (984))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 _ => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 49)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

theorem encodeVarint4_det_gen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (st0 : M.σ) (R : SepProp) (s0 : State)
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320) (doReserveSpecWithPlaced resStack s0 A lim))
    (hpc0 : s0.pc = (blkPl_292).base) (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintDetSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp0 : s0.spAligned = true) :
    ∃ P,
      (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_292 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintDetSpecOf resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s')
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (encodeVarintDetSpecOf resStack A lim).onPanic (x, st0) s0 sf ∗ R)) := by
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp0; exact hsp0
  simp only [encodeVarintDetSpecOf, encodeVarintFitSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v48, v40, v32, v24, v16, v8, ⟨hx0, hx1, hlen_bound, hfits0⟩, hpre⟩
  refine ⟨((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗
      (vecU8Buf A.repAlloc x.cap x.ptr x.bs ∗ A.pool lim st0 s0 ∗ stackAt (s0.sp - 48#64) resStack), ?_, ?_⟩
  · convert hpre using 1; sep_ac_rfl
  refine step_encVarint4_prologue_placed
    (F := vecU8Buf A.repAlloc x.cap x.ptr x.bs ∗ stackAt (s0.sp - 48#64) resStack)
    A lim H x.val x.v x.cap x.ptr s0.sp v48 v40 v32 v24 v16 v8 x.bs st0
    hpc0 hrun0 rfl halign hx0 hx1 (by sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hinv0 : VecPushBudgetInv M lim x st0 x.cap x.ptr x.bs (encodeVarintAux 10 x.val).length st0 :=
    VecPushBudgetInv.init x st0 hfits0
  have hcap0 : VecCapStepInv x x.cap x.bs (encodeVarintAux 10 x.val).length :=
    VecCapStepInv.init x
  have hbs0 : x.bs ++ encodeVarintAux 10 x.val = x.bs ++ encodeVarint x.val := rfl
  cases hult0 : x.val.ult 128#64
  · simp only [hult0, ↓reduceIte, Bool.false_eq_true] at hpc1
    have hbs1 := encodeVarint_step_bs hbs0 hult0 rfl
    have hrem0 := rem_len_step hbs0 hbs1; have hinv0s := hinv0.of_rem_eq hrem0; have hcap0s := hcap0.of_rem_eq hrem0
    refine step_encVarint4_s1_placed (F := FSave) A lim H hdoReserve x.val x.v x.cap x.ptr s0.sp v48 v40 x.bs st0
      (stage_len_lt_of_step hlen_bound hinv0.res hbs0) (fun hcap_eq => hinv0s.fits_reserve x.v hcap_eq)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by dsimp [FSave]; sep_ac_rfl) ?_
    intro s2 cap1 ptr1 v48_1 v40_1 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 hge1 hpres1 hstep1
    have hinv1 := hinv0s.step (byte := varintContByte x.val) hge1 hpres1 hstep1
    have hcap1 := hcap0s.step (byte := varintContByte x.val) hstep1
    cases hult1 : (x.val >>> 7).ult 128#64
    · simp only [hult1, ↓reduceIte, Bool.false_eq_true] at hpc2 hx0_2
      have hbs2 := encodeVarint_step_bs (nextV := x.val >>> 14) hbs1 hult1 (ushr_ushr_7 x.val 7 14)
      have hrem1 := rem_len_step hbs1 hbs2; have hinv1s := hinv1.of_rem_eq hrem1; have hcap1s := hcap1.of_rem_eq hrem1
      refine step_encVarint4_s2_placed (F := FSave) A lim H hdoReserve x.val x.v cap1 ptr1 s0.sp v48_1 v40_1 _ _
        (stage_len_lt_of_step hlen_bound hinv1.res hbs1) (fun hcap_eq => hinv1s.fits_reserve x.v hcap_eq)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 rfl ?_
      intro s3 cap2 ptr2 v48_2 v40_2 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 hge2 hpres2 hstep2
      have hinv2 := hinv1s.step (byte := varintContByte (x.val >>> 7)) hge2 hpres2 hstep2
      have hcap2 := hcap1s.step (byte := varintContByte (x.val >>> 7)) hstep2
      cases hult2 : (x.val >>> 14).ult 128#64
      · simp only [hult2, ↓reduceIte, Bool.false_eq_true] at hpc3 hx0_3
        have hbs3 := encodeVarint_step_bs (nextV := x.val >>> 21) hbs2 hult2 (ushr_ushr_7 x.val 14 21)
        have hrem2 := rem_len_step hbs2 hbs3; have hinv2s := hinv2.of_rem_eq hrem2; have hcap2s := hcap2.of_rem_eq hrem2
        refine step_encVarint4_s3_placed (F := FSave) A lim H hdoReserve x.val x.v cap2 ptr2 s0.sp v48_2 v40_2 _ _
          (stage_len_lt_of_step hlen_bound hinv2.res hbs2) (fun hcap_eq => hinv2s.fits_reserve x.v hcap_eq)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 rfl ?_
        intro s4 cap3 ptr3 v48_3 v40_3 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 hge3 hpres3 hstep3
        have hinv3 := hinv2s.step (byte := varintContByte (x.val >>> 14)) hge3 hpres3 hstep3
        have hcap3 := hcap2s.step (byte := varintContByte (x.val >>> 14)) hstep3
        cases hult3 : (x.val >>> 21).ult 128#64
        · simp only [hult3, ↓reduceIte, Bool.false_eq_true] at hpc4 hx0_4
          have hbs4 := encodeVarint_step_bs (nextV := x.val >>> 28) hbs3 hult3 (ushr_ushr_7 x.val 21 28)
          have hrem3 := rem_len_step hbs3 hbs4
          have hinv3s := hinv3.of_rem_eq hrem3
          have hcap3s := hcap3.of_rem_eq hrem3
          refine step_encVarint4_s4_placed (F := FSave) A lim H hdoReserve
            x.val x.v cap3 ptr3 s0.sp v48_3 v40_3 _ _
            (stage_len_lt_of_step hlen_bound hinv3.res hbs3)
            (fun hcap_eq => hinv3s.fits_reserve x.v hcap_eq)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 rfl ?_
          intro s5 cap4 ptr4 v48_4 v40_4 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 hge4 hpres4 hstep4
          have hinv4 := hinv3s.step (byte := varintContByte (x.val >>> 21)) hge4 hpres4 hstep4
          have hcap4 := hcap3s.step (byte := varintContByte (x.val >>> 21)) hstep4
          cases hult4 : (x.val >>> 28).ult 128#64
          · simp only [hult4, ↓reduceIte, Bool.false_eq_true] at hpc5 hx0_5
            have hbs5 := encodeVarint_step_bs (nextV := x.val >>> 35) hbs4 hult4 (ushr_ushr_7 x.val 28 35)
            have hrem4 := rem_len_step hbs4 hbs5
            have hinv4s := hinv4.of_rem_eq hrem4
            have hcap4s := hcap4.of_rem_eq hrem4
            refine step_encVarint4_s5_placed (F := FSave) A lim H hdoReserve
              x.val x.v cap4 ptr4 s0.sp v48_4 v40_4 _ _
              (stage_len_lt_of_step hlen_bound hinv4.res hbs4)
              (fun hcap_eq => hinv4s.fits_reserve x.v hcap_eq)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 rfl ?_
            intro s6 cap5 ptr5 v48_5 v40_5 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6 hge5 hpres5 hstep5
            have hinv5 := hinv4s.step (byte := varintContByte (x.val >>> 28)) hge5 hpres5 hstep5
            have hcap5 := hcap4s.step (byte := varintContByte (x.val >>> 28)) hstep5
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6 hx0_6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              have hrem5 := rem_len_step hbs5 hbs6
              have hinv5s := hinv5.of_rem_eq hrem5
              have hcap5s := hcap5.of_rem_eq hrem5
              refine step_encVarint4_s6_placed (F := FSave) A lim H hdoReserve
                x.val x.v cap5 ptr5 s0.sp v48_5 v40_5 _ _
                (stage_len_lt_of_step hlen_bound hinv5.res hbs5)
                (fun hcap_eq => hinv5s.fits_reserve x.v hcap_eq)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx12_6 hcs6 rfl ?_
              intro s7 cap6 ptr6 v48_6 v40_6 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7 hge6 hpres6 hstep6
              have hinv6 := hinv5s.step (byte := varintContByte (x.val >>> 35)) hge6 hpres6 hstep6
              have hcap6 := hcap5s.step (byte := varintContByte (x.val >>> 35)) hstep6
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7 hx0_7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                have hrem6 := rem_len_step hbs6 hbs7
                have hinv6s := hinv6.of_rem_eq hrem6
                have hcap6s := hcap6.of_rem_eq hrem6
                refine step_encVarint4_s7_placed (F := FSave) A lim H hdoReserve
                  x.val x.v cap6 ptr6 s0.sp v48_6 v40_6 _ _
                  (stage_len_lt_of_step hlen_bound hinv6.res hbs6)
                  (fun hcap_eq => hinv6s.fits_reserve x.v hcap_eq)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx11_7 hx12_7 hcs7 rfl ?_
                intro s8 cap7 ptr7 v48_7 v40_7 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 hge7 hpres7 hstep7
                have hinv7 := hinv6s.step (byte := varintContByte (x.val >>> 42)) hge7 hpres7 hstep7
                have hcap7 := hcap6s.step (byte := varintContByte (x.val >>> 42)) hstep7
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8 hx0_8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  have hrem7 := rem_len_step hbs7 hbs8
                  have hinv7s := hinv7.of_rem_eq hrem7
                  have hcap7s := hcap7.of_rem_eq hrem7
                  refine step_encVarint4_s8_placed (F := FSave) A lim H hdoReserve
                    x.val x.v cap7 ptr7 s0.sp v48_7 v40_7 _ _
                    (stage_len_lt_of_step hlen_bound hinv7.res hbs7)
                    (fun hcap_eq => hinv7s.fits_reserve x.v hcap_eq)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl ?_
                  intro s9 cap8 ptr8 v48_8 v40_8 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9 hge8 hpres8 hstep8
                  have hinv8 := hinv7s.step (byte := varintContByte (x.val >>> 49)) hge8 hpres8 hstep8
                  have hcap8 := hcap7s.step (byte := varintContByte (x.val >>> 49)) hstep8
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9 hx0_9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    have hrem8 := rem_len_step hbs8 hbs9
                    have hinv8s := hinv8.of_rem_eq hrem8
                    have hcap8s := hcap8.of_rem_eq hrem8
                    refine step_encVarint4_s9_placed
                      (F := ((s0.sp - 48#64) ↦₆₄ v48_8) ∗ ((s0.sp - 40#64) ↦₆₄ v40_8) ∗ FSave)
                      A lim H hdoReserve x.val x.v cap8 ptr8 s0.sp _ _ hult8
                      (stage_len_lt_of_step hlen_bound hinv8.res hbs8)
                      (fun hcap_eq => hinv8s.fits_reserve x.v hcap_eq)
                      hpc9 hrun9 hsp9 halign htr9 hx1_9 hx8_9 hx9_9 hx10_9 hx12_9 hcs9 (by sep_ac_rfl) ?_
                    intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 hge9 hpres9 hstep9
                    have hinv9 := hinv8s.step (byte := varintContByte (x.val >>> 56)) hge9 hpres9 hstep9
                    have hcap9 := hcap8s.step (byte := varintContByte (x.val >>> 56)) hstep9
                    have hbs_exit := encodeVarint_exit_bs_s9 hbs9 hult8
                    have hrem9 := rem_len_exit hbs9 hbs_exit
                    exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 _ 1#64 cap9 ptr9 v48_8 v40_8 _
                      (hinv9.of_rem_eq hrem9) (hcap9.of_rem_eq hrem9) hbs_exit
                      (stage_len_lt_of_exit hlen_bound hinv9.res hbs_exit)
                      hpc10 hrun10 hsp10 halign htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 (by dsimp [FSave]; sep_ac_rfl)
                  · simp only [hult8, ↓reduceIte] at hpc9 hx0_9
                    have hbs_exit := encodeVarint_exit_bs hbs8 hult8
                    have hrem8 := rem_len_exit hbs8 hbs_exit
                    exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 56) cap8 ptr8 v48_8 v40_8 _
                      (hinv8.of_rem_eq hrem8) (hcap8.of_rem_eq hrem8) hbs_exit
                      (stage_len_lt_of_exit hlen_bound hinv8.res hbs_exit)
                      hpc9 hrun9 hsp9 halign htr9 hx0_9 hx1_9 hx8_9 hx9_9 hcs9 rfl
                · simp only [hult7, ↓reduceIte] at hpc8 hx0_8
                  have hbs_exit := encodeVarint_exit_bs hbs7 hult7
                  have hrem7 := rem_len_exit hbs7 hbs_exit
                  exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 49) cap7 ptr7 v48_7 v40_7 _
                    (hinv7.of_rem_eq hrem7) (hcap7.of_rem_eq hrem7) hbs_exit
                    (stage_len_lt_of_exit hlen_bound hinv7.res hbs_exit)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hcs8 rfl
              · simp only [hult6, ↓reduceIte] at hpc7 hx0_7
                have hbs_exit := encodeVarint_exit_bs hbs6 hult6
                have hrem6 := rem_len_exit hbs6 hbs_exit
                exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 42) cap6 ptr6 v48_6 v40_6 _
                  (hinv6.of_rem_eq hrem6) (hcap6.of_rem_eq hrem6) hbs_exit
                  (stage_len_lt_of_exit hlen_bound hinv6.res hbs_exit)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hcs7 rfl
            · simp only [hult5, ↓reduceIte] at hpc6 hx0_6
              have hbs_exit := encodeVarint_exit_bs hbs5 hult5
              have hrem5 := rem_len_exit hbs5 hbs_exit
              exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 35) cap5 ptr5 v48_5 v40_5 _
                (hinv5.of_rem_eq hrem5) (hcap5.of_rem_eq hrem5) hbs_exit
                (stage_len_lt_of_exit hlen_bound hinv5.res hbs_exit)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hcs6 rfl
          · simp only [hult4, ↓reduceIte] at hpc5 hx0_5
            have hbs_exit := encodeVarint_exit_bs hbs4 hult4
            have hrem4 := rem_len_exit hbs4 hbs_exit
            exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 28) cap4 ptr4 v48_4 v40_4 _
              (hinv4.of_rem_eq hrem4) (hcap4.of_rem_eq hrem4) hbs_exit
              (stage_len_lt_of_exit hlen_bound hinv4.res hbs_exit)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hcs5 rfl
        · simp only [hult3, ↓reduceIte] at hpc4 hx0_4
          have hbs_exit := encodeVarint_exit_bs hbs3 hult3
          have hrem3 := rem_len_exit hbs3 hbs_exit
          exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 21) cap3 ptr3 v48_3 v40_3 _
            (hinv3.of_rem_eq hrem3) (hcap3.of_rem_eq hrem3) hbs_exit
            (stage_len_lt_of_exit hlen_bound hinv3.res hbs_exit)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hcs4 rfl
      · simp only [hult2, ↓reduceIte] at hpc3 hx0_3
        have hbs_exit := encodeVarint_exit_bs hbs2 hult2
        have hrem2 := rem_len_exit hbs2 hbs_exit
        exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 14) cap2 ptr2 v48_2 v40_2 _
          (hinv2.of_rem_eq hrem2) (hcap2.of_rem_eq hrem2) hbs_exit
          (stage_len_lt_of_exit hlen_bound hinv2.res hbs_exit)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hcs3 rfl
    · simp only [hult1, ↓reduceIte] at hpc2 hx0_2
      have hbs_exit := encodeVarint_exit_bs hbs1 hult1
      have hrem1 := rem_len_exit hbs1 hbs_exit
      exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 7) cap1 ptr1 v48_1 v40_1 _
        (hinv1.of_rem_eq hrem1) (hcap1.of_rem_eq hrem1) hbs_exit
        (stage_len_lt_of_exit hlen_bound hinv1.res hbs_exit)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hcs2 rfl
  · simp only [hult0, ↓reduceIte] at hpc1
    have hbs_exit := encodeVarint_exit_bs hbs0 hult0
    have hrem0 := rem_len_exit hbs0 hbs_exit
    exact step_encVarint4_det_exit_placed hres A lim H hdoReserve x st0 st0 x.val x.cap x.ptr v48 v40 x.bs
      (hinv0.of_rem_eq hrem0) (hcap0.of_rem_eq hrem0) hbs_exit
      (stage_len_lt_of_exit hlen_bound hinv0.res hbs_exit)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by sep_ac_rfl)

theorem encodeVarint4_det_placed_ok_of_doReserve [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320)
      (withLsCodeLoaded lsmpl (doReserveSpecOf resStack A lim))) :
    subroutine_ok (lsProg_292 H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp
  intro (x, st0) R s0 hpc0 hrun0 hpre hsp0
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcode0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encodeVarint4_det_gen_placed_ok A lim H hres x st0 R s0
    (doReserve7_with_placed_of_ok A lim s0 hcode0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

theorem encode_varint4_det_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_292).rebase (blkPl_292).base H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpec A lim)) :=
  encodeVarint4_det_placed_ok_of_doReserve (resStack := doReserveStack) (by decide) A lim H
    (ls_subroutine_ok_of_block (callerProg := lsProg_292 H) (do_reserve_7_placed_ok h_panic hshim halloc hrealloc))

theorem encode_varint4_det_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_292).rebase (blkPl_292).base H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecX A lim)) :=
  encodeVarint4_det_placed_ok_of_doReserve (resStack := doReserveStackX) (by decide) A lim H
    (ls_subroutine_ok_of_block (callerProg := lsProg_292 H) (do_reserve_7_placed_ok_x h_panic hshim halloc hrealloc))

theorem encodeVarint4_fit_placed_ok_of_doReserve [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    (hdoReserve : subroutine_ok (lsProg_292 H) (lsmpl.base 320)
      (withLsCodeLoaded lsmpl (doReserveSpecOf resStack A lim))) :
    subroutine_ok (lsProg_292 H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A lim)) :=
  subroutine_ok_withLsCodeLoaded_encodeVarintFit_of_det (encodeVarint4_det_placed_ok_of_doReserve hres A lim H hdoReserve)

theorem encode_varint4_fit_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeVarint4FitPlacedOk A lim H :=
  subroutine_ok_withLsCodeLoaded_encodeVarintFit_of_det (encode_varint4_det_placed_ok h_panic hshim halloc hrealloc)

theorem encode_varint4_fit_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeVarint4FitPlacedOkX A lim H :=
  subroutine_ok_withLsCodeLoaded_encodeVarintFit_of_det (encode_varint4_det_placed_ok_x h_panic hshim halloc hrealloc)

theorem encodeVarintSpecOf_of_encodeVarintFitSpecOf [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {resStack : Nat} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeVarintFitSpecOf resStack A lim))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (encodeVarintSpecOf resStack A lim)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hsp =>
    h.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withLsCodeLoaded] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
  refine ⟨hpre.1, ?_⟩; have hpre2 := hpre.2
  simp only [encodeVarintSpecOf, encodeVarintFitSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hpre2 ⊢
  exact ⟨⟨hpre2.1.1, hpre2.1.2.1,
    hpre2.1.2.2.1.imp (fun hle => by have := (encodeVarint_length_bounds x.val).2; omega) id,
    hpre2.1.2.2.2⟩, hpre2.2⟩

theorem encode_varint4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_292).rebase (blkPl_292).base H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)) :=
  encodeVarintSpecOf_of_encodeVarintFitSpecOf (encode_varint4_fit_placed_ok h_panic hshim halloc hrealloc)

theorem encode_varint4_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked) (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_292).rebase (blkPl_292).base H) (blkPl_292).base
      (withLsCodeLoaded lsmpl (encodeVarintSpecX A lim)) :=
  encodeVarintSpecOf_of_encodeVarintFitSpecOf (encode_varint4_fit_placed_ok_x h_panic hshim halloc hrealloc)

end LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4Budget
