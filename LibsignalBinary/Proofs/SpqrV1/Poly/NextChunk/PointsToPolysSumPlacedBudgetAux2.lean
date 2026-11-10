/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
public meta import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded `Vec<Poly>` Deallocation

Relocatable `[LibsignalPlacement]` verification of `basisElemDeallocLoop_placed_sepWP`
(`+3948 -> +3976`) and `lagrangeSumCleanup_placed_sepWP` (`+3908 -> +4004`) threading
`RustCliAllocBudget M`, `BudgetLimits`, and `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux2

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement blkPC_416 blkPl_416 lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.LibsignalSpqrV1 (Poly)
open CryptoVerification.SpqrV1.Poly (polyListOf)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (basisVecAt beq_m1_one_sum_pl
   exists_pow_two_eq_eight_sm_pl exists_pow_two_eq_two_sm_pl
   mul24_ofNat_sum_nat_pl mul24_ofNat_sum_pl ofNat_pos_ne_zero
   polyHeader_entails_memRegion24 polyListOf_cons_fbl polyOf_entails_dealloc_sum_pl
   shl_one_cap_toNat_nat sub1_ofNat_sum_add_pl sub1_ofNat_sum_pl)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
  (sepWP_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
  (AllocContractsPlaced)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem fs_setMem_pre (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
private theorem sigActions_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem brkStart_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).brkStart = s.brkStart := by cases s; rfl
private theorem oracle_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).oracle = s.oracle := by cases s; rfl
private theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  exists_pow_two_eq_two_sm_pl exists_pow_two_eq_eight_sm_pl
  sub1_ofNat_sum_pl sub1_ofNat_sum_add_pl mul24_ofNat_sum_pl mul24_ofNat_sum_nat_pl
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

set_option maxHeartbeats 800000 in
/-- Budget-threaded element-by-element deallocation loop (`+3948 -> +3976`) over
    `polyListOf A.repAlloc base polysRest`, emitting a `FreeOnlyEvs` event sequence. -/
theorem basisElemDeallocLoop_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext) :
    ∀ (polysRest : List Poly) (n : Nat) {st : M.σ}
      (hrest_ne : polysRest ≠ [])
      (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
      (hrest_bound : polysRest.length ≤ n)
      (hplen : ∀ p ∈ polysRest, p.coefficients.length = n)
      (s : State) (fsp base : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
      (hpc : s.pc = (blkPl_416).base + 3948#64)
      (hrun : s.status = .Running) (hsp : s.sp = fsp)
      (hx20 : s.readReg64 .x20 = base + 8#64)
      (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 polysRest.length)
      (hcont : ∀ (evs : List AllocEvent) (s1 : State),
        FreeOnlyEvs evs →
        s1.pc = (blkPl_416).base + 3976#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x19 = s.readReg64 .x19 →
        s1.readReg64 .x24 = s.readReg64 .x24 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = s.readReg64 .x27 →
        s1.readReg64 .x28 = s.readReg64 .x28 →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
          (A.pool lim (M.stepEvents evs st) s1 ∗
           memRegion base (24 * polysRest.length) ∗
           stackAt fsp allocHookStack ∗ Frame) post),
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
        (A.pool lim st s ∗
         polyListOf A.repAlloc base polysRest ∗
         stackAt fsp allocHookStack ∗ Frame) post
  | [], _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | p :: pTail, n, st, _, hn_pos, hn, hrest_bound, hplen, s, fsp, base, hfsp_align, Frame,
    hpc, hrun, hsp, hx20, hx25, hcont => by
    have hp_len : p.coefficients.length = n := hplen p (List.mem_cons_self ..)
    have htail_len : ∀ q ∈ pTail, q.coefficients.length = n :=
      fun q hq => hplen q (List.mem_cons_of_mem p hq)
    have hdealloc := hA.dealloc_ok
    dsimp only [rustCliDeallocBudgetSpec] at hdealloc
    have hsub1 := sub1_ofNat_sum_pl pTail.length
    have hsub1_add := sub1_ofNat_sum_add_pl pTail.length
    have hbeq1 := beq_m1_one_sum_pl (m := pTail.length) (by simp at hrest_bound; omega)
    have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
    rw [polyListOf_cons_fbl]
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left
        (polyOf_entails_dealloc_sum_pl A.repAlloc base p n hn_pos hp_len)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
    apply SepWP.exists_elim; intro cap
    apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; rintro ⟨hcap_lt, hptr, hcap⟩
    have hcap_bne : ¬(cap == 0#64) = true := by simpa [beq_iff_eq] using hcap
    have hcap_eq0 : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    have hcap_shl := shl_one_cap_toNat_nat hcap_lt
    have hcap2_toNat : (BitVec.ofNat 64 (cap.toNat * 2)).toNat = cap.toNat * 2 :=
      Nat.mod_eq_of_lt (by omega)
    rw [show (p :: pTail).length = pTail.length + 1 by simp] at hx25
    try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
    apply sepWP_seg_416 (mid := lsρ spqrRustDeallocSym)
    intro _m_strip0
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hcap_eq0, Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hcap_eq0, Bool.false_eq_true, ↓reduceIte])
      fun _m_real0 _hnsp0 => ?_
    refine SepWP.transport_budgetPool
      (_hnsp0.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hcap_eq0, Bool.false_eq_true, ↓reduceIte]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    wp_conv_pre => simp only [arm64_norm, wp_norm, hrun, hsp, hx20]
    wp_call hdealloc (ptr, cap.toNat * 2, 2, st)
    clear hdealloc
    have htr_sf : sf.trace = s.trace := by
      have ht := (by assumption : AllocCallPreserved _ sf).2.1
      simpa [arm64_norm, wp_norm, hsp] using ht
    have hsp_sf : sf.sp = fsp := by
      simp only [arm64_norm, wp_norm, hsp, *]
    have hx20_sf : sf.readReg64 (Reg.gpr 20#5) = base + 8#64 := by
      simp only [arm64_norm, wp_norm, Reg.x20, hsp, hx20, *]
    have hx25_sf : sf.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 (pTail.length + 1) := by
      simp only [arm64_norm, wp_norm, Reg.x25, hsp, hx25, *]
    have hevs0 : FreeOnlyEvs (rustDeallocEvents (cap.toNat * 2) 2) :=
      FreeOnlyEvs.singleton 2 (cap.toNat * 2)
    have hhdr24 := polyHeader_entails_memRegion24 base cap ptr (BitVec.ofNat 64 n)
    cases pTail with
    | nil =>
      apply sepWP_seg_416 (mid := (blkPl_416).base + 3976#64)
      intro _m_strip1
      wp_steps 4
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_nil, decide_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_nil, decide_true, ↓reduceIte])
        fun _m_real1 _hnsp1 => ?_
      refine SepWP.transport_budgetPool
        (_hnsp1.toVmPreserved
          (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_nil, decide_true, ↓reduceIte]))
        (hnext := ?_)
      simp only [State.setMem_setMem]
      have h24_1 : 24 * [p].length = 24 := rfl
      rw [h24_1] at hcont
      simp only [polyListOf, arrayAt, sepConj_emp]
      refine SepWP.weaken_pre ?_
        (hcont (rustDeallocEvents (cap.toNat * 2) 2) _ hevs0
          (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_nil, decide_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_nil, decide_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf])
          (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, htr_sf])
          (by simp only [arm64_norm, wp_norm, hrun, hrun_sf, hsp, hsp_sf, *])
          (by simp only [arm64_norm, wp_norm, Reg.x19, hrun, hrun_sf, hsp, hsp_sf, *])
          (by simp only [arm64_norm, wp_norm, Reg.x24, hrun, hrun_sf, hsp, hsp_sf, *])
          (by simp only [arm64_norm, wp_norm, Reg.x26, hrun, hrun_sf, hsp, hsp_sf, *])
          (by simp only [arm64_norm, wp_norm, Reg.x27, hrun, hrun_sf, hsp, hsp_sf, *])
          (by simp only [arm64_norm, wp_norm, Reg.x28, hrun, hrun_sf, hsp, hsp_sf, *])
          (by simp only [arm64_norm, wp_norm, Reg.x29, hrun, hrun_sf, hsp, hsp_sf, *]))
      try simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf]
      refine Entails.trans (Entails.of_eq (show _ =
        ((base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗ ((base + 16#64) ↦₆₄ BitVec.ofNat 64 n)) ∗
        (A.pool lim (M.stepEvents (rustDeallocEvents (cap.toNat * 2) 2) st) _ ∗
         stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hhdr24) (Entails.of_eq (by sep_ac_rfl))
    | cons p2 pTail' =>
      apply sepWP_seg_416 (mid := (blkPl_416).base + 3948#64)
      intro _m_strip1
      wp_steps 4
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_cons,
              Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_cons,
              Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
        fun _m_real1 _hnsp1 => ?_
      refine SepWP.transport_budgetPool
        (_hnsp1.toVmPreserved
          (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_cons,
                Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte]))
        (hnext := ?_)
      simp only [State.setMem_setMem]
      have hne' : p2 :: pTail' ≠ [] := List.cons_ne_nil _ _
      have hbound' : (p2 :: pTail').length ≤ n := by simp at hrest_bound ⊢; omega
      have hbase20 : base + 8#64 + 24#64 = (base + 24#64) + 8#64 := by bv_omega
      refine SepWP.weaken_pre ?_
        (basisElemDeallocLoop_placed_sepWP hA (p2 :: pTail') n
          (st := M.stepEvents (rustDeallocEvents (cap.toNat * 2) 2) st)
          hne' hn_pos hn hbound' htail_len
          _ fsp (base + 24#64) hfsp_align
          (memRegion base 24 ∗ Frame)
          (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_cons,
                Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq1, List.length_cons,
                Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf])
          (by simp only [arm64_norm, wp_norm, Reg.x20, hrun_sf, hsp_sf, hx20_sf, hbase20])
          (by simp only [arm64_norm, wp_norm, Reg.x25, hrun_sf, hsp_sf, hx25_sf, hsub1, hsub1_add]) ?_)
      · try simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf]
        refine Entails.trans (Entails.of_eq (show _ =
          ((base ↦₆₄ cap) ∗ ((base + 8#64) ↦₆₄ ptr) ∗ ((base + 16#64) ↦₆₄ BitVec.ofNat 64 n)) ∗
          (A.pool lim (M.stepEvents (rustDeallocEvents (cap.toNat * 2) 2) st) _ ∗
           polyListOf A.repAlloc (base + 24#64) (p2 :: pTail') ∗
           stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hhdr24) (Entails.of_eq (by sep_ac_rfl))
      · intro evsTail s1 hevsTail hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx24_1 hx26_1 hx27_1 hx28_1 hx29_1
        have hjoin :
            memRegion base 24 ∗ memRegion (base + 24#64) (24 * (p2 :: pTail').length) =
            memRegion base (24 * (p :: p2 :: pTail').length) := by
          have hm : 24 * (p :: p2 :: pTail').length = 24 + 24 * (p2 :: pTail').length := by
            simp [Nat.mul_add]; omega
          rw [hm, ProofLib.memRegion_split' (b := base) (n := 24) (k := 24 * (p2 :: pTail').length)
            (b' := base + 24#64) rfl (by bv_omega) (by simp at hrest_bound; omega)]
        have hstep_app :
            M.stepEvents evsTail (M.stepEvents (rustDeallocEvents (cap.toNat * 2) 2) st) =
              M.stepEvents (rustDeallocEvents (cap.toNat * 2) 2 ++ evsTail) st :=
          (M.stepEvents_append _ _ st).symm
        refine SepWP.weaken_pre
          (by rw [← hjoin, hstep_app]; exact Entails.of_eq (by sep_ac_rfl))
          (hcont (rustDeallocEvents (cap.toNat * 2) 2 ++ evsTail) s1
            (FreeOnlyEvs.append hevs0 hevsTail)
            hpc1 hrun1 hsp1
            (by rw [htr1]; simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, htr_sf])
            (by rw [hvregs1]; simp only [arm64_norm, wp_norm, hrun, hrun_sf, hsp, hsp_sf, *])
            (by rw [hx19_1]; simp only [arm64_norm, wp_norm, Reg.x19, hrun, hrun_sf, hsp, hsp_sf, *])
            (by rw [hx24_1]; simp only [arm64_norm, wp_norm, Reg.x24, hrun, hrun_sf, hsp, hsp_sf, *])
            (by rw [hx26_1]; simp only [arm64_norm, wp_norm, Reg.x26, hrun, hrun_sf, hsp, hsp_sf, *])
            (by rw [hx27_1]; simp only [arm64_norm, wp_norm, Reg.x27, hrun, hrun_sf, hsp, hsp_sf, *])
            (by rw [hx28_1]; simp only [arm64_norm, wp_norm, Reg.x28, hrun, hrun_sf, hsp, hsp_sf, *])
            (by rw [hx29_1]; simp only [arm64_norm, wp_norm, Reg.x29, hrun, hrun_sf, hsp, hsp_sf, *]))

set_option maxHeartbeats 800000 in
/-- Budget-threaded cleanup block of `Poly::lagrange_sum` (`+3908 -> +4004`):
    copies `[fsp + 664..680]` (`accPtr, n`) to `[fsp + 640..656]`, deallocates each element of
    `basisVecAt A.repAlloc basisPtr polys`, and deallocates `basisPtr` (`24 * n` bytes, align `8`),
    emitting a `FreeOnlyEvs` event sequence. -/
theorem lagrangeSumCleanup_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (polys : List Poly) (n : Nat)
    (hpolys_ne : polys ≠ []) (hpolys_len : polys.length = n)
    (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
    (hplen : ∀ p ∈ polys, p.coefficients.length = n)
    (s : State) (fsp accPtr basisPtr ptVecPtr cIdx v27 u640 u648 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 3908#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ (evs : List AllocEvent) (s1 : State),
      FreeOnlyEvs evs →
      s1.pc = (blkPl_416).base + 4004#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 n →
      s1.readReg64 .x20 = cIdx →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim (M.stepEvents evs st) s1 ∗
         ((fsp + 16#64) ↦₆₄ cIdx) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 640#64) ↦₆₄ accPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       basisVecAt A.repAlloc basisPtr polys ∗
       ((fsp + 16#64) ↦₆₄ cIdx) ∗
       ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗
       ((fsp + 648#64) ↦₆₄ u648) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  have hdealloc := hA.dealloc_ok
  dsimp only [rustCliDeallocBudgetSpec] at hdealloc
  obtain ⟨hn_ne0, _⟩ := ofNat_pos_ne_zero hn_pos hn
  have hn_eq0 : (BitVec.ofNat 64 n == 0#64) = false := hn_ne0
  have h24n_toNat : (BitVec.ofNat 64 (24 * n)).toNat = 24 * n := Nat.mod_eq_of_lt (by omega)
  have h8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl
  unfold basisVecAt
  simp only [sepConj_pure_left_comm, hpolys_len, sepConj_assoc]
  apply SepWP.pure_elim; intro hbasis_ne
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
  apply sepWP_seg_416 (mid := (blkPl_416).base + 3948#64)
  intro _m_strip0
  wp_steps 7
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hx25, hn_eq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hx25, hn_eq0, Bool.false_eq_true, ↓reduceIte])
    fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx25, hn_eq0, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.weaken_pre
    (by try simp only [arm64_norm, wp_norm, hrun, hsp]
        exact Entails.of_eq (by sep_ac_rfl))
    (basisElemDeallocLoop_placed_sepWP hA polys n (st := st)
      hpolys_ne hn_pos hn (by omega) hplen
      _ fsp basisPtr hfsp_align
      (A.repAlloc.live basisPtr (24 * n) 8 ∗
       ((fsp + 16#64) ↦₆₄ cIdx) ∗
       ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 640#64) ↦₆₄ accPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame)
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx25, hn_eq0, Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx25, hn_eq0, Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, Reg.x20, hrun, hsp, hx24])
      (by simp only [arm64_norm, wp_norm, Reg.x25, hrun, hsp, hx25, hpolys_len]) ?_)
  intro evs1 s1 hevs1 hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx24_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [hpolys_len]
  have hx19_s1 : s1.readReg64 .x19 = BitVec.ofNat 64 n := by
    rw [hx19_1]; simp only [arm64_norm, wp_norm, Reg.x19, hrun, hsp]
  have hx24_s1 : s1.readReg64 .x24 = basisPtr := by
    rw [hx24_1]; simp only [arm64_norm, wp_norm, Reg.x24, hrun, hsp, hx24]
  have hx26_s1 : s1.readReg64 .x26 = ptVecPtr := by
    rw [hx26_1]; simp only [arm64_norm, wp_norm, Reg.x26, hrun, hsp, hx26]
  have hx27_s1 : s1.readReg64 .x27 = v27 := by
    rw [hx27_1]; simp only [arm64_norm, wp_norm, Reg.x27, hrun, hsp, hx27]
  have hx28_s1 : s1.readReg64 .x28 = 24#64 := by
    rw [hx28_1]; simp only [arm64_norm, wp_norm, Reg.x28, hrun, hsp, hx28]
  have hx29_s1 : s1.readReg64 .x29 = fsp + 1104#64 := by
    rw [hx29_1]; simp only [arm64_norm, wp_norm, Reg.x29, hrun, hsp, hx29]
  apply sepWP_seg_416 (mid := lsρ spqrRustDeallocSym)
  intro _m_strip1
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hrun1, hsp1, hx19_s1, hx24_s1, hn_eq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hrun1, hsp1, hx19_s1, hx24_s1, hn_eq0, Bool.false_eq_true, ↓reduceIte])
    fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hrun1, hsp1, hx19_s1, hx24_s1, hn_eq0, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_conv_pre => simp only [arm64_norm, wp_norm, hrun1, hsp1]
  wp_call hdealloc (basisPtr, 24 * n, 8, M.stepEvents evs1 st)
  clear hdealloc
  have htr_sf : sf.trace = s.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf).2.1
    rw [show s.trace = s1.trace by symm; rw [htr1]; simp only [arm64_norm, wp_norm]]
    simpa [arm64_norm, wp_norm, hsp1] using ht
  have hsp_sf : sf.sp = fsp := by
    simp only [arm64_norm, wp_norm, hsp1, *]
  have hstep_app :
      M.stepEvents (rustDeallocEvents (24 * n) 8) (M.stepEvents evs1 st) =
        M.stepEvents (evs1 ++ rustDeallocEvents (24 * n) 8) st :=
    (M.stepEvents_append _ _ st).symm
  have hevs_all : FreeOnlyEvs (evs1 ++ rustDeallocEvents (24 * n) 8) :=
    FreeOnlyEvs.append hevs1 (FreeOnlyEvs.singleton 8 (24 * n))
  refine SepWP.weaken_pre
    (by rw [hstep_app, hsp1]; exact Entails.of_eq (by sep_ac_rfl))
    (hcont (evs1 ++ rustDeallocEvents (24 * n) 8) sf hevs_all hpc_sf hrun_sf hsp_sf htr_sf
      (by rw [hvregs, hvregs1]; simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, Reg.x19, hrun1, hsp1, hx19_s1, *])
      (by simp only [arm64_norm, wp_norm, Reg.x20, hrun1, hsp1, *])
      (by simp only [arm64_norm, wp_norm, Reg.x26, hrun1, hsp1, hx26_s1, *])
      (by simp only [arm64_norm, wp_norm, Reg.x27, hrun1, hsp1, hx27_s1, *])
      (by simp only [arm64_norm, wp_norm, Reg.x28, hrun1, hsp1, hx28_s1, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, hrun1, hsp1, hx29_s1, *]))

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux2
