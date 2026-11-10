/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.Base
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-threaded helpers for `SessionStructure::encode_raw`

Defines the segment allocation envelope `EncRawSegEnv` and relocatable `[LibsignalPlacement]`
call wrappers for block `14` (`lsProg_14 H`), threading `LibsignalCodeLoaded`, `VmPreserved`, and
`A.pool lim st`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open CryptoGames.LibsignalSession (ReceiverChain)
open CryptoVerification (
  LibsignalPlacement lsmpl LibsignalCodeLoaded withLsCodeLoaded sepWP_mono_lscl
  ls_subroutine_ok_of_block subroutine_ok_withLsCodeLoaded_of_plain
  lsMemcpySym lsρ ls_hook_ok_of_mem blkPC_10 blkPl_10 blkPC_13 blkPl_13
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchet (reserveCap DoReserveCall)
open CryptoVerification.LibsignalTripleRatchet.Prost (encodeVarintStack EncodeVarintGhost)
open CryptoVerification.E2E.Record (lenField)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 lsProg_14)
open CryptoVerification.E2E.Record.Serialization (
  encodeChainStack encChainMem protoChainAt EncodeChainGhost
)
open CryptoVerification.E2E.Record.Serialization.EncodeRawAux (
  entails_of_sep_focus satisfies_of_sep_focus
  encodeRawSubStack stackAt_sub_to_encodeVarint_er stackAt_sub_to_doReserve_er
  stackAt_sub_to_encodeChain vecU8At_expose_slice chainAt_eq_protoChainAt_er
  reserveCap_bounds_add
)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv SeqEnv rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (
  BoundedRustEvs EncodeChainEnv encodeChainSpec
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.BaseBudget (
  sepWPp_call_lscl_noPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (
  pushByteStep pushBytesEvents encodeVarintEvents EncodeVarintEnv encodeVarintSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents doReserveSpec doReserveSpecWithStack framelessMemcpyBudgetSpec
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `BoundedRustEvs` and `EncRawSegEnv` composition -/

theorem boundedRustEvs_of_seqEnv {c₁ c₂ r₁ r₂ : Nat} {evs : List AllocEvent}
    (h : SeqEnv (BoundedRustEvs c₁ r₁) (BoundedRustEvs c₂ r₂) evs) :
    BoundedRustEvs (c₁ + c₂) (max r₁ r₂) evs := by
  rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
  · exact h1.mono (Nat.le_add_right _ _) (Nat.le_max_left _ _)
  · exact h1.append h2

theorem boundedRustEvs_rustAlloc1 {newCap maxReq : Nat}
    (hpos : 1 ≤ newCap) (hmax : newCap ≤ MallocngMaxAllocSize) (hreq : newCap ≤ maxReq) :
    BoundedRustEvs 1 maxReq (rustAllocEvents newCap 1) := by
  have hcond : 1 ≤ 16 ∧ 1 ≤ newCap := ⟨by decide, hpos⟩
  simp only [BoundedRustEvs, rustAllocEvents, hcond, and_self, ↓reduceIte,
    List.length_singleton, Nat.le_refl, true_and, List.mem_singleton]
  rintro _ rfl
  exact ⟨hmax, hreq, fun _ _ h => AllocEvent.noConfusion h, fun _ _ _ h => AllocEvent.noConfusion h⟩

theorem boundedRustEvs_rustRealloc1 {oldCap newCap maxReq : Nat}
    (hpos : 1 ≤ newCap) (hmax : newCap ≤ MallocngMaxAllocSize) (hreq : newCap ≤ maxReq) :
    BoundedRustEvs 1 maxReq (rustReallocEvents oldCap newCap 1) := by
  have hcond : 1 ≤ 16 ∧ 1 ≤ newCap := ⟨by decide, hpos⟩
  simp only [BoundedRustEvs, rustReallocEvents, hcond, and_self, ↓reduceIte,
    List.length_singleton, Nat.le_refl, true_and, List.mem_singleton]
  rintro _ rfl
  refine ⟨hmax, hreq, fun _ _ h => AllocEvent.noConfusion h, fun al _ _ h => ?_⟩
  injection h with hal _ _
  subst hal
  decide

private theorem reserveCap_le_maxReq {cap len add outLen : Nat}
    (hcap : cap ≤ outLen) (hlen : len + add ≤ outLen) :
    reserveCap cap len add ≤ 2 * outLen + 16 := by
  unfold reserveCap
  omega

private theorem two_mul_add_16_le_mallocngMax {outLen : Nat} (hlt : outLen < 2 ^ 61) :
    2 * outLen + 16 ≤ MallocngMaxAllocSize := by
  unfold MallocngMaxAllocSize
  omega

theorem doReserveEnv_sub_boundedRustEvs {x : DoReserveCall} {outLen : Nat}
    (hcap : x.cap.toNat ≤ outLen)
    (hlen : x.bs.length + x.additional ≤ outLen)
    (hout : outLen < 2 ^ 61)
    {evs : List AllocEvent} (hevs : DoReserveEnv x evs) :
    BoundedRustEvs 1 (2 * outLen + 16) evs := by
  rw [hevs]
  unfold doReserveEvents
  dsimp only
  have hpos : 1 ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
    unfold reserveCap; omega
  have hreq : reserveCap x.cap.toNat x.bs.length x.additional ≤ 2 * outLen + 16 :=
    reserveCap_le_maxReq hcap hlen
  have hmax : reserveCap x.cap.toNat x.bs.length x.additional ≤ MallocngMaxAllocSize :=
    Nat.le_trans hreq (two_mul_add_16_le_mallocngMax hout)
  split
  · exact boundedRustEvs_rustAlloc1 hpos hmax hreq
  · exact boundedRustEvs_rustRealloc1 hpos hmax hreq

private theorem pushBytesEvents_bounded :
    ∀ (n cap len outLen : Nat),
      len + n ≤ outLen →
      outLen < 2 ^ 61 →
      BoundedRustEvs n (2 * outLen + 16) (pushBytesEvents n cap len)
  | 0, _, _, outLen, _, _ => BoundedRustEvs.nil 0 (2 * outLen + 16)
  | n + 1, cap, len, outLen, hlen, hout => by
    unfold pushBytesEvents pushByteStep
    by_cases hlt : len < cap
    · simp only [hlt, ↓reduceIte, List.nil_append]
      exact (pushBytesEvents_bounded n cap (len + 1) outLen (by omega) hout).mono
        (by omega) (Nat.le_refl _)
    · simp only [hlt, ↓reduceIte]
      have hcap_le : cap ≤ outLen := by omega
      have hpos : 1 ≤ reserveCap cap len 1 := by unfold reserveCap; omega
      have hreq : reserveCap cap len 1 ≤ 2 * outLen + 16 :=
        reserveCap_le_maxReq hcap_le (by omega)
      have hmax : reserveCap cap len 1 ≤ MallocngMaxAllocSize :=
        Nat.le_trans hreq (two_mul_add_16_le_mallocngMax hout)
      have hstep : BoundedRustEvs 1 (2 * outLen + 16)
          (if cap = 0 then rustAllocEvents (reserveCap cap len 1) 1
           else rustReallocEvents cap (reserveCap cap len 1) 1) := by
        split
        · exact boundedRustEvs_rustAlloc1 hpos hmax hreq
        · exact boundedRustEvs_rustRealloc1 hpos hmax hreq
      have hrest := pushBytesEvents_bounded n (reserveCap cap len 1) (len + 1) outLen (by omega) hout
      have happ := hstep.append hrest
      rw [Nat.max_self] at happ
      exact happ.mono (by omega) (Nat.le_refl _)

theorem encodeVarint_length_pos (v : BitVec 64) :
    1 ≤ (encodeVarint v).length := by
  unfold encodeVarint encodeVarintAux
  split <;> simp

theorem encodeVarintEnv_sub_boundedRustEvs {x : EncodeVarintGhost} {outLen : Nat}
    (hlen : x.bs.length + (encodeVarint x.val).length ≤ outLen)
    (hout : outLen < 2 ^ 61)
    {evs : List AllocEvent} (hevs : EncodeVarintEnv x evs) :
    BoundedRustEvs (encodeVarint x.val).length (2 * outLen + 16) evs := by
  rw [hevs]
  exact pushBytesEvents_bounded (encodeVarint x.val).length x.cap.toNat x.bs.length outLen hlen hout

/-- Segment-level `BoundedRustEvs` envelope for non-chain `encode_raw` steps appending `addedLen`
bytes onto a `bsLen`-byte prefix. -/
def EncRawSegEnv (bsLen addedLen : Nat) (evs : List AllocEvent) : Prop :=
  BoundedRustEvs (4 * addedLen) (2 * (bsLen + addedLen) + 16) evs

theorem encRawSegEnv_nil (bsLen addedLen : Nat) :
    EncRawSegEnv bsLen addedLen [] :=
  BoundedRustEvs.nil _ _

theorem encRawSegEnv_mono {bs₁ a₁ bs₂ a₂ : Nat} {evs : List AllocEvent}
    (ha : a₁ ≤ a₂) (hout : bs₁ + a₁ ≤ bs₂ + a₂)
    (h : EncRawSegEnv bs₁ a₁ evs) :
    EncRawSegEnv bs₂ a₂ evs :=
  h.mono (by omega) (by omega)

theorem encRawSegEnv_append {bsLen a₁ a₂ : Nat} {evs₁ evs₂ : List AllocEvent}
    (h1 : EncRawSegEnv bsLen a₁ evs₁)
    (h2 : EncRawSegEnv (bsLen + a₁) a₂ evs₂) :
    EncRawSegEnv bsLen (a₁ + a₂) (evs₁ ++ evs₂) := by
  have happ := h1.append h2
  refine happ.mono (by omega) ?_
  omega

theorem fitsEnv_encRawSeg_left {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bsLen a₁ a₂ : Nat}
    (h : FitsEnv M lim st (EncRawSegEnv bsLen (a₁ + a₂))) :
    FitsEnv M lim st (EncRawSegEnv bsLen a₁) :=
  h.mono fun _ h1 => encRawSegEnv_mono (by omega) (by omega) h1

theorem fitsEnv_encRawSeg_right {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bsLen a₁ a₂ : Nat} {evs₁ : List AllocEvent}
    (h : FitsEnv M lim st (EncRawSegEnv bsLen (a₁ + a₂)))
    (h1 : EncRawSegEnv bsLen a₁ evs₁) :
    FitsEnv M lim (M.stepEvents evs₁ st) (EncRawSegEnv (bsLen + a₁) a₂) := by
  have hseq : FitsEnv M lim st
      (SeqEnv (EncRawSegEnv bsLen a₁) (EncRawSegEnv (bsLen + a₁) a₂)) := by
    refine h.mono fun evs hs => ?_
    rcases hs with h_only | ⟨e1, e2, rfl, he1, he2⟩
    · exact encRawSegEnv_mono (by omega) (by omega) h_only
    · exact encRawSegEnv_append he1 he2
  exact hseq.seq_right h1

theorem fitsEnv_doReserve_of_encRawSeg {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : DoReserveCall} {bsLen addedLen : Nat}
    (ha_pos : 1 ≤ addedLen)
    (hcap : x.cap.toNat ≤ bsLen + addedLen)
    (hlen : x.bs.length + x.additional ≤ bsLen + addedLen)
    (hout : bsLen + addedLen < 2 ^ 61)
    (h : FitsEnv M lim st (EncRawSegEnv bsLen addedLen)) :
    FitsEnv M lim st (DoReserveEnv x) :=
  h.mono fun _ hevs =>
    (doReserveEnv_sub_boundedRustEvs hcap hlen hout hevs).mono (by omega) (Nat.le_refl _)

theorem fitsEnv_encodeVarint_of_encRawSeg {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : EncodeVarintGhost} {bsLen addedLen : Nat}
    (ha : (encodeVarint x.val).length ≤ addedLen)
    (hlen : x.bs.length + (encodeVarint x.val).length ≤ bsLen + addedLen)
    (hout : bsLen + addedLen < 2 ^ 61)
    (h : FitsEnv M lim st (EncRawSegEnv bsLen addedLen)) :
    FitsEnv M lim st (EncodeVarintEnv x) :=
  h.mono fun _ hevs =>
    (encodeVarintEnv_sub_boundedRustEvs hlen hout hevs).mono (by omega) (Nat.le_refl _)

/-! ## Relocatable `[LibsignalPlacement]` call wrappers (block `14`) -/

/-- Lifts a `SepWP` basic block into `SepWPp` while threading `LibsignalCodeLoaded` and `VmPreserved`. -/
theorem sepWPp_of_sepWP_lscl_vm_er {prog : Program} {pl : MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      VmPreserved s sm ∧
        (LibsignalCodeLoaded pl sm.mem → VmPreserved s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm ⟨hvm, hnext⟩ => hnext hclm hvm)

abbrev sepWPp_call_lscl_noPanic_er := @sepWPp_call_lscl_noPanic

theorem encraw_call_doReserve_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)))
    (sp0 v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8)) (add : Nat)
    (st : M.σ)
    (hcap_le : cap.toNat ≤ bs.length + add)
    (hlen_lt : bs.length + add < 2 ^ 62)
    (hfit : FitsEnv M lim st (DoReserveEnv (DoReserveCall.mk v cap ptr bs add)))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 13)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v)
    (hx1 : (s.readReg64 .x1).toNat = bs.length)
    (hx2 : (s.readReg64 .x2).toNat = add)
    (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (newCap p' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      DoReserveEnv (DoReserveCall.mk v cap ptr bs add) evs →
      bs.length + add ≤ newCap.toNat →
      newCap.toNat < 2 ^ 63 →
      SepWPp (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc v newCap p' bs ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_14 H) ret s P Q Qp := by
  have hcall : subroutine_ok (lsProg_14 H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec M A lim)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hDR
  obtain ⟨hres_bound, hnew_ge, hnew_lt⟩ := reserveCap_bounds_add hcap_le hlen_lt
  refine sepWPp_call_lscl_noPanic (x := (DoReserveCall.mk v cap ptr bs add, st))
    (F := memRegion (sp0 - 80#64 - 17104#64) 12896 ∗ F)
    hcall hpc hrun halign hcl hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_doReserve_er (sp0 - 80#64)] at hm
    simp only [doReserveSpec, doReserveSpecWithStack, hsp,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hres_bound, hfit⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    dsimp only [doReserveSpec, doReserveSpecWithStack]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun p' => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_
      (hnext sm (BitVec.ofNat 64 (reserveCap cap.toNat bs.length add)) p'
        (doReserveEvents (DoReserveCall.mk v cap ptr bs add))
        hpcm hrunm hclm hspm htrm' hcsm rfl hnew_ge hnew_lt)
    rw [stackAt_sub_to_doReserve_er (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_encodeVarint_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)))
    (sp0 val v cap ptr ret_pc : BitVec 64) (bs : List (BitVec 8))
    (st : M.σ)
    (hlen_lt : bs.length + 10 < 2 ^ 62)
    (hfit : FitsEnv M lim st (EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 10)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩ evs →
      SepWPp (lsProg_14 H) ret sm
        ((vecU8At A.repAlloc v cap' ptr' (bs ++ encodeVarint val) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_14 H) ret s P Q Qp := by
  have hcall : subroutine_ok (lsProg_14 H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A lim)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hEV
  refine sepWPp_call_lscl_noPanic (x := (⟨val, v, cap, ptr, bs⟩, st))
    (F := memRegion (sp0 - 80#64 - 17104#64) 12848 ∗ F)
    hcall hpc hrun halign hcl hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeVarint_er (sp0 - 80#64)] at hm
    simp only [encodeVarintSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, Or.inr hlen_lt, hfit⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [encodeVarintSpec, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun cap' =>
      SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.pure_elim fun _ => ?_
    have hPullEvs :
        (vecU8At A.repAlloc v cap' ptr' (bs ++ encodeVarint val) ∗
          ⌜EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩ evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeVarintStack ∗
          memRegion (sp0 - 80#64 - 17104#64) 12848 ∗ F) =
        (⌜EncodeVarintEnv ⟨val, v, cap, ptr, bs⟩ evs⌝ ∗
          ((vecU8At A.repAlloc v cap' ptr' (bs ++ encodeVarint val) ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)) := by
      rw [stackAt_sub_to_encodeVarint_er (sp0 - 80#64)]
      sep_ac_rfl
    rw [hPullEvs]
    refine SepWPp.pure_elim fun hevs => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    exact hnext sm cap' ptr' evs hpcm hrunm hclm hspm htrm' hcsm hevs

theorem encraw_call_memcpy_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hmc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (v cap ptr srcPtr ret_pc : BitVec 64) (bs payload : List (BitVec 8))
    (st : M.σ)
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0#64)
    (hne : payload ≠ [])
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsρ lsMemcpySym)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = ptr + BitVec.ofNat 64 bs.length)
    (hx1 : s.readReg64 .x1 = srcPtr)
    (hx2 : (s.readReg64 .x2).toNat = payload.length)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs ∗ (srcPtr ↦ₛ payload) ∗ A.pool lim st s) ∗ F := by sep_focus)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = s.sp →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      SepWPp (lsProg_14 H) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
            (cap.toNat - bs.length - payload.length) ∗
          (srcPtr ↦ₛ payload) ∗ A.pool lim st sm) ∗ F)
        Q Qp) :
    SepWPp (lsProg_14 H) ret s P Q Qp := by
  have hcall : subroutine_ok (lsProg_14 H) (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl framelessMemcpyBudgetSpec) :=
    subroutine_ok_withLsCodeLoaded_of_plain (ls_hook_ok_of_mem (prog := lsProg_14 H) hmc)
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  refine sepWPp_call_lscl_noPanic (x := (ptr + BitVec.ofNat 64 bs.length, srcPtr, payload))
    (F := ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
             (cap.toNat - bs.length - payload.length) ∗
           A.pool lim st s) ∗ F)
    hcall hpc hrun halign hcl hlr ?_ ?_
  · intro R' hm
    rw [hP, vecU8At_expose_slice A.repAlloc v cap ptr bs payload.length hle hcap hptr hpos] at hm
    simp only [framelessMemcpyBudgetSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hclm hcsm
    simp only [framelessMemcpyBudgetSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm, hvm⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    rw [← A.pool_of_vmPreserved hvm]
    refine SepWPp.weaken_pre ?_ (hnext sm hvm hpcm hrunm hclm hspm htrm' hcsm)
    exact entails_of_sep_focus (by sep_focus)

/-- Envelope-parameterized `encode::<Chain>` specification (`encodeChainSpec` when `chainEnv := EncodeChainEnv`). -/
def encodeChainSpecWithEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (chainEnv : EncodeChainGhost → List AllocEvent → Prop) :
    Spec (EncodeChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 ∧
      FitsEnv M lim st (chainEnv x)⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp encodeChainStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ chainEnv x evs⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ lenField x.tag (encChainMem x.gc))) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp encodeChainStack

theorem encodeChainSpecWithEnv_eq (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    encodeChainSpecWithEnv M A lim EncodeChainEnv = encodeChainSpec M A lim := rfl

theorem encraw_call_protoEncodeChain_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {chainEnv : EncodeChainGhost → List AllocEvent → Prop}
    {H : String → Option (State → State)}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecWithEnv M A lim chainEnv)))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (st : M.σ)
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    (hfit : FitsEnv M lim st (chainEnv ⟨tag, a, gc, v, cap, ptr, bs⟩))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 12)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (protoChainAt A.repAlloc gc a ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      chainEnv ⟨tag, a, gc, v, cap, ptr, bs⟩ evs →
      SepWPp (lsProg_14 H) ret sm
        ((protoChainAt A.repAlloc gc a ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_14 H) ret s P Q Qp := by
  have hcall : subroutine_ok (lsProg_14 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecWithEnv M A lim chainEnv)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_14 H) hEC
  refine sepWPp_call_lscl_noPanic (x := (⟨tag, a, gc, v, cap, ptr, bs⟩, st))
    (F := memRegion (sp0 - 80#64 - 17104#64) 8464 ∗ F)
    hcall hpc hrun halign hcl hlr ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_encodeChain (sp0 - 80#64)] at hm
    simp only [encodeChainSpecWithEnv, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, htag, hlen_lt, hfit⟩, ?_⟩
    apply satisfies_of_sep_focus hm
    sep_focus
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [encodeChainSpecWithEnv, hsp, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun cap' =>
      SepWPp.exists_elim fun ptr' => ?_
    refine SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    have htrm' : sm.trace = s0.trace := htrm.trans htr
    refine SepWPp.weaken_pre ?_ (hnext sm cap' ptr' evs hpcm hrunm hclm hspm htrm' hcsm hevs)
    rw [stackAt_sub_to_encodeChain (sp0 - 80#64)]
    exact entails_of_sep_focus (by sep_focus)

theorem encraw_call_encodeChain_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {chainEnv : EncodeChainGhost → List AllocEvent → Prop}
    {H : String → Option (State → State)}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpecWithEnv M A lim chainEnv)))
    (tag : Nat) (sp0 a v cap ptr ret_pc : BitVec 64)
    (gc : ChainGhost × ReceiverChain) (bs : List (BitVec 8))
    (st : M.σ)
    (htag : tag = 6 ∨ tag = 7)
    (hlen_lt : bs.length + (lenField tag (encChainMem gc)).length < 2 ^ 32)
    (hfit : FitsEnv M lim st (chainEnv ⟨tag, a, gc, v, cap, ptr, bs⟩))
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 12)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 80#64)
    (halign : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (chainAt A.repAlloc gc a ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F := by sep_focus)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64) (evs : List AllocEvent),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 80#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      chainEnv ⟨tag, a, gc, v, cap, ptr, bs⟩ evs →
      SepWPp (lsProg_14 H) ret sm
        ((chainAt A.repAlloc gc a ∗
          vecU8At A.repAlloc v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F)
        Q Qp) :
    SepWPp (lsProg_14 H) ret s P Q Qp := by
  have hP' : P = (protoChainAt A.repAlloc gc a ∗ vecU8At A.repAlloc v cap ptr bs ∗
      A.pool lim st s ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
      (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F) := by
    rw [hP, chainAt_eq_protoChainAt_er A.repAlloc gc a]; sep_ac_rfl
  refine encraw_call_protoEncodeChain_env_placed hEC tag sp0 a v cap ptr ret_pc gc bs st
    htag hlen_lt hfit hpc hrun hcl hsp halign htr hlr hx0 hx1 hx2 hP' ?_
  intro sm cap' ptr' evs hpcm hrunm hclm hspm htrm hcsm hevs
  have hPostEq :
      ((protoChainAt A.repAlloc gc a ∗
        vecU8At A.repAlloc v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗
        (⌜gc.1.srk.bytes.length = 33 ∧ gc.1.priv.bytes = []⌝ ∗ F)) =
      ((chainAt A.repAlloc gc a ∗
        vecU8At A.repAlloc v cap' ptr' (bs ++ lenField tag (encChainMem gc)) ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (sp0 - 80#64) encodeRawSubStack) ∗ F) := by
    rw [chainAt_eq_protoChainAt_er A.repAlloc gc a]; sep_ac_rfl
  rw [hPostEq]
  exact hnext sm cap' ptr' evs hpcm hrunm hclm hspm htrm hcsm hevs

abbrev encraw_call_protoEncodeChain_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpec M A lim))) :=
  @encraw_call_protoEncodeChain_env_placed _ M A lim EncodeChainEnv H hEC

abbrev encraw_call_encodeChain_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hEC : subroutine_ok (lsProg_12 H) (blkPl_12).base
      (withLsCodeLoaded lsmpl (encodeChainSpec M A lim))) :=
  @encraw_call_encodeChain_env_placed _ M A lim EncodeChainEnv H hEC

end LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
