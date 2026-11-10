/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Envelopes, Epilogues, and Cache-Hit Exit for `Dir::get`

Defines the `DirGetEnv` allocator event envelopes matching `DirGhost.get`, `VmPreserved` lifts for
`bcmp` and `memcpy`, and the budget-threaded epilogues and cache-hit exit on Block 589.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SignalSession.Cli.Get.Helpers
open CryptoVerification.SignalSession.Cli.Get.PlacedHelpers
  (HighCalleeSaved arrayAt_dirEntry_cons call_lscro_frame cstk_le_pow64 ite_false_eq
   lt_pow64_of_lt_pow32 lt_pow64_of_lt_pow63 ofNat64_toNat_of_lt32 ofNat64_toNat_of_lt63
   pure_sepConj_pure_assoc sepWPp_exists_left sepWPp_pure_mid2
   sepWPp_unfold_vecU8 seq_lscro_state spAligned_of_sp_eq subroutine_ok_lscro_withFsInv
   vecBuf_dirEntry_expose)
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ChainProofs (bytesAt bytesAt_false bytesAt_true)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli dealloc_lscro_of_cli session_memcpy_region_lscro_of_cli
   shim_lscro_of_cli)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `Dir::get` `AllocEvent` Envelopes & `find?` Lookup Lemmas -/

/-- Path-construction `AllocEvent` envelope on a cache miss in `Dir::get`:
    clones `name` (`allocBytes1Events name`) when `dirPath = []`, and runs `PathEnv dirPath name`
    when `dirPath ≠ []`. -/
def DirGetPathEnv (PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (dirPath name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  if dirPath = [] then evs = allocBytes1Events name else PathEnv dirPath name evs

/-- Post-`read_file` error-allocation `AllocEvent` envelope on a cache miss in `Dir::get`:
    `[]` on `.ok _` and `rustAllocEvents 22 1` (`"file could not be read"`) on `.error ()`. -/
def DirGetErrAllocEnv (rd : ReadRule) (F0 : FsFiles) (pth : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  match rd F0 pth with
  | .ok _ => evs = []
  | .error () => evs = rustAllocEvents 22 1

/-- Post-`read_file` `AllocEvent` envelope including optional `FreeOnlyEvs` temporary path-buffer
    deallocation. -/
def DirGetAfterReadEnv (rd : ReadRule) (F0 : FsFiles) (pth : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (DirGetErrAllocEnv rd F0 pth) FreeOnlyEvs

/-- Cache-miss `AllocEvent` envelope of `Dir::get`: `DirGetPathEnv` followed by `ReadEnv` and
    `DirGetAfterReadEnv`. -/
def DirGetMissEnv
    (PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (DirGetPathEnv PathEnv dir.path name)
    (SeqEnv (ReadEnv F0 (CryptoVerification.SignalSession.Cli.pathOf dir.path name))
      (DirGetAfterReadEnv rd F0 (CryptoVerification.SignalSession.Cli.pathOf dir.path name)))

/-- Composed `AllocEvent` envelope of `Dir::get` (`Block 589`), matching `DirGhost.get`:
    on a cache hit `d.changed.find? (fun e => e.1 == name) = some e`, clones `e.2`
    (`allocBytes1Events e.2`); on a cache miss (`none`), runs `DirGetMissEnv`. -/
def DirGetEnv
    (PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (rd : ReadRule) (F0 : FsFiles) (d : DirGhost) (name : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  match d.changed.find? (fun e => e.1 == name) with
  | some e => evs = allocBytes1Events e.2
  | none => DirGetMissEnv PathEnv ReadEnv rd F0 d name evs

theorem find?_append_cons_eq (name bs : List (BitVec 8))
    (rest : List (List (BitVec 8) × List (BitVec 8))) :
    ∀ (pre : List (List (BitVec 8) × List (BitVec 8))),
      (∀ e ∈ pre, e.1 ≠ name) →
      (pre ++ (name, bs) :: rest).find? (fun e => e.1 == name) = some (name, bs)
  | [], _ => by simp
  | hd :: tl, hne => by
    have hhd : (hd.1 == name) = false := beq_false_of_ne (hne hd List.mem_cons_self)
    simp only [List.cons_append, List.find?_cons, hhd]
    exact find?_append_cons_eq name bs rest tl (fun e he => hne e (List.mem_cons_of_mem _ he))

theorem find?_eq_none_of_forall_ne (name : List (BitVec 8)) :
    ∀ (ch : List (List (BitVec 8) × List (BitVec 8))),
      (∀ e ∈ ch, e.1 ≠ name) →
      ch.find? (fun e => e.1 == name) = none
  | [], _ => rfl
  | hd :: tl, hne => by
    have hhd : (hd.1 == name) = false := beq_false_of_ne (hne hd List.mem_cons_self)
    simp only [List.find?_cons, hhd]
    exact find?_eq_none_of_forall_ne name tl (fun e he => hne e (List.mem_cons_of_mem _ he))

theorem dirGetEnv_of_hit
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {F0 : FsFiles} {d : DirGhost} {name bs : List (BitVec 8)}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    (hch : d.changed = pre ++ (name, bs) :: rest)
    (hne : ∀ e ∈ pre, e.1 ≠ name) :
    DirGetEnv PathEnv ReadEnv rd F0 d name = (· = allocBytes1Events bs) := by
  funext evs
  unfold DirGetEnv
  rw [hch, find?_append_cons_eq name bs rest pre hne]

theorem dirGetEnv_of_miss
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {F0 : FsFiles} {d : DirGhost} {name : List (BitVec 8)}
    (hne : ∀ e ∈ d.changed, e.1 ≠ name) :
    DirGetEnv PathEnv ReadEnv rd F0 d name = DirGetMissEnv PathEnv ReadEnv rd F0 d name := by
  funext evs
  unfold DirGetEnv
  rw [find?_eq_none_of_forall_ne name d.changed hne]

/-! ## 2. `VmPreserved`-Strengthened `bcmp` & `memcpy` Lifts on Block `589` -/

theorem bcmp_lscro_vm_ok_at_589 [LibsignalPlacement] {H : LibsignalHooks}
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec)) :
    subroutine_ok (lsProg_589 H) (lsρ cliBcmpName)
      (StoreKit.withLsCodeRoLoaded lsmpl (withVmPreserved cliBcmpSpec)) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_ultra_of_mem (prog := lsProg_589 H) (i := 589) hBcmp (by decide))

theorem memcpy_bytesAt_lscro_vm_ok_at_589 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (ro : Bool) :
    subroutine_ok (lsProg_589 H) (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (withStack (withVmPreserved (sessionMemcpyBytesAtSpec ro)) extHookStack)) := by
  cases ro
  · have hmc := session_memcpy_region_lscro_of_cli (callerProg := lsProg_589 H)
      (stk := extHookStack) hC
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec extHookStack)).pre
          (dst, src, bs) s0 ∗ R := by
      apply CryptoVerification.SignalSession.Cli.Store.PlacedCommon.satisfies_lscro_pre hcrl0
      simp only [withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, bytesAt_false,
        sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1⟩, hpre0.2⟩
    refine hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [StoreKit.withLsCodeRoLoaded, withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
        bytesAt_false, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl ⟨‹_›, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨‹_›, ‹_›, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨‹_›, hoom⟩))
  · have hmc_ro : subroutine_ok (lsProg_589 H) (lsρ memcpyName)
        (withVmPreserved sessionMemcpyRegionROSpec) :=
      ls_hook_ok_ultra_of_mem (prog := lsProg_589 H) (i := 589) hRO (by decide)
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    obtain ⟨_hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (withVmPreserved sessionMemcpyRegionROSpec).pre (dst, src, bs) s0 ∗
          (stackAt s0.sp extHookStack ∗ R) := by
      simp only [withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionROSpec, bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨hpre0.1, hpre0.2⟩
    refine hmc_ro.mono_outcome (dst, src, bs) (stackAt s0.sp extHookStack ∗ R)
        s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simp only [StoreKit.withLsCodeRoLoaded, withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionROSpec, bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, hpost.2⟩
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpan
      exact False.elim hpan.1
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hex
      exact False.elim hex.1
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hoom
      exact False.elim hoom.1

/-! ## 3. Postcondition & Panic Helpers for `SpecsPlacedBudget.dirGetSpecPlaced` -/

def dirGetPostQPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) (x : DirGetGhost) (st0 : M.σ) (s0 : State)
    (Fr R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ Fr) →
      (sf.mem ⊨ (SpecsPlacedBudget.dirGetSpecPlaced rd pathOk A lim GetEnv stk).post (x, st0) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def dirGetPanicQpPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (stk : Nat) (x : DirGetGhost) (st0 : M.σ) (s0 : State)
    (Fr R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ Fr) →
      (sf.mem ⊨ (SpecsPlacedBudget.dirGetSpecPlaced rd pathOk A lim GetEnv stk).onPanic (x, st0) s0 sf ∗ R)

theorem dirGetPostQPlacedBudget_perm [LibsignalPlacement] {M : AllocCostModel}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {stk : Nat} {x : DirGetGhost} {st0 : M.σ} {s0 sf : State}
    {Fr R P1 P2 : SepProp}
    (h : dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0 Fr R sf P2)
    (heq : P1 = P2) :
    dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0 Fr R sf P1 :=
  heq ▸ h

theorem dirGetPanicQpBudget_false [LibsignalPlacement] {M : AllocCostModel}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {stk : Nat} {x : DirGetGhost} {st0 : M.σ} {s0 sf : State}
    {Fr R F' : SepProp} :
    dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0 Fr R sf (⌜False⌝ ∗ F') := by
  intro hm
  exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hm))

theorem false_of_fsInv_false_budget {F0 : FsFiles} {T0 : List TraceEvent} {sf : State}
    {m : Memory} {R : SepProp}
    (h : m ⊨ (⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ R) : False := by
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at h
  exact h.2.1

theorem panicQpBudget_of_fsInv_false [LibsignalPlacement] {M : AllocCostModel}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {stk : Nat} {x : DirGetGhost} {st0 : M.σ} {s0 sf : State} {Fr R : SepProp}
    {F0 : FsFiles} {T0 : List TraceEvent} {Frame : SepProp} :
    dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0 Fr R sf
      ((⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ Frame) :=
  fun hm => False.elim (false_of_fsInv_false_budget (by rw [sepConj_assoc] at hm; exact hm))

theorem dirGetPostQBudget_of_ret [LibsignalPlacement] {M : AllocCostModel}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {evs : List AllocEvent}
    {s0 sf : State} {r : Except Unit (List (BitVec 8))} {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace ∧
      GetEnv s0.fs.files x.dir x.name evs)
    (hsp : sf.sp = s0.sp) (hcs : CalleeSavedPreserved s0 sf) :
    dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
      (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R sf
      ((getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗ memRegion (s0.sp - 112#64) 112 ∗
        A.pool lim (M.stepEvents evs st0) sf) ∗ Extra) := by
  refine ⟨fun hm => ?_, hsp, hcs⟩
  have hperm :
      ((getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
          bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 112#64) cstk ∗ memRegion (s0.sp - 112#64) 112 ∗
          A.pool lim (M.stepEvents evs st0) sf) ∗ Extra) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) =
      (getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗
          stackAt (s0.sp - 112#64) cstk ∗ memRegion (s0.sp - 112#64) 112) ∗
        A.pool lim (M.stepEvents evs st0) sf) ∗
      (Extra ∗ R) := by sep_ac_rfl
  rw [hperm] at hm
  have hm1 := Satisfies.drop_mid hm
  have hjoin := stackAt_dirGet_join s0.sp hstk hfull
  have hm2 : sf.mem ⊨
      (getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st0) sf) ∗ R :=
    Satisfies.mono
      (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hjoin)))))
      hm1
  have hex :
      getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st0) sf ⊢
      (SpecsPlacedBudget.dirGetSpecPlaced rd pathOk A lim GetEnv stk).post (x, st0) s0 sf := by
    dsimp only [SpecsPlacedBudget.dirGetSpecPlaced, StoreKit.withLsCodeRoLoaded]
    refine Entails.trans ?_ (Entails.sepExists_intro evs)
    refine sepConj_mono ?_ (Entails.refl _)
    refine Entails.trans (Entails.pure_right hres (Entails.refl _)) ?_
    exact Entails.sepExists_intro
      (P := fun r' =>
        ⌜r' = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace ∧
          GetEnv s0.fs.files x.dir x.name evs⌝ ∗
          getResultAt A.repAlloc x.ret r') r
  exact Satisfies.mono (sepConj_mono_left hex) hm2

/-! ## 4. Shared Epilogues (`+284` and `+464`) on Block `589` -/

theorem step_epilogue_284_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {evs : List AllocEvent}
    {s0 s : State} {r : Except Unit (List (BitVec 8))}
    {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpc : s.pc = (blkPl_589).base + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace ∧
      GetEnv s0.fs.files x.dir x.name evs) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.pool lim (M.stepEvents evs st0) s) ∗ Extra)
      (dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  unfold savedRegsAt
  apply SepWPp.of_sepWP_ret
  dsimp only [lsProg_589]
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.fold (frame_0x70_join (s0.sp - 112#64) s0) (by unfold savedRegsAt; sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine dirGetPostQPlacedBudget_perm
    (dirGetPostQBudget_of_ret (evs := evs) (r := r) (Extra := Extra)
      hstk hfull ?_ (by simp only [wp_norm, arm64_norm]) ?_)
    (by sep_ac_rfl)
  · exact ⟨hres.1, by simp only [wp_norm, arm64_norm, hres.2.1], hres.2.2⟩
  · exact ⟨by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simpa only [wp_norm, arm64_norm] using hhcs.1,
           by simpa only [wp_norm, arm64_norm] using hhcs.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs.2.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs.2.2.2.1,
           by simp only [wp_norm, arm64_norm],
           by simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hhcs.2.2.2.2⟩

theorem step_dealloc_epilogue_464_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {evs_pre : List AllocEvent}
    {s0 s : State} {r : Except Unit (List (BitVec 8))}
    {pathCap pathPtr pathLenW : BitVec 64} {Extra R : SepProp}
    (hC : AllocContractsXCliPlaced A lim H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 464#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx1 : s.readReg64 .x1 = pathCap)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hcap_ne : pathCap ≠ 0#64) (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace ∧
      GetEnv s0.fs.files x.dir x.name (evs_pre ++ rustDeallocEvents pathCap.toNat 1)) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((getResultAt A.repAlloc x.ret r ∗ dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ pathLenW) ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.repAlloc.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
        A.pool lim (M.stepEvents evs_pre st0) s) ∗ Extra)
      (dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_589 H) hC
  clear hC
  have hcap_pos : 0 < pathCap.toNat := by
    by_contra h0
    have hz : pathCap.toNat = 0 := by omega
    exact hcap_ne (BitVec.eq_of_toNat_eq (by simpa using hz))
  have hlay : RustLayoutOk pathCap.toNat 1 := ⟨⟨hcap_pos, ⟨0, rfl⟩, by omega⟩, by omega⟩
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
  refine seq_lscro_state (mid := lsρ lsRustDeallocSymCli) hcrl ?_
  dsimp only [lsProg_589]
  wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  dsimp only [RustCliAllocBudget.repAlloc]
  refine call_lscro_frame (x := (pathPtr, pathCap.toNat, 1, M.stepEvents evs_pre st0))
    (T := A.pool lim (M.stepEvents evs_pre st0) _ ∗
      A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
      stackAt (s0.sp - 112#64) extHookStack)
    hdealloc hcrl1 (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [wp_norm, arm64_norm] using hsp_al)
    (by wp_norm_lhs)
    (by dsimp only [TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
          LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
          LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
        simp only [wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm],
                hlay,
                by simp (config := { decide := true }) only [Reg.x30, Reg.lr, wp_norm, arm64_norm]⟩)
    (by sep_frame)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ => dirGetPanicQpBudget_false)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 _ => ?_)
  dsimp only [TripleRatchet.Hooks2Budget.rustDeallocExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
  simp only [wp_norm, hsp, sepConj_assoc, ← M.stepEvents_append]
  refine SepWPp.pure_left fun htr1 => ?_
  have hhcs1 : HighCalleeSaved s0 sf1 :=
    hhcs.of_step_call hcs1
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
  have hsp1_eq : sf1.sp = s0.sp - 112#64 := by
    rw [hsp1]; simp only [wp_norm, arm64_norm, *]
  have htr1_s : sf1.trace = s.trace := htr1
  have hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ pathLenW) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64 + 24#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 24#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  have hcstk_join :
      memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
        stackAt (s0.sp - 112#64) extHookStack ⊢
      stackAt (s0.sp - 112#64) cstk := by
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    exact Entails.refl _
  unfold savedRegsAt
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.fold hp24 (by sep_frame)
  apply SepWP.fold hcstk_join (by sep_frame)
  apply SepWP.fold (frame_0x70_join (s0.sp - 112#64) s0) (by unfold savedRegsAt; sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine dirGetPostQPlacedBudget_perm
    (dirGetPostQBudget_of_ret (evs := evs_pre ++ rustDeallocEvents pathCap.toNat 1) (r := r) (Extra := Extra)
      hstk hfull ?_ (by simp only [wp_norm, arm64_norm]) ?_)
    (by dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl)
  · exact ⟨hres.1, by simp only [wp_norm, arm64_norm, htr1_s, hres.2.1], hres.2.2⟩
  · exact ⟨by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simpa only [wp_norm, arm64_norm] using hhcs1.1,
           by simpa only [wp_norm, arm64_norm] using hhcs1.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs1.2.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs1.2.2.2.1,
           by simp only [wp_norm, arm64_norm],
           by simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hhcs1.2.2.2.2⟩

/-! ## 5. Cache-Hit Exit (`+112`) on Block `589` -/

theorem step_hit_exit_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {s0 s : State}
    {changedCap changedPtr : BitVec 64}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {bs : List (BitVec 8)} {Extra R : SepProp}
    (hC : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hfit0 : FitsEnv M lim st0 (DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name))
    (hGetEnv : ∀ evs, DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name evs →
      GetEnv s0.fs.files x.dir x.name evs)
    (hchanged : x.dir.changed = pre ++ ((x.name, bs) :: rest))
    (hne : ∀ e ∈ pre, e.1 ≠ x.name)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 112#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx23 : s.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
        arrayAt (dirEntryAt A.repAlloc) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 24#64) x.dir.path) ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 s) ∗ Extra)
      (dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hget : x.dir.get rd s0.fs.files x.name = .ok bs := by
    cases hdir : x.dir with | mk p ch =>
    simp only [hdir] at hchanged ⊢
    rw [hchanged, dirGhost_get_append_of_ne pre ((x.name, bs) :: rest) p rd s0.fs.files x.name hne,
        dirGhost_get_cons_eq]
  have hEnv_eq := dirGetEnv_of_hit (PathEnv := PathEnv) (ReadEnv := ReadEnv)
    (rd := rd) (F0 := s0.fs.files) hchanged hne
  have hrepack_dir :
      (vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
        arrayAt (dirEntryAt A.repAlloc) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48))) ∗
        strRefAt (x.self + 24#64) x.dir.path ⊢
      dirAt A.repAlloc x.self x.dir := by
    have hentry_eq :
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
          arrayAt (dirEntryAt A.repAlloc) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest =
        arrayAt (dirEntryAt A.repAlloc) 48 (changedPtr + BitVec.ofNat 64 (48 * pre.length))
          ((x.name, bs) :: rest) := by
      dsimp only [arrayAt, dirEntryAt]
      sep_ac_rfl
    have happ_eq :
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
          arrayAt (dirEntryAt A.repAlloc) 48 (changedPtr + BitVec.ofNat 64 (48 * pre.length))
            ((x.name, bs) :: rest) =
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr x.dir.changed := by
      rw [hchanged, arrayAt_dirEntry_append]
    have hlhs_eq :
        (vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
          vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
          arrayAt (dirEntryAt A.repAlloc) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
          (if changedCap = 0 then emp
           else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48))) =
        vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          arrayAt (dirEntryAt A.repAlloc) 48 changedPtr x.dir.changed ∗
          (if changedCap = 0 then emp
           else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48)) := by
      rw [← happ_eq, ← hentry_eq]; sep_ac_rfl
    unfold dirAt vecOf vecAt
    refine sepConj_mono ?_ (Entails.refl _)
    refine Entails.trans ?_ (Entails.sepExists_intro changedCap)
    refine Entails.trans ?_ (Entails.sepExists_intro changedPtr)
    rw [vecBuf_dirEntry_expose, hlhs_eq]
    exact sepConj_mono_right (Entails.pure_right hcap_ok (Entails.refl _))
  refine SepWPp.perm
    (P' := vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        arrayAt (dirEntryAt A.repAlloc) 48 changedPtr pre ∗
        vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        arrayAt (dirEntryAt A.repAlloc) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.repAlloc.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 24#64) x.dir.path) ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 s) ∗ Extra))
    ?_ (by sep_frame)
  refine sepWPp_unfold_vecU8 fun valCap valPtr hbs_le hvcap_lt hvptr_ne => ?_
  rw [memRegion_48_split6 x.ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun r0 => sepWPp_exists_left fun r1 =>
    sepWPp_exists_left fun r2 => sepWPp_exists_left fun r3 =>
    sepWPp_exists_left fun r4 => sepWPp_exists_left fun r5 => ?_
  have hbs_lt63 : bs.length < 2 ^ 63 := by omega
  have hbs_lt64 : bs.length < 2 ^ 64 := by omega
  have hv24_32 : (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) + 8#64 =
      changedPtr + BitVec.ofNat 64 (48 * pre.length) + 32#64 := by bv_omega
  have hv24_40 : (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) + 16#64 =
      changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 := by bv_omega
  have hx23_sub8 : (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) + (-8#64) =
      changedPtr + BitVec.ofNat 64 (48 * pre.length) + 32#64 := by bv_omega
  rw [hv24_32, hv24_40]
  have hrepack_val :
      ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) ↦₆₄ valCap) ∗
        ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 32#64) ↦₆₄ valPtr) ∗
        ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (valPtr ↦ₛ bs) ∗
        (if valCap = 0 then emp
         else A.repAlloc.live valPtr valCap.toNat 1 ∗
           memRegion (valPtr + BitVec.ofNat 64 bs.length) (valCap.toNat - bs.length)) ⊢
      vecU8 A.repAlloc (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs := by
    dsimp only [vecU8]
    refine Entails.trans ?_ (Entails.sepExists_intro valCap)
    refine Entails.trans ?_ (Entails.sepExists_intro valPtr)
    rw [vecU8At_expose, hv24_32, hv24_40]
    exact Entails.pure_right ⟨hbs_le, hvcap_lt, hvptr_ne⟩ (Entails.refl _)
  have hbs_cases : bs = [] ∨ 0 < bs.length := by cases bs <;> simp
  rcases hbs_cases with rfl | hbs_pos
  · clear hC hRO
    have hevs_nil : GetEnv s0.fs.files x.dir x.name [] := by
      apply hGetEnv
      rw [hEnv_eq]
      rfl
    refine seq_lscro_state (mid := (blkPl_589).base + 284#64) hcrl ?_
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at *
    dsimp only [lsProg_589]
    wp_steps_sync_pool ((blkPl_589).base + 284#64)
    have hret8 : (x.ret + 8#64) + 8#64 = x.ret + 16#64 := by bv_omega
    have hret16 : (x.ret + 8#64) + 16#64 = x.ret + 24#64 := by bv_omega
    have hvec0 :
        ((x.ret + 8#64) ↦₆₄ 0#64) ∗ ((x.ret + 16#64) ↦₆₄ 1#64) ∗ ((x.ret + 24#64) ↦₆₄ 0#64) ⊢
        vecU8 A.repAlloc (x.ret + 8#64) [] := by
      have h0 := vecU8_of_zero A.repAlloc (x.ret + 8#64)
      rwa [hret8, hret16] at h0
    apply SepWP.fold hvec0 (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A.repAlloc x.ret r1 r0 []) (by sep_frame)
    apply SepWP.fold hrepack_val (by sep_frame)
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _
    refine SepWPp.perm
      (step_epilogue_284_budget (evs := []) hstk hfull hsp0_al
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        ⟨hget.symm, by simp only [wp_norm, arm64_norm, *], hevs_nil⟩)
      (by simp only [M.stepEvents_nil]; sep_frame)
  · have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
      ofNat_beq_zero_false hbs_pos hbs_lt64
    have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs_lt64]
    have hlay : RustLayoutOk bs.length 1 := ⟨⟨hbs_pos, ⟨0, rfl⟩, by omega⟩, by omega⟩
    have hEnv_pos : DirGetEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name
        (rustAllocEvents bs.length 1) := by
      rw [hEnv_eq]
      simp [allocBytes1Events, Nat.ne_of_gt hbs_pos]
    have hfit_bs : FitsEvents M lim st0 (rustAllocEvents bs.length 1) :=
      hfit0 _ hEnv_pos
    have hevs_pos : GetEnv s0.fs.files x.dir x.name (rustAllocEvents bs.length 1) :=
      hGetEnv _ hEnv_pos
    have hshim := shim_lscro_of_cli (callerProg := lsProg_589 H) (stk := extHookStack) hC
    have halloc := allocNoOom_lscro_of_cli (callerProg := lsProg_589 H) hC
    have hmc := memcpy_bytesAt_lscro_vm_ok_at_589 hC hRO false
    clear hC hRO
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    refine seq_lscro_state (mid := lsρ lsRustNoAllocShimSymCli) hcrl ?_
    dsimp only [lsProg_589]
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    refine call_lscro_frame (x := ())
      (T := stackAt (s0.sp - 112#64) extHookStack)
      hshim hcrl1 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by simp only [withStack, sessionShimBudgetSpec, withVmPreserved,
            CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
            emp_sepConj, pure_true_sepConj, wp_norm, hsp])
      trivial (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQpBudget_false)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hcrl2 => ?_)
    dsimp only [withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hvm1 => SepWPp.pure_left fun htr1 => ?_
    refine SepWPp.transport_budgetPool hvm1 (hnext := ?_)
    simp only [wp_norm, hsp, sepConj_assoc]
    have hhcs1 : HighCalleeSaved s0 sf1 :=
      hhcs.of_step_call hcs1
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp1_al : sf1.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hsp1
    have hsp1_eq : sf1.sp = s0.sp - 112#64 := by rw [hsp1]; simp only [wp_norm, arm64_norm, *]
    have hx19_1 : sf1.readReg64 .x19 = x.ret := by
      have := hcs1.1; simp only [wp_norm, arm64_norm, *] at this; exact this
    have hx20_1 : sf1.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      have := hcs1.2.1; simp only [wp_norm, arm64_norm] at this; exact this
    have hx22_1 : sf1.readReg64 .x22 = valPtr := by
      have := hcs1.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this
    have htr1_s0 : sf1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
    refine seq_lscro_state (mid := lsρ lsRustAllocSymCli) hcrl2 ?_
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl3
    refine call_lscro_frame (x := (bs.length, 1, st0))
      (T := A.pool lim st0 _ ∗ stackAt (s0.sp - 112#64) extHookStack)
      halloc hcrl3 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp1_al)
      (by wp_norm_lhs)
      (by dsimp only [TripleRatchet.Hooks2Budget.rustAllocNoOomSpecWithStack,
            rustCliAllocNoOomSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomSpec]
          simp only [wp_norm, hsp1_eq]; rfl)
      (by refine ⟨by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm],
                  hlay, hfit_bs,
                  by simp (config := { decide := true }) only [Reg.x30, Reg.lr, wp_norm, arm64_norm]⟩)
      (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQpBudget_false)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 hcrl4 => ?_)
    dsimp only [TripleRatchet.Hooks2Budget.rustAllocNoOomSpecWithStack,
      rustCliAllocNoOomSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomSpec]
    simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp1_eq, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨hacp2, hoom_ne, _⟩ => ?_
    set buf := sf2.readReg64 (Reg.gpr 0#5)
    have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
    have hhcs2 : HighCalleeSaved s0 sf2 :=
      hhcs1.of_step_call hcs2
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp2_al : sf2.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp1_al) hsp2
    have hsp2_eq : sf2.sp = s0.sp - 112#64 := by rw [hsp2]; simp only [wp_norm, arm64_norm, *]
    have hx19_2 : sf2.readReg64 .x19 = x.ret := by
      have := hcs2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_1
    have hx20_2 : sf2.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      have := hcs2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_1
    have hx22_2 : sf2.readReg64 .x22 = valPtr := by
      have := hcs2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22_1
    have htr2_s0 : sf2.trace = s0.trace := by
      rw [hacp2.2.1]; simp only [wp_norm, arm64_norm, *]
    refine seq_lscro_state (mid := lsρ memcpyName) hcrl4 ?_
    wp_steps_sync_pool (lsρ memcpyName)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl5
    refine call_lscro_frame (x := (buf, valPtr, bs))
      (T := memRegion buf bs.length ∗ (valPtr ↦ₛ bs) ∗
        stackAt (s0.sp - 112#64) extHookStack)
      hmc hcrl5 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp2_al)
      (by wp_norm_lhs)
      (by simp only [withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
            bytesAt_false, sepConj_assoc, wp_norm, hsp2_eq]; rfl)
      (by refine ⟨rfl,
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm, *],
                  by omega⟩)
      (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQpBudget_false)
      (fun sf3 hpc3 hrun3 hsp3 hcs3 hcrl6 => ?_)
    dsimp only [withStack, withVmPreserved, sessionMemcpyBytesAtSpec, bytesAt_false]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hvm3 => SepWPp.pure_left fun ⟨_, htr3⟩ => ?_
    refine SepWPp.transport_budgetPool hvm3 (hnext := ?_)
    simp only [wp_norm, hsp2_eq, sepConj_assoc]
    have hhcs3 : HighCalleeSaved s0 sf3 :=
      hhcs2.of_step_call hcs3
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp3_eq : sf3.sp = s0.sp - 112#64 := by rw [hsp3]; simp only [wp_norm, arm64_norm, *]
    have hx19_3 : sf3.readReg64 .x19 = x.ret := by
      have := hcs3.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_2
    have hx20_3 : sf3.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      have := hcs3.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_2
    have hx21_3 : sf3.readReg64 .x21 = buf := by
      have := hcs3.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this
    have htr3_s0 : sf3.trace = s0.trace := by rw [htr3]; simp only [wp_norm, arm64_norm, *]
    have hcstk_join :
        memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
          stackAt (s0.sp - 112#64) extHookStack ⊢
        stackAt (s0.sp - 112#64) cstk := by
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
      exact Entails.refl _
    refine seq_lscro_state (mid := (blkPl_589).base + 284#64) hcrl6 ?_
    wp_steps_sync_pool ((blkPl_589).base + 284#64)
    have hret8 : (x.ret + 8#64) + 8#64 = x.ret + 16#64 := by bv_omega
    have hret16 : (x.ret + 8#64) + 16#64 = x.ret + 24#64 := by bv_omega
    have hvec_pos :
        ((x.ret + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((x.ret + 16#64) ↦₆₄ buf) ∗
          ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          A.live buf bs.length 1 ∗ (buf ↦ₛ bs) ⊢
        vecU8 A.repAlloc (x.ret + 8#64) bs := by
      have hp := vecU8_of_pos A.repAlloc (x.ret + 8#64) buf bs hbs_pos hbs_lt63 hoom_ne
      rwa [hret8, hret16] at hp
    simp only [RustCliAllocBudget.repAlloc_live_norm] at hrepack_val hrepack_dir
    apply SepWP.fold hvec_pos (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A.repAlloc x.ret r1 r0 bs) (by sep_frame)
    apply SepWP.fold hrepack_val (by sep_frame)
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.fold hcstk_join (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _
    refine SepWPp.perm
      (step_epilogue_284_budget (evs := rustAllocEvents bs.length 1) hstk hfull hsp0_al
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs3.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        ⟨hget.symm, by simp only [wp_norm, arm64_norm, *], hevs_pos⟩)
      (by sep_frame)

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
