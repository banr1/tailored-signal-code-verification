/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PureBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.ElfLsRetAddr -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Envelopes and Exit Branches for `Dir::put::<&str>` (Block 543)

Defines `DirPutStrEnv`, budget-threaded callee and `SepWPp` combinators, and the cache-hit and
cache-miss exit branches (`+164`, `+188`, `+244`) on Block 543.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  LibsignalHooks LibsignalPlacement ls_hook_ok_ultra_of_mem lsmpl lsρ
)
open CryptoVerification.RustHeap (
  LayoutOk arrayAt vecAt vecBuf vecHeader vecOf vecU8 vecU8At
)
open CryptoVerification.LibsignalTripleRatchetRepr (strRefAt)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack memcpyName sessionMemcpyRegionSpec sessionShimSpec withStack
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain
  withLsCodeRoLoaded
)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyBytesAtSpec sessionMemcpyRegionROSpec)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt bytesAt_false bytesAt_true)
open CryptoVerification.SignalSession (
  lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
)
open CryptoVerification.SignalSession.Cli (
  DirGhost DirPutStrGhost cliBcmpName cliBcmpSpec dirAt dirEntryAt
)
open CryptoVerification.SignalSession.Cli.Placed (blkPl_543 lsProg_543)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.PutStr.Helpers (
  PresHigh beq_ofNat_zero_eq_false calleeSavedPreserved_of_restored growOne_cap_gt
  madd_slot_eq nameBuf nameBuf_drop_nil nameBuf_for_dealloc ofNat_eq_of_toNat_eq
  ofNat_toNat_of_lt pointsTo64_three_entails_memRegion24 savedSlots savedSlots_merge
  sepWPp_exists_left sepWPp_pure_left sepWPp_weaken_pre
  setOrPush_eq_append_singleton_of_forall_ne stackAt_split_sub vecBuf_dirEntry_expose_slot
  vecOf_dirEntry_hit_assemble vecOf_dirEntry_push_assemble vecU8Heap vecU8Heap_drop_zero
  vecU8Heap_for_dealloc
)
open CryptoVerification.SignalSession.Cli.PutStr.PlacedHelpers (
  CurEq atOff543 sepWPp_cut_543 sepWPp_cut_rebase_543 sepWPp_eq_pre stackAt_split_sp
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  VmPreserved rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustAllocNoOomExternSpecWithStack rustDeallocExternSpecWithStack
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget (GrowOneDirEnv growOneDirRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (
  DirPutTailEnv dirPutTailEnv_hit_freeOnly dirPutTailEnv_miss_grow dirPutTailEnv_miss_nil
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsXCliPlaced dirPutStrSpecPlaced growOneDirSpecPlaced
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (
  allocNoOomExtern_lscro_of_cli dealloc_lscro_of_cli session_memcpy_region_lscro_of_cli
  shim_lscro_of_cli
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Canonical Event Envelope `DirPutStrEnv` -/

/-- Canonical `AllocEvent` envelope for `Dir::put::<&str>` (Block `543`):
- when `name = []`, no `to_owned` allocation occurs (`DirPutTailEnv dir name`);
- when `name ≠ []`, `to_owned` allocates `rustAllocEvents name.length 1` followed by
  `DirPutTailEnv dir name`. -/
def DirPutStrEnv (dir : DirGhost) (name _bytes : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  if name = [] then
    DirPutTailEnv dir name evs
  else
    SeqEnv (· = rustAllocEvents name.length 1) (DirPutTailEnv dir name) evs

theorem dirPutStrEnv_of_nil {dir : DirGhost} {name bytes : List (BitVec 8)}
    {evs : List AllocEvent} (hnil : name = []) (ht : DirPutTailEnv dir name evs) :
    DirPutStrEnv dir name bytes ([] ++ evs) := by
  unfold DirPutStrEnv
  rw [List.nil_append]
  split
  · exact ht
  · rename_i hc; exact (hc hnil).elim

theorem dirPutStrEnv_of_nonempty {dir : DirGhost} {name bytes : List (BitVec 8)}
    {evsTail : List AllocEvent} (hne : name ≠ []) (ht : DirPutTailEnv dir name evsTail) :
    DirPutStrEnv dir name bytes (rustAllocEvents name.length 1 ++ evsTail) := by
  unfold DirPutStrEnv
  split
  · rename_i hc; exact (hne hc).elim
  · exact SeqEnv.append rfl ht

/-! ## 2. Budget-Threaded Callee Bridges & `SepWPp` Combinators -/

/-- Stack-equipped `VmPreserved` shim contract matching `session2ShimSpecX`. -/
def session2ShimBudgetSpecX : Spec Unit where
  pre := fun _ s0 => ⌜True⌝ ∗ stackAt s0.sp extHookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp extHookStack

theorem shim_ok_at_dirPutStr_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_543 H) (lsρ lsRustNoAllocShimSymCli)
      (withLsCodeRoLoaded lsmpl session2ShimBudgetSpecX) := by
  have h := shim_lscro_of_cli (callerProg := lsProg_543 H) (stk := extHookStack) hC
  refine subroutine_ok_outcome_intro fun u R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (withStack sessionShimBudgetSpec extHookStack)).pre u s0 ∗ R := by
    apply satisfies_lscro_pre hcrl0
    simpa only [session2ShimBudgetSpecX, withStack, sessionShimBudgetSpec, sessionShimSpec,
      emp_sepConj, sepConj_assoc, satisfies_pure_sepConj, true_and] using hpre0
  refine h.mono_outcome u R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, session2ShimBudgetSpecX, withStack,
      sessionShimBudgetSpec, sessionShimSpec] at hpost ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem allocNoOom_ok_at_dirPutStr_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_543 H) (lsρ lsRustAllocSymCli)
      (withLsCodeRoLoaded lsmpl (rustAllocNoOomExternSpecWithStack M A lim false extHookStack)) :=
  allocNoOomExtern_lscro_of_cli (callerProg := lsProg_543 H) hC

theorem dealloc_ok_at_dirPutStr_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_543 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)) :=
  dealloc_lscro_of_cli (callerProg := lsProg_543 H) hC

theorem memcpy_bytesAt_lscro_ok_at_543 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (hC : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (ro : Bool) :
    subroutine_ok (lsProg_543 H) (lsρ memcpyName)
      (withLsCodeRoLoaded lsmpl
        (withStack (withVmPreserved (sessionMemcpyBytesAtSpec ro)) extHookStack)) := by
  cases ro
  · have hmc := session_memcpy_region_lscro_of_cli (callerProg := lsProg_543 H)
      (stk := extHookStack) hC
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionBudgetSpec extHookStack)).pre
          (dst, src, bs) s0 ∗ R := by
      apply satisfies_lscro_pre hcrl0
      simp only [withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
        bytesAt_false, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1⟩, hpre0.2⟩
    refine hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [withLsCodeRoLoaded, withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
        bytesAt_false, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr hoom))
  · have hmc_ro : subroutine_ok (lsProg_543 H) (lsρ memcpyName)
        (withVmPreserved sessionMemcpyRegionROSpec) :=
      ls_hook_ok_ultra_of_mem hRO (by decide)
    refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
    obtain ⟨_hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (withVmPreserved sessionMemcpyRegionROSpec).pre (dst, src, bs) s0 ∗
          (stackAt s0.sp extHookStack ∗ R) := by
      simp only [withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionROSpec, bytesAt_true, sepConj_assoc,
        satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨hpre0.1, hpre0.2⟩
    refine hmc_ro.mono_outcome (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0
      hpc hrun hpre' hal fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simp only [withLsCodeRoLoaded, withStack, withVmPreserved, sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionROSpec, bytesAt_true, sepConj_assoc,
        satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, hpost.2⟩
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [withVmPreserved, sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1

theorem bcmp_lscro_ok_at_dirPutStr_543 [LibsignalPlacement]
    (H : LibsignalHooks)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec)) :
    subroutine_ok (lsProg_543 H) (lsρ cliBcmpName)
      (withLsCodeRoLoaded lsmpl (withVmPreserved cliBcmpSpec)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_ultra_of_mem hBcmp (by decide))

theorem call_lscro_wpp [LibsignalPlacement] {α : Type} {prog : Program}
    {callee ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee (withLsCodeRoLoaded lsmpl spec))
    (x : α) {s : State} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    {φ : Prop} (hspec : spec.pre x s = ⌜φ⌝ ∗ T) (hφ : φ) (hP : P = T ∗ F)
    (hpan : ∀ sf, Qp sf (spec.onPanic x s sf ∗ F))
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog target_pc s P Q Qp :=
  CryptoVerification.SignalSession.Cli.PutStr.PlacedHelpers.call_lscro_wpp
    hcall x hcrl hpc hrun hsp_align hlr hspec hφ hP hpan hexit hoom hnext

theorem tailcall_lscro_frame [LibsignalPlacement] {α : Type} {prog : Program}
    {callee ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee (withLsCodeRoLoaded lsmpl spec))
    (x : α) {φ : Prop} {s : State} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T) (hφ : φ) (hP : P = T ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝)
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hret : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → Q sf (spec.post x s sf ∗ F)) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.SignalSession.Cli.PutStr.PlacedHelpers.tailcall_lscro_frame
    hcall x hcrl hpc hrun hsp hlr hspec hφ hP hpan hexit hoom hret

abbrev DirPutStrPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (x : DirPutStrGhost) (st0 : M.σ) (s0 : State) (stk : Nat) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (dirPutStrSpecPlaced A lim PutStrEnv stk).post (x, st0) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev DirPutStrPanicPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (x : DirPutStrGhost) (st0 : M.σ) (s0 : State) (stk : Nat) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (dirPutStrSpecPlaced A lim PutStrEnv stk).onPanic (x, st0) s0 sf ∗ R)

theorem panic_false_wpp_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : DirPutStrGhost} {st0 : M.σ} {s0 : State} {stk : Nat}
    {R : SepProp} {sf : State} {F : SepProp} :
    DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R sf (⌜False⌝ ∗ F) := by
  intro hm
  rw [sepConj_assoc] at hm
  exact (not_satisfies_false_sepConj hm).elim

/-- Instantiate the postcondition `∃∗ evs : List AllocEvent` of `DirPutStrPostPlaced` with a
concrete witness `evs₀`, leaving a `wp_done`-ready postcondition matching `Placed.lean`. -/
theorem sepWPp_post_evs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : DirPutStrGhost} {st0 : M.σ} {s0 s : State} {stk : Nat}
    {prog : Program} {ret : BitVec 64} {P R : SepProp}
    (evs₀ : List AllocEvent)
    (hEnv : PutStrEnv x.dir x.name x.bytes evs₀)
    (h : SepWPp prog ret s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
            bytesAt x.nameRo x.nameA x.name ∗ memRegion x.bytesV 24 ∗
            stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs₀ st0) sf) ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R)) :
    SepWPp prog ret s P
      (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
      (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', P_f, hm', hpost, hsp', hcs'⟩ | hpan | hoom⟩ := h R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', P_f, hm', ⟨fun hmf => ?_, hsp', hcs'⟩⟩⟩
    have h0 := hpost hmf
    dsimp only [dirPutStrSpecPlaced, withLsCodeRoLoaded]
    refine Satisfies.mono (sepConj_mono_left ?_) h0
    refine Entails.sepExists_right evs₀ ?_
    exact Entails.pure_left fun htr => Entails.pure_right ⟨htr, hEnv⟩ (Entails.refl _)
  · exact ⟨sf, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-! ## 3. Hit & Miss Exit Branches (`+188`, `+164`, `+244`) -/

/-- Shared post-drop tail of the hit branch starting at `+188` on Block `543`. -/
theorem step_hit_copy_and_exit_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (x : DirPutStrGhost) (st0 : M.σ) (evsPre evsOld : List AllocEvent)
    (R : SepProp) (s0 s : State)
    (pre rest : List (List (BitVec 8) × List (BitVec 8)))
    (cap ptr curBase namePtr bCap bPtr d0 d1 d2 : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hhit : ¬ ∀ p ∈ x.dir.changed, p.1 ≠ x.name)
    (hfOld : FreeOnlyEvs evsOld)
    (hWrap : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
      PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail))
    (hput_eq : (x.dir.put x.name x.bytes).changed = pre ++ (x.name, x.bytes) :: rest)
    (hcur : curBase = ptr + BitVec.ofNat 64 (pre.length * 48))
    (hle : (pre ++ (x.name, x.bytes) :: rest).length ≤ cap.toNat)
    (hbound : cap.toNat * 48 < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hcap : cap ≠ 0)
    (hsp_align0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = atOff543 188)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64)
    (htr : s.trace = s0.trace)
    (hhigh : PresHigh s0 s)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20 : s.readReg64 .x20 = x.bytesV)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx22 : s.readReg64 .x22 = curBase + 24#64)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    let cal := max growStk extHookStack
    let stCur := M.stepEvents evsOld (M.stepEvents evsPre st0)
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        vecU8 A.repAlloc curBase x.name ∗
        ((curBase + 24#64) ↦₆₄ d0) ∗ ((curBase + 32#64) ↦₆₄ d1) ∗
        ((curBase + 40#64) ↦₆₄ d2) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
          ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A.repAlloc namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool lim stCur s)
      (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
      (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R) := by
  intro cal stCur
  have hdealloc := dealloc_ok_at_dirPutStr_543 hC
  have hdir_ent :
      vecOf A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self (pre ++ (x.name, x.bytes) :: rest) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ⊢
        dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) := by
    unfold dirAt
    rw [hput_eq]
    exact Entails.refl _
  have hhit_ent :
      (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        vecU8 A.repAlloc curBase x.name ∗
        (((curBase + 24#64) ↦₆₄ bCap) ∗ ((curBase + 32#64) ↦₆₄ bPtr) ∗
          ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A.repAlloc bCap bPtr x.bytes) ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
          ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ⊢
        vecOf A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self
          (pre ++ (x.name, x.bytes) :: rest) :=
    vecOf_dirEntry_hit_assemble A.repAlloc x.self cap ptr curBase bCap bPtr
      pre rest x.name x.bytes hcur hle hbound hptr hcap
  clear hcur
  by_cases hnil : x.name = []
  · have hx19_z : s.readReg64 .x19 = 0#64 := by
      rw [hx19, hnil]; rfl
    have hdrop_name : nameBuf A.repAlloc namePtr x.name ⊢ emp := by
      rw [hnil]; exact nameBuf_drop_nil A.repAlloc namePtr
    have hEnvNil : PutStrEnv x.dir x.name x.bytes (evsPre ++ evsOld) :=
      hWrap evsOld (dirPutTailEnv_hit_freeOnly hhit hfOld)
    have hst_eq : stCur = M.stepEvents (evsPre ++ evsOld) st0 :=
      (M.stepEvents_append evsPre evsOld st0).symm
    rw [hst_eq]
    apply sepWPp_post_evs (evsPre ++ evsOld) hEnvNil
    dsimp only [DirPutStrPanicPlaced, dirPutStrSpecPlaced,
      withLsCodeRoLoaded, atOff543, savedSlots] at hpc ⊢
    clear hC hdealloc hcrl
    rcases hhigh with ⟨hx27, hx28, hvregs⟩
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    apply SepWP.fold hdrop_name (by sep_frame)
    apply SepWP.fold (savedSlots_merge s0 (cal := cal) hstk hstk_max) (by sep_frame)
    apply SepWP.fold
      (pointsTo64_three_entails_memRegion24 x.bytesV bCap bPtr (BitVec.ofNat 64 x.bytes.length))
      (by sep_frame)
    apply SepWP.fold hhit_ent (by sep_frame)
    apply SepWP.fold hdir_ent (by sep_frame)
    wp_done
  · have hpos : 0 < x.name.length := List.length_pos_of_ne_nil hnil
    have hx19_nz : (BitVec.ofNat 64 x.name.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by omega)
    have hx19_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat_toNat_of_lt (by omega)
    dsimp only [atOff543, savedSlots] at hpc hdealloc ⊢
    clear hC
    apply sepWPp_cut_543 (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.fold (savedSlots_merge s0 (cal := cal) hstk hstk_max) (by sep_frame)
    apply SepWP.fold
      (pointsTo64_three_entails_memRegion24 x.bytesV bCap bPtr (BitVec.ofNat 64 x.bytes.length))
      (by sep_frame)
    apply SepWP.fold hhit_ent (by sep_frame)
    apply SepWP.fold hdir_ent (by sep_frame)
    apply SepWP.fold (nameBuf_for_dealloc A.repAlloc namePtr x.name hnil) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 hcrl_s1
    conv => arg 4; rw [← hs1]
    rw [show ∀ (P0 L1 M1 Pool D1 N1 B24 S1 : SepProp),
          (P0 ∗ L1 ∗ M1) ∗ Pool ∗ D1 ∗ N1 ∗ B24 ∗ S1 =
            P0 ∗ (Pool ∗ L1 ∗ M1 ∗ D1 ∗ N1 ∗ B24 ∗ S1) from
          fun _ _ _ _ _ _ _ _ => by sep_ac_rfl]
    refine sepWPp_pure_left fun ⟨_hnp_ne0, hlay_name⟩ => ?_
    have hsp_s1 : s1.sp = s0.sp := by
      rw [hs1]; simp only [wp_norm, arm64_norm]
    have hsp_align_s1 : s1.spAligned = true := by
      simpa only [State.spAligned, hsp_s1] using hsp_align0
    have htr_s1 : s1.trace = s0.trace := by
      rw [hs1]; simp only [wp_norm, arm64_norm]; exact htr
    have hcs_s1 : CalleeSavedPreserved s0 s1 := by
      refine calleeSavedPreserved_of_restored
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm])
        ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.2⟩
    rw [← hsp_s1, stackAt_split_sub s1.sp (show extHookStack ≤ stk by omega) hstk_max]
    apply tailcall_lscro_frame hdealloc (namePtr, x.name.length, 1, stCur)
      (F := dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.bytesV 24 ∗
        memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack))
      (hcrl := hcrl_s1)
      (hpc := by rw [hs1]; simp only [wp_norm, arm64_norm])
      (hrun := by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hrun)
      (hsp := hsp_align_s1)
      (hlr := by rw [hs1]; simp only [wp_norm, arm64_norm])
      (hspec := rfl)
      (hφ := ⟨by rw [hs1]; simp only [wp_norm, arm64_norm],
              by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx19_toNat,
              by rw [hs1]; simp only [wp_norm, arm64_norm],
              ⟨hlay_name, by decide⟩,
              by rw [hs1]; simpa only [Reg.x30, Reg.lr, wp_norm, arm64_norm] using hlr_ls⟩)
      (hP := by dsimp only [RustCliAllocBudget.repAlloc]; sep_ac_rfl)
      (hpan := fun _ => rfl)
      (hexit := fun _ _ => rfl)
      (hoom := fun _ => rfl)
    intro sf _hpcf _hrunf hspf hcsf
    refine ⟨?_, hspf.trans hsp_s1, hcs_s1.trans hcsf⟩
    intro hm
    dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hm
    dsimp only [dirPutStrSpecPlaced, withLsCodeRoLoaded]
    have hstk_re :
        memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
          stackAt s1.sp extHookStack =
          stackAt s0.sp stk := by
      rw [← stackAt_split_sub s1.sp (show extHookStack ≤ stk by omega) hstk_max, hsp_s1]
    set evsTail := evsOld ++ rustDeallocEvents x.name.length 1
    have hEnvDealloc : PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail) :=
      hWrap evsTail (dirPutTailEnv_hit_freeOnly hhit
        (FreeOnlyEvs.append hfOld (FreeOnlyEvs.singleton 1 x.name.length)))
    have hst_final :
        M.stepEvents (rustDeallocEvents x.name.length 1) stCur =
          M.stepEvents (evsPre ++ evsTail) st0 := by
      dsimp only [stCur, evsTail]
      rw [← M.stepEvents_append evsOld, ← M.stepEvents_append evsPre]
    rw [hst_final] at hm
    rw [show ((⌜sf.trace = s1.trace⌝ ∗
          A.pool lim (M.stepEvents (evsPre ++ evsTail) st0) sf ∗
          stackAt s1.sp extHookStack) ∗
          (dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
            bytesAt x.nameRo x.nameA x.name ∗
            memRegion x.bytesV 24 ∗
            memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack))) ∗ R =
        ⌜sf.trace = s1.trace⌝ ∗
          (dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) ∗
            bytesAt x.nameRo x.nameA x.name ∗
            memRegion x.bytesV 24 ∗
            (memRegion (s1.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
              stackAt s1.sp extHookStack) ∗
            A.pool lim (M.stepEvents (evsPre ++ evsTail) st0) sf ∗ R) by sep_ac_rfl] at hm
    rw [satisfies_pure_sepConj, hstk_re] at hm
    rcases hm with ⟨htr_sf1, hmem_sf⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evsPre ++ evsTail, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr_sf1.trans htr_s1, hEnvDealloc⟩, ?_⟩
    ac_nf at hmem_sf ⊢

/-- Hit branch entry at `+164` on Block `543`. -/
theorem step_hit_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (x : DirPutStrGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    (R : SepProp) (s0 s : State)
    (pre rest : List (List (BitVec 8) × List (BitVec 8)))
    (oldBs : List (BitVec 8))
    (cap ptr curBase namePtr bCap bPtr oldCap oldPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hname32 : x.name.length < 2 ^ 32)
    (hhit : ¬ ∀ p ∈ x.dir.changed, p.1 ≠ x.name)
    (hWrap : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
      PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail))
    (hput_eq : (x.dir.put x.name x.bytes).changed = pre ++ (x.name, x.bytes) :: rest)
    (hcur : curBase = ptr + BitVec.ofNat 64 (pre.length * 48))
    (hle : (pre ++ (x.name, x.bytes) :: rest).length ≤ cap.toNat)
    (hbound : cap.toNat * 48 < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hcap : cap ≠ 0)
    (hsp_align0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = atOff543 164)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 80#64)
    (htr : s.trace = s0.trace)
    (hhigh : PresHigh s0 s)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20 : s.readReg64 .x20 = x.bytesV)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx25 : s.readReg64 .x25 = curBase + 32#64)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    let cal := max growStk extHookStack
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
        A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
        arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
        vecU8 A.repAlloc curBase x.name ∗
        ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
        ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
        vecU8Heap A.repAlloc oldCap oldPtr oldBs ∗
        arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
        memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
          ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A.repAlloc namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool lim (M.stepEvents evsPre st0) s)
      (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
      (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R) := by
  intro cal
  have hcur' : CurEq curBase (ptr + BitVec.ofNat 64 (pre.length * 48)) := ⟨hcur⟩
  clear hcur
  have hdealloc := dealloc_ok_at_dirPutStr_543 hC
  by_cases hold0 : oldCap = 0#64
  · subst hold0
    apply sepWPp_cut_rebase_543 (mid := atOff543 188) hcrl
    dsimp only [atOff543] at hpc ⊢
    wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 188)
    apply SepWP.fold (vecU8Heap_drop_zero A.repAlloc oldPtr oldBs) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
    · subst hP1
      conv => arg 4; rw [← hs1]
      apply sepWPp_eq_pre
      · exact step_hit_copy_and_exit_543 hC x st0 evsPre [] R s0 s1
          pre rest cap ptr curBase namePtr bCap bPtr
          0#64 oldPtr (BitVec.ofNat 64 oldBs.length)
          hstk hstk_max hname32 hhit FreeOnlyEvs.nil hWrap
          hput_eq hcur'.out hle hbound hptr hcap hsp_align0 hcrl_s1
          (by rw [hs1]; try dsimp +zetaDelta only [atOff543]; simp only [wp_norm, arm64_norm])
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hrun)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hsp)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact htr)
          ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.1,
           by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
           by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx19)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx20)
          (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx21)
          (by rw [hs1]; simp only [wp_norm, arm64_norm])
      · rw [M.stepEvents_nil]
        try dsimp +zetaDelta only [savedSlots, bytesAt]
        try rw [emp_sepConj]
        try rw [sepConj_emp]
        try simp only [wp_norm, arm64_norm]
        try rw [Nat.mul_comm 48]
        try sep_ac_rfl
  · have hold_beq : (oldCap == 0#64) = false := beq_false_of_ne hold0
    apply sepWPp_cut_rebase_543 (mid := lsρ lsRustDeallocSymCli) hcrl
    dsimp only [atOff543] at hpc ⊢
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.fold (vecU8Heap_for_dealloc A.repAlloc oldCap oldPtr oldBs hold0) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 P1 hcrl_s1 ⟨hs1, hP1⟩
    · subst hP1
      conv => arg 4; rw [← hs1]
      rw [show ∀ (P0 L0 M0 Z : SepProp),
            (P0 ∗ L0 ∗ M0) ∗ Z = P0 ∗ L0 ∗ M0 ∗ Z from
            fun _ _ _ _ => by sep_ac_rfl]
      refine sepWPp_pure_left fun ⟨_holdp_ne0, hlay_old⟩ => ?_
      have hsp_s1 : s1.sp = s0.sp - 80#64 := by
        rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hsp
      have htr_s1 : s1.trace = s0.trace := by
        rw [hs1]; simp only [wp_norm, arm64_norm]; try exact htr
      rw [stackAt_split_sp hsp_s1 (Nat.le_max_right growStk extHookStack) (by omega)]
      apply call_lscro_wpp hdealloc (oldPtr, oldCap.toNat, 1, M.stepEvents evsPre st0)
        (ret_pc := atOff543 188)
        (F := (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 (pre ++ (x.name, x.bytes) :: rest).length) ∗
          A.repAlloc.live ptr (cap.toNat * 48) 8 ∗
          arrayAt (dirEntryAt A.repAlloc) 48 ptr pre ∗
          vecU8 A.repAlloc curBase x.name ∗
          ((curBase + 24#64) ↦₆₄ oldCap) ∗ ((curBase + 32#64) ↦₆₄ oldPtr) ∗
          ((curBase + 40#64) ↦₆₄ BitVec.ofNat 64 oldBs.length) ∗
          arrayAt (dirEntryAt A.repAlloc) 48 (curBase + 48#64) rest ∗
          memRegion (ptr + BitVec.ofNat 64 ((pre ++ (x.name, x.bytes) :: rest).length * 48))
            ((cap.toNat - (pre ++ (x.name, x.bytes) :: rest).length) * 48) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A.repAlloc namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
          savedSlots s0)
        (hcrl := hcrl_s1)
        (hpc := by rw [hs1]; rfl)
        (hrun := by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hrun)
        (hsp_align := by
          have hsp_eq : s1.sp = s.sp := by rw [hs1]; simp only [wp_norm, arm64_norm]
          simpa only [State.spAligned, hsp_eq] using hsp_align)
        (hlr := by rw [hs1]; try dsimp +zetaDelta only [atOff543]; simp only [wp_norm, arm64_norm])
        (hspec := rfl)
        (hφ := ⟨by rw [hs1]; simp only [wp_norm, arm64_norm],
                by rw [hs1]; simp only [wp_norm, arm64_norm],
                by rw [hs1]; simp only [wp_norm, arm64_norm],
                ⟨hlay_old, by decide⟩,
                by
                  have hlr1 : s1.readReg64 .lr = atOff543 188 := by
                    rw [hs1]; try dsimp +zetaDelta only [atOff543]; simp only [wp_norm, arm64_norm]
                  rw [hlr1]
                  exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add
                    543 188#64 (by decide) (by decide)⟩)
        (hP := by
          try dsimp +zetaDelta only [savedSlots, bytesAt, RustCliAllocBudget.repAlloc]
          try rw [emp_sepConj]
          try rw [sepConj_emp]
          try simp only [wp_norm, arm64_norm]
          try rw [Nat.mul_comm 48]
          try sep_ac_rfl)
        (hpan := fun _ => panic_false_wpp_543)
        (hexit := fun _ _ => rfl)
        (hoom := fun _ => rfl)
      intro sm hpcm hrunm hspm hcsm hcrlm
      dsimp only [rustDeallocExternSpecWithStack,
        LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
      try simp only [sepConj_assoc]
      refine sepWPp_pure_left fun htr_sm0 => ?_
      have hstk_back :
          memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - extHookStack) ∗
            stackAt s1.sp extHookStack =
            stackAt (s0.sp - 80#64) cal := by
        rw [← stackAt_split_sub s1.sp (Nat.le_max_right growStk extHookStack) (by omega), hsp_s1]
      rw [show ∀ (Pool StkE A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19 A20 A21 : SepProp),
            Pool ∗ StkE ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗
              A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ A20 ∗ A21 =
            A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ A11 ∗
              A12 ∗ A13 ∗ A14 ∗ A15 ∗ A16 ∗ A17 ∗ A18 ∗ A19 ∗ (A20 ∗ StkE) ∗ A21 ∗ Pool from
            fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by sep_ac_rfl]
      rw [hstk_back]
      have hhigh_s1 : PresHigh s0 s1 :=
        ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hhigh.2.2⟩
      exact step_hit_copy_and_exit_543 hC x st0 evsPre (rustDeallocEvents oldCap.toNat 1) R s0 sm
        pre rest cap ptr curBase namePtr bCap bPtr
        oldCap oldPtr (BitVec.ofNat 64 oldBs.length)
        hstk hstk_max hname32 hhit (FreeOnlyEvs.singleton 1 oldCap.toNat) hWrap
        hput_eq hcur'.out hle hbound hptr hcap hsp_align0 hcrlm
        hpcm hrunm
        (hspm.trans hsp_s1)
        (htr_sm0.trans htr_s1)
        (hhigh_s1.of_callee hcsm)
        (hcsm.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx19))
        (hcsm.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx20))
        (hcsm.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; try exact hx21))
        (hcsm.2.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]))

/-- Miss exit at `+244` on Block `543`. -/
theorem step_miss_543 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {growStk stk : Nat}
    (hgrow : subroutine_ok (lsProg_543 H) (lsmpl.base 586) (growOneDirSpecPlaced A lim growStk))
    (x : DirPutStrGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    (R : SepProp) (s0 s : State)
    (cap ptr namePtr bCap bPtr : BitVec 64)
    (hstk : 0x50 + max growStk extHookStack ≤ stk)
    (hstk_max : stk ≤ 2 ^ 64)
    (hlen32 : x.dir.changed.length < 2 ^ 32)
    (hmiss : ∀ e ∈ x.dir.changed, e.1 ≠ x.name)
    (hFitTail : FitsEnv M lim (M.stepEvents evsPre st0) (DirPutTailEnv x.dir x.name))
    (hWrap : ∀ evsTail, DirPutTailEnv x.dir x.name evsTail →
      PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = atOff543 244)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 80#64)
    (htr : s.trace = s0.trace)
    (hhigh : PresHigh s0 s)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.name.length)
    (hx20 : s.readReg64 .x20 = x.bytesV)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx22 : s.readReg64 .x22 = x.self)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length)
    (hx24 : s.readReg64 .x24 = ptr) :
    let cal := max growStk extHookStack
    SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s
      ((x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
        vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed ∗
        strRefAt (x.self + 0x18#64) x.dir.path ∗
        bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A.repAlloc namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        stackAt (s0.sp - 80#64) cal ∗
        savedSlots s0 ∗
        A.pool lim (M.stepEvents evsPre st0) s)
      (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
      (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R) := by
  intro cal
  have hpush : ∀ (s1 : State) (cap1 ptr1 : BitVec 64) (evsTail : List AllocEvent),
      DirPutTailEnv x.dir x.name evsTail →
      x.dir.changed.length < cap1.toNat →
      s1.pc = atOff543 256 →
      s1.status = .Running →
      s1.spAligned = true →
      s1.sp = s0.sp - 80#64 →
      s1.trace = s0.trace →
      PresHigh s0 s1 →
      s1.readReg64 .x19 = BitVec.ofNat 64 x.name.length →
      s1.readReg64 .x20 = x.bytesV →
      s1.readReg64 .x21 = namePtr →
      s1.readReg64 .x22 = x.self →
      s1.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length →
      s1.readReg64 .x24 = ptr1 →
      SepWPp (lsProg_543 H) (s0.readReg64 Reg.lr) s1
        ((x.self ↦₆₄ cap1) ∗ ((x.self + 8#64) ↦₆₄ ptr1) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap1 ptr1 x.dir.changed ∗
          strRefAt (x.self + 0x18#64) x.dir.path ∗
          bytesAt x.nameRo x.nameA x.name ∗
          nameBuf A.repAlloc namePtr x.name ∗
          (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
          ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
          vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
          stackAt (s0.sp - 80#64) cal ∗
          savedSlots s0 ∗
          A.pool lim (M.stepEvents evsTail (M.stepEvents evsPre st0)) s1)
        (DirPutStrPostPlaced A lim PutStrEnv x st0 s0 stk R)
        (DirPutStrPanicPlaced A lim PutStrEnv x st0 s0 stk R) := by
    intro s1 cap1 ptr1 evsTail htail hlt1 hpc1 hrun1 hspa1 hsp1 htr1 hhigh1
      hr19 hr20 hr21 hr22 hr23 hr24
    have hEnvPush : PutStrEnv x.dir x.name x.bytes (evsPre ++ evsTail) :=
      hWrap evsTail htail
    rw [← M.stepEvents_append evsPre evsTail st0]
    apply sepWPp_post_evs (evsPre ++ evsTail) hEnvPush
    dsimp only [DirPutStrPanicPlaced, dirPutStrSpecPlaced,
      withLsCodeRoLoaded, atOff543] at hpc1 ⊢
    rcases hhigh1 with ⟨hr27, hr28, hvregs1⟩
    apply sepWPp_weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (vecBuf_dirEntry_expose_slot A.repAlloc cap1 ptr1 x.dir.changed hlt1)))))
    dsimp only
    rw [show ∀ (A1 A2 A3 P0 B1 B2 B3 E6 Z : SepProp),
          A1 ∗ A2 ∗ A3 ∗ (P0 ∗ B1 ∗ B2 ∗ B3 ∗ E6) ∗ Z =
            P0 ∗ E6 ∗ A1 ∗ A2 ∗ A3 ∗ B1 ∗ B2 ∗ B3 ∗ Z from
          fun _ _ _ _ _ _ _ _ _ => by sep_ac_rfl]
    refine sepWPp_pure_left fun ⟨hle1, hbound1, hptr1, hcap1_ne⟩ => ?_
    set slot := ptr1 + BitVec.ofNat 64 (x.dir.changed.length * 48)
    refine sepWPp_exists_left fun u0 => ?_
    simp only [sepConj_assoc]
    refine sepWPp_exists_left fun u1 => ?_
    refine sepWPp_exists_left fun u2 => ?_
    refine sepWPp_exists_left fun u3 => ?_
    refine sepWPp_exists_left fun u4 => ?_
    refine sepWPp_exists_left fun u5 => ?_
    apply SepWPp.of_sepWP_ret
    have hslot_eq : ptr1 + BitVec.ofNat 64 x.dir.changed.length * 48#64 = slot :=
      madd_slot_eq ptr1 x.dir.changed.length
    have hlen1_eq : BitVec.ofNat 64 x.dir.changed.length + 1#64 =
        BitVec.ofNat 64 (x.dir.changed.length + 1) := by
      rw [← BitVec.ofNat_add]
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    apply SepWP.fold (savedSlots_merge s0 (cal := cal) hstk hstk_max) (by sep_frame)
    apply SepWP.fold
      (pointsTo64_three_entails_memRegion24 x.bytesV bCap bPtr (BitVec.ofNat 64 x.bytes.length))
      (by sep_frame)
    apply SepWP.fold
      (vecOf_dirEntry_push_assemble A.repAlloc x.self cap1 ptr1 namePtr bCap bPtr
        x.dir.changed x.name x.bytes hle1 hbound1 hptr1 hcap1_ne)
      (by sep_frame)
    have hput : (x.dir.put x.name x.bytes).changed = x.dir.changed ++ [(x.name, x.bytes)] :=
      setOrPush_eq_append_singleton_of_forall_ne x.name x.bytes x.dir.changed hmiss
    have hdir :
        vecOf A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self
            (x.dir.changed ++ [(x.name, x.bytes)]) ∗
          strRefAt (x.self + 0x18#64) x.dir.path ⊢
          dirAt A.repAlloc x.self (x.dir.put x.name x.bytes) := by
      unfold dirAt
      rw [hput]
      exact Entails.refl _
    apply SepWP.fold hdir (by sep_frame)
    wp_done
  have hpull_len :
      vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed =
        ⌜x.dir.changed.length ≤ cap.toNat⌝ ∗
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed := by
    apply Entails.antisymm
    · unfold vecBuf
      refine Entails.pure_left fun h => ?_
      exact Entails.pure_right h.1 (Entails.pure_right h (Entails.refl _))
    · exact Entails.pure_left fun _ => Entails.refl _
  rw [hpull_len]
  rw [show ∀ (A1 A2 A3 P0 B Z : SepProp),
        A1 ∗ A2 ∗ A3 ∗ (P0 ∗ B) ∗ Z = P0 ∗ A1 ∗ A2 ∗ A3 ∗ B ∗ Z from
        fun _ _ _ _ _ _ => by sep_ac_rfl]
  refine sepWPp_pure_left fun hle_cap => ?_
  by_cases heq_bv : BitVec.ofNat 64 x.dir.changed.length = cap
  · have hcap_eq : x.dir.changed.length = cap.toNat := by
      have ht := congrArg BitVec.toNat heq_bv
      rwa [ofNat_toNat_of_lt (by omega)] at ht
    have hcap32 : cap.toNat < 2 ^ 32 := by omega
    have hbeq_eq : (BitVec.ofNat 64 x.dir.changed.length == cap) = true :=
      beq_iff_eq.mpr heq_bv
    have hFitGrow :
        FitsEnv M lim (M.stepEvents evsPre st0)
          (GrowOneDirEnv ⟨x.self, cap, ptr, x.dir.changed⟩) :=
      FitsEnv.mono (fun evs hg => by
        dsimp only [GrowOneDirEnv] at hg
        rw [hg, ← heq_bv]
        exact dirPutTailEnv_miss_grow hmiss) hFitTail
    apply sepWPp_cut_543 (mid := lsmpl.base 586) hcrl
    dsimp only [atOff543] at hpc ⊢
    wp_steps_sync_pool (lsmpl.base 586)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 hcrl_s1
    conv => arg 4; rw [← hs1]
    have hsp_s1 : s1.sp = s0.sp - 80#64 := by
      rw [hs1]; simp only [wp_norm, arm64_norm]; exact hsp
    have htr_s1 : s1.trace = s0.trace := by
      rw [hs1]; simp only [wp_norm, arm64_norm]; exact htr
    rw [← hsp_s1, stackAt_split_sub s1.sp (Nat.le_max_left growStk extHookStack) (by omega)]
    have hvec_in :
        (x.self ↦₆₄ cap) ∗ ((x.self + 8#64) ↦₆₄ ptr) ∗
          ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 x.dir.changed.length) ∗
          vecBuf A.repAlloc 48 8 (dirEntryAt A.repAlloc) cap ptr x.dir.changed =
          vecAt A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self cap ptr x.dir.changed := by
      unfold vecAt vecHeader
      sep_ac_rfl
    apply call_lscro_wpp hgrow (⟨x.self, cap, ptr, x.dir.changed⟩, M.stepEvents evsPre st0)
      (ret_pc := atOff543 328)
      (F := strRefAt (x.self + 0x18#64) x.dir.path ∗
        bytesAt x.nameRo x.nameA x.name ∗
        nameBuf A.repAlloc namePtr x.name ∗
        (x.bytesV ↦₆₄ bCap) ∗ ((x.bytesV + 8#64) ↦₆₄ bPtr) ∗
        ((x.bytesV + 16#64) ↦₆₄ BitVec.ofNat 64 x.bytes.length) ∗
        vecU8Heap A.repAlloc bCap bPtr x.bytes ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cal - 80) ∗
        memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
        savedSlots s0)
      (hcrl := hcrl_s1)
      (hpc := by rw [hs1]; simp only [wp_norm, arm64_norm])
      (hrun := by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hrun)
      (hsp_align := by
        have hsp_eq : s1.sp = s.sp := by rw [hs1]; simp only [wp_norm, arm64_norm]
        simpa only [State.spAligned, hsp_eq] using hsp_align)
      (hlr := by rw [hs1]; dsimp [atOff543]; simp only [wp_norm, arm64_norm])
      (hspec := rfl)
      (hφ := ⟨by rw [hs1]; simp only [wp_norm, arm64_norm], hcap32, hFitGrow⟩)
      (hP := by
        rw [← hvec_in]
        sep_ac_rfl)
      (hpan := fun _ => panic_false_wpp_543)
      (hexit := fun _ _ => rfl)
      (hoom := fun _ => rfl)
    intro sm hpcm hrunm hspm hcsm hcrlm
    have hsp_sm : sm.sp = s0.sp - 80#64 := hspm.trans hsp_s1
    have hsp_align_sm : sm.spAligned = true := by
      have hsp_eq : sm.sp = s.sp := hspm.trans (by rw [hs1]; simp only [wp_norm, arm64_norm])
      simpa only [State.spAligned, hsp_eq] using hsp_align
    have hhigh_s1 : PresHigh s0 s1 :=
      ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.1,
       by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.2⟩
    have hhigh_sm : PresHigh s0 sm := hhigh_s1.of_callee hcsm
    have hx19_sm : sm.readReg64 .x19 = BitVec.ofNat 64 x.name.length :=
      hcsm.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx19)
    have hx20_sm : sm.readReg64 .x20 = x.bytesV :=
      hcsm.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx20)
    have hx21_sm : sm.readReg64 .x21 = namePtr :=
      hcsm.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx21)
    have hx22_sm : sm.readReg64 .x22 = x.self :=
      hcsm.2.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx22)
    have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 x.dir.changed.length :=
      hcsm.2.2.2.2.1.trans (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx23)
    dsimp only [growOneDirRawSpec]
    refine sepWPp_exists_left fun evsGrow => ?_
    simp only [sepConj_assoc]
    refine sepWPp_pure_left fun ⟨htr_sm0, hgEnv⟩ => ?_
    have htail_grow : DirPutTailEnv x.dir x.name evsGrow := by
      dsimp only [GrowOneDirEnv] at hgEnv
      rw [hgEnv, ← heq_bv]
      exact dirPutTailEnv_miss_grow hmiss
    have htr_sm : sm.trace = s0.trace := htr_sm0.trans htr_s1
    refine sepWPp_exists_left fun ptr' => ?_
    set newCap := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
    have hlt_new : x.dir.changed.length < newCap.toNat :=
      growOne_cap_gt hcap_eq hlen32
    unfold vecAt vecHeader
    simp only [sepConj_assoc]
    apply sepWPp_cut_543 (mid := atOff543 256) hcrlm
    dsimp only [atOff543] at hpcm ⊢
    wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 256)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s2 hs2 _hcrl_s2
    conv => arg 4; rw [← hs2]
    have hstack_back :
        memRegion (s1.sp - BitVec.ofNat 64 cal) (cal - growStk) ∗
          stackAt s1.sp growStk =
          stackAt (s0.sp - 80#64) cal := by
      rw [← stackAt_split_sub s1.sp (Nat.le_max_left growStk extHookStack) (by omega), hsp_s1]
    apply sepWPp_eq_pre
    · exact hpush s2 newCap ptr' evsGrow htail_grow hlt_new
        (by rw [hs2]; dsimp [atOff543]; simp only [wp_norm, arm64_norm])
        (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hrunm)
        (by
          have hsp_eq : s2.sp = sm.sp := by rw [hs2]; simp only [wp_norm, arm64_norm]
          simpa only [State.spAligned, hsp_eq] using hsp_align_sm)
        (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hsp_sm)
        (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact htr_sm)
        ⟨by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hhigh_sm.1,
         by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hhigh_sm.2.1,
         by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hhigh_sm.2.2⟩
        (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx19_sm)
        (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx20_sm)
        (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx21_sm)
        (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx22_sm)
        (by rw [hs2]; simp only [wp_norm, arm64_norm]; exact hx23_sm)
        (by rw [hs2]; simp only [wp_norm, arm64_norm])
    · rw [← hstack_back, hsp_s1]
      sep_ac_rfl
  · have hlt_cap : x.dir.changed.length < cap.toNat := by
      by_contra hge
      have heq_nat : cap.toNat = x.dir.changed.length := by omega
      exact heq_bv (ofNat_eq_of_toNat_eq heq_nat).symm
    have hbeq_ne : (BitVec.ofNat 64 x.dir.changed.length == cap) = false :=
      beq_false_of_ne heq_bv
    apply sepWPp_cut_543 (mid := atOff543 256) hcrl
    dsimp only [atOff543] at hpc ⊢
    wp_steps_sync_pool ((blkPl_543).base + BitVec.ofNat 64 256)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro s1 hs1 _hcrl_s1
    conv => arg 4; rw [← hs1]
    apply sepWPp_eq_pre
    · exact hpush s1 cap ptr [] (dirPutTailEnv_miss_nil hmiss) hlt_cap
        (by rw [hs1]; dsimp [atOff543]; simp only [wp_norm, arm64_norm])
        (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hrun)
        (by
          have hsp_eq : s1.sp = s.sp := by rw [hs1]; simp only [wp_norm, arm64_norm]
          simpa only [State.spAligned, hsp_eq] using hsp_align)
        (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hsp)
        (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact htr)
        ⟨by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.1,
         by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hhigh.2.2⟩
        (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx19)
        (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx20)
        (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx21)
        (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx22)
        (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx23)
        (by rw [hs1]; simp only [wp_norm, arm64_norm]; exact hx24)
    · rw [M.stepEvents_nil]
      sep_ac_rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
