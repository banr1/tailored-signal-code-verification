/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
meta import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Off-Trajectory Shadow Fallback `HookOk` at `strippedMallocngBudget`

Proves `HookOk` for `shadowFallback keep lim mmpl g.{alloc, dealloc, realloc}` against
`rustCli{Alloc, Dealloc, Realloc}BudgetSpec` at `strippedMallocngBudget` from `CliGhostAllocHooks`,
together with `HookOk` for `hookMemcpy` and `hookNoop` under `withVmPreserved`.
-/

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsShadowHooksFd

public section

set_option autoImplicit false
set_option linter.dupNamespace false

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet
  (framelessMemcpySpec framelessMemcpy_hookOk noAllocShimSpec noAllocShim_hookOk)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits FitsEvents MallocngCostModelIface
   MallocngCostModelSound NullAllowed OomPreserved RustLayoutOk VmPreserved
   rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
   rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (mallocngHookBudgetPool mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
  (CodeBlocksPermStripped keepsFrozen_offTraj_reStrip pool_stripped_of_satisfies
   restoreMallocngRXMem restoreMallocngRXS satisfies_mallocngPool_restoreRx
   satisfies_stripCodec_iff satisfies_strippedPool_of_mallocng_keepOut sc_brk sc_bs sc_fs
   sc_mem sc_pma sc_r64 sc_sp sc_st sc_sym sc_tp sc_tr stripCodecMem stripCodecS
   stripCodec_perm strippedMallocngBudget strippedMallocngBudget_live strippedMallocngPool)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)

/-- Off-trajectory shadow hook wrapper: when `lim.enforced` holds, temporarily restores `.rx` on
`mallocng` code blocks before running `fn`, then re-strips `.x` on `mallocng` blocks according to
`keep` while leaving permissions outside `mallocng` untouched. -/
@[expose] def shadowFallback (keep : BitVec 64 → Bool) (lim : BudgetLimits)
    (mmpl : Obj.MultiPlacement) (fn : State → State) (s : State) : State :=
  if lim.enforced then
    stripCodecS (fun a => keep a || !(VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome)
      (fn (restoreMallocngRXS mmpl s))
  else fn s

private theorem keepOut_agree_mallocng (keep : BitVec 64 → Bool) (mmpl : Obj.MultiPlacement) :
    ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true →
      (keep a || !(VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome) = keep a := by
  intro a ha
  simp [ha]

private theorem strippedPool_lim_eq_of_not_enforced {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} (henf : ¬ lim.enforced = true) :
    (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim =
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim := by
  funext st s
  change strippedMallocngPool keep M I γ mmpl tp brkStart lim st s =
    mallocngHookBudgetPool M I γ mmpl tp brkStart lim st s
  unfold strippedMallocngPool
  simp [henf]

private theorem shadowFallback_eq_of_not_enforced {keep : BitVec 64 → Bool}
    {lim : BudgetLimits} {mmpl : Obj.MultiPlacement} {fn : State → State}
    (henf : ¬ lim.enforced = true) :
    shadowFallback keep lim mmpl fn = fn := by
  funext s
  unfold shadowFallback
  simp [henf]

private theorem returned_reStrip_eq (mmpl : Obj.MultiPlacement) (k : BitVec 64 → Bool)
    (s0 s1 : State) :
    Returned (restoreMallocngRXS mmpl s0) s1 = Returned s0 (stripCodecS k s1) := by
  cases s0; cases s1; rfl

private theorem ccPreserved_reStrip_eq (mmpl : Obj.MultiPlacement) (k : BitVec 64 → Bool)
    (s0 s1 : State) :
    CallingConventionPreserved (restoreMallocngRXS mmpl s0) s1 =
      CallingConventionPreserved s0 (stripCodecS k s1) := by
  cases s0; cases s1; rfl

private theorem allocCallPreserved_reStrip_eq (mmpl : Obj.MultiPlacement) (k : BitVec 64 → Bool)
    (s0 s1 : State) :
    AllocCallPreserved (restoreMallocngRXS mmpl s0) s1 =
      AllocCallPreserved s0 (stripCodecS k s1) := by
  cases s0; cases s1; rfl

private theorem oomPreserved_reStrip_eq (mmpl : Obj.MultiPlacement) (k : BitVec 64 → Bool)
    (s0 s1 : State) :
    OomPreserved (restoreMallocngRXS mmpl s0) s1 =
      OomPreserved s0 (stripCodecS k s1) := by
  cases s0; cases s1; rfl

/-- Off-trajectory `HookOk` for `shadowFallback keep lim mmpl g.alloc` at
`strippedMallocngBudget keep M I hS γ mmpl tp brkStart`. -/
theorem hookOk_shadowFallback_alloc [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g) :
    HookOk (shadowFallback keep lim mmpl g.alloc)
      (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false) := by
  by_cases henf : lim.enforced = true
  · intro ⟨size, align, st⟩ R s0 hrun hpre hsp
    let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
    let A1 := strippedMallocngBudget keep M I hS γ mmpl tp brkStart
    let keepOut := fun a => keep a || !(VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome
    let s_rx := restoreMallocngRXS mmpl s0
    let s1 := g.alloc s_rx
    have hsf_eq : shadowFallback keep lim mmpl g.alloc s0 = stripCodecS keepOut s1 := by
      unfold shadowFallback; simp [henf, keepOut, s1, s_rx]
    rw [hsf_eq]
    let preRest : SepProp :=
      ⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
        RustLayoutOk size align ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        stackAt s0.sp allocHookStack ∗ R
    have hPre1 : (rustCliAllocBudgetSpec M A1 lim false).pre (size, align, st) s0 ∗ R =
        A1.pool lim st s0 ∗ preRest := by
      dsimp only [rustCliAllocBudgetSpec, preRest]; sep_ac_rfl
    have hPool1 : s0.mem ⊨ A1.pool lim st s0 ∗ preRest := hPre1 ▸ hpre
    have hcs : CodeBlocksPermStripped keep mmpl s0 := pool_stripped_of_satisfies hPool1 henf
    have hPool0 : s_rx.mem ⊨ A0.pool lim st s_rx ∗ preRest :=
      satisfies_mallocngPool_restoreRx hPool1
    have hPre0 : (rustCliAllocBudgetSpec M A0 lim false).pre (size, align, st) s_rx ∗ R =
        A0.pool lim st s_rx ∗ preRest := by
      have hr0 : s_rx.readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
      have hr1 : s_rx.readReg64 .x1 = s0.readReg64 .x1 := by cases s0; rfl
      have hrlr : s_rx.readReg64 .lr = s0.readReg64 .lr := by cases s0; rfl
      have hrsp : s_rx.sp = s0.sp := by cases s0; rfl
      dsimp only [rustCliAllocBudgetSpec, preRest]
      rw [hr0, hr1, hrlr, hrsp]
      sep_ac_rfl
    have hrun_rx : s_rx.status = .Running := by cases s0; exact hrun
    have hsp_rx : s_rx.spAligned = true := by cases s0; exact hsp
    obtain ⟨hkf1, hsym1, hout1⟩ := hG.alloc (size, align, st) R s_rx hrun_rx (hPre0.symm ▸ hPool0) hsp_rx
    have hkf : s0.mem.KeepsFrozen (stripCodecS keepOut s1).mem := by
      rw [sc_mem]
      exact keepsFrozen_offTraj_reStrip hcs (by cases s0; exact hkf1)
    have hsym : (stripCodecS keepOut s1).symtab = s0.symtab := by
      rw [sc_sym, hsym1]; cases s0; rfl
    refine ⟨hkf, hsym, ?_⟩
    rcases hout1 with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨(returned_reStrip_eq mmpl keepOut s0 s1) ▸ hret,
        (ccPreserved_reStrip_eq mmpl keepOut s0 s1) ▸ hcc, ?_⟩
      let st' := if s1.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st
      let postTail : SepProp :=
        if s1.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
        else ⌜(s1.readReg64 .x0).toNat % align = 0⌝ ∗ A0.live (s1.readReg64 .x0) size align ∗
          memRegion (s1.readReg64 .x0) size
      let postRest : SepProp :=
        ⌜AllocCallPreserved s0 (stripCodecS keepOut s1)⌝ ∗ stackAt s0.sp allocHookStack ∗
          postTail ∗ R
      have hPost0 : (rustCliAllocBudgetSpec M A0 lim false).post (size, align, st) s_rx s1 ∗ R =
          A0.pool lim st' s1 ∗ postRest := by
        have hacp := allocCallPreserved_reStrip_eq mmpl keepOut s0 s1
        have hrsp : s_rx.sp = s0.sp := by cases s0; rfl
        dsimp only [rustCliAllocBudgetSpec, st', postTail, postRest]
        rw [hacp, hrsp]
        simp only [Bool.false_eq_true, ↓reduceIte]
        sep_ac_rfl
      have hSat1 : (stripCodecS keepOut s1).mem ⊨
          A1.pool lim st' (stripCodecS keepOut s1) ∗ postRest :=
        satisfies_strippedPool_of_mallocng_keepOut (keepOut_agree_mallocng keep mmpl)
          (hPost0 ▸ hpost)
      have hPost1 : (rustCliAllocBudgetSpec M A1 lim false).post (size, align, st) s0
          (stripCodecS keepOut s1) ∗ R =
          A1.pool lim st' (stripCodecS keepOut s1) ∗ postRest := by
        have hlive : A1.live = A0.live := strippedMallocngBudget_live keep M I hS γ mmpl tp brkStart
        dsimp only [rustCliAllocBudgetSpec, st', postTail, postRest]
        simp only [Bool.false_eq_true, ↓reduceIte, sc_r64, hlive]
        sep_ac_rfl
      exact hPost1.symm ▸ hSat1
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · refine Or.inr (Or.inr (Or.inr ⟨by rw [sc_st]; exact ho_st, ?_⟩))
      rw [sc_mem, satisfies_stripCodec_iff]
      have hoomEq : (rustCliAllocBudgetSpec M A1 lim false).onOom (size, align, st) s0
          (stripCodecS keepOut s1) =
          (rustCliAllocBudgetSpec M A0 lim false).onOom (size, align, st) s_rx s1 := by
        dsimp only [rustCliAllocBudgetSpec]
        rw [oomPreserved_reStrip_eq mmpl keepOut s0 s1]
      rwa [hoomEq]
  · have hSpecEq :
        rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false =
          rustCliAllocBudgetSpec M
            (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim false := by
      unfold rustCliAllocBudgetSpec
      simp only [strippedPool_lim_eq_of_not_enforced henf, strippedMallocngBudget_live]
    rw [shadowFallback_eq_of_not_enforced henf, hSpecEq]
    exact hG.alloc

/-- Off-trajectory `HookOk` for `shadowFallback keep lim mmpl g.dealloc` at
`strippedMallocngBudget keep M I hS γ mmpl tp brkStart`. -/
theorem hookOk_shadowFallback_dealloc [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g) :
    HookOk (shadowFallback keep lim mmpl g.dealloc)
      (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim) := by
  by_cases henf : lim.enforced = true
  · intro ⟨p, size, align, st⟩ R s0 hrun hpre hsp
    let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
    let A1 := strippedMallocngBudget keep M I hS γ mmpl tp brkStart
    let keepOut := fun a => keep a || !(VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome
    let s_rx := restoreMallocngRXS mmpl s0
    let s1 := g.dealloc s_rx
    have hsf_eq : shadowFallback keep lim mmpl g.dealloc s0 = stripCodecS keepOut s1 := by
      unfold shadowFallback; simp [henf, keepOut, s1, s_rx]
    rw [hsf_eq]
    have hlive : A1.live = A0.live := strippedMallocngBudget_live keep M I hS γ mmpl tp brkStart
    let preRest : SepProp :=
      ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧ (s0.readReg64 .x2).toNat = align ∧
        LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        A0.live p size align ∗ memRegion p size ∗ stackAt s0.sp allocHookStack ∗ R
    have hPre1 : (rustCliDeallocBudgetSpec M A1 lim).pre (p, size, align, st) s0 ∗ R =
        A1.pool lim st s0 ∗ preRest := by
      dsimp only [rustCliDeallocBudgetSpec, preRest]; rw [hlive]; sep_ac_rfl
    have hPool1 : s0.mem ⊨ A1.pool lim st s0 ∗ preRest := hPre1 ▸ hpre
    have hcs : CodeBlocksPermStripped keep mmpl s0 := pool_stripped_of_satisfies hPool1 henf
    have hPool0 : s_rx.mem ⊨ A0.pool lim st s_rx ∗ preRest :=
      satisfies_mallocngPool_restoreRx hPool1
    have hPre0 : (rustCliDeallocBudgetSpec M A0 lim).pre (p, size, align, st) s_rx ∗ R =
        A0.pool lim st s_rx ∗ preRest := by
      have hr0 : s_rx.readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
      have hr1 : s_rx.readReg64 .x1 = s0.readReg64 .x1 := by cases s0; rfl
      have hr2 : s_rx.readReg64 .x2 = s0.readReg64 .x2 := by cases s0; rfl
      have hrlr : s_rx.readReg64 .lr = s0.readReg64 .lr := by cases s0; rfl
      have hrsp : s_rx.sp = s0.sp := by cases s0; rfl
      dsimp only [rustCliDeallocBudgetSpec, preRest]
      rw [hr0, hr1, hr2, hrlr, hrsp]
      sep_ac_rfl
    have hrun_rx : s_rx.status = .Running := by cases s0; exact hrun
    have hsp_rx : s_rx.spAligned = true := by cases s0; exact hsp
    obtain ⟨hkf1, hsym1, hout1⟩ := hG.dealloc (p, size, align, st) R s_rx hrun_rx (hPre0.symm ▸ hPool0) hsp_rx
    have hkf : s0.mem.KeepsFrozen (stripCodecS keepOut s1).mem := by
      rw [sc_mem]
      exact keepsFrozen_offTraj_reStrip hcs (by cases s0; exact hkf1)
    have hsym : (stripCodecS keepOut s1).symtab = s0.symtab := by
      rw [sc_sym, hsym1]; cases s0; rfl
    refine ⟨hkf, hsym, ?_⟩
    rcases hout1 with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
    · refine Or.inl ⟨(returned_reStrip_eq mmpl keepOut s0 s1) ▸ hret,
        (ccPreserved_reStrip_eq mmpl keepOut s0 s1) ▸ hcc, ?_⟩
      let st' := M.stepEvents (rustDeallocEvents size align) st
      let postRest : SepProp :=
        ⌜AllocCallPreserved s0 (stripCodecS keepOut s1) ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
          stackAt s0.sp allocHookStack ∗ R
      have hPost0 : (rustCliDeallocBudgetSpec M A0 lim).post (p, size, align, st) s_rx s1 ∗ R =
          A0.pool lim st' s1 ∗ postRest := by
        have hacp := allocCallPreserved_reStrip_eq mmpl keepOut s0 s1
        have hrsp : s_rx.sp = s0.sp := by cases s0; rfl
        dsimp only [rustCliDeallocBudgetSpec, st', postRest]
        rw [hacp, hrsp]
        sep_ac_rfl
      have hSat1 : (stripCodecS keepOut s1).mem ⊨
          A1.pool lim st' (stripCodecS keepOut s1) ∗ postRest :=
        satisfies_strippedPool_of_mallocng_keepOut (keepOut_agree_mallocng keep mmpl)
          (hPost0 ▸ hpost)
      have hPost1 : (rustCliDeallocBudgetSpec M A1 lim).post (p, size, align, st) s0
          (stripCodecS keepOut s1) ∗ R =
          A1.pool lim st' (stripCodecS keepOut s1) ∗ postRest := by
        dsimp only [rustCliDeallocBudgetSpec, st', postRest]
        sep_ac_rfl
      exact hPost1.symm ▸ hSat1
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · exact False.elim (not_satisfies_false_sepConj ho)
  · have hSpecEq :
        rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim =
          rustCliDeallocBudgetSpec M
            (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim := by
      unfold rustCliDeallocBudgetSpec
      simp only [strippedPool_lim_eq_of_not_enforced henf, strippedMallocngBudget_live]
    rw [shadowFallback_eq_of_not_enforced henf, hSpecEq]
    exact hG.dealloc

/-- Off-trajectory `HookOk` for `shadowFallback keep lim mmpl g.realloc` at
`strippedMallocngBudget keep M I hS γ mmpl tp brkStart`. -/
theorem hookOk_shadowFallback_realloc [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g) :
    HookOk (shadowFallback keep lim mmpl g.realloc)
      (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim) := by
  by_cases henf : lim.enforced = true
  · intro ⟨p, old, align, new, bs, st⟩ R s0 hrun hpre hsp
    let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
    let A1 := strippedMallocngBudget keep M I hS γ mmpl tp brkStart
    let keepOut := fun a => keep a || !(VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome
    let s_rx := restoreMallocngRXS mmpl s0
    let s1 := g.realloc s_rx
    have hsf_eq : shadowFallback keep lim mmpl g.realloc s0 = stripCodecS keepOut s1 := by
      unfold shadowFallback; simp [henf, keepOut, s1, s_rx]
    rw [hsf_eq]
    have hlive : A1.live = A0.live := strippedMallocngBudget_live keep M I hS γ mmpl tp brkStart
    let preRest : SepProp :=
      ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧ (s0.readReg64 .x2).toNat = align ∧
        (s0.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
        bs.length ≤ new ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
        A0.live p old align ∗ (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
        stackAt s0.sp allocHookStack ∗ R
    have hPre1 : (rustCliReallocBudgetSpec M A1 lim).pre (p, old, align, new, bs, st) s0 ∗ R =
        A1.pool lim st s0 ∗ preRest := by
      dsimp only [rustCliReallocBudgetSpec, preRest]; rw [hlive]; sep_ac_rfl
    have hPool1 : s0.mem ⊨ A1.pool lim st s0 ∗ preRest := hPre1 ▸ hpre
    have hcs : CodeBlocksPermStripped keep mmpl s0 := pool_stripped_of_satisfies hPool1 henf
    have hPool0 : s_rx.mem ⊨ A0.pool lim st s_rx ∗ preRest :=
      satisfies_mallocngPool_restoreRx hPool1
    have hPre0 : (rustCliReallocBudgetSpec M A0 lim).pre (p, old, align, new, bs, st) s_rx ∗ R =
        A0.pool lim st s_rx ∗ preRest := by
      have hr0 : s_rx.readReg64 .x0 = s0.readReg64 .x0 := by cases s0; rfl
      have hr1 : s_rx.readReg64 .x1 = s0.readReg64 .x1 := by cases s0; rfl
      have hr2 : s_rx.readReg64 .x2 = s0.readReg64 .x2 := by cases s0; rfl
      have hr3 : s_rx.readReg64 .x3 = s0.readReg64 .x3 := by cases s0; rfl
      have hrlr : s_rx.readReg64 .lr = s0.readReg64 .lr := by cases s0; rfl
      have hrsp : s_rx.sp = s0.sp := by cases s0; rfl
      dsimp only [rustCliReallocBudgetSpec, preRest]
      rw [hr0, hr1, hr2, hr3, hrlr, hrsp]
      sep_ac_rfl
    have hrun_rx : s_rx.status = .Running := by cases s0; exact hrun
    have hsp_rx : s_rx.spAligned = true := by cases s0; exact hsp
    obtain ⟨hkf1, hsym1, hout1⟩ :=
      hG.realloc (p, old, align, new, bs, st) R s_rx hrun_rx (hPre0.symm ▸ hPool0) hsp_rx
    have hkf : s0.mem.KeepsFrozen (stripCodecS keepOut s1).mem := by
      rw [sc_mem]
      exact keepsFrozen_offTraj_reStrip hcs (by cases s0; exact hkf1)
    have hsym : (stripCodecS keepOut s1).symtab = s0.symtab := by
      rw [sc_sym, hsym1]; cases s0; rfl
    refine ⟨hkf, hsym, ?_⟩
    rcases hout1 with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨(returned_reStrip_eq mmpl keepOut s0 s1) ▸ hret,
        (ccPreserved_reStrip_eq mmpl keepOut s0 s1) ▸ hcc, ?_⟩
      let st' := if s1.readReg64 .x0 = 0 then st else M.stepEvents (rustReallocEvents old new align) st
      let postTail : SepProp :=
        if s1.readReg64 .x0 = 0 then
          ⌜NullAllowed new align⌝ ∗ A0.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
        else
          ⌜(s1.readReg64 .x0).toNat % align = 0⌝ ∗ A0.live (s1.readReg64 .x0) new align ∗
            (s1.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (s1.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)
      let postRest : SepProp :=
        ⌜AllocCallPreserved s0 (stripCodecS keepOut s1)⌝ ∗ stackAt s0.sp allocHookStack ∗
          postTail ∗ R
      have hPost0 : (rustCliReallocBudgetSpec M A0 lim).post (p, old, align, new, bs, st) s_rx s1 ∗ R =
          A0.pool lim st' s1 ∗ postRest := by
        have hacp := allocCallPreserved_reStrip_eq mmpl keepOut s0 s1
        have hrsp : s_rx.sp = s0.sp := by cases s0; rfl
        dsimp only [rustCliReallocBudgetSpec, st', postTail, postRest]
        rw [hacp, hrsp]
        sep_ac_rfl
      have hSat1 : (stripCodecS keepOut s1).mem ⊨
          A1.pool lim st' (stripCodecS keepOut s1) ∗ postRest :=
        satisfies_strippedPool_of_mallocng_keepOut (keepOut_agree_mallocng keep mmpl)
          (hPost0 ▸ hpost)
      have hPost1 : (rustCliReallocBudgetSpec M A1 lim).post (p, old, align, new, bs, st) s0
          (stripCodecS keepOut s1) ∗ R =
          A1.pool lim st' (stripCodecS keepOut s1) ∗ postRest := by
        dsimp only [rustCliReallocBudgetSpec, st', postTail, postRest]
        simp only [sc_r64, hlive]
        sep_ac_rfl
      exact hPost1.symm ▸ hSat1
    · exact False.elim (not_satisfies_false_sepConj hp)
    · exact False.elim (not_satisfies_false_sepConj he)
    · refine Or.inr (Or.inr (Or.inr ⟨by rw [sc_st]; exact ho_st, ?_⟩))
      rw [sc_mem, satisfies_stripCodec_iff]
      have hoomEq : (rustCliReallocBudgetSpec M A1 lim).onOom (p, old, align, new, bs, st) s0
          (stripCodecS keepOut s1) =
          (rustCliReallocBudgetSpec M A0 lim).onOom (p, old, align, new, bs, st) s_rx s1 := by
        dsimp only [rustCliReallocBudgetSpec]
        rw [oomPreserved_reStrip_eq mmpl keepOut s0 s1]
      rwa [hoomEq]
  · have hSpecEq :
        rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim =
          rustCliReallocBudgetSpec M
            (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim := by
      unfold rustCliReallocBudgetSpec
      simp only [strippedPool_lim_eq_of_not_enforced henf, strippedMallocngBudget_live]
    rw [shadowFallback_eq_of_not_enforced henf, hSpecEq]
    exact hG.realloc

private theorem hookMemcpy_vm (s : State) : VmPreserved s (ProofLib.hookMemcpy s) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl,
    fun a => congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_writeBytes_norm _ _ _) a,
    fun _ _ _ => rfl⟩

/-- `HookOk` for `ProofLib.hookMemcpy` against `withVmPreserved framelessMemcpySpec`. -/
theorem hookOk_hookMemcpy_frameless_vm :
    HookOk ProofLib.hookMemcpy (withVmPreserved framelessMemcpySpec) :=
  hookOk_withVmPreserved framelessMemcpy_hookOk hookMemcpy_vm

/-- `HookOk` for `ProofLib.hookNoop` against `withVmPreserved noAllocShimSpec`. -/
theorem hookOk_hookNoop_noAllocShim_vm :
    HookOk ProofLib.hookNoop (withVmPreserved noAllocShimSpec) :=
  hookOk_withVmPreserved noAllocShim_hookOk (fun s => VmPreserved.refl s)

/-- `VmPreserved` transports across `stripCodecS keep` on both pre- and post-states. -/
theorem vmPreserved_stripCodec (keep : BitVec 64 → Bool) {u v : State}
    (hvm : VmPreserved u v) :
    VmPreserved (stripCodecS keep u) (stripCodecS keep v) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, fun a => ?_, fun fd hlo hhi => ?_⟩
  · simp only [sc_bs]; exact hvm.1.1
  · simp only [sc_brk]; exact hvm.1.2.1
  · simp only [sc_tp]; exact hvm.1.2.2
  · simp only [sc_pma]; exact hvm.2.1
  · simp only [sc_mem, stripCodec_perm, hvm.2.2.1 a]
  · simp only [sc_fs]; exact hvm.2.2.2 fd hlo hhi

/-- Stripped→stripped `SubroutineOutcome` transport for any `memcpyFn` satisfying
`HookOk memcpyFn (withVmPreserved framelessMemcpySpec)`. -/
theorem framelessMemcpy_stripped_to_stripped (keep : BitVec 64 → Bool)
    {memcpyFn : State → State}
    (hMcOk : HookOk memcpyFn (withVmPreserved framelessMemcpySpec)) (u : State) :
    ∀ x R,
      (stripCodecS keep u).status = .Running →
      ((stripCodecS keep u).mem ⊨
        (withVmPreserved framelessMemcpySpec).pre x (stripCodecS keep u) ∗ R) →
      (stripCodecS keep u).spAligned = true →
      SubroutineOutcome (withVmPreserved framelessMemcpySpec) x R
        (stripCodecS keep u) (stripCodecS keep (memcpyFn u)) := by
  rintro ⟨dst, src, bs⟩ R hrun_sc hpre_sc hsp_sc
  have hrun : u.status = .Running := by cases u; exact hrun_sc
  have hsp : u.spAligned = true := by cases u; exact hsp_sc
  have hpre_eq :
      (withVmPreserved framelessMemcpySpec).pre (dst, src, bs) (stripCodecS keep u) =
        (withVmPreserved framelessMemcpySpec).pre (dst, src, bs) u := by
    cases u; rfl
  have hpre : u.mem ⊨ (withVmPreserved framelessMemcpySpec).pre (dst, src, bs) u ∗ R := by
    rw [hpre_eq, sc_mem] at hpre_sc
    exact (satisfies_stripCodec_iff keep u.mem _).mp hpre_sc
  obtain ⟨_, _, hout⟩ := hMcOk (dst, src, bs) R u hrun hpre hsp
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨by generalize memcpyFn u = v at hret ⊢; cases u; cases v; exact hret,
      by generalize memcpyFn u = v at hcc ⊢; cases u; cases v; exact hcc, ?_⟩
    dsimp only [withVmPreserved, framelessMemcpySpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hvm, hpost_rest⟩ := hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_rest
    obtain ⟨⟨hx0, htr⟩, hmem_post⟩ := hpost_rest
    rw [sc_mem, satisfies_stripCodec_iff]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨vmPreserved_stripCodec keep hvm, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by rw [sc_r64]; exact hx0, by rw [sc_tr, sc_tr]; exact htr⟩, hmem_post⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsShadowHooksFd
