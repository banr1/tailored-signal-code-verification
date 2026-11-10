/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn -- proof-setup: allow-public-import
import ProofLib.SepLogic.HeapIntro

/-!
# Exact Clobber Endpoint for Ghost `memcpy` Hooks (`HooksDehook.MemcpyGhostExact`)

- **Role:** `Role::Proof` (untrusted proof module outside the TCB; #1255 H3 "G-exact" spike).
- **Overview:**
  Proves that every `linkedCallHook`-based `memcpy` ghost hook (`memcpyGhostHook`,
  `memcpyGhostHookBlk20`, `memcpyGhostHookPure20`, `f3EmptyMemcpyGhostHook`, `f3MemcpyGhostHook`,
  plus `memcpyGhostHookK` / `f3EmptyMemcpyGhostHookK` under `keep (u.readReg64 .lr) = false`) as
  well as `hookMemcpy` / `memcpyHook` satisfies `HookExactMemcpy`:
  - Under `u.status = .Running`, `u.spAligned = true`, register setup `(dst, src, len, lr)`,
    `u.mem.readBytes src len = bs`, `u.mem.RW dst len`, `u.mem.Readable src len`, and
    `len = 0 ∨ DisjointRegions dst len src len`, there exists `c : MemcpyClobber`
    (`{x1..x17, pstate}`) such that
    `f u = applyMemcpyClobber u (u.mem.writeBytes dst bs) lr c`.
  - Consequently, raw-`RunsTo` `memcpy` call sites step through `HookSatExactMemcpy H lsMemcpySym`
    via `s2_memcpy_step_placed_of_exact` / `placed_memcpy_step_of_exact` in the `∀ c : MemcpyClobber`
    shape with exact `mem = s.mem.writeBytes dst bs` (zero `S2Frame` re-anchoring).
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open Arm64.Process (pureWordsProg)
open VerifiedLibraries.Musl (memcpySrc memcpySymWords)
open CryptoVerification.SignalSession (CliHooks)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (
  MemcpyClobber applyMemcpyClobber
  codeLoaded_pureWordsProg_of_hasWords pureWords_memcpy_steps_exact
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre ActiveRealRun ExecFrozen linkedCallHook stepsUntil_of_stripS_standard
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostReplays (
  f3RealProg617 f3RealProg617_svc_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  mallocngBlockProg20_externAt_none mallocngBlockProg20_hasWords
  masterMemcpySpec memcpySpecK pureWordsProg_externAt_none pureWordsProg_memcpy_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  keepFsTrace_hookMemcpy_eq keepMemcpyBlk20
  memcpyGhostHook memcpyGhostHookBlk20 memcpyGhostHookK memcpyGhostHookPure20
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn (
  f3EmptyMemcpyGhostHook f3EmptyMemcpyGhostHook_eq
  f3EmptyMemcpyGhostHookK f3EmptyMemcpyGhostHookK_eq
  f3MemcpyGhostHook mallocngBlockProg20_svc_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookExactMemcpy hookMemcpy_exact
)

/-! ## 3. Separation-Logic Precondition & `stripExecOutside` Helpers -/

private theorem not_both_inRegion_of_disjoint {dst src x : BitVec 64} {n : Nat}
    (hn : n < 2 ^ 64) (hdisj : n = 0 ∨ DisjointRegions dst n src n)
    (hx1 : InRegion dst n x) (hx2 : InRegion src n x) : False := by
  rcases hdisj with rfl | ⟨hd1, hd2⟩
  · exact Nat.not_lt_zero _ hx1
  · dsimp only [InRegion] at hx1 hx2
    bv_omega

/-- Construct `u.mem ⊨ masterMemcpySpec.pre (true, dst, src, bs) u ∗ emp` directly from raw
    `RW`/`Readable` and non-overlap hypotheses. -/
theorem satisfies_masterMemcpy_pre_ro {u : State} {dst src : BitVec 64} {len : Nat}
    {bs : List (BitVec 8)}
    (hx0 : u.readReg64 .x0 = dst)
    (hx1 : u.readReg64 .x1 = src)
    (hx2 : (u.readReg64 .x2).toNat = len)
    (hread : u.mem.readBytes src len = bs)
    (hrw : u.mem.RW dst len)
    (hreadable : u.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len) :
    u.mem ⊨ masterMemcpySpec.pre (true, dst, src, bs) u ∗ emp := by
  have hbs_len : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_lt : bs.length < 2 ^ 64 := by rw [hbs_len, ← hx2]; exact (u.readReg64 .x2).isLt
  have hlen_le : bs.length ≤ 2 ^ 64 := Nat.le_of_lt hlen_lt
  rw [sepConj_emp]
  dsimp only [masterMemcpySpec, memcpySrc, cond]
  rw [satisfies_pure_sepConj]
  refine ⟨⟨hx0, hx1, hx2.trans hbs_len.symm⟩, ?_⟩
  let h₁ := regionHeap dst bs.length u.mem
  let h₂ := regionHeapRO src bs.length u.mem
  have hp : (memRegion dst bs.length) h₁ :=
    ((IsBlock.memRegion dst bs.length).iff h₁).mpr ⟨u.mem, trivial, rfl⟩
  have hq : (src ↦ᵣ bs) h₂ :=
    ((IsBlockRO.pointsToBytesRO src bs hlen_le).iff h₂).mpr ⟨u.mem, hbs_len.symm ▸ hread, rfl⟩
  have hm : (h₁.union h₂).Matches u.mem :=
    Heap.Matches.union
      (IsBlock.regionHeap_matches dst bs.length u.mem (hbs_len.symm ▸ hrw))
      (IsBlockRO.regionHeapRO_matches src bs.length u.mem (hbs_len.symm ▸ hreadable))
  have hd : h₁.Disjoint h₂ := by
    refine Heap.Disjoint.of_phys_left (ha := by simp [h₁, regionHeap])
      (hf := by simp [h₁, regionHeap]) (hm := by simp [h₁, regionHeap]) fun x => ?_
    by_cases hx_dst : InRegion dst bs.length x
    · have hx_src : ¬ InRegion src bs.length x := fun hxs =>
        not_both_inRegion_of_disjoint hlen_lt (hbs_len.symm ▸ hdisj) hx_dst hxs
      exact Or.inr (Or.inl (by simp [h₂, regionHeapRO, hx_src]))
    · exact Or.inl (by simp [h₁, regionHeap, hx_dst])
  exact Satisfies.sepConj_intro hd hp hq hm

private theorem strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (base : BitVec 64) (n : Nat),
      (stripExecOutside keep m).readBytes base n = m.readBytes base n
  | _, 0 => rfl
  | base, n + 1 => by
    simp only [Memory.readBytes, strip_read8, strip_readBytes keep m (base + 1#64) n]

private theorem strip_writeBytes (keep : BitVec 64 → Bool) (m : Memory) (base : BitVec 64)
    (bs : List (BitVec 8)) :
    (stripExecOutside keep m).writeBytes base bs = stripExecOutside keep (m.writeBytes base bs) := by
  induction bs generalizing m base with
  | nil => rfl
  | cons _ _ ih => simp only [Memory.writeBytes, strip_write8, ih]

private theorem writeBytes_perm_eq_local (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes base bs).perm = m.perm := by
  induction bs generalizing m base with
  | nil => rfl
  | cons b rest ih =>
    dsimp [Memory.writeBytes]
    rw [ih]
    funext a
    dsimp [Memory.write8, Memory.perm, Memory.rawPerm, Perm.rwx]
    by_cases ha : a = base
    · subst ha; simp only [↓reduceIte]; rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl
    · simp only [ha, ↓reduceIte]

private theorem strip_rw_of_rw (keep : BitVec 64 → Bool) {m : Memory} {dst : BitVec 64} {len : Nat}
    (hrw : m.RW dst len) : (stripExecOutside keep m).RW dst len := by
  intro a hin
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin)
  exact Memory.permNoLazy_eq_some_rw_iff.mpr
    ⟨(strip_perm_props keep m a).2.2.2.mpr hp, (strip_isLazyFree keep m a).trans hlf⟩

private theorem strip_readable_of_readable (keep : BitVec 64 → Bool) {m : Memory}
    {src : BitVec 64} {len : Nat} (hr : m.Readable src len) :
    (stripExecOutside keep m).Readable src len := by
  intro a hin
  obtain ⟨hpr, hlf⟩ := hr a hin
  exact ⟨((strip_perm_props keep m a).1).trans hpr, (strip_isLazyFree keep m a).trans hlf⟩

private theorem perm_eq_of_stripExecOutside_keepsFrozen_local
    {keep : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keep mf).perm a = (stripExecOutside keep m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  have hst := hstrip a
  rw [strip_perm, strip_perm] at hst
  have hfr0_a := hfr0 a
  have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a with
    | none =>
      cases hpf : mf.perm a with
      | none => rfl
      | some pf =>
        rw [hp0, hpf] at hst
        simp [Option.map] at hst
    | some p0 =>
      cases hpf : mf.perm a with
      | none =>
        rw [hp0, hpf] at hst
        simp [Option.map] at hst
      | some pf =>
        rw [hp0] at hfr0_a hfrozen0 hst
        rw [hpf] at hfrf_a hst
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩
        rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hst
        cases hk : keep a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;>
          simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem mem_eq_of_stripExecOutside_eq_and_perm_eq
    {keep : BitVec 64 → Bool} {m1 m2 : Memory}
    (hstrip : stripExecOutside keep m1 = stripExecOutside keep m2)
    (hperm : ∀ a : BitVec 64, m1.perm a = m2.perm a) :
    m1 = m2 := by
  apply Memory.ext; funext a
  have hc := congrFun (congrArg Memory.cells hstrip) a
  have hp := hperm a
  dsimp only [stripExecOutside, Memory.perm, Perm.rwx] at hc hp
  cases h1 : m1.cells a with
  | none =>
    cases h2 : m2.cells a with
    | none => rfl
    | some cb2 =>
      rw [h1, h2] at hc
      rcases cb2 with ⟨_ | _, _⟩ <;> cases hc
  | some cb1 =>
    cases h2 : m2.cells a with
    | none =>
      rw [h1, h2] at hc
      rcases cb1 with ⟨_ | _, _⟩ <;> cases hc
    | some cb2 =>
      rw [h1, h2] at hc hp
      rcases cb1 with ⟨_ | ⟨r1, w1, x1, lf1, an1⟩, b1⟩ <;>
        rcases cb2 with ⟨_ | ⟨r2, w2, x2, lf2, an2⟩, b2⟩
      · cases hc; rfl
      · cases hc
      · cases hc
      · simp only [Option.some.injEq, Perm.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl, rfl, -, -⟩
        unfold stripPerm at hc
        cases hk : keep a <;> cases x1 <;>
          simp only [hk, Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false,
            Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq, Prod.mk.injEq, Perm.mk.injEq] at hc <;>
          rcases hc with ⟨⟨-, -, -, rfl, rfl⟩, rfl⟩ <;> rfl

/-! ## 4. Main Ghost-Hook Exactness Theorems (`HookExactMemcpy`) -/

/-- Main exactness theorem for `memcpyGhostHook`: whenever `P_real` and `P_sub` use
    `Syscall.standard`, `P_real` is extern-free on `keep`, `P_sub` is extern-free everywhere, and
    `P_sub.hasWords entryTarget memcpySymWords` holds, `memcpyGhostHook keep P_real P_sub entryTarget`
    satisfies `HookExactMemcpy` (in both its `ActiveRealRun` and `hookMemcpy` fallback branches). -/
theorem memcpyGhostHook_exact
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords) :
    HookExactMemcpy (memcpyGhostHook keep P_real P_sub entryTarget) := by
  classical
  intro u dst src lr len bs hrun hsp hx0 hx1 hx2 hlr hread hrw hreadable hdisj
  have hPre : ActiveRealPre masterMemcpySpec u :=
    ⟨hrun, hsp, (true, dst, src, bs), emp,
      satisfies_masterMemcpy_pre_ro hx0 hx1 hx2 hread hrw hreadable hdisj⟩
  unfold memcpyGhostHook linkedCallHook
  simp only [hPre, ↓reduceDIte]
  by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget u
  · simp only [hReal, ↓reduceDIte]
    let s1 := u.setPC entryTarget
    let s1' := stripS keep s1
    have hcl_pw : (pureWordsProg entryTarget memcpySymWords).CodeLoaded s1'.mem := by
      have hm : s1'.mem = stripExecOutside keep u.mem := by cases u; rfl
      rw [hm]
      exact codeLoaded_pureWordsProg_of_hasWords hReal.2.2.1 hwords (by decide)
    have hs1'_run : s1'.status = .Running := by cases u; exact hrun
    have hs1'_pc : s1'.pc = entryTarget := by cases u; rfl
    have hs1'_x0 : s1'.readReg64 .x0 = dst := by cases u; exact hx0
    have hs1'_x1 : s1'.readReg64 .x1 = src := by cases u; exact hx1
    have hs1'_x2 : (s1'.readReg64 .x2).toNat = len := by cases u; exact hx2
    have hs1'_lr : s1'.readReg64 .lr = lr := by cases u; exact hlr
    have hs1'_read : s1'.mem.readBytes src len = bs := by
      have hm : s1'.mem = stripExecOutside keep u.mem := by cases u; rfl
      rw [hm, strip_readBytes, hread]
    have hs1'_rw : s1'.mem.RW dst len := by
      have hm : s1'.mem = stripExecOutside keep u.mem := by cases u; rfl
      rw [hm]; exact strip_rw_of_rw keep hrw
    have hs1'_readable : s1'.mem.Readable src len := by
      have hm : s1'.mem = stripExecOutside keep u.mem := by cases u; rfl
      rw [hm]; exact strip_readable_of_readable keep hreadable
    obtain ⟨c, hsteps_sub⟩ := pureWords_memcpy_steps_exact hcl_pw (fun a _ => hsub_no a)
      hs1'_run hs1'_pc hs1'_x0 hs1'_x1 hs1'_x2 hs1'_lr hs1'_read hs1'_rw hs1'_readable hdisj
    let sf_target := applyMemcpyClobber u (u.mem.writeBytes dst bs) lr c
    have hsf'_eq :
        applyMemcpyClobber s1' (s1'.mem.writeBytes dst bs) lr c = stripS keep sf_target := by
      have hm : s1'.mem = stripExecOutside keep u.mem := by cases u; rfl
      rw [hm, strip_writeBytes]
      cases u; rfl
    rw [hsf'_eq] at hsteps_sub
    have hpc_sft : (stripS keep sf_target).pc = u.readReg64 .lr := by
      have hpc0 : (stripS keep sf_target).pc = lr := by cases u; rfl
      exact hpc0.trans hlr.symm
    have hsp_sft : (stripS keep sf_target).sp = u.sp := by cases u; rfl
    have hst_sft : (stripS keep sf_target).status = .Running := by cases u; exact hrun
    have hstop' : SubroutineStop u (stripS keep sf_target) :=
      Or.inl ⟨hpc_sft, hsp_sft, hst_sft⟩
    have hnhalt' : (stripS keep sf_target).status ≠ .Halted := by
      rw [hst_sft]; decide
    obtain ⟨sf, huntil, hstop_sf, hsf_strip, hfr_sf⟩ :=
      stepsUntil_of_stripS_standard (s0 := u) hsvc_real hsvc_sub hreal_no
        (fun pc _ he => nomatch hsub_no pc ▸ he)
        hReal.2.1 hsteps_sub hstop' hnhalt' s1 rfl hReal.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
    refine ⟨c, hdet.trans ?_⟩
    have hstrip_mem : stripExecOutside keep sf.mem = stripExecOutside keep sf_target.mem := by
      have hm := (congrArg State.mem hsf_strip).symm
      simpa [stripS] using hm
    have hstrip_perm : ∀ a : BitVec 64,
        (stripExecOutside keep sf.mem).perm a = (stripExecOutside keep u.mem).perm a := by
      intro a
      rw [hstrip_mem]
      have hwb : sf_target.mem = u.mem.writeBytes dst bs := by cases u; rfl
      rw [hwb, ← strip_writeBytes]
      exact congrFun (writeBytes_perm_eq_local (stripExecOutside keep u.mem) dst bs) a
    have hperm_u : ∀ a : BitVec 64, sf.mem.perm a = u.mem.perm a :=
      perm_eq_of_stripExecOutside_keepsFrozen_local hReal.1 hfr_sf huntil.toSteps.keepsFrozen
        hstrip_perm
    have hperm_target : ∀ a : BitVec 64, sf.mem.perm a = sf_target.mem.perm a := by
      intro a
      have hwb : sf_target.mem = u.mem.writeBytes dst bs := by cases u; rfl
      rw [hwb, hperm_u a]
      exact (congrFun (writeBytes_perm_eq_local u.mem dst bs) a).symm
    have hmem_eq : sf.mem = sf_target.mem :=
      mem_eq_of_stripExecOutside_eq_and_perm_eq hstrip_mem hperm_target
    cases sf; cases sf_target
    dsimp only [stripS, State.setMem] at hsf_strip hmem_eq
    injection hsf_strip
    subst_vars
    rfl
  · simp only [hReal, ↓reduceDIte, keepFsTrace_hookMemcpy_eq]
    exact hookMemcpy_exact hrun hsp hx0 hx1 hx2 hlr hread hrw hreadable hdisj

theorem memcpyGhostHookBlk20_exact
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) :
    HookExactMemcpy (memcpyGhostHookBlk20 keep P_real mmpl) :=
  memcpyGhostHook_exact hsvc_real (mallocngBlockProg20_svc_eq mmpl) hreal_no
    (mallocngBlockProg20_externAt_none mmpl Syscall.standard)
    (mallocngBlockProg20_hasWords mmpl Syscall.standard)

theorem memcpyGhostHookPure20_exact
    {keep : BitVec 64 → Bool} {P_real : Program} (mmpl : MultiPlacement)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) :
    HookExactMemcpy (memcpyGhostHookPure20 keep P_real mmpl) :=
  memcpyGhostHook_exact hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none (mmpl.base 20) memcpySymWords)
    (pureWordsProg_memcpy_hasWords (mmpl.base 20))

theorem f3EmptyMemcpyGhostHook_exact
    (keep : BitVec 64 → Bool) {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords) :
    HookExactMemcpy (f3EmptyMemcpyGhostHook keep P_sub entryTarget) := by
  rw [f3EmptyMemcpyGhostHook_eq]
  exact memcpyGhostHook_exact rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords

theorem f3MemcpyGhostHook_exact
    {keep : BitVec 64 → Bool} (mpl mmpl : MultiPlacement) (W : CliHooks)
    (hreal_no : ∀ pc, keep pc = true → (f3RealProg617 mpl mmpl W).externAt? pc = none) :
    HookExactMemcpy (f3MemcpyGhostHook keep mpl mmpl W) :=
  memcpyGhostHookBlk20_exact mmpl (f3RealProg617_svc_eq mpl mmpl W) hreal_no

theorem f3MemcpyGhostHookNarrow_exact
    (mpl mmpl : MultiPlacement) (W : CliHooks)
    (hreal_no : ∀ pc, keepMemcpyBlk20 mmpl pc = true →
      (f3RealProg617 mpl mmpl W).externAt? pc = none) :
    HookExactMemcpy (f3MemcpyGhostHook (keepMemcpyBlk20 mmpl) mpl mmpl W) :=
  f3MemcpyGhostHook_exact mpl mmpl W hreal_no

/-- When `keep (u.readReg64 .lr) = false` and `ActiveRealPre masterMemcpySpec u` hold,
    `memcpyGhostHookK` agrees pointwise with `memcpyGhostHook`. -/
theorem memcpyGhostHookK_eq_of_keepLr_false
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) {u : State}
    (hPre : ActiveRealPre masterMemcpySpec u)
    (hlr_false : keep (u.readReg64 .lr) = false) :
    memcpyGhostHookK keep P_real P_sub entryTarget u =
      memcpyGhostHook keep P_real P_sub entryTarget u := by
  classical
  have hPreK : ActiveRealPre (memcpySpecK keep masterMemcpySpec) u := by
    rcases hPre with ⟨hrun, hsp, x, R, hsat⟩
    refine ⟨hrun, hsp, x, R, ?_⟩
    dsimp only [memcpySpecK]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hlr_false, hsat⟩
  unfold memcpyGhostHookK memcpyGhostHook linkedCallHook
  simp only [hPreK, hPre, ↓reduceDIte]

theorem memcpyGhostHookK_exact_of_keepLr_false
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    {u : State} {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hlr_false : keep (u.readReg64 .lr) = false)
    (hrun : u.status = .Running)
    (hsp : u.spAligned = true)
    (hx0 : u.readReg64 .x0 = dst)
    (hx1 : u.readReg64 .x1 = src)
    (hx2 : (u.readReg64 .x2).toNat = len)
    (hlr : u.readReg64 .lr = lr)
    (hread : u.mem.readBytes src len = bs)
    (hrw : u.mem.RW dst len)
    (hreadable : u.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len) :
    ∃ c : MemcpyClobber,
      memcpyGhostHookK keep P_real P_sub entryTarget u =
        applyMemcpyClobber u (u.mem.writeBytes dst bs) lr c := by
  have hPre : ActiveRealPre masterMemcpySpec u :=
    ⟨hrun, hsp, (true, dst, src, bs), emp,
      satisfies_masterMemcpy_pre_ro hx0 hx1 hx2 hread hrw hreadable hdisj⟩
  rw [memcpyGhostHookK_eq_of_keepLr_false keep P_real P_sub entryTarget hPre hlr_false]
  exact memcpyGhostHook_exact hsvc_real hsvc_sub hreal_no hsub_no hwords
    hrun hsp hx0 hx1 hx2 hlr hread hrw hreadable hdisj

theorem f3EmptyMemcpyGhostHookK_exact_of_keepLr_false
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    {u : State} {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hlr_false : keep (u.readReg64 .lr) = false)
    (hrun : u.status = .Running)
    (hsp : u.spAligned = true)
    (hx0 : u.readReg64 .x0 = dst)
    (hx1 : u.readReg64 .x1 = src)
    (hx2 : (u.readReg64 .x2).toNat = len)
    (hlr : u.readReg64 .lr = lr)
    (hread : u.mem.readBytes src len = bs)
    (hrw : u.mem.RW dst len)
    (hreadable : u.mem.Readable src len)
    (hdisj : len = 0 ∨ DisjointRegions dst len src len) :
    ∃ c : MemcpyClobber,
      f3EmptyMemcpyGhostHookK keep P_sub entryTarget u =
        applyMemcpyClobber u (u.mem.writeBytes dst bs) lr c := by
  rw [f3EmptyMemcpyGhostHookK_eq]
  exact memcpyGhostHookK_exact_of_keepLr_false rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords
    hlr_false hrun hsp hx0 hx1 hx2 hlr hread hrw hreadable hdisj

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact

-- AUTO-BRIDGE BEGIN
namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact
export LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (
  HookExactMemcpy HookSatExactMemcpy hookSatExactMemcpy_of_eq
  applyMemcpyClobber_ofState_eq hookMemcpy_eq_applyMemcpyClobber
  hookMemcpy_exact memcpyHook_exact
  s2_memcpy_step_placed_of_exact placed_memcpy_step_of_exact
)
end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact
-- AUTO-BRIDGE END
