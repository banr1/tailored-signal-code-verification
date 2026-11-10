/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq

/-!
# Per-Address `HooksUnfetchedPerPc` & Stock-Link `Steps` Lift (`ElfSlicesPqOomHooksUnfetchedPerPc`)

Stock-`ld.lld` replacement for `h2fsgen_HooksUnfetched` / `h2fsgen_hooksUnfetched_of_frozenZeroWord`
(`ElfSlicesPqOomH2FirstStopGeneric`) and `h2sl_realW_hooksUnfetched` (`ElfSlicesPqOomH2StepsLiftR2`).

## Why `h2fsgen_HooksUnfetched` Breaks on a Stock `ld.lld` Link

`h2fsgen_HooksUnfetched P2 m` demands `Program.pureMem.fetchMem m' pc = none` at **every** address
`pc` where `P2.externAt? pc ≠ none`. On a stock `ld.lld` link, hooked symbols backed by real linked
code (`"memmove"`, `"bcmp"`, `"strlen"` from `libc.a`; `lsWriteFileSym`, `lsWriteStdoutSym` from
`signal_session_io`; plus `"memset"` and `"memcpy"` prior to S2′) map executable `Perm.rx`
instructions at `pc`, so `Program.pureMem.fetchMem m' pc = some inst ≠ none`.

## Per-Address Replacement (`HooksUnfetchedPerPc`)

1. **Engine hook-before-fetch (`fetchMem_eq_none_of_externAt_ne_none`,
   `step_at_extern_fires_hook_without_fetch`)**: `Arm64.Program.fetchMem` checks
   `(prog.externAt? pc).isSome` **before** reading or decoding memory, and `Arm64.Step` at a hooked
   PC takes `Step.extern` / `Step.extern_fault` without consulting `s.mem` at `s.pc`. Consequently,
   real machine code sitting under an active hook in `P1` is **never fetched by `P1`**.
2. **Per-PC predicate (`HooksUnfetchedPerPc D P1 P2 m`)**: requires `Program.pureMem.fetchMem m' pc = none`
   **only** at addresses `pc` that satisfy **all three** of:
   - `D pc = true` (`pc` lies in the visited executable domain `D` of the `P1` subroutine run),
   - `P1.externAt? pc = none` (`P1` does **not** itself hook `pc` before fetch), and
   - `P2.externAt? pc ≠ none` (`P2` hooks `pc`).
   Every hooked real-code symbol on a stock link is discharged per address by either:
   - **(C1) Outside `D` (`D pc = false`)** — e.g. `"memmove"`, `"bcmp"`, `"strlen"`,
     `lsWriteFileSym`, `lsWriteStdoutSym` when `D` is the proved de-hooked callee domain;
   - **(C2) Hook-before-fetch in `P1` (`P1.externAt? pc ≠ none`)** — e.g. `"memcpy"` in
     `hole2_strCloneProg mpl` even when `"memcpy"` holds real `libc.a` instructions; or
   - **(C3) Frozen `0#32` stub (`m.read32 pc = 0#32`)** — for any `P1`-unhooked Z-stub in `D`.
3. **Zero-churn caller bridges (`stepsVisitedIn_of_allProg`, `stepsVisitedIn_of_det`,
   `stepsUntil_emptyProg_to_realW_perPc`, `stepsUntil_strClone_to_realW_perPc`,
   `branch2_f3LinkedCallHook_perPc`, `steps_of_direct_or_b_stub_on`)**:
   preserve `ActiveRealRun`, `ActiveF3ReadFileRun`, `ActiveReadStdinLinkedRun`, and
   `H2Branch2` / `H2StepsLiftR2` conclusion shapes with **zero** `h2sl_checkCompactZeroRxB` check.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHooksUnfetchedPerPc

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealRun ExecFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks
  (ActiveF3CallPre f3LinkedCallHook)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer
  (StubReachesTargetOn)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_HooksUnfetched h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det)

/-! ## 1. Engine Semantics: Active Hook Fires Before Instruction Fetch -/

/-- In the trusted ARM64 semantics, `Program.fetchMem` returns `none` whenever
    `P.externAt? pc ≠ none`, **regardless** of permissions or machine-code bytes in `m` at `pc`. -/
theorem fetchMem_eq_none_of_externAt_ne_none {P : Program} (m : Memory) {pc : BitVec 64}
    (hext : P.externAt? pc ≠ none) :
    P.fetchMem m pc = none := by
  unfold Program.fetchMem
  cases h : P.externAt? pc with
  | none => exact False.elim (hext h)
  | some _ => rfl

/-- Converse: any successful instruction fetch `P.fetchMem m pc = some inst` implies
    `P.externAt? pc = none` and `Program.pureMem.fetchMem m pc = some inst`. -/
theorem externAt_none_and_pureMem_of_fetchMem_some {P : Program} {m : Memory}
    {pc : BitVec 64} {inst : Instr}
    (hfm : P.fetchMem m pc = some inst) :
    P.externAt? pc = none ∧ Program.pureMem.fetchMem m pc = some inst := by
  unfold Program.fetchMem at hfm ⊢
  cases he : P.externAt? pc with
  | some _ =>
    rw [he] at hfm
    simp at hfm
  | none =>
    rw [he] at hfm
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm
    exact ⟨rfl, by
      simpa [Program.pureMem, Program.pureWithSvc, Program.ofSvc,
        Program.externAt?, Program.hookAtOff?] using hfm⟩

/-- At any PC where `P.externAt? s.pc = some f`, `Arm64.Step P s s'` **never** takes `Step.exec` or
    `Step.halt_unmapped`: the hook `f` fires (`Step.extern` or `Step.extern_fault`) without reading
    or decoding instruction bytes at `s.pc`, even if real `Perm.rx` code is mapped there. -/
theorem step_at_extern_fires_hook_without_fetch {P : Program} {s s' : State}
    {f : State → State} (hext : P.externAt? s.pc = some f) (hst : Step P s s') :
    s.status = .Running ∧
      ((s.mem.KeepsFrozen (f s).mem ∧ (f s).symtab = s.symtab ∧ s' = f s) ∨
       (¬ (s.mem.KeepsFrozen (f s).mem ∧ (f s).symtab = s.symtab) ∧
         s' = { s with status := .Exception "extern hook modified read-only memory or symbol table" })) := by
  cases hst with
  | exec _ hfm =>
    have hnone := fetchMem_eq_none_of_externAt_ne_none s.mem (by rw [hext]; rintro ⟨⟩)
    rw [hnone] at hfm
    cases hfm
  | halt_unmapped _ _ he0 =>
    rw [hext] at he0
    cases he0
  | extern hrun he hkf hsym =>
    rw [hext] at he
    cases he
    exact ⟨hrun, Or.inl ⟨hkf, hsym, rfl⟩⟩
  | extern_fault hrun he hbad =>
    rw [hext] at he
    cases he
    exact ⟨hrun, Or.inr ⟨hbad, rfl⟩⟩

private theorem evalInst_eq_of_svc_eq {P1 P2 : Program} (hsvc : P1.svc = P2.svc)
    (inst : Instr) (s : State) :
    P1.evalInst inst s = P2.evalInst inst s := by
  simp only [Program.evalInst, hsvc]

private theorem steps_preserves_halted {P : Program} {a b : State}
    (h : Steps P a b) (ha : a.status = .Halted) : b.status = .Halted := by
  induction h with
  | refl _ => exact ha
  | @step s1 _ _ h1 _ _ =>
    have hr : s1.status = .Running := by cases h1 <;> assumption
    rw [ha] at hr
    cases hr

private theorem not_subroutineStop_of_halted {s0 sf : State}
    (hstop : SubroutineStop s0 sf) : sf.status ≠ .Halted := by
  intro hh
  rcases hstop with ⟨_, _, hr⟩ | hpan | ⟨_, hex⟩ | hoom <;> rw [hh] at * <;> contradiction

/-! ## 2. Per-Address `HooksUnfetchedPerPc` & Stock-Link Criteria -/

/-- **Per-address replacement for `h2fsgen_HooksUnfetched`:**
    Requires `Program.pureMem.fetchMem m' pc = none` **only** at addresses `pc` inside the visited
    domain `D` (`D pc = true`) that are **unhooked in `P1`** (`P1.externAt? pc = none`) yet
    **hooked in `P2`** (`P2.externAt? pc ≠ none`).

    Consequently, real `Perm.rx` code under a `P2` hook at `pc` is sound whenever either:
    - `D pc = false` (`pc` is outside the subroutine's executable keep-domain `D`), or
    - `P1.externAt? pc ≠ none` (`P1` hooks `pc` too, so `P1` fires its hook before fetch). -/
@[expose] def HooksUnfetchedPerPc (D : BitVec 64 → Bool) (P1 P2 : Program) (m : Memory) : Prop :=
  ∀ (m' : Memory) (pc : BitVec 64),
    m.KeepsFrozen m' →
    D pc = true →
    P1.externAt? pc = none →
    P2.externAt? pc ≠ none →
      Program.pureMem.fetchMem m' pc = none

/-- Backward-compatible specialization: legacy `h2fsgen_HooksUnfetched P2 m` implies
    `HooksUnfetchedPerPc D P1 P2 m` for arbitrary `D` and `P1`. -/
theorem hooksUnfetchedPerPc_of_hooksUnfetched {D : BitVec 64 → Bool} {P1 P2 : Program} {m : Memory}
    (h : h2fsgen_HooksUnfetched P2 m) :
    HooksUnfetchedPerPc D P1 P2 m :=
  fun m' pc hkf _ _ he2 => h m' pc hkf he2

/-- Monotonicity in the visited domain `D`: shrinking `D` preserves `HooksUnfetchedPerPc`. -/
theorem hooksUnfetchedPerPc_mono {D1 D2 : BitVec 64 → Bool} {P1 P2 : Program} {m : Memory}
    (hsub : ∀ pc : BitVec 64, D1 pc = true → D2 pc = true)
    (h : HooksUnfetchedPerPc D2 P1 P2 m) :
    HooksUnfetchedPerPc D1 P1 P2 m :=
  fun m' pc hkf hD1 he1 he2 => h m' pc hkf (hsub pc hD1) he1 he2

/-- Preservation across `Memory.KeepsFrozen` evolutions. -/
theorem hooksUnfetchedPerPc_of_keepsFrozen {D : BitVec 64 → Bool} {P1 P2 : Program}
    {m0 m1 : Memory} (hkf01 : m0.KeepsFrozen m1)
    (h : HooksUnfetchedPerPc D P1 P2 m0) :
    HooksUnfetchedPerPc D P1 P2 m1 :=
  fun m' pc hkf1 heD he1 he2 => h m' pc (hkf01.trans hkf1) heD he1 he2

/-- **Zero-byte-check criterion (`0` `F3CodeInv` / `0#32` stubs needed):**
    Whenever every `P2`-hooked address inside `D` is already hooked in `P1` (in particular, when
    `P2.externAt? pc = none` across `D`), `HooksUnfetchedPerPc D P1 P2 m` holds for **every**
    memory `m`, even when arbitrary real code sits under hooks outside `D` or under `P1`-hooks! -/
theorem hooksUnfetchedPerPc_of_noNewExternOn {D : BitVec 64 → Bool} {P1 P2 : Program} (m : Memory)
    (hno : ∀ pc : BitVec 64, D pc = true → P1.externAt? pc = none → P2.externAt? pc = none) :
    HooksUnfetchedPerPc D P1 P2 m :=
  fun _ pc _ hD he1 he2 => False.elim (he2 (hno pc hD he1))

/-- **Hybrid per-address stock-link criterion ("outside `D` OR hook-before-fetch OR frozen `0#32`"):**
    Every `P2`-hooked address `pc` satisfies at least one of:
    1. `D pc = false` (real code outside `D`, e.g. `"memmove"`, `"bcmp"`, `"strlen"`,
       `lsWriteFileSym`, `lsWriteStdoutSym`),
    2. `P1.externAt? pc ≠ none` (hook fires before fetch in `P1`, e.g. `"memcpy"` in
       `hole2_strCloneProg mpl`), or
    3. `m` holds 4 frozen bytes reading as `0#32` (`Arm64.decode 0#32 = none`, e.g. Z-stubs in
       `extern_stubs_clean.o`). -/
theorem hooksUnfetchedPerPc_of_perPc {D : BitVec 64 → Bool} {P1 P2 : Program} {m : Memory}
    (hper : ∀ pc : BitVec 64, P2.externAt? pc ≠ none →
      D pc = false ∨
      P1.externAt? pc ≠ none ∨
      (m.Frozen (pc + 0#64) ∧ m.Frozen (pc + 1#64) ∧
       m.Frozen (pc + 2#64) ∧ m.Frozen (pc + 3#64) ∧
       m.read32 pc = 0#32)) :
    HooksUnfetchedPerPc D P1 P2 m := by
  intro m' pc hkf hD he1 he2
  rcases hper pc he2 with hOut | hHook1 | ⟨hf0, hf1, hf2, hf3, hz⟩
  · rw [hD] at hOut; cases hOut
  · exact False.elim (hHook1 he1)
  · have hr32 : m'.read32 pc = m.read32 pc := by
      simp only [Memory.read32, (hkf _ hf0).1, (hkf _ hf1).1, (hkf _ hf2).1, (hkf _ hf3).1]
    have hdec : Arm64.decode (m.read32 pc) = none := by
      rw [hz]; rfl
    unfold Program.fetchMem
    rw [hr32, hdec]
    simp only [ite_self]

/-! ## 3. Scoped + Hook-Aware `Steps` / `StepsUntil` Lift & Probe-Program `VisitedIn` Upgrade -/

/-- **Unified `Steps` lift via `h2fsgen_StepsVisitedIn D` + `HooksUnfetchedPerPc D P1 P2`:**
    Simultaneously generalizes `h2fsgen_steps_lift_of_visitedIn` (which forbade active hooks in `P1`)
    and `h2fsgen_steps_lift_of_hooksUnfetched` (which required global `0#32` stubs across all PCs):
    - On `Step.exec`, `externAt_none_and_pureMem_of_fetchMem_some` yields `P1.externAt? s1.pc = none`
      and `Program.pureMem.fetchMem s1.mem s1.pc = some inst`; combined with `D s1.pc = true` and
      `hunf`, this forces `P2.externAt? s1.pc = none`, so `P2` fetches the exact same `inst`.
    - On `Step.extern` / `Step.extern_fault`, `hext12` lifts the active hook directly without
      inspecting memory bytes at `s1.pc`. -/
theorem steps_lift_of_visitedIn_perPc
    {D : BitVec 64 → Bool} {P1 P2 : Program} {m0 : Memory} {sa sf : State}
    (hsvc : P1.svc = P2.svc)
    (hext12 : ∀ (pc : BitVec 64) (f : State → State),
      D pc = true → P1.externAt? pc = some f → P2.externAt? pc = some f)
    (hunf : HooksUnfetchedPerPc D P1 P2 m0)
    (hkf : m0.KeepsFrozen sa.mem)
    (hvis : h2fsgen_StepsVisitedIn D P1 sa sf)
    (hnhalt : sf.status ≠ .Halted) :
    Steps P2 sa sf := by
  induction hvis with
  | refl s => exact .refl s
  | @step s1 s2 _ hD h1 hrest ih =>
    have hkf2 : m0.KeepsFrozen s2.mem := hkf.trans h1.keepsFrozen
    cases h1 with
    | @exec inst hrun hfetch =>
      obtain ⟨he1, hpure⟩ := externAt_none_and_pureMem_of_fetchMem_some hfetch
      have he2 : P2.externAt? s1.pc = none := by
        by_contra hne
        have hnone := hunf s1.mem s1.pc hkf hD he1 hne
        rw [hpure] at hnone
        cases hnone
      have hfetch2 : P2.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem
        rw [he2]
        simpa [Program.fetchMem, Program.pureMem, Program.pureWithSvc,
          Program.ofSvc, Program.externAt?, Program.hookAtOff?] using hpure
      have ih2 := ih hkf2 hnhalt
      rw [evalInst_eq_of_svc_eq hsvc inst s1] at ih2
      exact .step (Step.exec hrun hfetch2) ih2
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt (steps_preserves_halted hrest.toSteps rfl))
    | extern hrun hext hkeep hsym =>
      exact .step (Step.extern hrun (hext12 s1.pc _ hD hext) hkeep hsym) (ih hkf2 hnhalt)
    | extern_fault hrun hext hnkeep =>
      exact .step (Step.extern_fault hrun (hext12 s1.pc _ hD hext) hnkeep) (ih hkf2 hnhalt)

/-- `StepsUntil P1 (SubroutineStop u)` specialization of `steps_lift_of_visitedIn_perPc`. -/
theorem stepsUntil_lift_of_visitedIn_perPc
    {D : BitVec 64 → Bool} {P1 P2 : Program} {u sa sf : State}
    (hsvc : P1.svc = P2.svc)
    (hext12 : ∀ (pc : BitVec 64) (f : State → State),
      D pc = true → P1.externAt? pc = some f → P2.externAt? pc = some f)
    (hunf : HooksUnfetchedPerPc D P1 P2 u.mem)
    (hkf : u.mem.KeepsFrozen sa.mem)
    (hvis : h2fsgen_StepsVisitedIn D P1 sa sf)
    (hstop : SubroutineStop u sf) :
    Steps P2 sa sf :=
  steps_lift_of_visitedIn_perPc hsvc hext12 hunf hkf hvis (not_subroutineStop_of_halted hstop)

/-- **Determinism transfer for `h2fsgen_StepsVisitedIn`:**
    Upgrades any `StepsUntil P1 stop s sf` witness (e.g. `Classical.choose hReal.2.2.2` inside an
    unchanged `ActiveRealRun` / `ActiveF3ReadFileRun` / `ActiveReadStdinLinkedRun`) using a separate
    `VisitedIn` witness `(sf', hu', hs', hvis')` (e.g. from
    `h2fsgen_real_subroutine_run_visitedIn_of_stripS`), without changing `ActiveRealRun`'s type. -/
theorem stepsVisitedIn_of_det {D : BitVec 64 → Bool} {P1 : Program} {stop : State → Prop}
    {s sf sf' : State}
    (hu : StepsUntil P1 stop s sf) (hs : stop sf)
    (hu' : StepsUntil P1 stop s sf') (hs' : stop sf')
    (hvis' : h2fsgen_StepsVisitedIn D P1 s sf') :
    h2fsgen_StepsVisitedIn D P1 s sf := by
  cases h2fsgen_stepsUntil_det hu hs hu' hs'
  exact hvis'

/-! ### Probe-Program Upgrade (`∀ P` First-Stop → `h2fsgen_StepsVisitedIn D`) -/

private def haltProbeProg (svc : State → State) (badPc : BitVec 64) : Program where
  base := 0#64
  code := []
  externs sym := if sym == "__probe_halt" then some (fun s => { s with status := .Halted }) else none
  stubs := [("__probe_halt", badPc.toNat)]
  svc := svc

private theorem haltProbeProg_externAt_self (svc : State → State) (badPc : BitVec 64) :
    (haltProbeProg svc badPc).externAt? badPc =
      some (fun s => { s with status := .Halted }) := by
  unfold haltProbeProg Program.externAt? Program.hookAtOff?
  simp [BitVec.sub_zero]

private theorem haltProbeProg_externAt_ne (svc : State → State) {badPc pc : BitVec 64}
    (hne : pc ≠ badPc) :
    (haltProbeProg svc badPc).externAt? pc = none := by
  unfold haltProbeProg Program.externAt? Program.hookAtOff?
  simp only [BitVec.sub_zero, List.findSome?_cons, List.findSome?_nil, Option.or_none]
  have hnat : (badPc.toNat == pc.toNat) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    exact hne (BitVec.eq_of_toNat_eq heq.symm)
  simp [hnat]

private theorem steps_eq_of_not_running {P : Program} {u v : State}
    (hnr : u.status ≠ .Running) (h : Steps P u v) : u = v := by
  cases h with
  | refl _ => rfl
  | step h1 _ =>
    have hr : u.status = .Running := by cases h1 <;> assumption
    exact False.elim (hnr hr)

private theorem step_of_externAt_eq {P Q : Program} {u v : State}
    (hsvc : P.svc = Q.svc)
    (heP : P.externAt? u.pc = none)
    (heQ : Q.externAt? u.pc = none)
    (hs : Step P u v) : Step Q u v := by
  have hfm_eq : Q.fetchMem u.mem u.pc = P.fetchMem u.mem u.pc := by
    unfold Program.fetchMem
    rw [heQ, heP]
  cases hs with
  | @exec inst hrun hfm =>
    rw [evalInst_eq_of_svc_eq hsvc inst u]
    exact Step.exec hrun (hfm_eq.trans hfm)
  | halt_unmapped hrun hfm _ =>
    exact Step.halt_unmapped hrun (hfm_eq.trans hfm) heQ
  | extern _ he _ _ => rw [heP] at he; cases he
  | extern_fault _ he _ => rw [heP] at he; cases he

private theorem step_det {P : Program} {s b1 b2 : State}
    (h1 : Step P s b1) (h2 : Step P s b2) : b1 = b2 := by
  cases h1 with
  | exec _ hfm1 =>
    cases h2 with
    | exec _ hfm2 => cases hfm1.symm.trans hfm2; rfl
    | halt_unmapped _ hfm2 _ => rw [hfm1] at hfm2; cases hfm2
    | extern _ he2 _ _ =>
      have ⟨he1, _⟩ := externAt_none_and_pureMem_of_fetchMem_some hfm1
      rw [he1] at he2; cases he2
    | extern_fault _ he2 _ =>
      have ⟨he1, _⟩ := externAt_none_and_pureMem_of_fetchMem_some hfm1
      rw [he1] at he2; cases he2
  | halt_unmapped _ hfm1 he1 =>
    cases h2 with
    | exec _ hfm2 => rw [hfm1] at hfm2; cases hfm2
    | halt_unmapped _ _ _ => rfl
    | extern _ he2 _ _ => rw [he1] at he2; cases he2
    | extern_fault _ he2 _ => rw [he1] at he2; cases he2
  | extern _ he1 hk1 hs1 =>
    cases h2 with
    | exec _ hfm2 =>
      have ⟨he2, _⟩ := externAt_none_and_pureMem_of_fetchMem_some hfm2
      rw [he2] at he1; cases he1
    | halt_unmapped _ _ he2 => rw [he2] at he1; cases he1
    | extern _ he2 _ _ => cases he1.symm.trans he2; rfl
    | extern_fault _ he2 hbad2 =>
      cases he1.symm.trans he2
      exact absurd ⟨hk1, hs1⟩ hbad2
  | extern_fault _ he1 hbad1 =>
    cases h2 with
    | exec _ hfm2 =>
      have ⟨he2, _⟩ := externAt_none_and_pureMem_of_fetchMem_some hfm2
      rw [he2] at he1; cases he1
    | halt_unmapped _ _ he2 => rw [he2] at he1; cases he1
    | extern _ he2 hk2 hs2 =>
      cases he1.symm.trans he2
      exact absurd ⟨hk2, hs2⟩ hbad1
    | extern_fault _ _ _ => rfl

private inductive PrefixUntil (D : BitVec 64 → Bool) (stop : State → Prop) (P1 : Program) :
    State → State → Prop where
  | refl (s : State) : PrefixUntil D stop P1 s s
  | step {u v w : State}
      (hnot : ¬ stop u)
      (hd : D u.pc = true)
      (hs : Step P1 u v)
      (hrest : PrefixUntil D stop P1 v w) :
      PrefixUntil D stop P1 u w

private theorem PrefixUntil.snoc {D : BitVec 64 → Bool} {stop : State → Prop} {P1 : Program}
    {a u v : State}
    (hp : PrefixUntil D stop P1 a u)
    (hnot : ¬ stop u)
    (hd : D u.pc = true)
    (hs : Step P1 u v) :
    PrefixUntil D stop P1 a v := by
  induction hp with
  | refl _ => exact .step hnot hd hs (.refl v)
  | step hn0 hd0 hs0 _ ih => exact .step hn0 hd0 hs0 (ih hnot hd hs)

private theorem replay_prefix_in_domain {D : BitVec 64 → Bool} {stop : State → Prop}
    {P1 Q : Program} {a b sf : State}
    (hsvc : P1.svc = Q.svc)
    (he1 : ∀ pc : BitVec 64, D pc = true → P1.externAt? pc = none)
    (heQ : ∀ pc : BitVec 64, D pc = true → Q.externAt? pc = none)
    (hPref : PrefixUntil D stop P1 a b)
    (hU : StepsUntil Q stop a sf)
    (hStop : stop sf) :
    StepsUntil Q stop b sf := by
  induction hPref with
  | refl _ => exact hU
  | @step u v _ hnot hDu hs1 _ ih =>
    cases hU with
    | refl _ => exact False.elim (hnot hStop)
    | step _ hsQ hrestQ =>
      have hsQ' : Step Q u v := step_of_externAt_eq hsvc (he1 u.pc hDu) (heQ u.pc hDu) hs1
      cases step_det hsQ' hsQ
      exact ih hrestQ

private theorem stepsVisitedIn_of_allProg_aux {D : BitVec 64 → Bool}
    {P1 : Program} {s0 sStart s1 sf0 : State}
    (he1 : ∀ pc : BitVec 64, D pc = true → P1.externAt? pc = none)
    (hAllP : ∀ (Q : Program), Q.svc = P1.svc →
      (∀ pc : BitVec 64, D pc = true → Q.externAt? pc = none) →
      ∃ sf : State, StepsUntil Q (SubroutineStop s0) sStart sf ∧ SubroutineStop s0 sf)
    (hU0 : StepsUntil P1 (SubroutineStop s0) s1 sf0) :
    PrefixUntil D (SubroutineStop s0) P1 sStart s1 →
    h2fsgen_StepsVisitedIn D P1 s1 sf0 := by
  induction hU0 with
  | refl s =>
    intro _
    exact .refl s
  | @step u v _ hcont hstep _ ih =>
    intro hPref
    have hDu : D u.pc = true := by
      by_cases hk : D u.pc = true
      · exact hk
      · have hkf : D u.pc = false := Bool.eq_false_iff.mpr hk
        have hno_probe : ∀ pc : BitVec 64, D pc = true →
            (haltProbeProg P1.svc u.pc).externAt? pc = none := by
          intro pc hpc
          refine haltProbeProg_externAt_ne P1.svc (fun heq => ?_)
          rw [heq, hkf] at hpc
          cases hpc
        obtain ⟨sfBad, hUBad0, hStopBad⟩ := hAllP (haltProbeProg P1.svc u.pc) rfl hno_probe
        have hUBad : StepsUntil (haltProbeProg P1.svc u.pc) (SubroutineStop s0) u sfBad :=
          replay_prefix_in_domain (P1 := P1) rfl he1 hno_probe hPref hUBad0 hStopBad
        cases hUBad with
        | refl _ => exact False.elim (hcont hStopBad)
        | @step _ w _ _ hstepBad hrestBad =>
          have heSelf := haltProbeProg_externAt_self P1.svc u.pc
          obtain ⟨_, hcases⟩ := step_at_extern_fires_hook_without_fetch heSelf hstepBad
          rcases hcases with ⟨_, _, rfl⟩ | ⟨_, rfl⟩
          · have hw_eq := steps_eq_of_not_running (by simp) hrestBad.toSteps
            have hsf_halt : sfBad.status = .Halted := hw_eq ▸ rfl
            exact False.elim (not_subroutineStop_of_halted hStopBad hsf_halt)
          · have hw_eq := steps_eq_of_not_running (by simp) hrestBad.toSteps
            have hsf_ex : sfBad.status =
                .Exception "extern hook modified read-only memory or symbol table" :=
              hw_eq ▸ rfl
            rcases hStopBad with ⟨_, _, hr⟩ | hp | ⟨_, hex⟩ | ho <;> rw [hsf_ex] at * <;>
              contradiction
    exact .step hDu hstep (ih (hPref.snoc hcont hDu hstep))

/-- **Generic probe-program `VisitedIn` upgrade:**
    Upgrades `StepsUntil P1 (SubroutineStop s0) sStart sf0` to `h2fsgen_StepsVisitedIn D P1 sStart sf0`
    whenever `P1` is extern-free on `D` and every program `Q` agreeing with `P1.svc` and extern-free
    on `D` reaches `SubroutineStop s0` from `sStart` (the exact universal `(R)` shape already proved
    in `H2FirstStopAlloc`, `H2FirstStopDealloc`, `H2FirstStopRealloc`, and `H2FirstStopReads`). -/
theorem stepsVisitedIn_of_allProg {D : BitVec 64 → Bool}
    {P1 : Program} {s0 sStart sf0 : State}
    (he1 : ∀ pc : BitVec 64, D pc = true → P1.externAt? pc = none)
    (hAllP : ∀ (Q : Program), Q.svc = P1.svc →
      (∀ pc : BitVec 64, D pc = true → Q.externAt? pc = none) →
      ∃ sf : State, StepsUntil Q (SubroutineStop s0) sStart sf ∧ SubroutineStop s0 sf)
    (hU0 : StepsUntil P1 (SubroutineStop s0) sStart sf0) :
    h2fsgen_StepsVisitedIn D P1 sStart sf0 :=
  stepsVisitedIn_of_allProg_aux he1 hAllP hU0 (.refl sStart)

/-- **Stock-ready replacement for `h2fsgen_stepsUntil_noExtern_lift_of_hooksUnfetched`:**
    Lifts `StepsUntil P1 (SubroutineStop u) (u.setPC entryTarget) sf` to `Steps P2 (u.setPC entryTarget) sf`
    with **zero `0#32` stub requirement on `P2`**, using `D`-scoped extern absence (`hext2_none`)
    plus either a `VisitedIn D` witness or `stepsVisitedIn_of_allProg`. -/
theorem stepsUntil_noExtern_lift_of_visitedIn
    {D : BitVec 64 → Bool} {P1 P2 : Program} {u sf : State} {entryTarget : BitVec 64}
    (hsvc : P1.svc = P2.svc)
    (hext1_none : ∀ pc : BitVec 64, D pc = true → P1.externAt? pc = none)
    (hext2_none : ∀ pc : BitVec 64, D pc = true → P2.externAt? pc = none)
    (hvis : h2fsgen_StepsVisitedIn D P1 (u.setPC entryTarget) sf)
    (hstop : SubroutineStop u sf) :
    Steps P2 (u.setPC entryTarget) sf :=
  stepsUntil_lift_of_visitedIn_perPc hsvc
    (fun pc _ hD he => nomatch (hext1_none pc hD) ▸ he)
    (hooksUnfetchedPerPc_of_noNewExternOn u.mem fun pc hD _ => hext2_none pc hD)
    (Memory.KeepsFrozen.refl u.mem)
    hvis hstop

/-! ## 4. Layout-Generic Instantiations on `P_real_W` (`H2StepsLiftR2` + `H2Branch2` + `strClone`) -/

private theorem realW_svc (mpl mmpl : MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

private theorem activeF3CallPre_of_f3LinkedCallHook_noException {α : Type}
    {keepSub : BitVec 64 → Bool} {P_empty P_sub : Program} {entryTarget : BitVec 64}
    {specOf' : GhostName → BitVec 64 → Spec α} {fallback : State → State} {u : State}
    (hnoex : ∀ msg,
      (f3LinkedCallHook keepSub P_empty P_sub entryTarget specOf' fallback u).status ≠
        .Exception msg) :
    ActiveF3CallPre specOf' u := by
  classical
  by_contra hnot
  apply hnoex "ghost-hook precondition violated"
  unfold f3LinkedCallHook
  simp [hnot]

/-- **Stock `ld.lld` direct stub witness (`stubPc = entryTarget`):**
    On a stock `ld.lld` link (`DirectOrBranchStub` left disjunct `stubPc = entryTarget`),
    `StubReachesTargetOn Inv P stubPc entryTarget` holds in `0` steps (`Steps.refl`). -/
theorem stubReachesTargetOn_of_direct {Inv : Memory → Prop} {P : Program}
    {stubPc entryTarget : BitVec 64} (heq : stubPc = entryTarget) :
    StubReachesTargetOn Inv P stubPc entryTarget := by
  intro u hpc _ _ _
  have hset : u.setPC entryTarget = u := by
    rw [← heq, ← hpc]
    cases u
    rfl
  rw [hset]
  exact .refl u

/-- **Replacement for `h2sl_realW_hooksUnfetched` on any de-hooked callee domain `keepSub`:**
    Requires **zero** `CodeInv` and **zero** `[0, 0, 0, 0]` stub checks (`h2sl_checkCompactZeroRxB`
    eliminated), so real `Perm.rx` code under `"memmove"`, `"bcmp"`, `"strlen"`, `lsWriteFileSym`,
    and `lsWriteStdoutSym` outside `keepSub` is unconditionally tolerated. -/
theorem realW_hooksUnfetchedPerPc_keepSub
    {keepSub : BitVec 64 → Bool}
    {mpl mmpl : MultiPlacement} (W : CliHooks) (m : Memory)
    (hno_ext : ∀ pc : BitVec 64, keepSub pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    HooksUnfetchedPerPc keepSub (Program.ofSvc Syscall.standard)
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) m :=
  hooksUnfetchedPerPc_of_noNewExternOn m fun pc hD _ => hno_ext pc hD

/-- **Stock-ready `<String as Clone>::clone` criterion on any domain `D`:**
    Even when `D` includes `"memcpy"` holding real `libc.a` instructions (prior to S2′),
    `HooksUnfetchedPerPc D P_strClone P_real_W m` holds because `P_strClone` hooks `"memcpy"` before
    fetch (`P_strClone.externAt? pc ≠ none`). -/
theorem realW_hooksUnfetchedPerPc_strClone_on
    {D : BitVec 64 → Bool} {P_strClone : Program} {mpl mmpl : MultiPlacement}
    {m : Memory} (W : CliHooks)
    (hper : ∀ pc : BitVec 64,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc ≠ none →
        D pc = false ∨
        P_strClone.externAt? pc ≠ none ∨
        (m.Frozen (pc + 0#64) ∧ m.Frozen (pc + 1#64) ∧
         m.Frozen (pc + 2#64) ∧ m.Frozen (pc + 3#64) ∧
         m.read32 pc = 0#32)) :
    HooksUnfetchedPerPc D P_strClone
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) m :=
  hooksUnfetchedPerPc_of_perPc hper

/-- **Drop-in stock replacement for `h2sl_stepsUntil_emptyProg_to_realW`:**
    Same `Steps P_real_W (u.setPC entryTarget) sf` conclusion as `H2StepsLiftR2.lean:988`, replacing
    `F3CodeInv` + `h2sl_realW_hooksUnfetched` with `hvis : h2fsgen_StepsVisitedIn keepSub`
    (obtained via `stepsVisitedIn_of_allProg` or `stepsVisitedIn_of_det`). -/
theorem stepsUntil_emptyProg_to_realW_perPc
    {keepSub : BitVec 64 → Bool} {mpl mmpl : MultiPlacement} (W : CliHooks)
    {u sf : State} {entryTarget : BitVec 64}
    (hno_ext : ∀ pc : BitVec 64, keepSub pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hvis : h2fsgen_StepsVisitedIn keepSub (Program.ofSvc Syscall.standard)
      (u.setPC entryTarget) sf)
    (hstop : SubroutineStop u sf) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) (u.setPC entryTarget) sf :=
  stepsUntil_noExtern_lift_of_visitedIn
    (D := keepSub)
    (P1 := Program.ofSvc Syscall.standard)
    (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
    (rfl.trans (realW_svc mpl mmpl W).symm)
    (fun _ _ => rfl)
    hno_ext
    hvis hstop

/-- **Drop-in stock replacement for `h2sl_stepsUntil_strClone_to_realW`:**
    Same `Steps P_real_W sa sf` conclusion as `H2StepsLiftR2.lean:1008`, with **zero**
    `h2sl_checkCompactZeroRxB` dependency! -/
theorem stepsUntil_strClone_to_realW_perPc
    {D : BitVec 64 → Bool} {P_strClone : Program} {mpl mmpl : MultiPlacement}
    (W : CliHooks)
    {u sa sf : State}
    (hsvc : P_strClone.svc = Syscall.standard)
    (hext_sub : ∀ (pc : BitVec 64) (f : State → State),
      D pc = true → P_strClone.externAt? pc = some f →
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = some f)
    (hunf : HooksUnfetchedPerPc D P_strClone
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u.mem)
    (hkf : u.mem.KeepsFrozen sa.mem)
    (hvis : h2fsgen_StepsVisitedIn D P_strClone sa sf)
    (hstop : SubroutineStop u sf) :
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) sa sf :=
  stepsUntil_lift_of_visitedIn_perPc
    (D := D)
    (P1 := P_strClone)
    (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
    (hsvc.trans (realW_svc mpl mmpl W).symm)
    hext_sub hunf hkf hvis hstop

/-- **Layout-generic end-to-end proof of `H2Branch2.h2b2_branch2_f3LinkedCallHook` without
    `h2sl_realW_hooksUnfetched`:**
    Identical conclusion and unchanged `ActiveRealRun` / `f3LinkedCallHook` types (`0` edits to
    HOOKS-LEAD files), obtaining `h2fsgen_StepsVisitedIn keepSub` via `stepsVisitedIn_of_allProg`
    from the standard universal `(R)` lemma `hR_allProg` (`h2fsalloc_*_firstStop_keepSub`,
    `h2fsdealloc_firstStop_keepSub`, `h2fsrealloc_firstStop_of_keep`). -/
theorem branch2_f3LinkedCallHook_perPc {α β : Type}
    {keepSub : BitVec 64 → Bool} {P_sub : Program} {Inv : Memory → Prop}
    {mpl mmpl : MultiPlacement}
    (W : CliHooks)
    {stubPc entryTarget : BitVec 64}
    {specOf : GhostName → BitVec 64 → Spec α}
    {specOf' : GhostName → BitVec 64 → Spec β}
    {fallback : State → State}
    (hno_ext : ∀ pc : BitVec 64, keepSub pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hCodeOfInv : ∀ {m : Memory}, Inv m → P_sub.CodeLoaded (stripExecOutside keepSub m))
    (hInvKeepsFrozen : ∀ {m m' : Memory}, Inv m → m.KeepsFrozen m' → Inv m')
    (hStub : StubReachesTargetOn Inv
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) stubPc entryTarget)
    (hPreImp : ∀ s : State, ActiveF3CallPre specOf' s → ActiveF3CallPre specOf s)
    (hR_allProg : ∀ {s0 : State},
      ActiveF3CallPre specOf s0 →
      ExecFrozen s0.mem →
      keepSub (s0.readReg64 .lr) = false →
      P_sub.CodeLoaded (stripExecOutside keepSub s0.mem) →
      ∀ (P : Program), P.svc = Syscall.standard →
        (∀ pc : BitVec 64, keepSub pc = true → P.externAt? pc = none) →
        ∃ sf : State,
          StepsUntil P (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
          SubroutineStop s0 sf ∧
          sf.fs = s0.fs ∧
          FsTraced CryptoVerification.SignalSession.Cli.RunGlue.IsFsC s0 sf ∧
          ExecFrozen sf.mem)
    {u : State}
    (hpc : u.pc = stubPc)
    (hrun : u.status = .Running)
    (hnoex : ∀ msg,
      (f3LinkedCallHook keepSub (Program.ofSvc Syscall.standard) P_sub entryTarget
        specOf' fallback u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem)
    (hlr : keepSub (u.readReg64 .lr) = false)
    (hInv : Inv u.mem) :
    let f := f3LinkedCallHook keepSub (Program.ofSvc Syscall.standard) P_sub entryTarget
      specOf' fallback
    Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W) u (f u) ∧
      ExecFrozen (f u).mem ∧
      Inv (f u).mem ∧
      (f u).fs = u.fs := by
  classical
  dsimp only
  have hActPre' : ActiveF3CallPre specOf' u :=
    activeF3CallPre_of_f3LinkedCallHook_noException hnoex
  have hActPre : ActiveF3CallPre specOf u := hPreImp u hActPre'
  have hCodeRx : P_sub.CodeLoaded (stripExecOutside keepSub u.mem) := hCodeOfInv hInv
  have hAll := hR_allProg hActPre hFr hlr hCodeRx
  have hReal : ActiveRealRun keepSub (Program.ofSvc Syscall.standard) P_sub entryTarget u :=
    ⟨hFr, hlr, hCodeRx, hAll (Program.ofSvc Syscall.standard) rfl fun _ _ => rfl⟩
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hfu :
      f3LinkedCallHook keepSub (Program.ofSvc Syscall.standard) P_sub entryTarget
        specOf' fallback u = Classical.choose hReal.2.2.2 := by
    unfold f3LinkedCallHook
    simp only [hActPre', hReal, ↓reduceDIte]
  have hvis :
      h2fsgen_StepsVisitedIn keepSub (Program.ofSvc Syscall.standard)
        (u.setPC entryTarget) (Classical.choose hReal.2.2.2) :=
    stepsVisitedIn_of_allProg
      (fun _ _ => rfl)
      (fun Q hsvc hno =>
        let ⟨sf, huQ, hsQ, _, _, _⟩ := hAll Q hsvc hno
        ⟨sf, huQ, hsQ⟩)
      hchoose.1
  have hBody :
      Steps (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (u.setPC entryTarget) (Classical.choose hReal.2.2.2) :=
    stepsUntil_emptyProg_to_realW_perPc W hno_ext hvis hchoose.2.1
  have hkf : u.mem.KeepsFrozen (Classical.choose hReal.2.2.2).mem := by
    simpa only [State.setPC] using hchoose.1.toSteps.keepsFrozen
  rw [hfu]
  exact ⟨(hStub u hpc hrun hFr hInv).trans hBody,
    hchoose.2.2.2.2,
    hInvKeepsFrozen hInv hkf,
    hchoose.2.2.1⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHooksUnfetchedPerPc

