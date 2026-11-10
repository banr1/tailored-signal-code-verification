/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.Exec
public import ProofLib.ObjectLoad
public import ProofLib.Simulation
public import ProofLib.VCGen

/-!
# Monadic and Oracle-Valued Hooks for ARM64 Programs

Extends `Program.overrides` to monadic hook tables `OracleExterns M := String -> Option (State -> M State)`
with small-step and fuel execution (`stepStateWithOracle`, `execUntilPCWithOracle`). Provides
`PureOracleHandler` to lower oracle hooks to pure overrides (`simulateQ_execUntilPCWithOracle`),
counted execution judgments (`RunsToAt`, `RunsTo`), and the indexed query-response free monad
`FreeOracle`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-! ## Pure Handler Typeclass and `FreeOracle` Monad -/

/-- A pure handler interface `H` for an oracle/effect monad `M : Type -> Type`:
    interprets any computation `M α` into `Id α` (`= α`) as a monad morphism preserving `pure` and
    `bind`. Marking `H : outParam Type` lets callers write `hooks.withHandler impl` and
    `hooks.KeepFrozen` without passing `H` explicitly. -/
class PureOracleHandler (M : Type → Type) (H : outParam Type) [Monad M] where
  /-- Evaluate an oracle computation `c : M α` using pure handler `impl : H`. -/
  eval : H → ∀ {α : Type}, M α → Id α
  /-- `eval impl` preserves `pure`. -/
  eval_pure : ∀ (impl : H) {α : Type} (x : α),
    eval impl (pure x) = (Pure.pure x : Id α)
  /-- `eval impl` commutes with `>>=`. -/
  eval_bind : ∀ (impl : H) {α β : Type} (m : M α) (f : α → M β),
    eval impl (m >>= f) = (Bind.bind (eval impl m) (fun a => eval impl (f a)) : Id β)

/-- Indexed family of oracle query domains and response codomains. -/
abbrev OracleFamily (ι : Type) := ι → Type × Type

/-- Free monad over an indexed oracle family `spec : OracleFamily ι`. -/
inductive FreeOracle {ι : Type} (spec : OracleFamily ι) : Type → Type where
  | pure {α : Type} (val : α) : FreeOracle spec α
  | queryBind {α : Type} (i : ι) (q : (spec i).1)
      (cont : (spec i).2 → FreeOracle spec α) : FreeOracle spec α

namespace FreeOracle

variable {ι : Type} {spec : OracleFamily ι}

/-- Perform a single oracle query at index `i` with input `q`. -/
def query (i : ι) (q : (spec i).1) : FreeOracle spec (spec i).2 :=
  .queryBind i q .pure

protected def bind {α β : Type} : FreeOracle spec α → (α → FreeOracle spec β) → FreeOracle spec β
  | .pure a, f => f a
  | .queryBind i q k, f => .queryBind i q (fun r => FreeOracle.bind (k r) f)

instance : Monad (FreeOracle spec) where
  pure := .pure
  bind := FreeOracle.bind

@[simp] theorem pure_def {α : Type} (x : α) :
    (Pure.pure x : FreeOracle spec α) = .pure x := rfl

@[simp] theorem bind_pure_left {α β : Type} (x : α) (f : α → FreeOracle spec β) :
    (.pure x >>= f : FreeOracle spec β) = f x := rfl

@[simp] theorem bind_queryBind {α β : Type} (i : ι) (q : (spec i).1)
    (k : (spec i).2 → FreeOracle spec α) (f : α → FreeOracle spec β) :
    (.queryBind i q k >>= f : FreeOracle spec β) = .queryBind i q (fun r => k r >>= f) := rfl

@[simp] theorem query_bind {α : Type} (i : ι) (q : (spec i).1)
    (f : (spec i).2 → FreeOracle spec α) :
    (query i q >>= f) = .queryBind i q f := rfl

protected theorem bind_pure_right {α : Type} (m : FreeOracle spec α) :
    (m >>= Pure.pure) = m := by
  induction m with
  | pure _ => rfl
  | queryBind _ _ _ ih =>
    simp only [bind_queryBind]
    congr 1; funext r; exact ih r

protected theorem bind_assoc {α β γ : Type} (m : FreeOracle spec α)
    (f : α → FreeOracle spec β) (g : β → FreeOracle spec γ) :
    ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  induction m with
  | pure _ => rfl
  | queryBind _ _ _ ih =>
    simp only [bind_queryBind]
    congr 1; funext r; exact ih r

instance : LawfulMonad (FreeOracle spec) :=
  LawfulMonad.mk'
    (id_map := fun m => FreeOracle.bind_pure_right m)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := FreeOracle.bind_assoc)

/-- A pure deterministic handler answering queries of `spec : OracleFamily ι`. -/
abbrev Handler (spec : OracleFamily ι) := ∀ (i : ι), (spec i).1 → (spec i).2

/-- Evaluate a `FreeOracle spec α` computation using a pure handler `impl`. -/
def simulate (impl : Handler spec) {α : Type} : FreeOracle spec α → Id α
  | .pure a => a
  | .queryBind i q k => simulate impl (k (impl i q))

@[simp] theorem simulate_pure (impl : Handler spec) {α : Type} (x : α) :
    simulate impl (Pure.pure x : FreeOracle spec α) = (Pure.pure x : Id α) := rfl

@[simp] theorem simulate_query (impl : Handler spec) (i : ι) (q : (spec i).1) :
    simulate impl (query i q) = (Pure.pure (impl i q) : Id (spec i).2) := rfl

@[simp] theorem simulate_bind (impl : Handler spec) {α β : Type}
    (m : FreeOracle spec α) (f : α → FreeOracle spec β) :
    simulate impl (m >>= f) =
      (Bind.bind (simulate impl m) (fun a => simulate impl (f a)) : Id β) := by
  induction m with
  | pure _ => rfl
  | queryBind i q k ih => exact ih (impl i q)

instance : PureOracleHandler (FreeOracle spec) (Handler spec) where
  eval impl _ c := simulate impl c
  eval_pure := simulate_pure
  eval_bind := simulate_bind

end FreeOracle

/-! ## Oracle-Valued Hook Tables and Execution -/

/-- A monadic / oracle-valued hook table: maps symbol names to one-step state transitions in `M`. -/
abbrev OracleExterns (M : Type → Type) :=
  String → Option (State → M State)

section Definitions

variable {M : Type → Type} [Monad M]

/-- The oracle hook at offset `off`: `none` if an extern sits at a stub there (it takes
    precedence, as in `Program.hookAtOff?`), else the oracle hook of a defined symbol at `off`. -/
def _root_.Arm64.Program.oracleHookAtOff? (prog : Program)
    (hooks : OracleExterns M) (off : Nat) : Option (State → M State) :=
  match prog.stubs.findSome? fun (n, o) => if o == off then prog.externs n else none with
  | some _ => none
  | none => prog.symbols.findSome? fun (n, o) => if o == off then hooks n else none

/-- The oracle hook, if any, whose entry point is `pc`. -/
def _root_.Arm64.Program.oracleExternAt? (prog : Program)
    (hooks : OracleExterns M) (pc : BitVec 64) : Option (State → M State) :=
  prog.oracleHookAtOff? hooks (pc - prog.base).toNat

/-- One step of `prog` with oracle hooks `hooks`: at an oracle-hooked entry point, run the hook
    (one monadic computation in `M`); otherwise take the deterministic step `stepState` lifted with
    `pure`. Returns `none` when the machine is not running (as for `stepState`). -/
def stepStateWithOracle (prog : Program)
    (hooks : OracleExterns M) (s : State) : Option (M State) :=
  match s.status with
  | .Running =>
    match prog.oracleExternAt? hooks s.pc with
    | some f => some (f s)
    | none => (stepState prog s).map pure
  | _ => none

/-- `execUntilPC` with oracle hooks: run at most `fuel` steps, stopping as soon as
    `s.pc = target` or `s.status ≠ .Running`; a step at an oracle-hooked entry point runs in `M`. -/
def execUntilPCWithOracle (fuel : Nat) (prog : Program)
    (hooks : OracleExterns M) (target : BitVec 64) (s : State) : M State :=
  match fuel with
  | 0 => pure s
  | fuel + 1 =>
    if s.pc == target || s.status != .Running then
      pure s
    else
      match stepStateWithOracle prog hooks s with
      | some c => c >>= execUntilPCWithOracle fuel prog hooks target
      | none => pure s

/-- Replace each oracle hook by the pure hook that answers the hook's queries with `impl`. -/
def OracleExterns.withHandler {H : Type} [PureOracleHandler M H] (hooks : OracleExterns M)
    (impl : H) : String → Option (State → State) :=
  fun sym => (hooks sym).map fun f s => PureOracleHandler.eval impl (f s)

/-- The oracle analogue of `Program.HooksKeepFrozen`: whatever the oracles answer (every pure
    handler `impl`), every hook keeps frozen memory (`Memory.KeepsFrozen`) and preserves the symbol
    table. -/
def OracleExterns.KeepFrozen {H : Type} [PureOracleHandler M H] (hooks : OracleExterns M) :
    Prop :=
  ∀ (impl : H) (sym : String) (f : State → State) (s : State),
    hooks.withHandler impl sym = some f → s.mem.KeepsFrozen (f s).mem ∧ (f s).symtab = s.symtab

end Definitions

/-! ## Bridge to Pure `execUntilPC` -/

theorem List.findSome?_map_option {α β γ : Type} (l : List α) (g : α → Option β) (h : β → γ) :
    (l.findSome? g).map h = l.findSome? (fun a => (g a).map h) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.findSome?_cons]
    cases g a <;> simp [ih]

/-- A program without overrides: its hooks are the stub externs only. -/
theorem Program.hookAtOff?_of_overrides {prog : Program} (hO : ∀ sym, prog.overrides sym = none)
    (off : Nat) :
    prog.hookAtOff? off =
      prog.stubs.findSome? fun (n, o) => if o == off then prog.externs n else none := by
  unfold Program.hookAtOff?
  have : (prog.symbols.findSome? fun (n, o) => if o == off then prog.overrides n else none) =
      none := by
    rw [List.findSome?_eq_none_iff]
    intro p _
    simp [hO]
  rw [this, Option.or_none]

section Bridge

variable {M : Type → Type} {H : Type} [Monad M] [PureOracleHandler M H]

/-- Where the oracle hooks answered by `impl` are found, compared with the oracle hooks. -/
theorem Program.hookAtOff?_withHandler (prog : Program) (hO : ∀ sym, prog.overrides sym = none)
    (hooks : OracleExterns M) (impl : H) (off : Nat) :
    ({ prog with overrides := hooks.withHandler impl } : Program).hookAtOff? off =
      match prog.oracleHookAtOff? hooks off with
      | some g => some fun s => PureOracleHandler.eval impl (g s)
      | none => prog.hookAtOff? off := by
  rw [Program.hookAtOff?_of_overrides hO]
  unfold Program.hookAtOff? Program.oracleHookAtOff?
  dsimp only
  cases hstub : prog.stubs.findSome? (fun (n, o) => if o == off then prog.externs n else none) with
  | some f => rfl
  | none =>
    simp only [Option.none_or]
    rw [show (prog.symbols.findSome? fun (n, o) => if o == off then
        hooks.withHandler impl n else none) =
        (prog.symbols.findSome? fun (n, o) => if o == off then hooks n else none).map
          (fun f s => PureOracleHandler.eval impl (f s)) by
      rw [List.findSome?_map_option]
      congr 1
      funext p
      by_cases hp : (p.2 == off) = true
      · simp only [hp, ↓reduceIte]; rfl
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, Option.map_none]]
    cases prog.symbols.findSome? (fun (n, o) => if o == off then hooks n else none) <;> rfl

/-- For a program without overrides, answering the oracle queries of
    `execUntilPCWithOracle` with a pure handler `impl` gives `ProofLib.execUntilPC` on the program
    whose overrides are `hooks.withHandler impl`. -/
theorem simulateQ_execUntilPCWithOracle (impl : H) (prog : Program)
    (hooks : OracleExterns M) (hO : ∀ sym, prog.overrides sym = none)
    (fuel : Nat) (target : BitVec 64) (s : State) :
    PureOracleHandler.eval impl (execUntilPCWithOracle fuel prog hooks target s) =
      (Pure.pure (execUntilPC fuel { prog with overrides := hooks.withHandler impl } target s) :
        Id State) := by
  induction fuel generalizing s with
  | zero =>
    simp only [execUntilPCWithOracle, execUntilPC, PureOracleHandler.eval_pure]
  | succ fuel ih =>
    unfold execUntilPCWithOracle execUntilPC
    split
    · exact PureOracleHandler.eval_pure impl s
    · rename_i hstop
      have hrun : s.status = .Running := by
        cases hs : s.status with
        | Running => rfl
        | _ => simp [hs] at hstop; exact Bool.noConfusion (hstop.2 : true = false)
      unfold stepStateWithOracle stepState
      rw [hrun]
      simp only
      have hext : ({ prog with overrides := hooks.withHandler impl } : Program).externAt? s.pc =
          match prog.oracleExternAt? hooks s.pc with
          | some g => some fun s => PureOracleHandler.eval impl (g s)
          | none => prog.externAt? s.pc :=
        Program.hookAtOff?_withHandler prog hO hooks impl _
      rw [hext]
      cases hk : prog.oracleExternAt? hooks s.pc with
      | some f =>
        simp only
        rw [PureOracleHandler.eval_bind]
        exact ih _
      | none =>
        simp only
        have hfm : ({ prog with overrides := hooks.withHandler impl } : Program).fetchMem s.mem
            s.pc = prog.fetchMem s.mem s.pc := by
          unfold Program.fetchMem
          rw [hext, hk]
        rw [hfm]
        cases prog.externAt? s.pc with
        | some g =>
          simp only [Option.map_some]
          rw [PureOracleHandler.eval_bind, PureOracleHandler.eval_pure (M := M)]
          exact ih _
        | none =>
          simp only
          cases prog.fetchMem s.mem s.pc <;>
          · simp only [Option.map_some]
            rw [PureOracleHandler.eval_bind, PureOracleHandler.eval_pure (M := M)]
            exact ih _

/-- With oracle hooks that keep frozen memory for every pure handler, the pure program under
    every handler satisfies `Program.HooksKeepFrozen` (given that the program's own hooks do). -/
theorem OracleExterns.KeepFrozen.hooksKeepFrozen {prog : Program} {hooks : OracleExterns M}
    (hO : ∀ sym, prog.overrides sym = none) (hK : hooks.KeepFrozen)
    (hP : prog.HooksKeepFrozen) (impl : H) :
    ({ prog with overrides := hooks.withHandler impl } : Program).HooksKeepFrozen := by
  intro pc f s hf
  have hext := Program.hookAtOff?_withHandler prog hO hooks impl (pc - prog.base).toNat
  change ({ prog with overrides := hooks.withHandler impl } : Program).externAt? pc = _ at hext
  rw [hext] at hf
  cases hk : prog.oracleHookAtOff? hooks (pc - prog.base).toNat with
  | none => rw [hk] at hf; exact hP pc f s hf
  | some g =>
    rw [hk] at hf
    simp only [Option.some.injEq] at hf
    subst hf
    unfold Program.oracleHookAtOff? at hk
    split at hk
    · exact nomatch hk
    · obtain ⟨⟨n, o⟩, -, hp⟩ := List.exists_of_findSome?_eq_some hk
      simp only at hp
      split at hp
      · exact hK impl n (fun s => PureOracleHandler.eval impl (g s)) s
          (by simp [OracleExterns.withHandler, hp])
      · exact nomatch hp

end Bridge

/-! ## Counted Runs (`RunsToAt`, `RunsTo`) -/

section CountedRuns

variable {M : Type → Type} [Monad M]

/-- `n` hook-free steps from `s` reach a state satisfying `P`, uniformly in the extra fuel
    (assuming the code is loaded). -/
def RunsToAt (prog : Program) (hooks : OracleExterns M) (target : BitVec 64) (n : Nat)
    (s : State) (P : State → Prop) : Prop :=
  prog.CodeLoaded s.mem → ∃ s', (∀ j, execUntilPCWithOracle (j + n) prog hooks target s =
    execUntilPCWithOracle j prog hooks target s') ∧ P s' ∧ prog.CodeLoaded s'.mem

/-- Running from `s` with `j + n` fuel and continuing with `k` gives `m`, for every `j`
    (assuming the code is loaded). -/
def RunsTo {α : Type} (prog : Program) (hooks : OracleExterns M) (target : BitVec 64)
    (n : Nat) (s : State) (k : State → M α) (m : M α) : Prop :=
  prog.CodeLoaded s.mem → ∀ j, (execUntilPCWithOracle (j + n) prog hooks target s >>= k) = m

variable {prog : Program} {hooks : OracleExterns M} {target : BitVec 64}

@[simp] theorem execUntilPCWithOracle_zero (s : State) :
    execUntilPCWithOracle 0 prog hooks target s = pure s := rfl

theorem RunsToAt.refl {s : State} {P : State → Prop} (h : P s) :
    RunsToAt prog hooks target 0 s P :=
  fun hL => ⟨s, fun _ => rfl, h, hL⟩

/-- Weaken the postcondition of `RunsToAt`. -/
theorem RunsToAt.weaken {n : Nat} {s : State} {P Q : State → Prop}
    (h : RunsToAt prog hooks target n s P) (himp : ∀ s', P s' → Q s') :
    RunsToAt prog hooks target n s Q := by
  intro hL
  obtain ⟨s', heq, hP, hL'⟩ := h hL
  exact ⟨s', heq, himp s' hP, hL'⟩

/-- Chain two `RunsToAt` segments of lengths `n` and `m`. -/
theorem RunsToAt.trans {n m : Nat} {s : State} {P Q : State → Prop}
    (h1 : RunsToAt prog hooks target n s P)
    (h2 : ∀ s', P s' → RunsToAt prog hooks target m s' Q) :
    RunsToAt prog hooks target (m + n) s Q := by
  intro hL
  obtain ⟨s1, heq1, hP, hL1⟩ := h1 hL
  obtain ⟨s2, heq2, hQ, hL2⟩ := h2 s1 hP hL1
  refine ⟨s2, fun j => ?_, hQ, hL2⟩
  rw [← Nat.add_assoc, heq1 (j + m), heq2 j]

/-- One step of `execUntilPCWithOracle` when not at the target and running. -/
theorem execUntilPCWithOracle_succ_running {fuel : Nat} {s : State} (hne : s.pc ≠ target)
    (hrun : s.status = .Running) :
    execUntilPCWithOracle (fuel + 1) prog hooks target s =
      match stepStateWithOracle prog hooks s with
      | some c => c >>= execUntilPCWithOracle fuel prog hooks target
      | none => Pure.pure s := by
  have hc : (s.pc == target || s.status != .Running) = false := by
    rw [hrun]; simp [hne]; rfl
  rw [execUntilPCWithOracle, hc]
  rfl

/-- One ordinary instruction step (no oracle hook, not at the target). The instruction is
    fetched from the code image (`Program.fetch`, which is `none` at any hook). -/
theorem RunsToAt.step [LawfulMonad M] {n : Nat} {s : State} {inst : Instr} {P : State → Prop}
    (hne : s.pc ≠ target) (hrun : s.status = .Running)
    (hhook : prog.oracleExternAt? hooks s.pc = none)
    (hfetch : prog.fetch s.pc = some inst)
    (h : RunsToAt prog hooks target n (prog.evalInst inst s) P) :
    RunsToAt prog hooks target (n + 1) s P := by
  intro hL
  have hext : prog.externAt? s.pc = none := by
    unfold Program.fetch at hfetch
    split at hfetch
    · exact nomatch hfetch
    · rename_i hne'; simpa using hne'
  have hfm := Program.fetchMem_of_fetch hL hfetch
  have hL' : prog.CodeLoaded (prog.evalInst inst s).mem :=
    (Step.exec (prog := prog) hrun hfm).codeLoaded hL
  obtain ⟨s', heq, hP, hL''⟩ := h hL'
  refine ⟨s', fun j => ?_, hP, hL''⟩
  rw [← heq j]
  show execUntilPCWithOracle ((j + n) + 1) prog hooks target s = _
  rw [execUntilPCWithOracle_succ_running hne hrun]
  simp only [stepStateWithOracle, hrun, hhook, stepState, hext, hfm, Option.map_some]
  rw [pure_bind]

/-- The target is reached: extra fuel does not change the run. -/
theorem execUntilPCWithOracle_of_pc_eq {s : State} (hpc : s.pc = target) (fuel : Nat) :
    execUntilPCWithOracle fuel prog hooks target s = Pure.pure s := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [execUntilPCWithOracle]
    simp [hpc]

/-- Compose a hook-free segment with the rest of the run. -/
theorem RunsToAt.seq {α : Type} {n m : Nat} {s : State} {P : State → Prop}
    {k : State → M α} {res : M α}
    (h1 : RunsToAt prog hooks target n s P)
    (h2 : ∀ s', P s' → RunsTo prog hooks target m s' k res) :
    RunsTo prog hooks target (m + n) s k res := by
  intro hL j
  obtain ⟨s', heq, hP, hL'⟩ := h1 hL
  rw [← Nat.add_assoc, heq (j + m)]
  exact h2 s' hP hL' j

/-- The run has returned to the target: continue with `k`. -/
theorem RunsTo.done [LawfulMonad M] {α : Type} {s : State} {k : State → M α}
    {res : M α} (hpc : s.pc = target) (h : k s = res) :
    RunsTo prog hooks target 0 s k res := by
  intro _ j
  rw [Nat.add_zero, execUntilPCWithOracle_of_pc_eq hpc, pure_bind, h]

/-- A hooked step: the hook `f` runs (in `M`), then the run continues. -/
theorem RunsTo.hook [LawfulMonad M] {α : Type} {n : Nat} {s : State} {f : State → M State}
    {k : State → M α} {res : M α}
    (hne : s.pc ≠ target) (hrun : s.status = .Running)
    (hhook : prog.oracleExternAt? hooks s.pc = some f)
    (h : prog.CodeLoaded s.mem → ∀ j,
      (f s >>= fun s' => execUntilPCWithOracle (j + n) prog hooks target s' >>= k) = res) :
    RunsTo prog hooks target (n + 1) s k res := by
  intro hL j
  show (execUntilPCWithOracle ((j + n) + 1) prog hooks target s >>= k) = res
  rw [execUntilPCWithOracle_succ_running hne hrun]
  simp only [stepStateWithOracle, hrun, hhook]
  rw [bind_assoc]
  exact h hL j


/-- Use a counted run: every fuel `≥ n` gives `res` (if the code is loaded). -/
theorem RunsTo.exec {α : Type} {n : Nat} {s : State} {k : State → M α}
    {res : M α} (h : RunsTo prog hooks target n s k res) (hL : prog.CodeLoaded s.mem)
    (fuel : Nat) (hle : n ≤ fuel) :
    (execUntilPCWithOracle fuel prog hooks target s >>= k) = res := by
  have := h hL (fuel - n)
  rwa [Nat.sub_add_cancel hle] at this


end CountedRuns

/-- Oracle hooks are only found at hooked offsets. -/
theorem Program.oracleHookAtOff?_eq_none {M : Type → Type} {prog : Program}
    {hooks : OracleExterns M} {hookedOffs : List Nat}
    (h_check : prog.symbols.all (fun p => hookedOffs.contains p.2 || (hooks p.1).isNone) = true)
    {off : Nat} (h_not_in : hookedOffs.contains off = false) :
    prog.oracleHookAtOff? hooks off = none := by
  unfold Program.oracleHookAtOff?
  split
  · rfl
  · generalize prog.symbols = syms at h_check
    induction syms with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.all_cons, Bool.and_eq_true, Bool.or_eq_true] at h_check
      simp only [List.findSome?]
      by_cases heq : (p.2 == off) = true
      · have hp : p.2 = off := beq_iff_eq.mp heq
        rcases h_check.1 with h_in | h_none
        · rw [hp, h_not_in] at h_in; contradiction
        · rw [heq]
          simp only [↓reduceIte, Option.isNone_iff_eq_none.mp h_none]
          exact ih h_check.2
      · rw [Bool.eq_false_of_ne_true heq]
        exact ih h_check.2


/-- The return address `target` is disjoint from every code offset `b + off` with `off < bound`. -/
def RetAway (bound : Nat) (b target : BitVec 64) : Prop :=
  ∀ off : Nat, off < bound → b + BitVec.ofNat 64 off ≠ target

theorem RetAway.ne_add {bound : Nat} {b target : BitVec 64} (h : RetAway bound b target)
    (off : Nat) (hoff : off < bound := by decide) :
    b + BitVec.ofNat 64 off ≠ target :=
  h off hoff

theorem RetAway.ne_base {bound : Nat} (hpos : 0 < bound := by decide)
    {b target : BitVec 64} (h : RetAway bound b target) :
    b ≠ target := by
  simpa using h 0 hpos

/-- Take one ordinary instruction step in a `RunsToAt` goal and normalize the resulting state. -/
macro "oracle_step" : tactic =>
  `(tactic| (
    refine RunsToAt.step (inst := ?inst) ?hne ?hrun ?hhook ?hfetch ?_
    case hfetch => ((try simp (config := { decide := true }) only [arm64_norm, *]) <;> rfl)
    case hne =>
      ((try simp only [arm64_norm, *]) <;>
       first
       | decide
       | exact RetAway.ne_add (by assumption) _
       | exact RetAway.ne_base (by decide) (by assumption))
    case hhook => ((try simp (config := { decide := true }) only [arm64_norm, *]) <;> rfl)
    case hrun => (simp only [arm64_norm, *])
    try dsimp only [Program.evalInst, execInst, execInstWithSvc, execAddSubImm, execAddSubExt, execAddSubShift, execAddSubCarry, execLogicalImm,
      execLogicalShift, execMoveWide, execBitfield, execCondSelect, execCondCompare,
      execDataProc1, execDataProc2, execDataProc3, execLdr, execLdrLit, execStr, execLdp, execStp,
      evalLogical, evalBitfield, evalAddrMode, AddrMode.baseReg, checkRegSPAligned,
      checkAddrSPAligned, MemWidth.isAligned, State.spAligned, extendVal, Reg.fromZRBits,
      Reg.fromSPBits]
    try simp (config := { decide := true }) only [arm64_norm, *]
    try arm64_discharge_perms_internal))

end ProofLib

end
