/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Placed
import Arm64.Trusted.Spec.Hoare
import all Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Relocatable `main` I/O Callees (`[LibsignalPlacement]`)

Relocatable `[LibsignalPlacement]` counterparts of `IoHooks.lean` on Block `617` (`lsProg_617 H`),
discharging `MainIoPlaced` over `cliExternsPlaced mmpl W` and ghost-extended hook maps.
-/

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoVerification CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.HooksE

/-! ## `HookOk` on Placed I/O Specs -/

theorem writeStdoutHook_ok_placed (stk : Nat) :
    HookOk writeStdoutHook (writeStdoutSpecPlaced stk) := by
  intro x R s0 hrun hpre _
  simp only [writeStdoutSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1⟩, hmem⟩ := hpre
  obtain ⟨hlen, hrd⟩ := (IsBlock.pointsToBytes x.buf x.bs).read hmem
  have hcan := (IsBlock.pointsToBytes x.buf x.bs).canRead hlen hmem
  rw [← hx0] at hrd hcan
  rw [writeStdoutHook_eq hx1 hcan hrd]
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [writeStdoutSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨rfl, rfl, List.prefix_append _ _, ?_⟩, hmem⟩
  change ProcessOutcome.traceStreamBytes .stdout (s0.trace ++ TraceEvent.ofBytes .stdout x.bs) = _
  rw [traceStreamBytes_append, traceStreamBytes_ofBytes_stdout]

private theorem writeFile_outcome_placed {stk : Nat} {x : WriteFileGhost} {R : SepProp}
    {s0 : State} {ok : Bool} {fs' : FsState} (hrun : s0.status = .Running)
    (hmem : s0.mem ⊨ (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp stk ∗ R)
    (hpost :
      let sf := unitResult ok ((s0.appendTrace [.fileChanged (pathStr x.path)]).setFs fs')
      match cliIo.wr s0.fs.files x.path x.bs with
      | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
      | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) :
    let sf := unitResult ok ((s0.appendTrace [.fileChanged (pathStr x.path)]).setFs fs')
    s0.mem.KeepsFrozen sf.mem ∧ sf.symtab = s0.symtab ∧
      SubroutineOutcome (writeFileSpecPlaced cliIo stk) x R s0 sf := by
  intro sf
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  simp only [writeFileSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hpost, List.prefix_append _ _, ?_⟩, hmem⟩
  change ProcessOutcome.traceStreamBytes .stdout (s0.trace ++ [.fileChanged (pathStr x.path)]) = _
  rw [traceStreamBytes_append, traceStreamBytes_fileChanged, List.append_nil]

theorem writeFileHook_ok_placed (stk : Nat) :
    HookOk writeFileHook (writeFileSpecPlaced cliIo stk) := by
  intro x R s0 hrun hpre _
  simp only [writeFileSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hlen32, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1
  obtain ⟨hlenP, hrdP⟩ := (IsBlock.pointsToBytes x.pathA x.path).read hmem
  have hcanP := (IsBlock.pointsToBytes x.pathA x.path).canRead hlenP hmem
  have hmemB : s0.mem ⊨ (x.buf ↦ₛ x.bs) ∗ (x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ R := by
    rw [sepConj_left_comm]; exact hmem
  obtain ⟨hlenB, hrdB⟩ := (IsBlock.pointsToBytes x.buf x.bs).read hmemB
  have hcanB := (IsBlock.pointsToBytes x.buf x.bs).canRead hlenB hmemB
  rw [← hx0] at hrdP hcanP
  rw [← hx2] at hrdB hcanB
  rw [writeFileHook_eq hx1 hx3 (by rw [hcanP, hcanB]; rfl) hrdP hrdB hpok' hpok.2.2]
  simp only
  cases hA : blockingAncestorF s0.fs.files (pathStr x.path) with
  | some a =>
    exact writeFile_outcome_placed hrun hmem (by simp only [cliIo, cliWr, hA]; exact ⟨rfl, rfl⟩)
  | none =>
    cases hB : s0.fs.files (pathStr x.path) with
    | none =>
      exact writeFile_outcome_placed hrun hmem
        (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, funext fun q => files_setFile _ _ _ q⟩)
    | some e =>
      cases e with
      | dir =>
        exact writeFile_outcome_placed hrun hmem
          (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, rfl⟩)
      | file b =>
        exact writeFile_outcome_placed hrun hmem
          (by simp only [cliIo, cliWr, hA, hB]; exact ⟨rfl, funext fun q => files_setFile _ _ _ q⟩)

theorem readFileHook_okOn_placed (stk : Nat) :
    HookOkOn (fun x s => ¬ ReadFileOom x s) readFileHook
      (readFileLitSpecPlaced cliIo E2E.HooksE.A0 stk) := by
  intro x R s0 hnoom hrun hpre _
  simp only [readFileLitSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx8, hlen32, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1
  have hlenP : x.path.length ≤ 2 ^ 64 := by omega
  have hrdP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).read hmem
  have hcanP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).canRead hlenP hmem
  have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
      ((x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
    rw [sepConj_left_comm]; exact hmem
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
  rw [← hx0] at hrdP hcanP
  rw [← hx8] at hcanW
  have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
    readPath_eq_pathStr hx1 hrdP
  have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
    (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.2.2)
  rw [hp] at heq
  have hrd : ∀ r, readView s0.fs (pathStr x.path) = r →
      cliIo.rd s0.fs.files x.path = (match r with | none => .error () | some bs => .ok bs) := by
    intro r hr
    show cliRd s0.fs.files x.path = _
    unfold cliRd
    rw [← readView_eq_readViewF, hr]
    cases r <;> rfl
  cases hv : readView s0.fs (pathStr x.path) with
  | none =>
    rw [hv] at heq
    dsimp only at heq
    obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok hx8 hmemR
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readFileLitSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.error (), ⟨rfl, (hrd none hv).symm, rfl⟩, ?_⟩
    simp only [ioVecAt, sepConj_assoc] at hm ⊢
    exact hm
  | some bs =>
    rw [hv] at heq
    dsimp only at heq
    have hfit : bs ≠ [] → E2E.bumpAddr? s0.mem bs.length 1 ≠ none :=
      fun hne hnone => hnoom ⟨bs, hv, hne, hnone⟩
    obtain ⟨m, hsf, hkf, hm⟩ := vecOk_ok hx8 hmemR hfit
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readFileLitSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.ok bs, ⟨rfl, (hrd (some bs) hv).symm, rfl⟩, ?_⟩
    simp only [ioVecAt] at hm ⊢
    exact hm

theorem readStdinHook_okOn_placed (stk : Nat) :
    HookOkOn (fun x s => ¬ ReadStdinOom x s) readStdinHook
      (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk) := by
  intro x R s0 hnoom hrun hpre _
  simp only [readStdinSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hin⟩, hmem⟩ := hpre
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmem
  rw [← hx8] at hcanW
  obtain ⟨fs', hfs', heq⟩ := readStdinHook_eq hcanW hin
  by_cases hcap : x.bs.length ≤ stdinCapBytes
  · simp only [hcap, ↓reduceIte] at heq
    have hfit : x.bs ≠ [] → E2E.bumpAddr? (s0.setFs fs').mem x.bs.length 1 ≠ none :=
      fun hne hnone => hnoom ⟨hcap, hne, hnone⟩
    obtain ⟨m, hsf, hkf, hm⟩ := vecOk_ok (s := s0.setFs fs') hx8 hmem hfit
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readStdinSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.ok x.bs, ⟨hfs', by simp [readStdinResult, hcap], rfl⟩, ?_⟩
    simp only [ioVecAt] at hm ⊢
    exact hm
  · simp only [hcap, ↓reduceIte] at heq
    obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok (s := s0.setFs fs') hx8 hmem
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readStdinSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.error (), ⟨hfs', by simp [readStdinResult, hcap], rfl⟩, ?_⟩
    simp only [ioVecAt, sepConj_assoc] at hm ⊢
    exact hm

theorem readFileHook_okOom_placed (stk : Nat) :
    HookOkOn ReadFileOom readFileHook (readFileLitSpecPlaced cliIo E2E.HooksE.A0 stk) := by
  intro x R s0 hoom hrun hpre0 hsp
  have hpre := hpre0
  simp only [readFileLitSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx8, hlen32, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1
  have hlenP : x.path.length ≤ 2 ^ 64 := by omega
  have hrdP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).read hmem
  have hcanP := (IsBlockRO.pointsToBytesRO x.pathA x.path hlenP).canRead hlenP hmem
  have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
      ((x.pathA ↦ᵣ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
    rw [sepConj_left_comm]; exact hmem
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
  rw [← hx0] at hrdP hcanP
  rw [← hx8] at hcanW
  have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
    readPath_eq_pathStr hx1 hrdP
  have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
    (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.2.2)
  rw [hp] at heq
  obtain ⟨bs, hv, hne, hnone⟩ := hoom
  rw [hv] at heq
  dsimp only at heq
  rw [heq, vecOk_oom hne hnone]
  exact HooksOkAux.allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre0 hsp

theorem readStdinHook_okOom_placed (stk : Nat) :
    HookOkOn ReadStdinOom readStdinHook (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk) := by
  intro x R s0 ⟨hcap, hne, hnone⟩ _ hpre0 _
  have hpre := hpre0
  simp only [readStdinSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hin⟩, hmem⟩ := hpre
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmem
  rw [← hx8] at hcanW
  obtain ⟨fs', -, heq⟩ := readStdinHook_eq hcanW hin
  simp only [hcap, ↓reduceIte] at heq
  rw [heq, vecOk_oom (s := s0.setFs fs') hne hnone]
  refine ⟨Memory.KeepsFrozen.refl _, rfl, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
  change s0.mem ⊨ (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk).onPanic x s0
    (E2E.allocPanicHook (s0.setFs fs')) ∗ R
  simp only [readStdinSpecPlaced, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨HooksOkAux.allocFailedIn_allocPanicHook (s0.setFs fs'),
      HooksOkAux.trace_prefix_allocPanicHook (s0.setFs fs')⟩,
    Satisfies.mono (sepConj_mono_left (Entails.top_right fun _ => trivial)) hpre0⟩

theorem readFileHook_ok_placed (stk : Nat) :
    HookOk readFileHook (readFileLitSpecPlaced cliIo E2E.HooksE.A0 stk) :=
  hookOk_of_on (readFileHook_okOom_placed stk) (readFileHook_okOn_placed stk)

theorem readStdinHook_ok_placed (stk : Nat) :
    HookOk readStdinHook (readStdinSpecPlaced cliIo E2E.HooksE.A0 stk) :=
  hookOk_of_on (readStdinHook_okOom_placed stk) (readStdinHook_okOn_placed stk)

/-! ## `MainIoPlaced` Assembly on `cliExternsPlaced` and Ghost Overlays -/

theorem cliExternsPlaced_writeFile (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsWriteFileSym = some writeFileHook :=
  main_cliExternsPlaced_row mmpl W
    (List.mem_append_right _ (List.mem_of_getElem? (i := 3) rfl))

theorem cliExternsPlaced_writeStdout (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsWriteStdoutSym = some writeStdoutHook :=
  main_cliExternsPlaced_row mmpl W
    (List.mem_append_right _ (List.mem_of_getElem? (i := 4) rfl))

theorem cliExternsPlaced_memrchr (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliExternsPlaced mmpl W lsMemrchrSym = some memrchrHook :=
  main_cliExternsPlaced_row mmpl W
    (List.mem_append_right _ (List.mem_of_getElem? (i := 5) rfl))

theorem writeFile_rocl_ok_of_lookup [LibsignalPlacement] {H : LibsignalHooks} (stk : Nat)
    (hLookup : H lsWriteFileSym = some writeFileHook) :
    subroutine_ok (lsProg_617 H) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlaced cliIo stk)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617)
      ⟨writeFileHook, hLookup, writeFileHook_ok_placed stk⟩ (by decide)

theorem writeStdout_rocl_ok_of_lookup [LibsignalPlacement] {H : LibsignalHooks} (stk : Nat)
    (hLookup : H lsWriteStdoutSym = some writeStdoutHook) :
    subroutine_ok (lsProg_617 H) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlaced stk)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617)
      ⟨writeStdoutHook, hLookup, writeStdoutHook_ok_placed stk⟩ (by decide)

theorem writeFile_rocl_ok_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (stk : Nat) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsWriteFileSym)
      (withLsRoCl lsmpl (writeFileSpecPlaced cliIo stk)) :=
  writeFile_rocl_ok_of_lookup stk (cliExternsPlaced_writeFile mmpl W)

theorem writeStdout_rocl_ok_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (stk : Nat) :
    subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsWriteStdoutSym)
      (withLsRoCl lsmpl (writeStdoutSpecPlaced stk)) :=
  writeStdout_rocl_ok_of_lookup stk (cliExternsPlaced_writeStdout mmpl W)

theorem readStdin_rocl_ok_of_hookSat [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat} (hSat : HookSat H lsReadStdinSym (readStdinSpecPlaced cliIo A stk)) :
    subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A stk)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hSat (by decide)

theorem readFile_rocl_ok_of_hookSat [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {stk : Nat} (hSat : HookSat H lsReadFileSym (readFileLitSpecPlaced cliIo A stk)) :
    subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A stk)) :=
  subroutine_ok_rocl_of_plain <|
    ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617) hSat (by decide)

theorem readStdin_rocl_ok_of_lookup [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {f : State → State} {stk : Nat}
    (hLookup : H lsReadStdinSym = some f)
    (hOk : HookOk f (readStdinSpecPlaced cliIo A stk)) :
    subroutine_ok (lsProg_617 H) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A stk)) :=
  readStdin_rocl_ok_of_hookSat ⟨f, hLookup, hOk⟩

theorem readFile_rocl_ok_of_lookup [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {f : State → State} {stk : Nat}
    (hLookup : H lsReadFileSym = some f)
    (hOk : HookOk f (readFileLitSpecPlaced cliIo A stk)) :
    subroutine_ok (lsProg_617 H) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A stk)) :=
  readFile_rocl_ok_of_hookSat ⟨f, hLookup, hOk⟩

/-- Assembles `MainIoPlaced` over a ghost-extended hook map `H` from `HookSat` witnesses for
`read_stdin`/`read_file` and hook-table lookups for `write_file`/`write_stdout`. -/
theorem mainIo_of_lookup_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (stk : Nat)
    (hReadStdin : HookSat H lsReadStdinSym (readStdinSpecPlaced cliIo A stk))
    (hReadFile : HookSat H lsReadFileSym (readFileLitSpecPlaced cliIo A stk))
    (hWriteFile : H lsWriteFileSym = some writeFileHook)
    (hWriteStdout : H lsWriteStdoutSym = some writeStdoutHook) :
    MainIoPlaced A H cliIo stk where
  readStdin := readStdin_rocl_ok_of_hookSat hReadStdin
  readFile := readFile_rocl_ok_of_hookSat hReadFile
  writeFile := writeFile_rocl_ok_of_lookup stk hWriteFile
  writeStdout := writeStdout_rocl_ok_of_lookup stk hWriteStdout

/-- Assembles `MainIoPlaced` on `cliExternsPlaced mmpl W` given `subroutine_ok` for `read_stdin`
and `read_file`. -/
theorem mainIo_of_cliHooks_placed [LibsignalPlacement] {A : RustAlloc}
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (stk : Nat)
    (hReadStdin : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadStdinSym)
      (withLsRoCl lsmpl (readStdinSpecPlaced cliIo A stk)))
    (hReadFile : subroutine_ok (lsProg_617 (cliExternsPlaced mmpl W)) (lsρ lsReadFileSym)
      (withLsRoCl lsmpl (readFileLitSpecPlaced cliIo A stk))) :
    MainIoPlaced A (cliExternsPlaced mmpl W) cliIo stk where
  readStdin := hReadStdin
  readFile := hReadFile
  writeFile := writeFile_rocl_ok_placed mmpl W stk
  writeStdout := writeStdout_rocl_ok_placed mmpl W stk

end CryptoVerification.SignalSession.Cli.MainHops
