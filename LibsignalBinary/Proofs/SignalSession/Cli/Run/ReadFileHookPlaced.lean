/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHookPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `signal_session_io::read_file` Contracts

Establishes `HookOk` for `readFileHook` against `readFileSpecPlaced` and lifts `HookSat` at
`lsReadFileSym` to `subroutine_ok` on any caller block under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunSkeleton

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunGlue
open CryptoVerification.E2E.HooksE.HooksOkAux

theorem cliReadFileHook_okOn_placed (stk : Nat) :
    HookOkOn (fun x s => ¬ CliReadFileOom x s) readFileHook
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk) := by
  intro x R s0 hnoom hrun hpre _
  simp only [readFileSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx8, _, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1.1
  obtain ⟨hlenP, hrdP⟩ := (IsBlock.pointsToBytes x.pathA x.path).read hmem
  have hcanP := (IsBlock.pointsToBytes x.pathA x.path).canRead hlenP hmem
  have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
      ((x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
  rw [← hx0] at hrdP hcanP
  rw [← hx8] at hcanW
  have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
    readPath_eq_pathStr hx1 hrdP
  have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
    (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.1.2.2)
  rw [hp] at heq
  have hrd : ∀ r, readView s0.fs (pathStr x.path) = r →
      cliIo.rd s0.fs.files x.path = (match r with | none => .error () | some bs => .ok bs) := by
    intro r hr
    show cliRd s0.fs.files x.path = _
    unfold cliRd
    rw [← readView_eq_readViewF, hr]
    rfl
  cases hv : readView s0.fs (pathStr x.path) with
  | none =>
    rw [hv] at heq
    dsimp only at heq
    obtain ⟨m, hsf, hkf, hm⟩ := vecErr_ok hx8 hmemR
    rw [heq, hsf]
    refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    simp only [readFileSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.error (), ⟨(hrd none hv).symm, rfl⟩, ?_⟩
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
    simp only [readFileSpecPlaced, sepConj_assoc, sepExists_sepConj_left,
      satisfies_sepExists, satisfies_pure_sepConj]
    refine ⟨.ok bs, ⟨(hrd (some bs) hv).symm, rfl⟩, ?_⟩
    simp only [ioVecAt] at hm ⊢
    exact hm

theorem cliReadFileHook_okOom_placed (stk : Nat) :
    HookOkOn CliReadFileOom readFileHook
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk) := by
  intro x R s0 hoom hrun hpre0 hsp
  have hpre := hpre0
  simp only [readFileSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx8, _, hpok⟩, hmem⟩ := hpre
  have hpok' : PathOk (pathStr x.path) = true := hpok.1.1
  obtain ⟨hlenP, hrdP⟩ := (IsBlock.pointsToBytes x.pathA x.path).read hmem
  have hcanP := (IsBlock.pointsToBytes x.pathA x.path).canRead hlenP hmem
  have hmemR : s0.mem ⊨ memRegion x.ret 24 ∗
      ((x.pathA ↦ₛ x.path) ∗ stackAt s0.sp stk ∗ E2E.HooksE.A0.pool ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  have hcanW := (IsBlock.memRegion x.ret 24).canWrite (by decide) hmemR
  rw [← hx0] at hrdP hcanP
  rw [← hx8] at hcanW
  have hp : readPath s0.mem (s0.readReg64 .x0) (s0.readReg64 .x1) = pathStr x.path :=
    readPath_eq_pathStr hx1 hrdP
  have heq := readFileHook_eq_readView s0 (by rw [hx1, hcanP, hcanW]; rfl)
    (by rw [hp]; exact hpok') (by rw [hx1]; exact hpok.1.2.2)
  rw [hp] at heq
  obtain ⟨bs, hv, hne, hnone⟩ := hoom
  rw [hv] at heq
  dsimp only at heq
  rw [heq, vecOk_oom hne hnone]
  exact allocPanicHook_ok (fun _ _ _ => rfl) x R s0 hrun hpre0 hsp

/-- `readFileHook` satisfies `readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk` at every stack budget `stk`. -/
theorem cliReadFileHook_ok_placed (stk : Nat) :
    HookOk readFileHook (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk) :=
  hookOk_of_on (cliReadFileHook_okOom_placed stk) (cliReadFileHook_okOn_placed stk)

theorem cliReadFilePlaced_hookSat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    (hRead : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk) :=
  hRead

/-- Lifts `HookSat` at `lsReadFileSym` to `subroutine_ok` for `readFileSpecPlaced` under `[LibsignalPlacement]`. -/
theorem cliReadFilePlaced_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (stk : Nat)
    {prog : Program} {i : Nat}
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hRead : subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :
    subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk) :=
  hRead

theorem cliReadFilePlaced_rocl_ok [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks) (stk : Nat)
    {prog : Program} {i : Nat}
    [IsLsBlockProg prog i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hRead : subroutine_ok prog (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :
    subroutine_ok prog (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 stk)) :=
  subroutine_ok_withLsCodeRoLoaded_of_plain (cliReadFilePlaced_ok mmpl g W stk hRead)

end CryptoVerification.SignalSession.Cli.RunSkeleton
