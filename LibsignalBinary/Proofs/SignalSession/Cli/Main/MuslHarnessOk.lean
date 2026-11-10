/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslElf

@[expose] public section

set_option autoImplicit false

/-!
# `MuslHarness` Instance from musl Startup and Exit Proofs

Proves `Cli.MuslHarness` (`muslHarness_ok`) generically from musl startup (`MuslElf.musl_startup`)
and exit (`MuslExit.musl_exit_ofImage`) hypotheses together with `argvAt_eq` (`InitStack.argvAt =
Cli.argvAt`).
-/

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.MuslExit CryptoVerification.SignalSession.MuslStart
  CryptoVerification.SignalSession.MuslElf

theorem argvAt_eq (a : BitVec 64) (ss : List (List (BitVec 8))) :
    InitStack.argvAt a ss = argvAt a ss := by
  induction ss generalizing a with
  | nil => rfl
  | cons s ss ih =>
    simp only [InitStack.argvAt, argvAt, ih]
    rfl

theorem musl_exit_bound {e : BitVec 64} (h : e.toNat + 4 ≤ InitStack.stackBase) :
    e.toNat + 0xb74 ≤ 2 ^ 64 := by
  have := InitStack.stackBase_eq
  omega

/-- Constructs `MuslHarness` for an ELF image with `main = entry - 89668`, `Fr := muslFiniFr entry`,
and entry precondition `mainEntryPre img A stk Statics`. -/
theorem muslHarness_ok {li : Obj.LinkedImage} {img : Obj.Image} (himg : Obj.Loads li img)
    (ext : String → Option (State → State)) {elf : ElfImage} {code : List (BitVec 8)}
    (hC : CliElfMusl elf code)
    (hend : img.base.toNat + img.code.length ≤ elf.entry.toNat)
    (hfS : MuslStartFetch ({ code } : Program) 0#64)
    (hfE : MuslExitFetch ({ code } : Program) 0#64)
    (hmain : entryOf img mainName = elf.entry - 85504#64)
    {A : RustAlloc} {stk : Nat} {Statics : SepProp} (hstk : stk ≤ cliStackBudget)
    {S : Nat → Prop}
    (hF : ∀ i s0, elf.loadState (cliInputs i) = .ok s0 → img.FrozenLoaded s0)
    (hR : ∀ i s0, elf.loadState (cliInputs i) = .ok s0 →
      SupportedOn 0#64 S s0.mem (A.pool ∗ Statics))
    (hS : ∀ k, S k → k < InitStack.stackBase ∧
      ¬((elf.entry + 0x2000#64).toNat ≤ k ∧ k < (elf.entry + 0x2000#64).toNat + 600)) :
    MuslHarness elf (cliProg img ext) (entryOf img mainName) (muslFiniFr elf.entry)
      (fun i => CliInputsOk i ∧ InputsLoadable i) (mainEntryPre img A stk Statics) := by
  intro hE i hi
  obtain ⟨hwf, hbrk⟩ := hE
  obtain ⟨⟨hargs, hfits⟩, hdirs, hfiles⟩ := hi
  have hbrk' : elf.brkStart.toNat ≤ InitStack.stackBase := hbrk
  have hargs' : ∀ a ∈ i.argv, ∀ c ∈ a.toList, 0 < c.toNat ∧ c.toNat < 128 :=
    fun a ha => (hargs a ha).2
  have hfits' : (i.argv.map fun a => a.length + 1 + 8).sum ≤ cliArgBudget := hfits
  obtain ⟨s0, sm, hload, hsteps, hpc, hrun, hal, hsp, hx0, hx1, hlr, hfs, htr, hmem, hstk_sp⟩ :=
    musl_startup himg (Rust.withPanics ext) hC hwf hbrk' hend hfS i.argv i.stdin i.files i.dirs
      hargs' hfits' hdirs hfiles stk hstk (R := A.pool ∗ Statics) (S := S) (hR i) hS
  refine ⟨s0, sm, hload, hsteps, hpc.trans hmain.symm, hrun, hal, hfs, htr, hx0, ?_, ?_⟩
  · have hFL : img.FrozenLoaded sm := (hF i s0 hload).of_keepsFrozen hsteps.keepsFrozen
    simp only [mainEntryPre, mainFrame, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hFL, hstk_sp⟩, ?_⟩
    rw [argvAt_eq] at hmem
    simpa only [InitStack.cliStrs, sepConj_assoc] using hmem
  · intro sr hsteps' hret hm
    have hL : ({ base := elf.entry, code } : Program).CodeLoaded sm.mem :=
      hsteps.codeLoaded (codeLoaded_of_text hC hwf hbrk' hload)
    exact musl_exit_ofImage himg (Rust.withPanics ext) hC.entry_page hend
      (musl_exit_bound (entry_bound elf hwf hbrk')) hfE hL hlr hal hsteps' hret hm

end CryptoVerification.SignalSession.Cli
