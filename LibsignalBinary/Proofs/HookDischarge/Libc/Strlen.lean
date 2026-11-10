/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Musl.Proofs.MemOps
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import

/-!
# Byte-Exact `strlen` Hook Discharge (`LibsignalBinary.Proofs.HookDischarge.Libc.Strlen`)

Byte-exact discharge of `strlen` against `ProofLib.StdStartup.muslStrlenWords` (`22` 32-bit
instruction words = `88` bytes, verified word-for-word identical to `rustc 1.98.1`'s
`aarch64-unknown-linux-musl/lib/self-contained/libc.a` `strlen.lo` `.text.strlen`, and placed in
`VerifiedLibraries.Musl.muslMemPlacedLib` block `2` via `muslStrlenRO_block_ok`). On
`stockhooks/train`'s snapshot ELF `strlen` is still a zero stub; these `self-contained/libc.a`
bytes enter the shipped binary on the `stock-lld` link at the second cutover.

## 8-Byte SWAR Trailing-Pad Premise (`G-STRLEN-PAD`)
Real `musl` `strlen` (`src/string/strlen.c`) aligns the pointer `x1` up to an 8-byte boundary
byte-by-byte (`+0x04..+0x18`) and then loads 64-bit aligned words `ldr x2, [x1]` (`+0x24`),
reading up to `7` trailing bytes past the terminating `0#8` within the same 8-byte aligned word
(in the engine's byte-granular permission model).
- Consequently, the unpadded consumer specs `MainHops.strlenSpec`, `CliExt.strlenSpec`, and
  `M24.CalleesRO.strlenSpecRO` (owning only `p ↦ₛ (s ++ [0#8])` or `p ↦ᵣ (s ++ [0#8])`) **cannot**
  hold without trailing-byte readability when `(p.toNat + s.length + 1) % 8 ≠ 0` and the remaining
  bytes of that 8-byte aligned word lack read permission in `s0.mem`.
- Every theorem below states that trailing-pad premise **explicitly**:
  1. `StrlenSwarPadBound p s pad`: `8 ≤ (p.toNat + s.length) % 8 + 1 + pad.length ∧
     p.toNat + (s.length + 1 + pad.length) < 2 ^ 64`.
  2. Explicit-pad specs (`strlen_cliStrlenPaddedSpec_ok` / `strlen_strlenPaddedSpecRO_ok`): ghost
     tuple `(p, s, pad)` carrying spatial trailing bytes `((p + BitVec.ofNat 64 (s.length + 1)) ↦ₛ
     pad)` / `↦ᵣ pad` in **both** `pre` and `post`.
  3. Precondition-only wrappers (`withStrlenPadRO`, `withStrlenRoDataPad`, `withStrlenAlignedEnd`):
     modify **only** `spec.pre (p, s) s0` while leaving the `(p, s)` ghost type and `spec.post`,
     `onPanic`, `onExit`, and `onOom` token-identical:
     - `withStrlenPadRO spec` (`strlen_strlenSpecRO_padRO_ok`, `strlen_mainStrlenSpec_padRO_ok`,
       `strlen_cliExtStrlenSpec_padRO_ok`, plus `muslMemPlacedLib` block `2`): adjoins duplicable
       `∃∗ pad, ⌜StrlenSwarPadBound p s pad⌝ ∗ ((p + (s.length + 1)) ↦ᵣ pad)` to `spec.pre`
       (discharged at `main`'s M1 `argv` loop by the readable initial stack bytes following each
       `argv[i]` NUL terminator, or from `RoDataAt` via `strlen_strlenSpecRO_roDataPad_ok`).
     - `withStrlenAlignedEnd spec` (`strlen_cliStrlenSpec_alignedEnd_ok` — `= MainHops.strlenSpec`
       by `rfl`, and `CliExt.strlenSpec` at `extHookStack` — and
       `strlen_strlenSpecRO_alignedEnd_ok`): when the NUL byte ends on an 8-byte boundary
       (`(p.toNat + s.length + 1) % 8 = 0`), `pad = []` suffices.
- **Program hypotheses:** The 17 `hasCode` / `MuslMemPlacement` theorems in §1–§3 and
  `muslMemPlacedLib_strlen_strlenSpecRO_padRO_ok` require only `prog.hasCode entry muslStrlenWords`
  + `entry.toNat + 88 ≤ 2 ^ 64`. The 3 `withVmPreserved` theorems in §4 hold **region-locally on
  any hook-free sub-program** (`∀ pc, prog.externAt? pc = none`, transferred to the hooked CLI
  program via the `K`-route as in `HooksDehook.MemsetCode`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Libc.Strlen

open Arm64 ProofLib
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open ProofLib.StdStartup (muslStrlenWords stdStrlenSpec stdStrlenROSpec muslStrlen_sepWP
  muslStrlen_ro_ok)
open VerifiedLibraries.Musl (MuslMemPlacement muslMemPlacedLib muslMemMpl muslStrlenRO_block_ok)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.CliExt (strlenSpec)
open CryptoVerification.SignalSession.Cli.MainHops (strlenSpec)
open LibsignalBinary.Heap (VmPreserved FdsHiFrame)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (cStrAt)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (cStrAtRO strlenSpecRO)

/-- Explicit 8-byte SWAR word-completion bound for `musl` `strlen(p)` on `s ++ [0#8]`: `pad`
    completes at least the 8-byte aligned word containing the NUL terminator `p + s.length` without
    64-bit address wrap-around. -/
@[expose] def StrlenSwarPadBound (p : BitVec 64) (s pad : List (BitVec 8)) : Prop :=
  8 ≤ (p.toNat + s.length) % 8 + 1 + pad.length ∧
    p.toNat + (s.length + 1 + pad.length) < 2 ^ 64

/-- Stack-parameterized mirror of `CryptoVerification.SignalSession.CliExt.strlenSpec` and
    `CryptoVerification.SignalSession.Cli.MainHops.strlenSpec`. -/
@[expose] def cliStrlenSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (p, s) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ ∀ b ∈ s, b ≠ 0#8⌝ ∗ cStrAt p s ∗ stackAt s0.sp hookStack
  post := fun (p, s) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      cStrAt p s ∗
      stackAt s0.sp hookStack

/-- `cliStrlenSpec hookStack` is definitionally (`rfl`) `MainHops.strlenSpec hookStack`. -/
theorem cliStrlenSpec_eq_mainHops (hookStack : Nat) :
    cliStrlenSpec hookStack =
      CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack := rfl

/-- `cliStrlenSpec extHookStack` is definitionally (`rfl`) `CliExt.strlenSpec`. -/
theorem cliStrlenSpec_extHookStack :
    cliStrlenSpec extHookStack = CryptoVerification.SignalSession.CliExt.strlenSpec := rfl

/-- `MainHops.strlenSpec extHookStack` is definitionally (`rfl`) `CliExt.strlenSpec`. -/
theorem mainHops_strlenSpec_extHookStack :
    CryptoVerification.SignalSession.Cli.MainHops.strlenSpec extHookStack =
      CryptoVerification.SignalSession.CliExt.strlenSpec := rfl

/-- `cliStrlenSpec` augmented in `pre` and `post` with mutable trailing bytes `pad` completing the
    8-byte SWAR word containing `p + s.length` (`G-STRLEN-PAD`). -/
@[expose] def cliStrlenPaddedSpec (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (p, s, pad) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ (∀ b ∈ s, b ≠ 0#8) ∧ StrlenSwarPadBound p s pad⌝ ∗
      cStrAt p s ∗
      ((p + BitVec.ofNat 64 (s.length + 1)) ↦ₛ pad) ∗
      stackAt s0.sp hookStack
  post := fun (p, s, pad) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      cStrAt p s ∗
      ((p + BitVec.ofNat 64 (s.length + 1)) ↦ₛ pad) ∗
      stackAt s0.sp hookStack

/-- Read-only twin of `cliStrlenPaddedSpec` (`M24.CalleesRO.strlenSpecRO` augmented in `pre` and
    `post` with `((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad)`). -/
@[expose] def strlenPaddedSpecRO (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (p, s, pad) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ (∀ b ∈ s, b ≠ 0#8) ∧ StrlenSwarPadBound p s pad⌝ ∗
      cStrAtRO p s ∗
      ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) ∗
      stackAt s0.sp hookStack
  post := fun (p, s, pad) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ sf.trace = s0.trace ∧ sf.fs = s0.fs⌝ ∗
      cStrAtRO p s ∗
      ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) ∗
      stackAt s0.sp hookStack

/-- Adjoin an explicit duplicable read-only 8-byte SWAR trailing-pad witness
    `∃∗ pad, ⌜StrlenSwarPadBound p s pad⌝ ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad)` to
    `spec.pre (p, s) s0`, leaving `spec.post`, `onPanic`, `onExit`, and `onOom` unchanged. -/
@[expose] def withStrlenPadRO (spec : Spec (BitVec 64 × List (BitVec 8))) :
    Spec (BitVec 64 × List (BitVec 8)) :=
  { spec with
    pre := fun (p, s) s0 =>
      (∃∗ pad : List (BitVec 8),
        ⌜StrlenSwarPadBound p s pad⌝ ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad)) ∗
        spec.pre (p, s) s0 }

/-- Adjoin a pure `.rodata` trailing-pad image fact `RoDataAt s0.mem (p + (s.length + 1)) pad`
    to `spec.pre (p, s) s0`, preserving `spec`'s spatial separation-logic footprint verbatim. -/
@[expose] def withStrlenRoDataPad (spec : Spec (BitVec 64 × List (BitVec 8))) :
    Spec (BitVec 64 × List (BitVec 8)) :=
  { spec with
    pre := fun (p, s) s0 =>
      ⌜∃ pad : List (BitVec 8),
        StrlenSwarPadBound p s pad ∧
          RoDataAt s0.mem (p + BitVec.ofNat 64 (s.length + 1)) pad⌝ ∗
        spec.pre (p, s) s0 }

/-- Adjoin the 8-byte aligned-NUL-end premise `(p.toNat + s.length + 1) % 8 = 0 ∧
    p.toNat + s.length + 1 < 2 ^ 64` (`pad = []`) to `spec.pre (p, s) s0`. -/
@[expose] def withStrlenAlignedEnd (spec : Spec (BitVec 64 × List (BitVec 8))) :
    Spec (BitVec 64 × List (BitVec 8)) :=
  { spec with
    pre := fun (p, s) s0 =>
      ⌜(p.toNat + s.length + 1) % 8 = 0 ∧ p.toNat + s.length + 1 < 2 ^ 64⌝ ∗
        spec.pre (p, s) s0 }

/-! ## 1. Separation-Logic & Pure-Words Helpers -/

private theorem cStrAt_sepConj_pad (p : BitVec 64) (s pad : List (BitVec 8)) :
    cStrAt p s ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ₛ pad) =
      (p ↦ₛ (s ++ [0#8] ++ pad)) := by
  dsimp only [cStrAt]
  have hlen : (s ++ [0#8]).length = s.length + 1 := by simp
  rw [pointsToBytes_append p (s ++ [0#8]) pad, hlen]

private theorem cStrAtRO_sepConj_pad (p : BitVec 64) (s pad : List (BitVec 8)) :
    cStrAtRO p s ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) =
      (p ↦ᵣ (s ++ [0#8] ++ pad)) := by
  dsimp only [cStrAtRO]
  have hlen : (s ++ [0#8]).length = s.length + 1 := by simp
  rw [pointsToBytesRO_append p (s ++ [0#8]) pad, hlen]

private theorem pureWordsProg_hasWords_strlen (entry : BitVec 64) :
    (pureWordsProg entry muslStrlenWords).hasWords entry muslStrlenWords :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range muslStrlenWords.length).all fun i =>
      (pureWordsProg 0#64 muslStrlenWords).readWordOff (4 * i) == muslStrlenWords[i]?) = true
    decide +kernel)

private theorem pureWordsProg_noSvcMsr_strlen (entry : BitVec 64) :
    (pureWordsProg entry muslStrlenWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 muslStrlenWords) rfl (by prove_all_instrs)

private theorem vmPreserved_of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

/-! ## 2. Forward Simulations from `stdStrlenROSpec` to Consumer `strlen` Specs -/

/-- `stdStrlenROSpec` forward-simulates `withStrlenPadRO (strlenSpecRO hookStack)`. -/
theorem stdStrlenRO_simulates_strlenSpecRO_padRO (hookStack : Nat := extHookStack) :
    SpecSimulates stdStrlenROSpec (withStrlenPadRO (strlenSpecRO hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, s⟩ R s0 hpre
  dsimp only [withStrlenPadRO, strlenSpecRO] at hpre
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpre
  obtain ⟨pad, hpre⟩ := hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hpad, hnw⟩, hpre⟩
  rw [sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hnz⟩, hmem⟩
  have hno_zero : 0#8 ∉ s := fun h0 => hnz 0#8 h0 rfl
  have hdrop : s0.mem ⊨ cStrAtRO p s ∗ (stackAt s0.sp hookStack ∗ R) :=
    Satisfies.of_sep_right hmem
  have hmem' : s0.mem ⊨ (p ↦ᵣ (s ++ [0#8] ++ pad)) ∗ (stackAt s0.sp hookStack ∗ R) := by
    rw [sepConj_left_comm, ← sepConj_assoc, cStrAtRO_sepConj_pad p s pad] at hmem
    exact hmem
  refine ⟨(p, s, pad), stackAt s0.sp hookStack ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [stdStrlenROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hno_zero, hpad, hnw⟩, hmem'⟩
  · dsimp only [stdStrlenROSpec] at hpost
    dsimp only [withStrlenPadRO, strlenSpecRO]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0_f, hmem_eq, hpres⟩, _⟩
    rw [hmem_eq]
    exact ⟨⟨hx0_f, hpres.2.1, hpres.1⟩, hdrop⟩

/-- `stdStrlenROSpec` forward-simulates `withStrlenPadRO (MainHops.strlenSpec hookStack)` (since
    `stdStrlenROSpec` proves `sf.mem = s0.mem`, restoring the caller's mutable `cStrAt p s` on exit). -/
theorem stdStrlenRO_simulates_mainStrlenSpec_padRO (hookStack : Nat := extHookStack) :
    SpecSimulates stdStrlenROSpec
      (withStrlenPadRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, s⟩ R s0 hpre
  dsimp only [withStrlenPadRO, CryptoVerification.SignalSession.Cli.MainHops.strlenSpec] at hpre
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpre
  obtain ⟨pad, hpre⟩ := hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hpad, hnw⟩, hpre⟩
  rw [sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hnz⟩, hmem⟩
  have hno_zero : 0#8 ∉ s := fun h0 => hnz 0#8 h0 rfl
  have hkeep : s0.mem ⊨ CryptoVerification.SignalSession.Cli.cStrAt p s ∗
      (stackAt s0.sp hookStack ∗ R) :=
    Satisfies.of_sep_right hmem
  dsimp only [CryptoVerification.SignalSession.Cli.cStrAt] at hmem
  rw [sepConj_left_comm] at hmem
  have hro_str : s0.mem ⊨ cStrAtRO p s ∗
      (((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) ∗ (stackAt s0.sp hookStack ∗ R)) :=
    Satisfies.pointsToBytes_to_ro hmem
  have hmem' : s0.mem ⊨ (p ↦ᵣ (s ++ [0#8] ++ pad)) ∗ (stackAt s0.sp hookStack ∗ R) := by
    rw [← sepConj_assoc, cStrAtRO_sepConj_pad p s pad] at hro_str
    exact hro_str
  refine ⟨(p, s, pad), stackAt s0.sp hookStack ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [stdStrlenROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hno_zero, hpad, hnw⟩, hmem'⟩
  · dsimp only [stdStrlenROSpec] at hpost
    dsimp only [withStrlenPadRO, CryptoVerification.SignalSession.Cli.MainHops.strlenSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0_f, hmem_eq, hpres⟩, _⟩
    rw [hmem_eq]
    exact ⟨⟨hx0_f, hpres.2.1, hpres.1⟩, hkeep⟩

/-- Lower `withStrlenPadRO spec` to `withStrlenRoDataPad spec` via `Satisfies.rodata_intro`. -/
theorem sim_roDataPad_of_padRO (spec : Spec (BitVec 64 × List (BitVec 8))) :
    SpecSimulates (withStrlenPadRO spec) (withStrlenRoDataPad spec) := by
  intro ⟨p, s⟩ R s0 hpre
  dsimp only [withStrlenRoDataPad, withStrlenPadRO] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨pad, hbound, hro, hread⟩, hspec⟩ := hpre
  have hlen : pad.length ≤ 2 ^ 64 := by
    have hnw := hbound.2
    omega
  refine ⟨(p, s), R, ?_, fun _ hout => hout⟩
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨pad, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hbound, Satisfies.rodata_intro hro hread hlen hspec⟩

/-- Lower `withStrlenPadRO spec` to `withStrlenAlignedEnd spec` via `pad = []`. -/
theorem sim_alignedEnd_of_padRO (spec : Spec (BitVec 64 × List (BitVec 8))) :
    SpecSimulates (withStrlenPadRO spec) (withStrlenAlignedEnd spec) := by
  intro ⟨p, s⟩ R s0 hpre
  dsimp only [withStrlenAlignedEnd, withStrlenPadRO] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hal, hnw⟩, hspec⟩ := hpre
  have hbound : StrlenSwarPadBound p s [] := by
    refine ⟨?_, ?_⟩ <;> simp only [List.length_nil] <;> omega
  refine ⟨(p, s), R, ?_, fun _ hout => hout⟩
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨[], ?_⟩
  simp only [pointsToBytesRO_nil, sepConj_emp, satisfies_pure_sepConj]
  exact ⟨hbound, hspec⟩

/-! ## 3. Real-Code `hasCode` Contracts (`muslStrlenWords`, `22` Words = `88` Bytes) -/

/-- Read-write `subroutine_ok` contract for static `musl` 1.2.5 AArch64 `strlen` (`↦ₛ`),
    mirroring `ProofLib.StdStartup.muslStrlen_ro_ok` from `muslStrlen_sepWP`. -/
theorem muslStrlen_ok (prog : Program) (entry : BitVec 64)
    (hc : prog.hasCode entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry stdStrlenSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨s, bs, pad⟩ R s0 hpc hrun hpre _hsp
  dsimp only [stdStrlenSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hno_zero, hpad, hno_wrap⟩, hmem⟩
  refine ⟨s ↦ₛ (bs ++ [0#8] ++ pad), hmem, SepWP.mono
    (muslStrlen_sepWP prog entry hc s0 s bs pad hpc hrun hx0 hno_zero hpad hno_wrap haddr) ?_⟩
  intro sf P_f _ _ ⟨⟨hx0_f, hsp_f, hcs_f, hmem_f, hpres_f⟩, hent⟩
  refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0_f, hmem_f, hpres_f⟩, Satisfies.mono (sepConj_mono_left hent) hm⟩

/-- Exact `libc.a` `strlen` bytes (`muslStrlenWords`) satisfy `cliStrlenPaddedSpec hookStack` on
    any program containing `muslStrlenWords` at `entry`. -/
theorem strlen_cliStrlenPaddedSpec_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasCode entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry (cliStrlenPaddedSpec hookStack) := by
  refine subroutine_ok_map (muslStrlen_ok prog entry hc haddr) ?_
  rintro ⟨p, s, pad⟩ R s0 hpre
  dsimp only [cliStrlenPaddedSpec, StrlenSwarPadBound] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hnz, hpad, hnw⟩, hmem⟩ := hpre
  have hno_zero : 0#8 ∉ s := fun h0 => hnz 0#8 h0 rfl
  rw [← sepConj_assoc, cStrAt_sepConj_pad p s pad] at hmem
  refine ⟨(p, s, pad), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [stdStrlenSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hno_zero, hpad, hnw⟩, hmem⟩
  · dsimp only [stdStrlenSpec] at hpost
    dsimp only [cliStrlenPaddedSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0_f, _hmem_eq, hpres⟩, hmem_f⟩
    refine ⟨⟨hx0_f, hpres.2.1, hpres.1⟩, ?_⟩
    rw [← cStrAt_sepConj_pad p s pad, sepConj_assoc] at hmem_f
    exact hmem_f

/-- Exact `libc.a` `strlen` bytes (`muslStrlenWords`) satisfy `strlenPaddedSpecRO hookStack`. -/
theorem strlen_strlenPaddedSpecRO_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasCode entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry (strlenPaddedSpecRO hookStack) := by
  refine subroutine_ok_map (muslStrlen_ro_ok prog entry hc haddr) ?_
  rintro ⟨p, s, pad⟩ R s0 hpre
  dsimp only [strlenPaddedSpecRO, StrlenSwarPadBound] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hnz, hpad, hnw⟩, hmem⟩ := hpre
  have hno_zero : 0#8 ∉ s := fun h0 => hnz 0#8 h0 rfl
  rw [← sepConj_assoc, cStrAtRO_sepConj_pad p s pad] at hmem
  refine ⟨(p, s, pad), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [stdStrlenROSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hno_zero, hpad, hnw⟩, hmem⟩
  · dsimp only [stdStrlenROSpec] at hpost
    dsimp only [strlenPaddedSpecRO]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0_f, _hmem_eq, hpres⟩, hmem_f⟩
    refine ⟨⟨hx0_f, hpres.2.1, hpres.1⟩, ?_⟩
    rw [← cStrAtRO_sepConj_pad p s pad, sepConj_assoc] at hmem_f
    exact hmem_f

/-- Headline consumer bridge (`M24.CalleesRO.strlenSpecRO`): exact `libc.a` `strlen` bytes satisfy
    `withStrlenPadRO (strlenSpecRO hookStack)` on any program containing `muslStrlenWords`. -/
theorem strlen_strlenSpecRO_padRO_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasCode entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry (withStrlenPadRO (strlenSpecRO hookStack)) :=
  (stdStrlenRO_simulates_strlenSpecRO_padRO hookStack).subroutine_ok
    (muslStrlen_ro_ok prog entry hc haddr)

/-- Pure `.rodata`-pad variant for `M24.CalleesRO.strlenSpecRO`. -/
theorem strlen_strlenSpecRO_roDataPad_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasCode entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry (withStrlenRoDataPad (strlenSpecRO hookStack)) :=
  (sim_roDataPad_of_padRO (strlenSpecRO hookStack)).subroutine_ok
    (strlen_strlenSpecRO_padRO_ok hookStack hc haddr)

/-- Read-write consumer bridge (`MainHops.strlenSpec`): exact `libc.a` `strlen` bytes satisfy
    `withStrlenPadRO (MainHops.strlenSpec hookStack)` on any program containing `muslStrlenWords`. -/
theorem strlen_mainStrlenSpec_padRO_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasCode entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withStrlenPadRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)) :=
  (stdStrlenRO_simulates_mainStrlenSpec_padRO hookStack).subroutine_ok
    (muslStrlen_ro_ok prog entry hc haddr)

/-- `CliExt.strlenSpec` specialization (`hookStack = extHookStack`) of
    `strlen_mainStrlenSpec_padRO_ok`. -/
theorem strlen_cliExtStrlenSpec_padRO_ok {prog : Program} {entry : BitVec 64}
    (hc : prog.hasCode entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec) :=
  strlen_mainStrlenSpec_padRO_ok extHookStack hc haddr

/-- Unpadded `cliStrlenSpec` (`= MainHops.strlenSpec`) for strings whose NUL byte ends on an 8-byte
    boundary (`(p.toNat + s.length + 1) % 8 = 0 ∧ p.toNat + s.length + 1 < 2 ^ 64`): `pad = []`. -/
theorem strlen_cliStrlenSpec_alignedEnd_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasCode entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry (withStrlenAlignedEnd (cliStrlenSpec hookStack)) :=
  (sim_alignedEnd_of_padRO (cliStrlenSpec hookStack)).subroutine_ok
    (strlen_mainStrlenSpec_padRO_ok hookStack hc haddr)

/-- Unpadded `M24.CalleesRO.strlenSpecRO` for strings whose NUL byte ends on an 8-byte boundary. -/
theorem strlen_strlenSpecRO_alignedEnd_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasCode entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry (withStrlenAlignedEnd (strlenSpecRO hookStack)) :=
  (sim_alignedEnd_of_padRO (strlenSpecRO hookStack)).subroutine_ok
    (strlen_strlenSpecRO_padRO_ok hookStack hc haddr)

/-! ## 4. `withVmPreserved` (`VmPreserved`) & `muslMemPlacedLib` Block-2 Bridges -/

private theorem lift_withVmPreserved_strlen {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (hpure : subroutine_ok (pureWordsProg entry muslStrlenWords) entry spec)
    (hc : prog.hasWords entry muslStrlenWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (hpre_mem : ∀ x (s : State) (m : Memory), spec.pre x (s.setMem m) = spec.pre x s)
    (hpost_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  have hlift := subroutine_ok_lift_pureWords_process hpure
    (pureWordsProg_noSvcMsr_strlen entry) hc h_no_ext
    (h_panic := hpan) (h_exit := hex) (h_oom := hoom)
    (h_pre_mem := hpre_mem) (h_post_mem := hpost_mem)
  refine subroutine_ok_map hlift
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
    (fun x R' s0 sf _ hp => by rw [hpan] at hp; exact not_satisfies_false_sepConj hp)
    (fun x code R' s0 sf _ he => by rw [hex] at he; exact not_satisfies_false_sepConj he)
    (fun x _ _ R' s0 sf _ ho => by rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [withVmPreserved] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨vmPreserved_of_processFieldsPreserved hpost.1, hpost.2⟩

/-- Headline budget-consumer bridge (`M24/CalleesRO.lean:587`): exact `libc.a` `strlen` bytes
    satisfy `withVmPreserved (withStrlenPadRO (strlenSpecRO hookStack))` (definitionally equal to
    `withStrlenPadRO (withVmPreserved (strlenSpecRO hookStack))`) on any hook-free program. -/
theorem strlen_strlenSpecRO_padRO_withVmPreserved_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasWords entry muslStrlenWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry (withVmPreserved (withStrlenPadRO (strlenSpecRO hookStack))) :=
  lift_withVmPreserved_strlen
    (strlen_strlenSpecRO_padRO_ok hookStack (pureWordsProg_hasWords_strlen entry) haddr)
    hc h_no_ext
    (hpre_mem := fun ⟨_, _⟩ _ _ => rfl)
    (hpost_mem := fun ⟨_, _⟩ _ _ _ _ => rfl)

/-- Budget-consumer bridge for `CliExt.strlenSpec`: exact `libc.a` `strlen` bytes satisfy
    `withVmPreserved (withStrlenPadRO CliExt.strlenSpec)` on any hook-free program. -/
theorem strlen_cliExtStrlenSpec_padRO_withVmPreserved_ok {prog : Program} {entry : BitVec 64}
    (hc : prog.hasWords entry muslStrlenWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withVmPreserved (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  lift_withVmPreserved_strlen
    (strlen_cliExtStrlenSpec_padRO_ok (pureWordsProg_hasWords_strlen entry) haddr)
    hc h_no_ext
    (hpre_mem := fun ⟨_, _⟩ _ _ => rfl)
    (hpost_mem := fun ⟨_, _⟩ _ _ _ _ => rfl)

/-- Region-local budget-consumer bridge for `cliStrlenPaddedSpec hookStack` (`↦ₛ` trailing pad in
    `pre` and `post`) on any hook-free program (`∀ pc, prog.externAt? pc = none`). -/
theorem strlen_cliStrlenPaddedSpec_withVmPreserved_ok {prog : Program} {entry : BitVec 64}
    (hookStack : Nat := extHookStack)
    (hc : prog.hasWords entry muslStrlenWords)
    (h_no_ext : ∀ pc, prog.externAt? pc = none)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok prog entry (withVmPreserved (cliStrlenPaddedSpec hookStack)) :=
  lift_withVmPreserved_strlen
    (strlen_cliStrlenPaddedSpec_ok hookStack (pureWordsProg_hasWords_strlen entry) haddr)
    hc h_no_ext
    (hpre_mem := fun ⟨_, _, _⟩ _ _ => rfl)
    (hpost_mem := fun ⟨_, _, _⟩ _ _ _ _ => rfl)

/-- Placement-generic `VerifiedLibraries.Musl.muslMemPlacedLib` block-`2` bridge (`MemOps.lean:431`
    `muslStrlenRO_block_ok`): `muslMemPlacedLib`'s `"strlen"` satisfies
    `muslMemPlacedLib.withCodeLoaded muslMemMpl (withStrlenPadRO (strlenSpecRO hookStack))`. -/
theorem muslMemPlacedLib_strlen_strlenSpecRO_padRO_ok [MuslMemPlacement]
    (hookStack : Nat := extHookStack) :
    subroutine_ok (muslMemPlacedLib.blockProgram muslMemMpl 2)
      (muslMemPlacedLib.fnAddr muslMemMpl "strlen")
      (muslMemPlacedLib.withCodeLoaded muslMemMpl (withStrlenPadRO (strlenSpecRO hookStack))) :=
  ((stdStrlenRO_simulates_strlenSpecRO_padRO hookStack).withCodeLoaded
    muslMemPlacedLib muslMemMpl).subroutine_ok muslStrlenRO_block_ok

end LibsignalBinary.Proofs.HookDischarge.Libc.Strlen
