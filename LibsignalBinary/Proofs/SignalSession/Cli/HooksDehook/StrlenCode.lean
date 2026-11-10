/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.Strlen
public import LibsignalBinary.Heap.Iface
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Proofs.HookDischarge.Libc.Strlen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliRun -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import

/-!
# Region-Local `strlen` Code Verification & Master Spec (`HooksDehook.StrlenCode`)

Card **L2-a1** (`strlen` de-hook code & master-spec layer, mirroring `HooksDehook.MemsetCode`,
`HooksDehook.MemcpyCode`, and `HooksDehook.BcmpCode` with the `a1` template fixes):

1. **Permission-free master state preservation (`StrlenStatePreserved`) AND full-permission
   process spec (`processStrlenSpec`):**
   - `abbrev StrlenStatePreserved := MemsetStatePreserved` (the 7 memory-permission-independent
     process/VM fields `fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`, `physMemAvail`),
     omitting `mem.perm` and `sf.mem = s0.mem` in `masterStrlenSpec.post` / `masterStrlenROSpec.post`
     so card `b` (`StrlenGhost`) can prove `SpecStripSInvariant keep masterStrlenSpec` by
     `cases s; rfl`.
   - Alongside `masterStrlenSpec`, this module exports full-permission `processStrlenSpec`
     (identical `pre`, with full `ProcessFieldsPreserved s0 sf`
     `= StdStatePreserved s0 sf` including pointwise `mem.perm` in `post`) plus its region-local
     `subroutine_ok` theorems (`subroutine_ok_processStrlen_of_hasWords` + `K` +
     `pureWordsProg`) and `vmPreserved_of_processFieldsPreserved`, so `StrlenGhost` can establish
     `VmPreserved` for the ghost hook (`activeRealRun_stdStatePreserved`) and lift to all
     `withVmPreserved` placed budget consumers.
2. **Zero-stack SWAR-padded master specs (`masterStrlenSpec`, `masterStrlenROSpec`) and
   `K`-narrowing (`strlenSpecK := memcpySpecK`):**
   - `masterStrlenSpec` requires zero stack bytes (`no stackAt`), NUL-free `s` (`0#8 ∉ s`), and the
     8-byte SWAR word-completion bound `StrlenSwarPadBound p s pad` (`G-STRLEN-PAD`), with
     `strlenSrc strRo padRo p s pad` (`bytesAt strRo p (s ++ [0#8]) ∗ bytesAt padRo (p + (s.length + 1)) pad`)
     in `pre` and `post`, `sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ StrlenStatePreserved s0 sf`
     in `post`, and `onPanic = onExit = onOom = ⌜False⌝`.
     Keeping `(strRo, padRo : Bool)` explicit (mirroring `MemcpyCode.masterMemcpySpec`'s `ro : Bool`)
     preserves mutable `cStrAt p s` (`strRo = false`) across `HookOk` without putting
     `sf.mem = s0.mem` in `post`.
   - `masterStrlenROSpec` is the pure read-only 3-tuple `(p, s, pad)` specialization
     (`strRo = true`, `padRo = true`, spatial `(p ↦ᵣ (s ++ [0#8] ++ pad))`).
3. **Single contiguous 1-block `P_sub` (`pureWordsProg base muslStrlenWords`) & region-local
   `subroutine_ok`:**
   `muslStrlenWords` is a single contiguous `22`-word (`88`-byte) leaf block with concrete
   `pureWordsProg_strlen_hasWords`, `pureWordsProg_strlen_processStrlen_ok`, and
   `pureWordsProg_strlen_masterStrlen_ok` (+ `K`, + `RO`). There is no trusted placed-lib entry
   for libc strings (`GK6c`); block-word identity comes from the untrusted `StrlenBlock` (`a2`)
   card + `K3(b)` after the `C2` cutover.
4. **`W`-free fallback `strlenHook` soundness (`hookStrlen_processStrlen_ok`,
   `hookStrlen_masterStrlen_ok`, `hookStrlen_masterStrlenVm_ok`):**
   `CryptoVerification.SignalSession.strlenHook` (`CliRun.lean:440`) has no `W : CliHooks`
   parameter and satisfies `processStrlenSpec`, `masterStrlenSpec`, `withVmPreserved masterStrlenSpec`,
   and their `RO` and `strlenSpecK` variants unconditionally.
5. **`HookOk` consequence lifts (bare, `withVmPreserved`, `strlenSpecK`, and `.inImage`):**
   - **Lifted here (all SWAR-padded consumer contracts — bare, `withVmPreserved`, `strlenSpecK`,
     and `.inImage`):**
     - `cliStrlenPaddedSpec hookStack` (`strRo = false`, `padRo = false`);
     - `strlenPaddedSpecRO hookStack` (`strRo = true`, `padRo = true`);
     - `withStrlenPadRO`, `withStrlenRoDataPad`, and `withStrlenAlignedEnd` applied to
       `M24.CalleesRO.strlenSpecRO hookStack` (`strRo = true`, `padRo = true`);
     - `withStrlenPadRO`, `withStrlenRoDataPad`, and `withStrlenAlignedEnd` applied to
       `MainHops.strlenSpec hookStack` (`= cliStrlenSpec hookStack`) and `CliExt.strlenSpec`
       (`strRo = false`, `padRo = true`).
   - **NOT lifted (bare unpadded `M24.CalleesRO.strlenSpecRO`, `MainHops.strlenSpec`,
     `CliExt.strlenSpec`):**
     Real `musl` SWAR `strlen` loads the aligned 8-byte word containing the terminating NUL byte,
     reading up to `7` bytes past `p + s.length`, and the ghost `linkedCallHook` returns
     `Status.Exception` whenever the master spec's SWAR-padded precondition fails. Callers of the
     unpadded specs (`M24/CalleesRO`, `Main/Proofs/*`, `CliExternsWitness`) must re-anchor to one
     of the padded contracts above (`EX-STRLEN-PAD`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open ProofLib.StdStartup (StdStatePreserved muslStrlenWords stdStrlenROSpec muslStrlen_ro_ok)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (strlenHook)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved FdsHiFrame)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (bytesAt cStrAt satisfies_bytesAt_to_ro)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (
  StrlenSwarPadBound cliStrlenSpec cliStrlenPaddedSpec strlenPaddedSpecRO
  withStrlenPadRO withStrlenRoDataPad withStrlenAlignedEnd
  sim_roDataPad_of_padRO sim_alignedEnd_of_padRO
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  MemsetStatePreserved pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  memcpySpecK hookOk_map_frame_pureAbort hookOk_memcpySpecK_of_plain
  hookOk_memcpySpecK_map_frame_pureAbort
  memcpySpecK_keepsFs memcpySpecK_withVmPreserved memcpySpecK_withOomPoolPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (cStrAtRO strlenSpecRO)

/-! ## 1. Master & Process `strlen` Specifications & Wrappers -/

/-- Reuse `MemsetStatePreserved` (`fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`,
    `physMemAvail`) via `abbrev` so `StrlenStatePreserved` is `rfl`-identical to
    `MemsetStatePreserved`, `MemcpyStatePreserved`, and `BcmpStatePreserved`. -/
abbrev StrlenStatePreserved (s0 sf : State) : Prop :=
  MemsetStatePreserved s0 sf

/-- `ProofLib.StdStartup.StdStatePreserved` and `ProofLib.ProcessFieldsPreserved` are definitionally
    (`rfl`) identical (the 7 `MemsetStatePreserved` fields plus pointwise `mem.perm`). -/
theorem stdStatePreserved_eq_processFieldsPreserved (s0 sf : State) :
    StdStatePreserved s0 sf = ProcessFieldsPreserved s0 sf := rfl

theorem StrlenStatePreserved.refl (s : State) : StrlenStatePreserved s s :=
  MemsetStatePreserved.refl s

theorem StrlenStatePreserved.of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : StrlenStatePreserved s0 sf :=
  MemsetStatePreserved.of_stdStatePreserved h

theorem StrlenStatePreserved.of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : StrlenStatePreserved s0 sf :=
  MemsetStatePreserved.of_stdStatePreserved h

theorem StrlenStatePreserved.toAllocCallPreserved {s0 sf : State}
    (h : StrlenStatePreserved s0 sf) (horc : sf.oracle = s0.oracle)
    (hsym : sf.symtab = s0.symtab) : AllocCallPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2.1, horc, hsym⟩

/-- `ProcessFieldsPreserved` (`= StdStatePreserved`, carrying pointwise `mem.perm` preservation)
    implies `VmPreserved`. -/
theorem vmPreserved_of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2,
    FdsHiFrame.of_fs_eq h.1⟩

/-- Spatial slice footprint for `masterStrlenSpec`: NUL-terminated string `s ++ [0#8]` at `p`
    with permission `strRo` (`false` = `↦ₛ`, `true` = `↦ᵣ`) and SWAR trailing bytes `pad` at
    `p + (s.length + 1)` with permission `padRo`. -/
@[expose] def strlenSrc (strRo padRo : Bool) (p : BitVec 64) (s pad : List (BitVec 8)) :
    SepProp :=
  bytesAt strRo p (s ++ [0#8]) ∗ bytesAt padRo (p + BitVec.ofNat 64 (s.length + 1)) pad

/-- Frameless zero-stack SWAR-padded master separation-logic contract for `strlen(p = x0)`:
    requires zero stack bytes (`no stackAt`), NUL-free `s` (`0#8 ∉ s`), 8-byte SWAR trailing-pad
    bound `StrlenSwarPadBound p s pad`, and `strlenSrc strRo padRo p s pad`; never panics, exits,
    or OOMs (`onPanic = onExit = onOom = ⌜False⌝`); sets `x0 = s.length`, preserves
    `StrlenStatePreserved s0 sf`, and preserves `strlenSrc strRo padRo p s pad`. -/
@[expose] def masterStrlenSpec :
    Spec (Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (strRo, padRo, p, s, pad) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ 0#8 ∉ s ∧ StrlenSwarPadBound p s pad⌝ ∗
      strlenSrc strRo padRo p s pad
  post := fun (strRo, padRo, p, s, pad) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ StrlenStatePreserved s0 sf⌝ ∗
      strlenSrc strRo padRo p s pad
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Full-permission process companion to `masterStrlenSpec` (`F1`): identical `pre`, carrying full
    `ProcessFieldsPreserved s0 sf` (`= StdStatePreserved s0 sf`, including pointwise `mem.perm`) in
    `post` so `StrlenGhost` can derive `VmPreserved` (`vmPreserved_of_processFieldsPreserved`). -/
@[expose] def processStrlenSpec :
    Spec (Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := masterStrlenSpec.pre
  post := fun (strRo, padRo, p, s, pad) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ ProcessFieldsPreserved s0 sf⌝ ∗
      strlenSrc strRo padRo p s pad
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Pure read-only 3-tuple `(p, s, pad)` specialization (`strRo = true`, `padRo = true`) of
    `masterStrlenSpec`: requires zero stack bytes, owns `(p ↦ᵣ (s ++ [0#8] ++ pad))`, never
    panics/exits/OOMs, and establishes `x0 = s.length` and `StrlenStatePreserved s0 sf`. -/
@[expose] def masterStrlenROSpec :
    Spec (BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (p, s, pad) s0 =>
    ⌜s0.readReg64 .x0 = p ∧ 0#8 ∉ s ∧ StrlenSwarPadBound p s pad⌝ ∗
      (p ↦ᵣ (s ++ [0#8] ++ pad))
  post := fun (p, s, pad) s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length ∧ StrlenStatePreserved s0 sf⌝ ∗
      (p ↦ᵣ (s ++ [0#8] ++ pad))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

theorem processStrlenSpec_pre_eq : processStrlenSpec.pre = masterStrlenSpec.pre := rfl

/-- `K`-route precondition narrowing (`abbrev` of `MemcpyCode.memcpySpecK`, `rfl`-equal to
    `MemsetCode.memsetSpecK`): conjoins `⌜keep (s.readReg64 .lr) = false⌝` to `spec.pre`. -/
abbrev strlenSpecK (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) : Spec α :=
  memcpySpecK keep spec

private theorem cStrAtRO_sepConj_pad (p : BitVec 64) (s pad : List (BitVec 8)) :
    cStrAtRO p s ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) =
      (p ↦ᵣ (s ++ [0#8] ++ pad)) := by
  dsimp only [cStrAtRO]
  have hlen : (s ++ [0#8]).length = s.length + 1 := by simp
  rw [pointsToBytesRO_append p (s ++ [0#8]) pad, hlen]

theorem strlenSrc_false_false (p : BitVec 64) (s pad : List (BitVec 8)) :
    strlenSrc false false p s pad =
      cStrAt p s ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ₛ pad) := rfl

theorem strlenSrc_false_true (p : BitVec 64) (s pad : List (BitVec 8)) :
    strlenSrc false true p s pad =
      cStrAt p s ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad) := rfl

theorem strlenSrc_true_true (p : BitVec 64) (s pad : List (BitVec 8)) :
    strlenSrc true true p s pad = (p ↦ᵣ (s ++ [0#8] ++ pad)) :=
  cStrAtRO_sepConj_pad p s pad

private theorem satisfies_strlenSrc_to_ro {m : Memory} {strRo padRo : Bool} {p : BitVec 64}
    {s pad : List (BitVec 8)} {R : SepProp}
    (h : m ⊨ strlenSrc strRo padRo p s pad ∗ R) :
    m ⊨ (p ↦ᵣ (s ++ [0#8] ++ pad)) ∗ R := by
  dsimp only [strlenSrc] at h
  rw [sepConj_assoc] at h
  have h1 := satisfies_bytesAt_to_ro h
  rw [sepConj_left_comm] at h1
  have h2 := satisfies_bytesAt_to_ro h1
  rw [sepConj_left_comm, ← sepConj_assoc] at h2
  change m ⊨ (cStrAtRO p s ∗ ((p + BitVec.ofNat 64 (s.length + 1)) ↦ᵣ pad)) ∗ R at h2
  rwa [cStrAtRO_sepConj_pad p s pad] at h2

/-! ## 2. Placement-Generic `pureWordsProg` `hasWords` & Region-Local `subroutine_ok` -/

/-- `muslStrlenWords` has `22` 32-bit instruction words (`88` bytes). -/
theorem muslStrlenWords_length : muslStrlenWords.length = 22 := rfl

/-- `pureWordsProg base muslStrlenWords` holds `muslStrlenWords` (`22` words) at `base`
    (concrete `hasWords` witness over the single contiguous `88`-byte hull). -/
theorem pureWordsProg_strlen_hasWords (base : BitVec 64) :
    (pureWordsProg base muslStrlenWords).hasWords base muslStrlenWords :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range muslStrlenWords.length).all fun i =>
      (pureWordsProg 0#64 muslStrlenWords).readWordOff (4 * i) == muslStrlenWords[i]?) = true
    decide +kernel)

private theorem pureWordsProg_noSvcMsr_strlen (base : BitVec 64) :
    (pureWordsProg base muslStrlenWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 muslStrlenWords) rfl (by prove_all_instrs)

private def masterStrlenCoreSpec :
    Spec (Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := masterStrlenSpec.pre
  post := fun (strRo, padRo, p, s, pad) _s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 s.length⌝ ∗
      strlenSrc strRo padRo p s pad
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem stdStrlenRO_simulates_masterStrlenCore :
    SpecSimulates stdStrlenROSpec masterStrlenCoreSpec := by
  refine SpecSimulates.of_map ?_
  rintro ⟨strRo, padRo, p, s, pad⟩ R s0 hpre
  dsimp only [masterStrlenCoreSpec, masterStrlenSpec, StrlenSwarPadBound] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hno0, hpad, hnw⟩, hmem⟩
  refine ⟨(p, s, pad), R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [stdStrlenROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hno0, hpad, hnw⟩, satisfies_strlenSrc_to_ro hmem⟩
  · dsimp only [stdStrlenROSpec] at hpost
    dsimp only [masterStrlenCoreSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0_f, hmem_eq, _⟩, _⟩
    rw [hmem_eq]
    exact ⟨hx0_f, hmem⟩

/-- Forward simulation `processStrlenSpec` → `masterStrlenSpec` (weakening
    `ProcessFieldsPreserved` to 7-field `StrlenStatePreserved`). -/
theorem processStrlen_simulates_masterStrlen :
    SpecSimulates processStrlenSpec masterStrlenSpec := by
  refine SpecSimulates.of_map ?_
  rintro ⟨strRo, padRo, p, s, pad⟩ R s0 hpre
  refine ⟨(strRo, padRo, p, s, pad), R, hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [processStrlenSpec, masterStrlenSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1.1, StrlenStatePreserved.of_processFieldsPreserved hpost.1.2⟩, hpost.2⟩

/-- Forward simulation `processStrlenSpec` → `withVmPreserved masterStrlenSpec` (extracting both
    `VmPreserved` and `StrlenStatePreserved` from `ProcessFieldsPreserved`). -/
theorem processStrlen_simulates_masterStrlenVm :
    SpecSimulates processStrlenSpec (withVmPreserved masterStrlenSpec) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨strRo, padRo, p, s, pad⟩ R s0 hpre
  refine ⟨(strRo, padRo, p, s, pad), R, hpre, fun sf _ _ hpost => ?_⟩
  dsimp only [processStrlenSpec, withVmPreserved, masterStrlenSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨vmPreserved_of_processFieldsPreserved hpost.1.2,
    ⟨hpost.1.1, StrlenStatePreserved.of_processFieldsPreserved hpost.1.2⟩, hpost.2⟩

/-- Pure-RO forward simulation `masterStrlenSpec` (`strRo = true`, `padRo = true`) →
    `masterStrlenROSpec`. -/
theorem masterStrlen_simulates_masterStrlenRO :
    SpecSimulates masterStrlenSpec masterStrlenROSpec := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, s, pad⟩ R s0 hpre
  refine ⟨(true, true, p, s, pad), R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [masterStrlenROSpec, masterStrlenSpec] at hpre ⊢
    rwa [strlenSrc_true_true p s pad]
  · dsimp only [masterStrlenSpec, masterStrlenROSpec] at hpost ⊢
    rwa [strlenSrc_true_true p s pad] at hpost

/-- Region-local `subroutine_ok` for full-permission `processStrlenSpec` (`F1`, carrying
    `ProcessFieldsPreserved` = `StdStatePreserved`) on any hook-free `P_sub` holding
    `muslStrlenWords` (`22` words = `88` bytes) at `entry` with `entry.toNat + 88 ≤ 2 ^ 64`. -/
theorem subroutine_ok_processStrlen_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok P_sub entry processStrlenSpec := by
  have hpure := stdStrlenRO_simulates_masterStrlenCore.subroutine_ok
    (muslStrlen_ro_ok _ entry (pureWordsProg_strlen_hasWords entry) haddr)
  have hlift := subroutine_ok_lift_pureWords_process hpure
    (pureWordsProg_noSvcMsr_strlen entry) hwords hsub_no
    (h_pre_mem := fun ⟨_, _, _, _, _⟩ _ _ => rfl)
    (h_post_mem := fun ⟨_, _, _, _, _⟩ _ _ _ _ => rfl)
  refine subroutine_ok_map hlift (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
  rcases x with ⟨strRo, padRo, p, s, pad⟩
  dsimp only [masterStrlenCoreSpec, processStrlenSpec] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩

/-- Region-local `subroutine_ok` for `strlenSpecK keep processStrlenSpec`. -/
theorem subroutine_ok_processStrlenK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok P_sub entry (strlenSpecK keep processStrlenSpec) := by
  refine subroutine_ok_mono (subroutine_ok_processStrlen_of_hasWords hsub_no hwords haddr)
    (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [strlenSpecK, memcpySpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Region-local `subroutine_ok` for `masterStrlenSpec` on any hook-free `P_sub` holding
    `muslStrlenWords` (`22` words = `88` bytes) at `entry` with `entry.toNat + 88 ≤ 2 ^ 64`. -/
theorem subroutine_ok_masterStrlen_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok P_sub entry masterStrlenSpec :=
  processStrlen_simulates_masterStrlen.subroutine_ok
    (subroutine_ok_processStrlen_of_hasWords hsub_no hwords haddr)

/-- Region-local `subroutine_ok` for `withVmPreserved masterStrlenSpec` on any hook-free `P_sub`
    holding `muslStrlenWords`. -/
theorem subroutine_ok_masterStrlenVm_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok P_sub entry (withVmPreserved masterStrlenSpec) :=
  processStrlen_simulates_masterStrlenVm.subroutine_ok
    (subroutine_ok_processStrlen_of_hasWords hsub_no hwords haddr)

/-- Region-local `subroutine_ok` for `strlenSpecK keep masterStrlenSpec` on any hook-free `P_sub`
    holding `muslStrlenWords`. -/
theorem subroutine_ok_masterStrlenK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok P_sub entry (strlenSpecK keep masterStrlenSpec) := by
  refine subroutine_ok_mono (subroutine_ok_masterStrlen_of_hasWords hsub_no hwords haddr)
    (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [strlenSpecK, memcpySpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Region-local `subroutine_ok` for `masterStrlenROSpec` on any hook-free `P_sub` holding
    `muslStrlenWords`. -/
theorem subroutine_ok_masterStrlenRO_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok P_sub entry masterStrlenROSpec :=
  masterStrlen_simulates_masterStrlenRO.subroutine_ok
    (subroutine_ok_masterStrlen_of_hasWords hsub_no hwords haddr)

/-- Region-local `subroutine_ok` for `strlenSpecK keep masterStrlenROSpec` on any hook-free
    `P_sub` holding `muslStrlenWords`. -/
theorem subroutine_ok_masterStrlenROK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry muslStrlenWords)
    (haddr : entry.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok P_sub entry (strlenSpecK keep masterStrlenROSpec) := by
  refine subroutine_ok_mono (subroutine_ok_masterStrlenRO_of_hasWords hsub_no hwords haddr)
    (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [strlenSpecK, memcpySpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Concrete `pureWordsProg base muslStrlenWords` instance satisfying `processStrlenSpec`. -/
theorem pureWordsProg_strlen_processStrlen_ok (base : BitVec 64)
    (haddr : base.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok (pureWordsProg base muslStrlenWords) base processStrlenSpec :=
  subroutine_ok_processStrlen_of_hasWords
    (pureWordsProg_externAt_none base muslStrlenWords)
    (pureWordsProg_strlen_hasWords base) haddr

/-- Concrete `pureWordsProg base muslStrlenWords` instance satisfying
    `strlenSpecK keep processStrlenSpec`. -/
theorem pureWordsProg_strlen_processStrlenK_ok (keep : BitVec 64 → Bool) (base : BitVec 64)
    (haddr : base.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok (pureWordsProg base muslStrlenWords) base
      (strlenSpecK keep processStrlenSpec) :=
  subroutine_ok_processStrlenK_of_hasWords keep
    (pureWordsProg_externAt_none base muslStrlenWords)
    (pureWordsProg_strlen_hasWords base) haddr

/-- Concrete `pureWordsProg base muslStrlenWords` instance satisfying `masterStrlenSpec`. -/
theorem pureWordsProg_strlen_masterStrlen_ok (base : BitVec 64)
    (haddr : base.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok (pureWordsProg base muslStrlenWords) base masterStrlenSpec :=
  subroutine_ok_masterStrlen_of_hasWords
    (pureWordsProg_externAt_none base muslStrlenWords)
    (pureWordsProg_strlen_hasWords base) haddr

/-- Concrete `pureWordsProg base muslStrlenWords` instance satisfying
    `strlenSpecK keep masterStrlenSpec`. -/
theorem pureWordsProg_strlen_masterStrlenK_ok (keep : BitVec 64 → Bool) (base : BitVec 64)
    (haddr : base.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok (pureWordsProg base muslStrlenWords) base
      (strlenSpecK keep masterStrlenSpec) :=
  subroutine_ok_masterStrlenK_of_hasWords keep
    (pureWordsProg_externAt_none base muslStrlenWords)
    (pureWordsProg_strlen_hasWords base) haddr

/-- Concrete `pureWordsProg base muslStrlenWords` instance satisfying `masterStrlenROSpec`. -/
theorem pureWordsProg_strlen_masterStrlenRO_ok (base : BitVec 64)
    (haddr : base.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok (pureWordsProg base muslStrlenWords) base masterStrlenROSpec :=
  subroutine_ok_masterStrlenRO_of_hasWords
    (pureWordsProg_externAt_none base muslStrlenWords)
    (pureWordsProg_strlen_hasWords base) haddr

/-- Concrete `pureWordsProg base muslStrlenWords` instance satisfying
    `strlenSpecK keep masterStrlenROSpec`. -/
theorem pureWordsProg_strlen_masterStrlenROK_ok (keep : BitVec 64 → Bool) (base : BitVec 64)
    (haddr : base.toNat + 88 ≤ 2 ^ 64) :
    subroutine_ok (pureWordsProg base muslStrlenWords) base
      (strlenSpecK keep masterStrlenROSpec) :=
  subroutine_ok_masterStrlenROK_of_hasWords keep
    (pureWordsProg_externAt_none base muslStrlenWords)
    (pureWordsProg_strlen_hasWords base) haddr

/-! ## 3. `W`-Free Fallback `strlenHook` Soundness -/

private theorem getD_append_right_zero (s : List (BitVec 8)) :
    (s ++ [0#8]).getD s.length 0#8 = 0#8 := by
  simp [List.getD]

private theorem getD_append_left {s : List (BitVec 8)} {m : Nat} (hm : m < s.length) :
    (s ++ [0#8]).getD m 0#8 = s[m] := by
  simp [List.getD, List.getElem?_append_left hm, hm]

/-- `W`-free fallback soundness (`F1` + `F3`): `strlenHook` (`CliRun.lean:440`, no `W : CliHooks`
    parameter) satisfies full-permission `processStrlenSpec` unconditionally (zero-stack
    precondition, `s0.mem` and all 8 `ProcessFieldsPreserved` fields unchanged, and `Nat.find`
    resolves to `s.length`). -/
theorem hookStrlen_processStrlen_ok : HookOk strlenHook processStrlenSpec := by
  rintro ⟨strRo, padRo, p, s, pad⟩ R s0 hrun hpre _hsp
  dsimp only [processStrlenSpec, masterStrlenSpec, StrlenSwarPadBound] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hno0, _hpad, hnw⟩, hmem⟩
  have hlen : (s ++ [0#8]).length ≤ 2 ^ 64 := by simp; omega
  have hmem_str : s0.mem ⊨ (p ↦ᵣ (s ++ [0#8])) ∗
      (bytesAt padRo (p + BitVec.ofNat 64 (s.length + 1)) pad ∗ R) := by
    dsimp only [strlenSrc] at hmem
    rw [sepConj_assoc] at hmem
    exact satisfies_bytesAt_to_ro hmem
  have hread : s0.mem.readBytes p (s ++ [0#8]).length = s ++ [0#8] :=
    (IsBlockRO.pointsToBytesRO p (s ++ [0#8]) hlen).read hmem_str
  have hcan0 : s0.mem.canRead p (s ++ [0#8]).length = true :=
    (IsBlockRO.pointsToBytesRO p (s ++ [0#8]) hlen).canRead hlen hmem_str
  have hcan : s0.mem.canRead p (s.length + 1) = true := by simpa using hcan0
  have hnul : s0.mem.read8 (p + BitVec.ofNat 64 s.length) = 0#8 := by
    rw [Memory.read8_of_readBytes s0.mem p (s ++ [0#8]) hread s.length (by simp)]
    exact getD_append_right_zero s
  have hex : ∃ n, s0.mem.canRead p (n + 1) = true ∧
      s0.mem.read8 (p + BitVec.ofNat 64 n) = 0#8 :=
    ⟨s.length, hcan, hnul⟩
  have hfind : Nat.find hex = s.length := by
    refine (Nat.find_eq_iff hex).mpr ⟨⟨hcan, hnul⟩, fun m hm ⟨_, hm0⟩ => ?_⟩
    rw [Memory.read8_of_readBytes s0.mem p (s ++ [0#8]) hread m (by simp; omega),
      getD_append_left hm] at hm0
    exact hno0 (hm0 ▸ List.getElem_mem hm)
  have heq : strlenHook s0 =
      retHook (fun st => st.writeReg64 .x0 (BitVec.ofNat 64 s.length)) s0 := by
    unfold strlenHook
    dsimp only
    simp only [hx0, hex, ↓reduceDIte, hfind]
  rw [heq]
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨?_, ?_, ?_⟩⟩
  · exact ⟨rfl, rfl, hrun⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only [processStrlenSpec, retHook, State.setPC, State.writeReg64, State.readReg64]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, hmem⟩

/-- `strlenHook` satisfies `strlenSpecK keep processStrlenSpec` for any `keep`. -/
theorem hookStrlen_processStrlenK_ok (keep : BitVec 64 → Bool) :
    HookOk strlenHook (strlenSpecK keep processStrlenSpec) :=
  hookOk_memcpySpecK_of_plain keep hookStrlen_processStrlen_ok

/-! ## 4. Generic `HookOk` Consequence Lifts from `masterStrlenSpec`, `processStrlenSpec`, & `withVmPreserved` -/

/-- Transport `HookOk` along `SpecSimulates`: any hook `f` satisfying `spec₁` also satisfies any
    `spec₂` forward-simulated by `spec₁`. -/
theorem SpecSimulates.hookOk {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) {f : State → State} (hh : HookOk f spec₁) :
    HookOk f spec₂ := by
  intro y R s0 hrun hpre hsp
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  obtain ⟨hkf, hsym, hout⟩ := hh x R₁ s0 hrun hpre₁ hsp
  exact ⟨hkf, hsym, hm (f s0) hout⟩

/-- Lift `SpecSimulates` across `strlenSpecK keep`. -/
theorem SpecSimulates.strlenSpecK (keep : BitVec 64 → Bool) {α β : Type}
    {spec₁ : Spec α} {spec₂ : Spec β} (hsim : SpecSimulates spec₁ spec₂) :
    SpecSimulates (StrlenCode.strlenSpecK keep spec₁) (StrlenCode.strlenSpecK keep spec₂) := by
  intro y R s0 hpre
  dsimp only [StrlenCode.strlenSpecK, memcpySpecK] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hlr, hpre₂⟩ := hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre₂
  refine ⟨x, R₁, ?_, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hlr, hpre₁⟩

/-- Lift `SpecSimulates` across `withVmPreserved` for any non-aborting `spec₁`. -/
theorem SpecSimulates.liftWithVmPreserved {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂)
    (hpan : spec₁.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec₁.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec₁.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates (withVmPreserved spec₁) (withVmPreserved spec₂) := by
  intro y R s0 hpre
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcc, hpost₁⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · dsimp only [withVmPreserved] at hpost₁
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost₁
    rcases hm sf (Or.inl ⟨hret, hcc, hpost₁.2⟩) with ⟨hret₂, hcc₂, hpost₂⟩ | habort
    · refine Or.inl ⟨hret₂, hcc₂, ?_⟩
      dsimp only [withVmPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hpost₁.1, hpost₂⟩
    · exact Or.inr habort
  · dsimp only [withVmPreserved] at hp
    rw [hpan] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [withVmPreserved] at he
    rw [hex] at he; exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [withVmPreserved] at ho
    rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Any `HookOk f spec` weakens to `HookOk f (strlenSpecK keep spec)` (reusing
    `MemcpyCode.hookOk_memcpySpecK_of_plain`). -/
theorem hookOk_strlenSpecK_of_plain (keep : BitVec 64 → Bool) {α : Type} {f : State → State}
    {spec : Spec α} (hh : HookOk f spec) :
    HookOk f (strlenSpecK keep spec) :=
  hookOk_memcpySpecK_of_plain keep hh

/-- Lift a ghost-reindexing frame/consequence derivation across `strlenSpecK keep` (reusing
    `MemcpyCode.hookOk_memcpySpecK_map_frame_pureAbort`). -/
theorem hookOk_strlenSpecK_map_frame_pureAbort (keep : BitVec 64 → Bool)
    {α β : Type} {f : State → State} {base : Spec α} {target : Spec β}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk f (strlenSpecK keep base))
    (hpre : ∀ y s0, target.pre y s0 ⊢ base.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf, sf = f s0 → sf.symtab = s0.symtab →
      base.post (g y) s0 sf ∗ F y s0 ⊢ target.post y s0 sf)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (strlenSpecK keep target) :=
  hookOk_memcpySpecK_map_frame_pureAbort keep g F hh hpre hpost hpan hex hoom

/-- Any `HookOk f spec` weakens to `HookOk f (spec.inImage img)` (dropping `⌜img.CodeLoaded s0.mem⌝`
    from `pre`). -/
theorem hookOk_inImage (img : Obj.Image) {α : Type} {f : State → State} {spec : Spec α}
    (hh : HookOk f spec) :
    HookOk f (spec.inImage img) := by
  intro x R s0 hrun hpre hsp
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hh x R s0 hrun hpre.2 hsp

/-- Any `HookOk f (strlenSpecK keep spec)` weakens to
    `HookOk f (strlenSpecK keep (spec.inImage img))`. -/
theorem hookOk_strlenSpecK_inImage (keep : BitVec 64 → Bool) (img : Obj.Image)
    {α : Type} {f : State → State} {spec : Spec α}
    (hh : HookOk f (strlenSpecK keep spec)) :
    HookOk f (strlenSpecK keep (spec.inImage img)) := by
  intro x R s0 hrun hpre hsp
  dsimp only [strlenSpecK, memcpySpecK, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hlr, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  refine hh x R s0 hrun ?_ hsp
  dsimp only [strlenSpecK, memcpySpecK]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hlr, hpre.2⟩

/-- Lift `HookOk f processStrlenSpec` to `HookOk f masterStrlenSpec`. -/
theorem hookOk_masterStrlen_of_processStrlen {f : State → State}
    (hh : HookOk f processStrlenSpec) :
    HookOk f masterStrlenSpec :=
  SpecSimulates.hookOk processStrlen_simulates_masterStrlen hh

/-- Lift `HookOk f processStrlenSpec` to `HookOk f (withVmPreserved masterStrlenSpec)`. -/
theorem hookOk_masterStrlenVm_of_processStrlen {f : State → State}
    (hh : HookOk f processStrlenSpec) :
    HookOk f (withVmPreserved masterStrlenSpec) :=
  SpecSimulates.hookOk processStrlen_simulates_masterStrlenVm hh

/-- Specialize `HookOk f masterStrlenSpec` to `HookOk f masterStrlenROSpec`. -/
theorem hookOk_masterStrlenRO_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) :
    HookOk f masterStrlenROSpec :=
  SpecSimulates.hookOk masterStrlen_simulates_masterStrlenRO hh

/-- Specialize `HookOk f (strlenSpecK keep masterStrlenSpec)` to
    `HookOk f (strlenSpecK keep masterStrlenROSpec)`. -/
theorem hookOk_masterStrlenROK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) :
    HookOk f (strlenSpecK keep masterStrlenROSpec) :=
  SpecSimulates.hookOk (SpecSimulates.strlenSpecK keep masterStrlen_simulates_masterStrlenRO) hh

/-- Specialize `HookOk f (withVmPreserved masterStrlenSpec)` to
    `HookOk f (withVmPreserved masterStrlenROSpec)`. -/
theorem hookOk_masterStrlenROVm_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) :
    HookOk f (withVmPreserved masterStrlenROSpec) :=
  SpecSimulates.hookOk (SpecSimulates.liftWithVmPreserved masterStrlen_simulates_masterStrlenRO) hh

/-- Specialize `HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec))` to
    `HookOk f (strlenSpecK keep (withVmPreserved masterStrlenROSpec))`. -/
theorem hookOk_masterStrlenROVmK_of_masterVm (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec))) :
    HookOk f (strlenSpecK keep (withVmPreserved masterStrlenROSpec)) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (SpecSimulates.liftWithVmPreserved masterStrlen_simulates_masterStrlenRO)) hh

theorem hookStrlen_masterStrlen_ok : HookOk strlenHook masterStrlenSpec :=
  hookOk_masterStrlen_of_processStrlen hookStrlen_processStrlen_ok

theorem hookStrlen_masterStrlenK_ok (keep : BitVec 64 → Bool) :
    HookOk strlenHook (strlenSpecK keep masterStrlenSpec) :=
  hookOk_memcpySpecK_of_plain keep hookStrlen_masterStrlen_ok

theorem hookStrlen_masterStrlenVm_ok : HookOk strlenHook (withVmPreserved masterStrlenSpec) :=
  hookOk_masterStrlenVm_of_processStrlen hookStrlen_processStrlen_ok

theorem hookStrlen_masterStrlenVmK_ok (keep : BitVec 64 → Bool) :
    HookOk strlenHook (strlenSpecK keep (withVmPreserved masterStrlenSpec)) :=
  hookOk_memcpySpecK_of_plain keep hookStrlen_masterStrlenVm_ok

theorem hookStrlen_masterStrlenRO_ok : HookOk strlenHook masterStrlenROSpec :=
  hookOk_masterStrlenRO_of_master hookStrlen_masterStrlen_ok

theorem hookStrlen_masterStrlenROK_ok (keep : BitVec 64 → Bool) :
    HookOk strlenHook (strlenSpecK keep masterStrlenROSpec) :=
  hookOk_masterStrlenROK_of_master keep (hookStrlen_masterStrlenK_ok keep)

theorem hookStrlen_masterStrlenROVm_ok : HookOk strlenHook (withVmPreserved masterStrlenROSpec) :=
  hookOk_masterStrlenROVm_of_masterVm hookStrlen_masterStrlenVm_ok

theorem hookStrlen_masterStrlenROVmK_ok (keep : BitVec 64 → Bool) :
    HookOk strlenHook (strlenSpecK keep (withVmPreserved masterStrlenROSpec)) :=
  hookOk_masterStrlenROVmK_of_masterVm keep (hookStrlen_masterStrlenVmK_ok keep)

/-! ### 4.1 Explicit-Pad Padded Consumer Contracts (`cliStrlenPaddedSpec`, `strlenPaddedSpecRO`) -/

/-- Forward simulation `masterStrlenSpec` (`strRo = false`, `padRo = false`) →
    `cliStrlenPaddedSpec hookStack` (framing `stackAt s0.sp hookStack`). -/
theorem masterStrlen_simulates_cliStrlenPadded (hookStack : Nat := extHookStack) :
    SpecSimulates masterStrlenSpec (cliStrlenPaddedSpec hookStack) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, s, pad⟩ R s0 hpre
  dsimp only [cliStrlenPaddedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hnz, hbound⟩, hmem⟩
  have hno0 : 0#8 ∉ s := fun h0 => hnz 0#8 h0 rfl
  refine ⟨(false, false, p, s, pad), stackAt s0.sp hookStack ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [masterStrlenSpec, strlenSrc_false_false]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hno0, hbound⟩, hmem⟩
  · dsimp only [masterStrlenSpec, strlenSrc_false_false] at hpost
    dsimp only [cliStrlenPaddedSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0_f, hst⟩, hmem_f⟩
    exact ⟨⟨hx0_f, hst.2.1, hst.1⟩, hmem_f⟩

/-- Lift `HookOk f masterStrlenSpec` to `HookOk f (cliStrlenPaddedSpec hookStack)`. -/
theorem hookOk_cliStrlenPadded_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) (hookStack : Nat := extHookStack) :
    HookOk f (cliStrlenPaddedSpec hookStack) :=
  SpecSimulates.hookOk (masterStrlen_simulates_cliStrlenPadded hookStack) hh

/-- Lift `HookOk f (strlenSpecK keep masterStrlenSpec)` to
    `HookOk f (strlenSpecK keep (cliStrlenPaddedSpec hookStack))`. -/
theorem hookOk_cliStrlenPaddedK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (cliStrlenPaddedSpec hookStack)) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep (masterStrlen_simulates_cliStrlenPadded hookStack)) hh

/-- Forward simulation `masterStrlenROSpec` → `strlenPaddedSpecRO hookStack` (framing
    `stackAt s0.sp hookStack`). -/
theorem masterStrlenRO_simulates_strlenPaddedRO (hookStack : Nat := extHookStack) :
    SpecSimulates masterStrlenROSpec (strlenPaddedSpecRO hookStack) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, s, pad⟩ R s0 hpre
  dsimp only [strlenPaddedSpecRO] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hnz, hbound⟩, hmem⟩
  have hno0 : 0#8 ∉ s := fun h0 => hnz 0#8 h0 rfl
  rw [← sepConj_assoc, cStrAtRO_sepConj_pad p s pad] at hmem
  refine ⟨(p, s, pad), stackAt s0.sp hookStack ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [masterStrlenROSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hno0, hbound⟩, hmem⟩
  · dsimp only [masterStrlenROSpec] at hpost
    dsimp only [strlenPaddedSpecRO]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0_f, hst⟩, hmem_f⟩
    rw [← cStrAtRO_sepConj_pad p s pad, sepConj_assoc] at hmem_f
    exact ⟨⟨hx0_f, hst.2.1, hst.1⟩, hmem_f⟩

/-- Lift `HookOk f masterStrlenSpec` to `HookOk f (strlenPaddedSpecRO hookStack)`. -/
theorem hookOk_strlenPaddedRO_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) (hookStack : Nat := extHookStack) :
    HookOk f (strlenPaddedSpecRO hookStack) :=
  SpecSimulates.hookOk (masterStrlenRO_simulates_strlenPaddedRO hookStack)
    (hookOk_masterStrlenRO_of_master hh)

/-- Lift `HookOk f (strlenSpecK keep masterStrlenSpec)` to
    `HookOk f (strlenSpecK keep (strlenPaddedSpecRO hookStack))`. -/
theorem hookOk_strlenPaddedROK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (strlenPaddedSpecRO hookStack)) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep (masterStrlenRO_simulates_strlenPaddedRO hookStack))
    (hookOk_masterStrlenROK_of_master keep hh)

/-! ### 4.2 Padded Read-Only Consumer Contracts (`M24.CalleesRO.strlenSpecRO`) -/

/-- Forward simulation `masterStrlenROSpec` → `withStrlenPadRO (strlenSpecRO hookStack)`
    (splitting `(p ↦ᵣ (s ++ [0#8] ++ pad))` on exit and dropping the duplicable RO pad via
    `Satisfies.of_sep_right`, without needing `sf.mem = s0.mem`). -/
theorem masterStrlenRO_simulates_strlenSpecRO_padRO (hookStack : Nat := extHookStack) :
    SpecSimulates masterStrlenROSpec (withStrlenPadRO (strlenSpecRO hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, s⟩ R s0 hpre
  dsimp only [withStrlenPadRO, strlenSpecRO] at hpre
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpre
  obtain ⟨pad, hpre⟩ := hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hbound, hpre⟩
  rw [sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hnz⟩, hmem⟩
  have hno0 : 0#8 ∉ s := fun h0 => hnz 0#8 h0 rfl
  have hmem' : s0.mem ⊨ (p ↦ᵣ (s ++ [0#8] ++ pad)) ∗ (stackAt s0.sp hookStack ∗ R) := by
    rw [sepConj_left_comm, ← sepConj_assoc, cStrAtRO_sepConj_pad p s pad] at hmem
    exact hmem
  refine ⟨(p, s, pad), stackAt s0.sp hookStack ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [masterStrlenROSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hno0, hbound⟩, hmem'⟩
  · dsimp only [masterStrlenROSpec] at hpost
    dsimp only [withStrlenPadRO, strlenSpecRO]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0_f, hst⟩, hmem_f⟩
    rw [← cStrAtRO_sepConj_pad p s pad, sepConj_assoc, sepConj_left_comm] at hmem_f
    exact ⟨⟨hx0_f, hst.2.1, hst.1⟩, Satisfies.of_sep_right hmem_f⟩

theorem hookOk_strlenSpecRO_padRO_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) (hookStack : Nat := extHookStack) :
    HookOk f (withStrlenPadRO (strlenSpecRO hookStack)) :=
  SpecSimulates.hookOk (masterStrlenRO_simulates_strlenSpecRO_padRO hookStack)
    (hookOk_masterStrlenRO_of_master hh)

theorem hookOk_strlenSpecRO_padROK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (withStrlenPadRO (strlenSpecRO hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep (masterStrlenRO_simulates_strlenSpecRO_padRO hookStack))
    (hookOk_masterStrlenROK_of_master keep hh)

theorem hookOk_strlenSpecRO_roDataPad_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) (hookStack : Nat := extHookStack) :
    HookOk f (withStrlenRoDataPad (strlenSpecRO hookStack)) :=
  SpecSimulates.hookOk (sim_roDataPad_of_padRO (strlenSpecRO hookStack))
    (hookOk_strlenSpecRO_padRO_of_master hh hookStack)

theorem hookOk_strlenSpecRO_roDataPadK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (withStrlenRoDataPad (strlenSpecRO hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep (sim_roDataPad_of_padRO (strlenSpecRO hookStack)))
    (hookOk_strlenSpecRO_padROK_of_master keep hh hookStack)

theorem hookOk_strlenSpecRO_alignedEnd_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) (hookStack : Nat := extHookStack) :
    HookOk f (withStrlenAlignedEnd (strlenSpecRO hookStack)) :=
  SpecSimulates.hookOk (sim_alignedEnd_of_padRO (strlenSpecRO hookStack))
    (hookOk_strlenSpecRO_padRO_of_master hh hookStack)

theorem hookOk_strlenSpecRO_alignedEndK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (withStrlenAlignedEnd (strlenSpecRO hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep (sim_alignedEnd_of_padRO (strlenSpecRO hookStack)))
    (hookOk_strlenSpecRO_padROK_of_master keep hh hookStack)

/-! ### 4.3 Padded Mutable-String Consumer Contracts (`MainHops.strlenSpec` = `cliStrlenSpec`, `CliExt.strlenSpec`) -/

/-- Forward simulation `masterStrlenSpec` (`strRo = false`, `padRo = true`) →
    `withStrlenPadRO (MainHops.strlenSpec hookStack)` (`= withStrlenPadRO (cliStrlenSpec hookStack)`),
    preserving mutable `cStrAt p s` and dropping the trailing RO pad on exit via
    `Satisfies.of_sep_right`. -/
theorem masterStrlen_simulates_mainStrlen_padRO (hookStack : Nat := extHookStack) :
    SpecSimulates masterStrlenSpec
      (withStrlenPadRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨p, s⟩ R s0 hpre
  dsimp only [withStrlenPadRO, CryptoVerification.SignalSession.Cli.MainHops.strlenSpec] at hpre
  rw [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hpre
  obtain ⟨pad, hpre⟩ := hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hbound, hpre⟩
  rw [sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hnz⟩, hmem⟩
  have hno0 : 0#8 ∉ s := fun h0 => hnz 0#8 h0 rfl
  refine ⟨(false, true, p, s, pad), stackAt s0.sp hookStack ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [masterStrlenSpec, strlenSrc_false_true]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    rw [sepConj_left_comm] at hmem
    exact ⟨⟨hx0, hno0, hbound⟩, hmem⟩
  · dsimp only [masterStrlenSpec, strlenSrc_false_true] at hpost
    dsimp only [withStrlenPadRO, CryptoVerification.SignalSession.Cli.MainHops.strlenSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0_f, hst⟩, hmem_f⟩
    rw [sepConj_left_comm] at hmem_f
    exact ⟨⟨hx0_f, hst.2.1, hst.1⟩, Satisfies.of_sep_right hmem_f⟩

theorem hookOk_mainStrlen_padRO_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) (hookStack : Nat := extHookStack) :
    HookOk f
      (withStrlenPadRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)) :=
  SpecSimulates.hookOk (masterStrlen_simulates_mainStrlen_padRO hookStack) hh

theorem hookOk_mainStrlen_padROK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep
      (withStrlenPadRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep (masterStrlen_simulates_mainStrlen_padRO hookStack)) hh

theorem hookOk_mainStrlen_roDataPad_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) (hookStack : Nat := extHookStack) :
    HookOk f
      (withStrlenRoDataPad (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)) :=
  SpecSimulates.hookOk
    (sim_roDataPad_of_padRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))
    (hookOk_mainStrlen_padRO_of_master hh hookStack)

theorem hookOk_mainStrlen_roDataPadK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep
      (withStrlenRoDataPad (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (sim_roDataPad_of_padRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)))
    (hookOk_mainStrlen_padROK_of_master keep hh hookStack)

theorem hookOk_mainStrlen_alignedEnd_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) (hookStack : Nat := extHookStack) :
    HookOk f
      (withStrlenAlignedEnd (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)) :=
  SpecSimulates.hookOk
    (sim_alignedEnd_of_padRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))
    (hookOk_mainStrlen_padRO_of_master hh hookStack)

theorem hookOk_mainStrlen_alignedEndK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep
      (withStrlenAlignedEnd (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (sim_alignedEnd_of_padRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)))
    (hookOk_mainStrlen_padROK_of_master keep hh hookStack)

theorem hookOk_cliExtStrlen_padRO_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) :
    HookOk f (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec) :=
  hookOk_mainStrlen_padRO_of_master hh extHookStack

theorem hookOk_cliExtStrlen_padROK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) :
    HookOk f
      (strlenSpecK keep (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  hookOk_mainStrlen_padROK_of_master keep hh extHookStack

theorem hookOk_cliExtStrlen_roDataPad_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) :
    HookOk f (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec) :=
  hookOk_mainStrlen_roDataPad_of_master hh extHookStack

theorem hookOk_cliExtStrlen_roDataPadK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) :
    HookOk f
      (strlenSpecK keep (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  hookOk_mainStrlen_roDataPadK_of_master keep hh extHookStack

theorem hookOk_cliExtStrlen_alignedEnd_of_master {f : State → State}
    (hh : HookOk f masterStrlenSpec) :
    HookOk f (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec) :=
  hookOk_mainStrlen_alignedEnd_of_master hh extHookStack

theorem hookOk_cliExtStrlen_alignedEndK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (strlenSpecK keep masterStrlenSpec)) :
    HookOk f
      (strlenSpecK keep (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  hookOk_mainStrlen_alignedEndK_of_master keep hh extHookStack

/-! ### 4.4 Placed Budget (`withVmPreserved`) Consumer Lifts (`F1`) -/

theorem withStrlenPadRO_withVmPreserved (spec : Spec (BitVec 64 × List (BitVec 8))) :
    withVmPreserved (withStrlenPadRO spec) = withStrlenPadRO (withVmPreserved spec) := rfl

theorem withStrlenRoDataPad_withVmPreserved (spec : Spec (BitVec 64 × List (BitVec 8))) :
    withVmPreserved (withStrlenRoDataPad spec) = withStrlenRoDataPad (withVmPreserved spec) := rfl

theorem withStrlenAlignedEnd_withVmPreserved (spec : Spec (BitVec 64 × List (BitVec 8))) :
    withVmPreserved (withStrlenAlignedEnd spec) = withStrlenAlignedEnd (withVmPreserved spec) := rfl

theorem hookOk_cliStrlenPadded_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (withVmPreserved (cliStrlenPaddedSpec hookStack)) :=
  SpecSimulates.hookOk
    (SpecSimulates.liftWithVmPreserved (masterStrlen_simulates_cliStrlenPadded hookStack)) hh

theorem hookOk_cliStrlenPadded_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec)))
    (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (withVmPreserved (cliStrlenPaddedSpec hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (SpecSimulates.liftWithVmPreserved (masterStrlen_simulates_cliStrlenPadded hookStack))) hh

theorem hookOk_strlenPaddedRO_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (withVmPreserved (strlenPaddedSpecRO hookStack)) :=
  SpecSimulates.hookOk
    (SpecSimulates.liftWithVmPreserved (masterStrlenRO_simulates_strlenPaddedRO hookStack))
    (hookOk_masterStrlenROVm_of_masterVm hh)

theorem hookOk_strlenPaddedRO_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec)))
    (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (withVmPreserved (strlenPaddedSpecRO hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (SpecSimulates.liftWithVmPreserved (masterStrlenRO_simulates_strlenPaddedRO hookStack)))
    (hookOk_masterStrlenROVmK_of_masterVm keep hh)

/-- Headline placed-budget consumer lift (`M24/CalleesRO.lean:587`). -/
theorem hookOk_strlenSpecRO_padRO_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (withVmPreserved (withStrlenPadRO (strlenSpecRO hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.liftWithVmPreserved (masterStrlenRO_simulates_strlenSpecRO_padRO hookStack))
    (hookOk_masterStrlenROVm_of_masterVm hh)

theorem hookOk_strlenSpecRO_padRO_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec)))
    (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (withVmPreserved (withStrlenPadRO (strlenSpecRO hookStack)))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (SpecSimulates.liftWithVmPreserved (masterStrlenRO_simulates_strlenSpecRO_padRO hookStack)))
    (hookOk_masterStrlenROVmK_of_masterVm keep hh)

theorem hookOk_strlenSpecRO_roDataPad_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (withVmPreserved (withStrlenRoDataPad (strlenSpecRO hookStack))) :=
  SpecSimulates.hookOk (sim_roDataPad_of_padRO (withVmPreserved (strlenSpecRO hookStack)))
    (hookOk_strlenSpecRO_padRO_withVmPreserved_of_masterVm hh hookStack)

theorem hookOk_strlenSpecRO_roDataPad_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec)))
    (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (withVmPreserved (withStrlenRoDataPad (strlenSpecRO hookStack)))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (sim_roDataPad_of_padRO (withVmPreserved (strlenSpecRO hookStack))))
    (hookOk_strlenSpecRO_padRO_withVmPreservedK_of_masterVm keep hh hookStack)

theorem hookOk_strlenSpecRO_alignedEnd_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (withVmPreserved (withStrlenAlignedEnd (strlenSpecRO hookStack))) :=
  SpecSimulates.hookOk (sim_alignedEnd_of_padRO (withVmPreserved (strlenSpecRO hookStack)))
    (hookOk_strlenSpecRO_padRO_withVmPreserved_of_masterVm hh hookStack)

theorem hookOk_strlenSpecRO_alignedEnd_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec)))
    (hookStack : Nat := extHookStack) :
    HookOk f
      (strlenSpecK keep (withVmPreserved (withStrlenAlignedEnd (strlenSpecRO hookStack)))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (sim_alignedEnd_of_padRO (withVmPreserved (strlenSpecRO hookStack))))
    (hookOk_strlenSpecRO_padRO_withVmPreservedK_of_masterVm keep hh hookStack)

theorem hookOk_mainStrlen_padRO_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f
      (withVmPreserved
        (withStrlenPadRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))) :=
  SpecSimulates.hookOk
    (SpecSimulates.liftWithVmPreserved (masterStrlen_simulates_mainStrlen_padRO hookStack)) hh

theorem hookOk_mainStrlen_padRO_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec)))
    (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep
      (withVmPreserved
        (withStrlenPadRO (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (SpecSimulates.liftWithVmPreserved (masterStrlen_simulates_mainStrlen_padRO hookStack))) hh

theorem hookOk_mainStrlen_roDataPad_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (withVmPreserved
      (withStrlenRoDataPad (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))) :=
  SpecSimulates.hookOk
    (sim_roDataPad_of_padRO
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)))
    (hookOk_mainStrlen_padRO_withVmPreserved_of_masterVm hh hookStack)

theorem hookOk_mainStrlen_roDataPad_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec)))
    (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (withVmPreserved
      (withStrlenRoDataPad (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (sim_roDataPad_of_padRO
        (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))))
    (hookOk_mainStrlen_padRO_withVmPreservedK_of_masterVm keep hh hookStack)

theorem hookOk_mainStrlen_alignedEnd_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) (hookStack : Nat := extHookStack) :
    HookOk f (withVmPreserved
      (withStrlenAlignedEnd
        (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))) :=
  SpecSimulates.hookOk
    (sim_alignedEnd_of_padRO
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)))
    (hookOk_mainStrlen_padRO_withVmPreserved_of_masterVm hh hookStack)

theorem hookOk_mainStrlen_alignedEnd_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec)))
    (hookStack : Nat := extHookStack) :
    HookOk f (strlenSpecK keep (withVmPreserved
      (withStrlenAlignedEnd
        (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack)))) :=
  SpecSimulates.hookOk
    (SpecSimulates.strlenSpecK keep
      (sim_alignedEnd_of_padRO
        (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.strlenSpec hookStack))))
    (hookOk_mainStrlen_padRO_withVmPreservedK_of_masterVm keep hh hookStack)

theorem hookOk_cliExtStrlen_padRO_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) :
    HookOk f (withVmPreserved (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  hookOk_mainStrlen_padRO_withVmPreserved_of_masterVm hh extHookStack

theorem hookOk_cliExtStrlen_padRO_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec))) :
    HookOk f (strlenSpecK keep
      (withVmPreserved (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  hookOk_mainStrlen_padRO_withVmPreservedK_of_masterVm keep hh extHookStack

theorem hookOk_cliExtStrlen_roDataPad_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) :
    HookOk f
      (withVmPreserved (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  hookOk_mainStrlen_roDataPad_withVmPreserved_of_masterVm hh extHookStack

theorem hookOk_cliExtStrlen_roDataPad_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec))) :
    HookOk f (strlenSpecK keep
      (withVmPreserved (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  hookOk_mainStrlen_roDataPad_withVmPreservedK_of_masterVm keep hh extHookStack

theorem hookOk_cliExtStrlen_alignedEnd_withVmPreserved_of_masterVm {f : State → State}
    (hh : HookOk f (withVmPreserved masterStrlenSpec)) :
    HookOk f
      (withVmPreserved
        (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  hookOk_mainStrlen_alignedEnd_withVmPreserved_of_masterVm hh extHookStack

theorem hookOk_cliExtStrlen_alignedEnd_withVmPreservedK_of_masterVm (keep : BitVec 64 → Bool)
    {f : State → State}
    (hh : HookOk f (strlenSpecK keep (withVmPreserved masterStrlenSpec))) :
    HookOk f (strlenSpecK keep
      (withVmPreserved
        (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  hookOk_mainStrlen_alignedEnd_withVmPreservedK_of_masterVm keep hh extHookStack

/-! ### 4.5 Definitional Commutations (`strlenSpecK := memcpySpecK` Re-exports) -/

theorem strlenSpecK_keepsFs (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    (strlenSpecK keep spec).keepsFs = strlenSpecK keep spec.keepsFs :=
  memcpySpecK_keepsFs keep spec

theorem strlenSpecK_withVmPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withVmPreserved (strlenSpecK keep spec) = strlenSpecK keep (withVmPreserved spec) :=
  memcpySpecK_withVmPreserved keep spec

theorem strlenSpecK_withOomPoolPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withOomPoolPreserved (strlenSpecK keep spec) =
      strlenSpecK keep (withOomPoolPreserved spec) :=
  memcpySpecK_withOomPoolPreserved keep spec

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode
