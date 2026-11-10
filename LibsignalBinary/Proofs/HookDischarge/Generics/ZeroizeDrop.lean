/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.StdStartup.MemOps
public import ProofLib.SepLogic.WP.StepsProcess
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common

/-!
# Byte-Exact `StaticSecret::drop` and `SharedSecret::drop` Hook Discharge (`LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop`)

Real-bytes discharge of the `x25519-dalek` 32-byte zeroize drop contracts in `signal-session`:

1. **`<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop`** (`zeroize32Words` /
   `zeroize32Instrs`, `63` 32-bit instruction words = `252` bytes, `0` B stack; matches
   `arm64-semantics/CaseStudies/Curve25519NeonEquiv/Proofs/Serial/Code.lean` `zeroize32Words`
   word-for-word) and the byte-for-byte identical body of
   **`<curve25519_dalek::montgomery::MontgomeryPoint as zeroize::Zeroize>::zeroize`**.
2. **`<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop`** (`sharedSecretDropInstrs`,
   `1` 32-bit unconditional tail-branch `b targetAddr` when `targetAddr - addr` is encodable as an
   ARM64 `B` `imm26 × 4` offset, `0` B stack) given the explicit code premise that
   `<MontgomeryPoint as Zeroize>::zeroize` (`zeroize32Instrs` / `zeroize32Words`) is loaded at
   `targetAddr`.

Covers every contract shape consumed by placed callers on `main` (process/budget `hasWords` variants
carry `h_no_ext : ∀ pc, P.externAt? pc = none` for hook-free sub-programs; `keepsFs` variants are
helper extras):
- `CryptoVerification.LibsignalTripleRatchet.zeroizeSecretSpec` and `keepsFs zeroizeSecretSpec`,
- `LibsignalBinary.Heap.SpecBudget.withVmPreserved zeroizeSecretSpec` (`rfl`/defeq-equal by body,
  not kernel-checked in this PR, to `DhStepBudgetSteps.zeroizeSecretBudgetSpec`),
  `keepsFs (withVmPreserved zeroizeSecretSpec)`, and
  `withFsPred Pfs (withVmPreserved zeroizeSecretSpec)` (`rfl`/defeq-equal by body, not
  kernel-checked in this PR, to `AgreeBudgetFd.withFsPred Pfs (withVmPreserved zeroizeSecretSpec)`),
- `CryptoVerification.SignalSession.CliExt.zeroizeSpec`, `keepsFs zeroizeSpec`,
  `withVmPreserved zeroizeSpec`, `keepsFs (withVmPreserved zeroizeSpec)`, and `zeroizeSpec.inImage img`,
- stack-parameterized `withStack` variants (`Libc.Common.withStack` and `Libc.Common.keepsFs` are
  `rfl`/defeq-equal by body to `Hooks2.withStack` / `CliExt.withStack` and `Arm64.Spec.keepsFs`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop

open Arm64 ProofLib
open ProofLib.StdStartup (hasInstrs)
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open CryptoVerification.LibsignalTripleRatchet (zeroizeSecretSpec extHookStack)
open CryptoVerification.SignalSession.CliExt (zeroizeSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack
  subroutine_ok_drop_keepsFs subroutine_ok_withStack
  subroutine_ok_withStack_keepsFs)

/-! ## 1. Mirror of `AgreeBudgetFd.withFsPred` & Generic Process-Preservation Combinators -/

/-- Mirror of `CryptoVerification.LibsignalTripleRatchet.AgreeBudgetFd.withFsPred`
    (`LibsignalBinary/Proofs/TripleRatchet/Keys/AgreeBudgetFd.lean:81`): threads an invariant
    `Pfs : FsState → Prop` across `spec.pre` and `spec.post`. -/
@[expose] def withFsPred {α : Type} (Pfs : FsState → Prop) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s => ⌜Pfs s.fs⌝ ∗ spec.pre x s
    post := fun x s0 sf => ⌜Pfs sf.fs⌝ ∗ spec.post x s0 sf }

/-- Any `subroutine_ok P entry (keepsFs spec)` preserves every predicate `Pfs : FsState → Prop`. -/
theorem subroutine_ok_withFsPred_of_keepsFs {α : Type} {P : Program} {entry : BitVec 64}
    {spec : Spec α} (Pfs : FsState → Prop)
    (h : subroutine_ok P entry (keepsFs spec))
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    subroutine_ok P entry (withFsPred Pfs spec) := by
  refine subroutine_ok_map h
    (fun x R s0 hpre => ?_)
    (fun x R' s0 sf _ hp => by
      dsimp only [keepsFs] at hp; rw [hpan] at hp; exact not_satisfies_false_sepConj hp)
    (fun x code R' s0 sf _ he => by
      dsimp only [keepsFs] at he; rw [hex] at he; exact not_satisfies_false_sepConj he)
    (fun x _ _ R' s0 sf _ ho => by
      dsimp only [keepsFs] at ho; rw [hoom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [withFsPred] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpfs, hpre'⟩
  refine ⟨x, R, hpre', fun sf hpost => ?_⟩
  dsimp only [keepsFs] at hpost
  dsimp only [withFsPred]
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1 ▸ hpfs, hpost.2⟩

/-- Decode `P.hasWords addr words` into `hasInstrs P addr instrs` whenever `words` decodes
    elementwise to `instrs`. -/
theorem hasInstrs_of_hasWords {P : Program} {addr : BitVec 64}
    {words : List (BitVec 32)} {instrs : List Instr}
    (hw : P.hasWords addr words)
    (hdec : (List.range instrs.length).all
      (fun i => Program.decodeWordAt words i == instrs[i]?) = true := by decide) :
    hasInstrs P addr instrs := by
  intro i hi
  have hall := List.all_eq_true.mp hdec i (List.mem_range.mpr hi)
  simp only [beq_iff_eq, List.getElem?_eq_getElem hi] at hall
  exact Program.fetch_of_hasWords_decodeAt i hw rfl hall

/-- Lift `subroutine_ok (pureWordsProg addr words) addr spec` to `keepsFs (withVmPreserved spec)`
    on any hook-free program `P` containing `words` at `addr`. -/
theorem subroutine_ok_keepsFs_withVmPreserved_of_pureWords {α : Type}
    {P : Program} {addr : BitVec 64} {words : List (BitVec 32)} {spec : Spec α}
    (hpure : subroutine_ok (pureWordsProg addr words) addr spec)
    (hall : (pureWordsProg addr words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)
    (hc : P.hasWords addr words)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_panic : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_exit : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (h_oom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_ne : words ≠ [] := by decide)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; rfl)
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; rfl) :
    subroutine_ok P addr (keepsFs (withVmPreserved spec)) := by
  have hlift := subroutine_ok_lift_pureWords_process hpure hall hc h_no_ext
    h_panic h_exit h_oom h_ne h_pre_mem h_post_mem
  refine subroutine_ok_map hlift
    (fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩)
    (fun x R' s0 sf _ hp => by rw [h_panic] at hp; exact not_satisfies_false_sepConj hp)
    (fun x code R' s0 sf _ he => by rw [h_exit] at he; exact not_satisfies_false_sepConj he)
    (fun x _ _ R' s0 sf _ ho => by rw [h_oom] at ho; exact False.elim (not_satisfies_false_sepConj ho))
  dsimp only [keepsFs, withVmPreserved] at hpost ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.1, hpost.1.toVmPreserved, hpost.2⟩

/-! ## 2. Instruction Words, Decoded `Instr` Lists, and Stepping Helpers -/

/-- Exact `63`-word (`252`-byte, `0`-byte stack) machine code emitted by `rustc 1.98.1`
    (`aarch64-unknown-linux-musl`) for both
    `<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop` and
    `<curve25519_dalek::montgomery::MontgomeryPoint as zeroize::Zeroize>::zeroize`. -/
@[expose] def zeroize32Words : List (BitVec 32) :=
  [ 0x3900001f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38001d1f#32, 0x38002d3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38003d1f#32, 0x38004d3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38005d1f#32, 0x38006d3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38007d1f#32, 0x38008d3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38009d1f#32, 0x3800ad3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x3800bd1f#32, 0x3800cd3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x3800dd1f#32, 0x3800ed3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x3800fd1f#32, 0x38010d3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38011d1f#32, 0x38012d3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38013d1f#32, 0x38014d3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38015d1f#32, 0x38016d3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38017d1f#32, 0x38018d3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x38019d1f#32, 0x3801ad3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x3801bd1f#32, 0x3801cd3f#32,
    0xaa0003e8#32, 0xaa0003e9#32, 0x3801dd1f#32, 0x3801ed3f#32,
    0x3801fc1f#32,
    0xd65f03c0#32 ]

/-- Exact `63`-instruction (`252`-byte, `0`-byte stack) 32-byte volatile-zeroize body decoded from
    `zeroize32Words`. -/
@[expose] def zeroize32Instrs : List Instr :=
  [ -- [ 0] +0x00: 0x3900001f  strb wzr, [x0]
    .str .B8 .xzr (.Offset .x0 0#64),
    -- [ 1..4] +0x04..+0x10: bytes 1, 2
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 1#64),
    .str .B8 .xzr (.PreIndex .x9 2#64),
    -- [ 5..8] +0x14..+0x20: bytes 3, 4
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 3#64),
    .str .B8 .xzr (.PreIndex .x9 4#64),
    -- [ 9..12] +0x24..+0x30: bytes 5, 6
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 5#64),
    .str .B8 .xzr (.PreIndex .x9 6#64),
    -- [13..16] +0x34..+0x40: bytes 7, 8
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 7#64),
    .str .B8 .xzr (.PreIndex .x9 8#64),
    -- [17..20] +0x44..+0x50: bytes 9, 10
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 9#64),
    .str .B8 .xzr (.PreIndex .x9 0xa#64),
    -- [21..24] +0x54..+0x60: bytes 11, 12
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0xb#64),
    .str .B8 .xzr (.PreIndex .x9 0xc#64),
    -- [25..28] +0x64..+0x70: bytes 13, 14
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0xd#64),
    .str .B8 .xzr (.PreIndex .x9 0xe#64),
    -- [29..32] +0x74..+0x80: bytes 15, 16
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0xf#64),
    .str .B8 .xzr (.PreIndex .x9 0x10#64),
    -- [33..36] +0x84..+0x90: bytes 17, 18
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0x11#64),
    .str .B8 .xzr (.PreIndex .x9 0x12#64),
    -- [37..40] +0x94..+0xa0: bytes 19, 20
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0x13#64),
    .str .B8 .xzr (.PreIndex .x9 0x14#64),
    -- [41..44] +0xa4..+0xb0: bytes 21, 22
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0x15#64),
    .str .B8 .xzr (.PreIndex .x9 0x16#64),
    -- [45..48] +0xb4..+0xc0: bytes 23, 24
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0x17#64),
    .str .B8 .xzr (.PreIndex .x9 0x18#64),
    -- [49..52] +0xc4..+0xd0: bytes 25, 26
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0x19#64),
    .str .B8 .xzr (.PreIndex .x9 0x1a#64),
    -- [53..56] +0xd4..+0xe0: bytes 27, 28
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0x1b#64),
    .str .B8 .xzr (.PreIndex .x9 0x1c#64),
    -- [57..60] +0xe4..+0xf0: bytes 29, 30
    .logicalShift .W64 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x9 .xzr .x0 .LSL 0,
    .str .B8 .xzr (.PreIndex .x8 0x1d#64),
    .str .B8 .xzr (.PreIndex .x9 0x1e#64),
    -- [61] +0xf4: 0x3801fc1f  strb wzr, [x0, #0x1f]!
    .str .B8 .xzr (.PreIndex .x0 0x1f#64),
    -- [62] +0xf8: 0xd65f03c0  ret
    .ret .lr ]

/-- Relocated `1`-instruction (`4`-byte) sequence for `<SharedSecret as Drop>::drop` at `addr`
    tail-jumping (`R_AARCH64_JUMP26`) to `<MontgomeryPoint as Zeroize>::zeroize` at `targetAddr`. -/
@[expose] def sharedSecretDropInstrs (addr targetAddr : BitVec 64) : List Instr :=
  [ .b (targetAddr - addr) ]

/-- `withStack zeroizeSecretSpec extHookStack` is definitionally (`rfl`) `CliExt.zeroizeSpec`. -/
theorem withStack_zeroizeSecretSpec_extHookStack :
    withStack zeroizeSecretSpec extHookStack = zeroizeSpec := rfl

private theorem pureWordsProg_hasWords_zeroize32 (entry : BitVec 64) :
    (pureWordsProg entry zeroize32Words).hasWords entry zeroize32Words :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range zeroize32Words.length).all fun i =>
      (pureWordsProg 0#64 zeroize32Words).readWordOff (4 * i) == zeroize32Words[i]?) = true
    decide +kernel)

private theorem pureWordsProg_noSvcMsr_zeroize32 (entry : BitVec 64) :
    (pureWordsProg entry zeroize32Words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  Program.allInstrs_of_code_eq (prog := pureWordsProg 0#64 zeroize32Words) rfl (by prove_all_instrs)

private theorem pureWordsProg_hasInstrs_zeroize32 (entry : BitVec 64) :
    hasInstrs (pureWordsProg entry zeroize32Words) entry zeroize32Instrs :=
  hasInstrs_of_hasWords (pureWordsProg_hasWords_zeroize32 entry)

private theorem fetch_at {P : Program} {base off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (h : hasInstrs P base ls)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (base + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := h.fetch_off i off hlt hoff
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi
  exact hf

private theorem fetch_at0 {P : Program} {base : BitVec 64} {ls : List Instr} {inst : Instr}
    (h : hasInstrs P base ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch base = some inst := by
  simpa using fetch_at 0 h hi rfl

private def FsTracePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace

private theorem FsTracePreserved.rfl (s : State) : FsTracePreserved s s :=
  ⟨Eq.refl _, Eq.refl _⟩

@[local simp] private theorem FsTracePreserved_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    FsTracePreserved s0 (s.writeReg64 r v) ↔ FsTracePreserved s0 s := by
  cases s; cases r <;> rfl

@[local simp] private theorem FsTracePreserved_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    FsTracePreserved s0 (s.writeReg32 r v) ↔ FsTracePreserved s0 s := by
  cases s; cases r <;> rfl

@[local simp] private theorem FsTracePreserved_setPState (s0 s : State) (p : PState) :
    FsTracePreserved s0 (s.setPState p) ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_advancePC (s0 s : State) :
    FsTracePreserved s0 s.advancePC ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_setPC (s0 s : State) (pc : BitVec 64) :
    FsTracePreserved s0 (s.setPC pc) ↔ FsTracePreserved s0 s := by
  cases s; rfl

@[local simp] private theorem FsTracePreserved_setMem (s0 s : State) (m : Memory) :
    FsTracePreserved s0 (s.setMem m) ↔ FsTracePreserved s0 s := by
  cases s; rfl

private theorem fs_eq_of_preserved {s0 sf : State} (h : FsTracePreserved s0 sf) :
    sf.fs = s0.fs := h.1

private theorem trace_eq_of_preserved {s0 sf : State} (h : FsTracePreserved s0 sf) :
    sf.trace = s0.trace := h.2

private theorem write8_zero32_eq (bs : List (BitVec 8)) (h : bs.length = 32) :
    ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
    (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8
      bs 0 0#8) 1 0#8) 2 0#8) 3 0#8)
      4 0#8) 5 0#8) 6 0#8) 7 0#8)
      8 0#8) 9 0#8) 10 0#8) 11 0#8)
      12 0#8) 13 0#8) 14 0#8) 15 0#8)
      16 0#8) 17 0#8) 18 0#8) 19 0#8)
      20 0#8) 21 0#8) 22 0#8) 23 0#8)
      24 0#8) 25 0#8) 26 0#8) 27 0#8)
      28 0#8) 29 0#8) 30 0#8) 31 0#8 = List.replicate 32 0#8 := by
  conv =>
    lhs
    arg 1; arg 1; arg 1; arg 1; arg 1; arg 1; arg 1; arg 1
    arg 1; arg 1; arg 1; arg 1; arg 1; arg 1; arg 1; arg 1
    arg 1; arg 1; arg 1; arg 1; arg 1; arg 1; arg 1; arg 1
    arg 1; arg 1; arg 1; arg 1; arg 1; arg 1; arg 1; arg 1
    rw [← ByteSlice.fillPrefix_zero bs 0#8]
  iterate 32 rw [ByteSlice.write8_fillPrefix bs 0#8 _ (by omega)]
  exact ByteSlice.fillPrefix_full h

/-! ## 3. Row 25 (`StaticSecret::drop`) & `<MontgomeryPoint as Zeroize>::zeroize` -/

set_option maxHeartbeats 1600000 in
/-- Unstacked `keepsFs` bridge (`0` stack bytes required): `zeroize32Instrs` at `addr` satisfies
    `keepsFs zeroizeSecretSpec`. -/
theorem zeroize32_zeroizeSecretSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr zeroize32Instrs) :
    subroutine_ok P addr (keepsFs zeroizeSecretSpec) := by
  apply subroutine_ok_of_sepWP_init
  intro a R s0 hpc hrun hpre _hsp
  dsimp only [keepsFs, zeroizeSecretSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hx0, hpre⟩ := hpre
  rw [memRegion_eq_exists_bytes a 32 (by decide), sepExists_sepConj_left,
    satisfies_sepExists] at hpre
  obtain ⟨bs, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hbs_len, hpre⟩ := hpre
  refine ⟨a ↦ₛ bs, hpre, ?_⟩
  have hf0 := fetch_at0 hcode
  have hf1 := fetch_at 1 (off := 0x04#64) hcode
  have hf2 := fetch_at 2 (off := 0x08#64) hcode
  have hf3 := fetch_at 3 (off := 0x0c#64) hcode
  have hf4 := fetch_at 4 (off := 0x10#64) hcode
  have hf5 := fetch_at 5 (off := 0x14#64) hcode
  have hf6 := fetch_at 6 (off := 0x18#64) hcode
  have hf7 := fetch_at 7 (off := 0x1c#64) hcode
  have hf8 := fetch_at 8 (off := 0x20#64) hcode
  have hf9 := fetch_at 9 (off := 0x24#64) hcode
  have hf10 := fetch_at 10 (off := 0x28#64) hcode
  have hf11 := fetch_at 11 (off := 0x2c#64) hcode
  have hf12 := fetch_at 12 (off := 0x30#64) hcode
  have hf13 := fetch_at 13 (off := 0x34#64) hcode
  have hf14 := fetch_at 14 (off := 0x38#64) hcode
  have hf15 := fetch_at 15 (off := 0x3c#64) hcode
  have hf16 := fetch_at 16 (off := 0x40#64) hcode
  have hf17 := fetch_at 17 (off := 0x44#64) hcode
  have hf18 := fetch_at 18 (off := 0x48#64) hcode
  have hf19 := fetch_at 19 (off := 0x4c#64) hcode
  have hf20 := fetch_at 20 (off := 0x50#64) hcode
  have hf21 := fetch_at 21 (off := 0x54#64) hcode
  have hf22 := fetch_at 22 (off := 0x58#64) hcode
  have hf23 := fetch_at 23 (off := 0x5c#64) hcode
  have hf24 := fetch_at 24 (off := 0x60#64) hcode
  have hf25 := fetch_at 25 (off := 0x64#64) hcode
  have hf26 := fetch_at 26 (off := 0x68#64) hcode
  have hf27 := fetch_at 27 (off := 0x6c#64) hcode
  have hf28 := fetch_at 28 (off := 0x70#64) hcode
  have hf29 := fetch_at 29 (off := 0x74#64) hcode
  have hf30 := fetch_at 30 (off := 0x78#64) hcode
  have hf31 := fetch_at 31 (off := 0x7c#64) hcode
  have hf32 := fetch_at 32 (off := 0x80#64) hcode
  have hf33 := fetch_at 33 (off := 0x84#64) hcode
  have hf34 := fetch_at 34 (off := 0x88#64) hcode
  have hf35 := fetch_at 35 (off := 0x8c#64) hcode
  have hf36 := fetch_at 36 (off := 0x90#64) hcode
  have hf37 := fetch_at 37 (off := 0x94#64) hcode
  have hf38 := fetch_at 38 (off := 0x98#64) hcode
  have hf39 := fetch_at 39 (off := 0x9c#64) hcode
  have hf40 := fetch_at 40 (off := 0xa0#64) hcode
  have hf41 := fetch_at 41 (off := 0xa4#64) hcode
  have hf42 := fetch_at 42 (off := 0xa8#64) hcode
  have hf43 := fetch_at 43 (off := 0xac#64) hcode
  have hf44 := fetch_at 44 (off := 0xb0#64) hcode
  have hf45 := fetch_at 45 (off := 0xb4#64) hcode
  have hf46 := fetch_at 46 (off := 0xb8#64) hcode
  have hf47 := fetch_at 47 (off := 0xbc#64) hcode
  have hf48 := fetch_at 48 (off := 0xc0#64) hcode
  have hf49 := fetch_at 49 (off := 0xc4#64) hcode
  have hf50 := fetch_at 50 (off := 0xc8#64) hcode
  have hf51 := fetch_at 51 (off := 0xcc#64) hcode
  have hf52 := fetch_at 52 (off := 0xd0#64) hcode
  have hf53 := fetch_at 53 (off := 0xd4#64) hcode
  have hf54 := fetch_at 54 (off := 0xd8#64) hcode
  have hf55 := fetch_at 55 (off := 0xdc#64) hcode
  have hf56 := fetch_at 56 (off := 0xe0#64) hcode
  have hf57 := fetch_at 57 (off := 0xe4#64) hcode
  have hf58 := fetch_at 58 (off := 0xe8#64) hcode
  have hf59 := fetch_at 59 (off := 0xec#64) hcode
  have hf60 := fetch_at 60 (off := 0xf0#64) hcode
  have hf61 := fetch_at 61 (off := 0xf4#64) hcode
  have hf62 := fetch_at 62 (off := 0xf8#64) hcode
  wp_steps 63
  rw [write8_zero32_eq bs hbs_len]
  apply SepWP.done
  · simp [wp_norm, arm64_norm]
  · exact hrun
  · refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
    · rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨fs_eq_of_preserved (by simp [FsTracePreserved.rfl]), ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨trace_eq_of_preserved (by simp [FsTracePreserved.rfl]), hm⟩
    · simp only [wp_norm, arm64_norm]
      rw [CalleeSavedPreserved_writeReg64_caller _ _ (Reg.gpr 0#5) _,
          CalleeSavedPreserved_writeReg64_caller _ _ (Reg.gpr 9#5) _,
          CalleeSavedPreserved_writeReg64_caller _ _ (Reg.gpr 8#5) _]
      exact CalleeSavedPreserved.rfl s0

/-- Unstacked bridge (`0` stack bytes required): `zeroize32Instrs` at `addr` satisfies
    `zeroizeSecretSpec` (exact consumer spec of `Initiate/HooksPlaced`, `ResponderCore/CryptoCalleesPlaced`,
    and `TripleRatchet/Keys/Agree`). -/
theorem zeroize32_zeroizeSecretSpec_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr zeroize32Instrs) :
    subroutine_ok P addr zeroizeSecretSpec :=
  subroutine_ok_drop_keepsFs (zeroize32_zeroizeSecretSpec_keepsFs_ok hcode)

/-- `withFsPred Pfs` variant of `zeroize32_zeroizeSecretSpec_ok`. -/
theorem zeroize32_zeroizeSecretSpec_withFsPred_ok {P : Program} {addr : BitVec 64}
    (Pfs : FsState → Prop) (hcode : hasInstrs P addr zeroize32Instrs) :
    subroutine_ok P addr (withFsPred Pfs zeroizeSecretSpec) :=
  subroutine_ok_withFsPred_of_keepsFs Pfs (zeroize32_zeroizeSecretSpec_keepsFs_ok hcode)

/-- Stack-parameterized `keepsFs` bridge for `StaticSecret::drop` (`hookStack` arbitrary). -/
theorem staticSecretDrop_withStack_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hookStack : Nat) (hcode : hasInstrs P addr zeroize32Instrs) :
    subroutine_ok P addr (keepsFs (withStack zeroizeSecretSpec hookStack)) :=
  subroutine_ok_withStack_keepsFs hookStack (zeroize32_zeroizeSecretSpec_keepsFs_ok hcode)

/-- Primary `keepsFs` bridge for `cliHookTable` row 25: `zeroize32Instrs` at `addr` satisfies
    `keepsFs CliExt.zeroizeSpec`. -/
theorem staticSecretDrop_zeroizeSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr zeroize32Instrs) :
    subroutine_ok P addr (keepsFs zeroizeSpec) :=
  staticSecretDrop_withStack_keepsFs_ok extHookStack hcode

/-- Primary bridge for `cliHookTable` row 25 (`CliExternsOk.staticDrop`): `zeroize32Instrs` at
    `addr` satisfies `CliExt.zeroizeSpec`. -/
theorem staticSecretDrop_zeroizeSpec_ok {P : Program} {addr : BitVec 64}
    (hcode : hasInstrs P addr zeroize32Instrs) :
    subroutine_ok P addr zeroizeSpec :=
  subroutine_ok_drop_keepsFs (staticSecretDrop_zeroizeSpec_keepsFs_ok hcode)

/-- `.inImage img` variant of `staticSecretDrop_zeroizeSpec_ok`. -/
theorem staticSecretDrop_zeroizeSpec_inImage_ok {P : Program} {addr : BitVec 64} (img : Obj.Image)
    (hcode : hasInstrs P addr zeroize32Instrs) :
    subroutine_ok P addr (zeroizeSpec.inImage img) :=
  subroutine_ok_inImage img (staticSecretDrop_zeroizeSpec_ok hcode)

/-- `hasWords` corollary of `zeroize32_zeroizeSecretSpec_ok`. -/
theorem zeroize32_zeroizeSecretSpec_hasWords_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr zeroize32Words) :
    subroutine_ok P addr zeroizeSecretSpec :=
  zeroize32_zeroizeSecretSpec_ok (hasInstrs_of_hasWords hc)

/-- `hasWords` corollary of `staticSecretDrop_zeroizeSpec_ok`. -/
theorem staticSecretDrop_zeroizeSpec_hasWords_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr zeroize32Words) :
    subroutine_ok P addr zeroizeSpec :=
  staticSecretDrop_zeroizeSpec_ok (hasInstrs_of_hasWords hc)

/-- Full `ProcessFieldsPreserved` unstacked bridge for `zeroize32Words` at `addr` on a hook-free
    program `P`. -/
theorem zeroize32_zeroizeSecretProcessSpec_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      { zeroizeSecretSpec with
        post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ zeroizeSecretSpec.post x s0 sf } :=
  subroutine_ok_lift_pureWords_process
    (zeroize32_zeroizeSecretSpec_ok (pureWordsProg_hasInstrs_zeroize32 addr))
    (pureWordsProg_noSvcMsr_zeroize32 addr) hc h_no_ext
    (h_pre_mem := by intro _ s _; cases s; rfl)
    (h_post_mem := by intro _ s0 sf _ _; cases s0; cases sf; rfl)

/-- Process- and VM-preserving unstacked `keepsFs` bridge: `zeroize32Words` at `addr` on a
    hook-free program satisfies `keepsFs (withVmPreserved zeroizeSecretSpec)`. -/
theorem zeroize32_zeroizeSecretBudgetSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withVmPreserved zeroizeSecretSpec)) :=
  subroutine_ok_keepsFs_withVmPreserved_of_pureWords
    (zeroize32_zeroizeSecretSpec_ok (pureWordsProg_hasInstrs_zeroize32 addr))
    (pureWordsProg_noSvcMsr_zeroize32 addr) hc h_no_ext

/-- Process- and VM-preserving unstacked bridge: `zeroize32Words` at `addr` on a hook-free
    program satisfies `withVmPreserved zeroizeSecretSpec` (`rfl`/defeq-equal by body to
    `DhStepBudgetSteps.zeroizeSecretBudgetSpec`; exact consumer spec of `Initiate/HooksPlacedBudget`,
    `CliHookSatPlacedBudget`, `ResponderCore/CryptoCalleesPlacedBudget`, `AgreeBudget`,
    `CreateChainBudget`, `DhStepBudgetSteps`, `DhStep433PlacedBudget`, and `RootTrapPlacedBudgetPart4`). -/
theorem zeroize32_zeroizeSecretBudgetSpec_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withVmPreserved zeroizeSecretSpec) :=
  subroutine_ok_drop_keepsFs (zeroize32_zeroizeSecretBudgetSpec_keepsFs_ok hc h_no_ext)

/-- Process-, VM-, and `FsState`-predicate-preserving unstacked bridge: `zeroize32Words` at `addr`
    on a hook-free program satisfies `withFsPred Pfs (withVmPreserved zeroizeSecretSpec)` (exact
    consumer spec of `AgreeBudgetFd`, `CreateChainBudgetFd`, and `ResponderCore/CryptoBridgePlacedBudgetFd`). -/
theorem zeroize32_zeroizeSecretBudgetSpec_withFsPred_ok {P : Program} {addr : BitVec 64}
    (Pfs : FsState → Prop)
    (hc : P.hasWords addr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)) :=
  subroutine_ok_withFsPred_of_keepsFs Pfs (zeroize32_zeroizeSecretBudgetSpec_keepsFs_ok hc h_no_ext)

/-- Stack-parameterized `keepsFs` + `withVmPreserved` bridge for `StaticSecret::drop`. -/
theorem staticSecretDrop_withStack_budget_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hookStack : Nat)
    (hc : P.hasWords addr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withStack (withVmPreserved zeroizeSecretSpec) hookStack)) :=
  subroutine_ok_withStack_keepsFs hookStack (zeroize32_zeroizeSecretBudgetSpec_keepsFs_ok hc h_no_ext)

/-- `keepsFs (withVmPreserved CliExt.zeroizeSpec)` bridge for `StaticSecret::drop`. -/
theorem staticSecretDrop_zeroizeBudgetSpec_keepsFs_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withVmPreserved zeroizeSpec)) :=
  subroutine_ok_keepsFs_withVmPreserved_of_pureWords
    (staticSecretDrop_zeroizeSpec_ok (pureWordsProg_hasInstrs_zeroize32 addr))
    (pureWordsProg_noSvcMsr_zeroize32 addr) hc h_no_ext

/-- `withVmPreserved CliExt.zeroizeSpec` bridge for `StaticSecret::drop`. -/
theorem staticSecretDrop_zeroizeBudgetSpec_ok {P : Program} {addr : BitVec 64}
    (hc : P.hasWords addr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withVmPreserved zeroizeSpec) :=
  subroutine_ok_drop_keepsFs (staticSecretDrop_zeroizeBudgetSpec_keepsFs_ok hc h_no_ext)

/-! ## 4. Row 26 (`SharedSecret::drop` `1`-Instruction Tail-Jump) -/

/-- Generic tail-jump combinator: a single unconditional `b (targetAddr - addr)` at `addr`
    inherits any PC-independent, non-panicking, non-exiting, non-OOM
    `subroutine_ok P targetAddr spec`. -/
theorem tailJump_subroutine_ok {α : Type} {P : Program} {addr targetAddr : BitVec 64}
    {spec : Spec α}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : subroutine_ok P targetAddr spec)
    (hpre_pc : ∀ x s pc, spec.pre x (s.setPC pc) = spec.pre x s := by intro _ s _; cases s; rfl)
    (hpost_pc : ∀ x s pc sf, spec.post x (s.setPC pc) sf = spec.post x s sf := by
      intro _ s _ _; cases s; rfl)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    subroutine_ok P addr spec := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hsp
  refine ⟨spec.pre x s0, hpre, ?_⟩
  have hf0 := fetch_at0 hb
  wp_step
  conv in State.setPC _ _ =>
    arg 2
    rw [show addr + (targetAddr - addr) = targetAddr by bv_omega]
  apply SepWP.call_subroutine_frame (ret_pc := s0.readReg64 .lr) htgt (x := x) (F := emp)
      (h_oom := fun R' sf _ ho => by
        rw [hoom] at ho
        exact False.elim (not_satisfies_false_sepConj ho))
  · rfl
  · exact hrun
  · exact hsp
  · rfl
  · intro R' hm_mid
    rw [emp_sepConj, hpre_pc]
    exact hm_mid
  · intro R' sf _ hp
    rw [hpan] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    rw [hex] at he
    exact not_satisfies_false_sepConj he
  · intro sf hpc_f hrun_f hsp_f hcs_f
    rw [sepConj_emp, hpost_pc]
    apply SepWP.done hpc_f hrun_f
    exact ⟨fun hm => hm, hsp_f, hcs_f⟩

/-- Unstacked `keepsFs` bridge for `SharedSecret::drop` (`0` stack bytes required), given
    `<MontgomeryPoint as Zeroize>::zeroize` (`zeroize32Instrs`) loaded at `targetAddr`. -/
theorem sharedSecretDrop_zeroizeSecretSpec_keepsFs_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : hasInstrs P targetAddr zeroize32Instrs) :
    subroutine_ok P addr (keepsFs zeroizeSecretSpec) :=
  tailJump_subroutine_ok hb (zeroize32_zeroizeSecretSpec_keepsFs_ok htgt)

/-- Unstacked bridge for `SharedSecret::drop` (`zeroizeSecretSpec`), matching placed callers in
    `Initiate/HooksPlaced`, `ResponderCore/CryptoCalleesPlaced`, and `TripleRatchet/Keys/Agree`. -/
theorem sharedSecretDrop_zeroizeSecretSpec_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : hasInstrs P targetAddr zeroize32Instrs) :
    subroutine_ok P addr zeroizeSecretSpec :=
  tailJump_subroutine_ok hb (zeroize32_zeroizeSecretSpec_ok htgt)

/-- `withFsPred Pfs` variant of `sharedSecretDrop_zeroizeSecretSpec_ok`. -/
theorem sharedSecretDrop_zeroizeSecretSpec_withFsPred_ok {P : Program}
    {addr targetAddr : BitVec 64} (Pfs : FsState → Prop)
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : hasInstrs P targetAddr zeroize32Instrs) :
    subroutine_ok P addr (withFsPred Pfs zeroizeSecretSpec) :=
  tailJump_subroutine_ok hb (zeroize32_zeroizeSecretSpec_withFsPred_ok Pfs htgt)

/-- Primary `keepsFs` bridge for `cliHookTable` row 26: `SharedSecret::drop` at `addr`
    tail-jumping to `MontgomeryPoint::zeroize` (`zeroize32Instrs`) at `targetAddr` satisfies
    `keepsFs CliExt.zeroizeSpec`. -/
theorem sharedSecretDrop_zeroizeSpec_keepsFs_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : hasInstrs P targetAddr zeroize32Instrs) :
    subroutine_ok P addr (keepsFs zeroizeSpec) :=
  tailJump_subroutine_ok hb (staticSecretDrop_zeroizeSpec_keepsFs_ok htgt)

/-- Primary bridge for `cliHookTable` row 26 (`CliExternsOk.sharedDrop`): `SharedSecret::drop` at
    `addr` tail-jumping to `MontgomeryPoint::zeroize` (`zeroize32Instrs`) at `targetAddr` satisfies
    `CliExt.zeroizeSpec`. -/
theorem sharedSecretDrop_zeroizeSpec_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : hasInstrs P targetAddr zeroize32Instrs) :
    subroutine_ok P addr zeroizeSpec :=
  tailJump_subroutine_ok hb (staticSecretDrop_zeroizeSpec_ok htgt)

/-- `.inImage img` variant of `sharedSecretDrop_zeroizeSpec_ok`. -/
theorem sharedSecretDrop_zeroizeSpec_inImage_ok {P : Program}
    {addr targetAddr : BitVec 64} (img : Obj.Image)
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : hasInstrs P targetAddr zeroize32Instrs) :
    subroutine_ok P addr (zeroizeSpec.inImage img) :=
  subroutine_ok_inImage img (sharedSecretDrop_zeroizeSpec_ok hb htgt)

/-- `hasWords` target corollary of `sharedSecretDrop_zeroizeSecretSpec_ok`. -/
theorem sharedSecretDrop_zeroizeSecretSpec_hasWords_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : P.hasWords targetAddr zeroize32Words) :
    subroutine_ok P addr zeroizeSecretSpec :=
  sharedSecretDrop_zeroizeSecretSpec_ok hb (hasInstrs_of_hasWords htgt)

/-- `hasWords` target corollary of `sharedSecretDrop_zeroizeSpec_ok`. -/
theorem sharedSecretDrop_zeroizeSpec_hasWords_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : P.hasWords targetAddr zeroize32Words) :
    subroutine_ok P addr zeroizeSpec :=
  sharedSecretDrop_zeroizeSpec_ok hb (hasInstrs_of_hasWords htgt)

/-- Full `ProcessFieldsPreserved` unstacked bridge for `SharedSecret::drop` on a hook-free `P`. -/
theorem sharedSecretDrop_zeroizeSecretProcessSpec_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : P.hasWords targetAddr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr
      { zeroizeSecretSpec with
        post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ zeroizeSecretSpec.post x s0 sf } :=
  tailJump_subroutine_ok hb (zeroize32_zeroizeSecretProcessSpec_ok htgt h_no_ext)

/-- Process- and VM-preserving unstacked `keepsFs` bridge for `SharedSecret::drop`, given
    `hasInstrs` for the `1`-insn tail-branch at `addr` and `hasWords` for
    `<MontgomeryPoint as Zeroize>::zeroize` (`zeroize32Words`) at `targetAddr` on a hook-free `P`. -/
theorem sharedSecretDrop_zeroizeSecretBudgetSpec_keepsFs_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : P.hasWords targetAddr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withVmPreserved zeroizeSecretSpec)) :=
  tailJump_subroutine_ok hb (zeroize32_zeroizeSecretBudgetSpec_keepsFs_ok htgt h_no_ext)

/-- Process- and VM-preserving unstacked bridge for `SharedSecret::drop` (`withVmPreserved zeroizeSecretSpec`,
    `rfl`/defeq-equal by body to `DhStepBudgetSteps.zeroizeSecretBudgetSpec`), matching placed callers in
    `Initiate/HooksPlacedBudget`, `CliHookSatPlacedBudget`, `ResponderCore/CryptoCalleesPlacedBudget`,
    `AgreeBudget`, `CreateChainBudget`, `DhStepBudgetSteps`, `DhStep433PlacedBudget`, and
    `RootTrapPlacedBudgetPart4`. -/
theorem sharedSecretDrop_zeroizeSecretBudgetSpec_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : P.hasWords targetAddr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withVmPreserved zeroizeSecretSpec) :=
  tailJump_subroutine_ok hb (zeroize32_zeroizeSecretBudgetSpec_ok htgt h_no_ext)

/-- Process-, VM-, and `FsState`-predicate-preserving unstacked bridge for `SharedSecret::drop`
    (`withFsPred Pfs (withVmPreserved zeroizeSecretSpec)`), matching placed callers in
    `AgreeBudgetFd`, `CreateChainBudgetFd`, and `ResponderCore/CryptoBridgePlacedBudgetFd`. -/
theorem sharedSecretDrop_zeroizeSecretBudgetSpec_withFsPred_ok {P : Program}
    {addr targetAddr : BitVec 64} (Pfs : FsState → Prop)
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : P.hasWords targetAddr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)) :=
  tailJump_subroutine_ok hb (zeroize32_zeroizeSecretBudgetSpec_withFsPred_ok Pfs htgt h_no_ext)

/-- Stack-parameterized `keepsFs` + `withVmPreserved` bridge for `SharedSecret::drop`. -/
theorem sharedSecretDrop_withStack_budget_keepsFs_ok {P : Program}
    {addr targetAddr : BitVec 64} (hookStack : Nat)
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : P.hasWords targetAddr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withStack (withVmPreserved zeroizeSecretSpec) hookStack)) :=
  tailJump_subroutine_ok hb (staticSecretDrop_withStack_budget_keepsFs_ok hookStack htgt h_no_ext)

/-- `keepsFs (withVmPreserved CliExt.zeroizeSpec)` bridge for `SharedSecret::drop`. -/
theorem sharedSecretDrop_zeroizeBudgetSpec_keepsFs_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : P.hasWords targetAddr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (keepsFs (withVmPreserved zeroizeSpec)) :=
  tailJump_subroutine_ok hb (staticSecretDrop_zeroizeBudgetSpec_keepsFs_ok htgt h_no_ext)

/-- `withVmPreserved CliExt.zeroizeSpec` bridge for `SharedSecret::drop`. -/
theorem sharedSecretDrop_zeroizeBudgetSpec_ok {P : Program}
    {addr targetAddr : BitVec 64}
    (hb : hasInstrs P addr (sharedSecretDropInstrs addr targetAddr))
    (htgt : P.hasWords targetAddr zeroize32Words)
    (h_no_ext : ∀ pc, P.externAt? pc = none) :
    subroutine_ok P addr (withVmPreserved zeroizeSpec) :=
  tailJump_subroutine_ok hb (staticSecretDrop_zeroizeBudgetSpec_ok htgt h_no_ext)

end LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop
