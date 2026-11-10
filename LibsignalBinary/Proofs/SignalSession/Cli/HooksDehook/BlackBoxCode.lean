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
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode -- proof-setup: allow-public-import

/-!
# Region-Local `subtle::black_box::<u8>` Code Verification & Master Spec (`HooksDehook.BlackBoxCode`)

Design-independent Stage `a1` (`D1-a1`) for de-hooking `subtle::black_box::<u8>`
(`lsBlackBoxSym` / `lsBlackBoxU8Sym` in `cliHookTablePlaced`, `5` words = `20` bytes
`blackBoxU8Words`, `16` bytes stack frame, no `lr` save; code identity on the stock binary comes
from the untrusted Stage `a2` card + K3(b), with no trusted placed-lib entry):

1. **Permission-free master contract (`masterBlackBoxSpec`), full-permission process contract
   (`processBlackBoxSpec`), `withVmPreserved` bundle (`masterBlackBoxBudgetSpec`), and `K`-narrowing
   (`blackBoxSpecK`)**:
   `masterBlackBoxSpec` refines `withStack LibsignalTripleRatchet.blackBoxSpec 16` by recording
   `BlackBoxStatePreserved` (`abbrev` of `MemsetStatePreserved`: `fs`, `trace`, `tpidrEl0`,
   `sigActions`, `brk`, `brkStart`, `physMemAvail`), omitting `mem.perm` so Stage `b`
   (`BlackBoxGhost`) can prove `SpecStripSInvariant`, while `processBlackBoxSpec` has the identical
   `pre` and carries full `ProcessFieldsPreserved` (including `mem.perm`) so Stage `b` can derive
   `VmPreserved` on real runs (`activeRealRun_stdStatePreserved`).
2. **Placement-generic `pureWordsProg` `hasWords` and region-local `subroutine_ok`**:
   Proves `subroutine_ok P_sub entry` for `processBlackBoxSpec`, `masterBlackBoxSpec`,
   `blackBoxSpecK keep masterBlackBoxSpec`, and `masterBlackBoxBudgetSpec` on any hook-free `P_sub`
   with `P_sub.hasWords entry blackBoxU8Words`.
3. **`W`-independent fallback idealized hook soundness (`blackBoxHook_masterBlackBox_ok`)**:
   Proves that `LibsignalSession.blackBoxHook` (with no `CliHooks` parameter) satisfies
   `processBlackBoxSpec`, `masterBlackBoxSpec`, `blackBoxSpecK keep masterBlackBoxSpec`, and
   `masterBlackBoxBudgetSpec`.
4. **`HookOk` consequence lifts to every honest (`16 ≤ hookStack ≤ 2 ^ 64`) consumer contract**:
   Covers `withStack LibsignalTripleRatchet.blackBoxSpec 16`,
   `withStack LibsignalTripleRatchet.blackBoxSpec hookStack`,
   `withStack blackBoxU8Spec hookStack`, `cliBlackBoxSpec hookStack`, and `CliExt.blackBoxSpec`
   (including `FindReceiverChainIndex.blackBoxSpec32` up to defeq by body), plus `.keepsFs`,
   `withFsPred Pfs`, `withVmPreserved`, and `blackBoxSpecK` variants.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxCode

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (withStack extHookStack)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)
open LibsignalBinary.Heap.Fine (
  hookOk_withVmPreserved blackBoxHook_vmPreserved
)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (withFsPred)
open LibsignalBinary.Proofs.HookDischarge.Generics.BlackBoxU8 (
  blackBoxU8Words cliBlackBoxSpec blackBoxU8Spec
  cliBlackBoxSpec_extHookStack blackBoxU8_16_processSpec_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  MemsetStatePreserved memsetSpecK
  pureWordsProg_externAt_none
  hookOk_frame_pureAbort hookOk_memsetSpecK_of_plain hookOk_memsetSpecK_frame_pureAbort
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode (
  hookOk_withFsPred_of_keepsFs
)

/-! ## 1. Master `black_box::<u8>` Specification & State Preservation -/

/-- Non-memory process/VM state fields preserved across real `subtle::black_box::<u8>`
    (`blackBoxU8Words`) and fallback `blackBoxHook`, reusing `MemsetStatePreserved` via `abbrev`
    and omitting `mem.perm` so Stage `b` (`BlackBoxGhost`) can prove `SpecStripSInvariant`. -/
abbrev BlackBoxStatePreserved : State → State → Prop := MemsetStatePreserved

theorem BlackBoxStatePreserved.refl (s : State) : BlackBoxStatePreserved s s :=
  MemsetStatePreserved.refl s

theorem BlackBoxStatePreserved.of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : BlackBoxStatePreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem BlackBoxStatePreserved.toProcessFieldsPreserved {s0 sf : State}
    (h : BlackBoxStatePreserved s0 sf) (hvm : VmPreserved s0 sf) :
    ProcessFieldsPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, hvm.2.2.1⟩

/-- Permission-free master specification for `subtle::black_box::<u8>`: requires `16` bytes of
    writable stack (`stackAt s0.sp 16`), masks `x0` to its low byte zero-extended to `64` bits,
    preserves `BlackBoxStatePreserved`, and never panics, exits, or OOMs. -/
@[expose] def masterBlackBoxSpec : Spec (BitVec 64) where
  pre := fun v s0 =>
    ⌜s0.readReg64 .x0 = v⌝ ∗ stackAt s0.sp 16
  post := fun v s0 sf =>
    ⌜sf.readReg64 .x0 = (v.setWidth 8).zeroExtend 64 ∧ BlackBoxStatePreserved s0 sf⌝ ∗
      stackAt s0.sp 16
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Full-permission process specification for `subtle::black_box::<u8>`: identical `pre` to
    `masterBlackBoxSpec`, strengthening `post` to full `ProcessFieldsPreserved` (`mem.perm`
    included) so Stage `b` (`BlackBoxGhost`) can derive `VmPreserved` on real runs. -/
@[expose] def processBlackBoxSpec : Spec (BitVec 64) where
  pre := fun v s0 =>
    ⌜s0.readReg64 .x0 = v⌝ ∗ stackAt s0.sp 16
  post := fun v s0 sf =>
    ⌜sf.readReg64 .x0 = (v.setWidth 8).zeroExtend 64 ∧ ProcessFieldsPreserved s0 sf⌝ ∗
      stackAt s0.sp 16
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- `processBlackBoxSpec.pre` is definitionally `masterBlackBoxSpec.pre`. -/
theorem processBlackBox_pre_eq_masterBlackBox_pre :
    processBlackBoxSpec.pre = masterBlackBoxSpec.pre := rfl

/-- Precondition identity helper matching `MemsetCode.stdMemset_pre_of_masterMemset_pre`. -/
theorem processBlackBox_pre_of_masterBlackBox_pre {v : BitVec 64} {R : SepProp} {s0 : State}
    (hp : s0.mem ⊨ masterBlackBoxSpec.pre v s0 ∗ R) :
    s0.mem ⊨ processBlackBoxSpec.pre v s0 ∗ R := hp

/-- `withVmPreserved` bundle of `masterBlackBoxSpec` (`withVmPreserved (withStack blackBoxSpec 16)`
    with `BlackBoxStatePreserved`). -/
abbrev masterBlackBoxBudgetSpec : Spec (BitVec 64) :=
  withVmPreserved masterBlackBoxSpec

/-- `K`-route precondition narrowing (`⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre`), reusing
    `MemsetCode.memsetSpecK` via `abbrev`. -/
abbrev blackBoxSpecK (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) : Spec α :=
  memsetSpecK keep spec

/-! ## 2. Placement-Generic `pureWordsProg` & Region-Local `subroutine_ok` -/

/-- Placement-generic `hasWords` witness for `pureWordsProg base blackBoxU8Words`. -/
theorem pureWordsProg_blackBoxU8_hasWords (base : BitVec 64) :
    (pureWordsProg base blackBoxU8Words).hasWords base blackBoxU8Words :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range blackBoxU8Words.length).all fun i =>
      (pureWordsProg 0#64 blackBoxU8Words).readWordOff (4 * i) == blackBoxU8Words[i]?) = true
    decide +kernel)

/-- Full-permission region-local `subroutine_ok` for `processBlackBoxSpec` on any hook-free `P_sub`
    holding `blackBoxU8Words` at `entry`. -/
theorem subroutine_ok_processBlackBox_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry blackBoxU8Words) :
    subroutine_ok P_sub entry processBlackBoxSpec := by
  refine subroutine_ok_mono (blackBoxU8_16_processSpec_ok hwords hsub_no)
    (fun _ _ _ hp => hp)
    (fun v R s0 sf hq => ?_)
  dsimp only [LibsignalBinary.Proofs.HookDischarge.Libc.Common.withStack,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec, processBlackBoxSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.2.1.1, hq.1⟩, hq.2.2⟩

/-- `K`-narrowed full-permission region-local `subroutine_ok` for `processBlackBoxSpec`. -/
theorem subroutine_ok_processBlackBoxK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry blackBoxU8Words) :
    subroutine_ok P_sub entry (blackBoxSpecK keep processBlackBoxSpec) := by
  refine subroutine_ok_mono (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords)
    (fun _ R s0 hp => ?_)
    (fun _ _ _ _ hq => hq)
  dsimp only [blackBoxSpecK, memsetSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Region-local `subroutine_ok` for `masterBlackBoxSpec` on any hook-free `P_sub` holding
    `blackBoxU8Words` at `entry`. -/
theorem subroutine_ok_masterBlackBox_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry blackBoxU8Words) :
    subroutine_ok P_sub entry masterBlackBoxSpec := by
  refine subroutine_ok_mono (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords)
    (fun _ _ _ hp => hp)
    (fun v R s0 sf hq => ?_)
  dsimp only [processBlackBoxSpec, masterBlackBoxSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, BlackBoxStatePreserved.of_processFieldsPreserved hq.1.2⟩, hq.2⟩

/-- Region-local `subroutine_ok` for `blackBoxSpecK keep masterBlackBoxSpec` on any hook-free
    `P_sub` holding `blackBoxU8Words`. -/
theorem subroutine_ok_masterBlackBoxK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry blackBoxU8Words) :
    subroutine_ok P_sub entry (blackBoxSpecK keep masterBlackBoxSpec) := by
  refine subroutine_ok_mono (subroutine_ok_masterBlackBox_of_hasWords hsub_no hwords)
    (fun _ R s0 hp => ?_)
    (fun _ _ _ _ hq => hq)
  dsimp only [blackBoxSpecK, memsetSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Region-local `subroutine_ok` for `masterBlackBoxBudgetSpec` (`withVmPreserved masterBlackBoxSpec`)
    on any hook-free `P_sub` holding `blackBoxU8Words`. -/
theorem subroutine_ok_masterBlackBoxBudget_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry blackBoxU8Words) :
    subroutine_ok P_sub entry masterBlackBoxBudgetSpec := by
  refine subroutine_ok_mono (subroutine_ok_processBlackBox_of_hasWords hsub_no hwords)
    (fun _ _ _ hp => hp)
    (fun v R s0 sf hq => ?_)
  dsimp only [processBlackBoxSpec, masterBlackBoxBudgetSpec, withVmPreserved, masterBlackBoxSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨hq.1.2.toVmPreserved,
    ⟨hq.1.1, BlackBoxStatePreserved.of_processFieldsPreserved hq.1.2⟩, hq.2⟩

/-- Placement-generic `pureWordsProg base blackBoxU8Words` satisfies `processBlackBoxSpec`. -/
theorem pureWordsProg_blackBoxU8_processBlackBox_ok (base : BitVec 64) :
    subroutine_ok (pureWordsProg base blackBoxU8Words) base processBlackBoxSpec :=
  subroutine_ok_processBlackBox_of_hasWords
    (pureWordsProg_externAt_none base blackBoxU8Words)
    (pureWordsProg_blackBoxU8_hasWords base)

/-- Placement-generic `pureWordsProg base blackBoxU8Words` satisfies `masterBlackBoxSpec`. -/
theorem pureWordsProg_blackBoxU8_masterBlackBox_ok (base : BitVec 64) :
    subroutine_ok (pureWordsProg base blackBoxU8Words) base masterBlackBoxSpec :=
  subroutine_ok_masterBlackBox_of_hasWords
    (pureWordsProg_externAt_none base blackBoxU8Words)
    (pureWordsProg_blackBoxU8_hasWords base)

/-- Placement-generic `pureWordsProg base blackBoxU8Words` satisfies
    `blackBoxSpecK keep masterBlackBoxSpec`. -/
theorem pureWordsProg_blackBoxU8_masterBlackBoxK_ok (keep : BitVec 64 → Bool) (base : BitVec 64) :
    subroutine_ok (pureWordsProg base blackBoxU8Words) base
      (blackBoxSpecK keep masterBlackBoxSpec) :=
  subroutine_ok_masterBlackBoxK_of_hasWords keep
    (pureWordsProg_externAt_none base blackBoxU8Words)
    (pureWordsProg_blackBoxU8_hasWords base)

/-- Placement-generic `pureWordsProg base blackBoxU8Words` satisfies `masterBlackBoxBudgetSpec`. -/
theorem pureWordsProg_blackBoxU8_masterBlackBoxBudget_ok (base : BitVec 64) :
    subroutine_ok (pureWordsProg base blackBoxU8Words) base masterBlackBoxBudgetSpec :=
  subroutine_ok_masterBlackBoxBudget_of_hasWords
    (pureWordsProg_externAt_none base blackBoxU8Words)
    (pureWordsProg_blackBoxU8_hasWords base)

/-! ## 3. `W`-Independent Fallback `blackBoxHook` Soundness -/

/-- The trusted-table idealized hook `LibsignalSession.blackBoxHook` (`W`-independent) satisfies
    `masterBlackBoxSpec` (needed by the ghost hook's fallback branch). -/
theorem blackBoxHook_masterBlackBox_ok :
    HookOk blackBoxHook masterBlackBoxSpec := by
  unfold blackBoxHook
  refine retHook_ok fun v R s0 _ hpre _ => ?_
  simp only [masterBlackBoxSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hv, hstk⟩
  subst hv
  refine ⟨Memory.KeepsFrozen.refl _, rfl, ‹_›,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [masterBlackBoxSpec, retHook]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨rfl, BlackBoxStatePreserved.refl s0⟩, hstk⟩

/-- `blackBoxHook` (`W`-independent) satisfies `blackBoxSpecK keep masterBlackBoxSpec`. -/
theorem blackBoxHook_masterBlackBoxK_ok (keep : BitVec 64 → Bool) :
    HookOk blackBoxHook (blackBoxSpecK keep masterBlackBoxSpec) :=
  hookOk_memsetSpecK_of_plain keep blackBoxHook_masterBlackBox_ok

/-- `blackBoxHook` (`W`-independent) satisfies `masterBlackBoxBudgetSpec`
    (`withVmPreserved masterBlackBoxSpec`). -/
theorem blackBoxHook_masterBlackBoxBudget_ok :
    HookOk blackBoxHook masterBlackBoxBudgetSpec :=
  hookOk_withVmPreserved blackBoxHook_masterBlackBox_ok blackBoxHook_vmPreserved

/-- `blackBoxHook` (`W`-independent) satisfies `blackBoxSpecK keep masterBlackBoxBudgetSpec`. -/
theorem blackBoxHook_masterBlackBoxBudgetK_ok (keep : BitVec 64 → Bool) :
    HookOk blackBoxHook (blackBoxSpecK keep masterBlackBoxBudgetSpec) :=
  hookOk_memsetSpecK_of_plain keep blackBoxHook_masterBlackBoxBudget_ok

/-- `blackBoxHook` (`W`-independent) also satisfies full-permission `processBlackBoxSpec`. -/
theorem blackBoxHook_processBlackBox_ok :
    HookOk blackBoxHook processBlackBoxSpec := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) blackBoxHook_masterBlackBoxBudget_ok
    (fun _ _ => by
      dsimp only [processBlackBoxSpec, masterBlackBoxBudgetSpec, withVmPreserved, masterBlackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterBlackBoxBudgetSpec, withVmPreserved, masterBlackBoxSpec, processBlackBoxSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hvm =>
    Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right ⟨hx0, hst.toProcessFieldsPreserved hvm⟩ (Entails.refl _)

/-! ## 4. Generic `HookOk` Consequence Lifts from `masterBlackBoxSpec` -/

private theorem zeroExtend64_setWidth32_eq (b : BitVec 8) :
    (b.zeroExtend 64).setWidth 32 = b.zeroExtend 32 := by
  bv_omega

private theorem zeroExtend64_setWidth8_eq (b : BitVec 8) :
    (b.zeroExtend 64).setWidth 8 = b := by
  bv_omega

/-- Lift `HookOk f masterBlackBoxSpec` to minimal `16`-byte stack
    `HookOk f (withStack LibsignalTripleRatchet.blackBoxSpec 16)`. -/
theorem hookOk_sessionBlackBox16_of_master {f : State → State}
    (hh : HookOk f masterBlackBoxSpec) :
    HookOk f (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16) := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun _ _ => by
      dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec,
        masterBlackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterBlackBoxSpec, withStack,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun ⟨hx0, hst⟩ =>
    Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- `K`-narrowed lift to `blackBoxSpecK keep (withStack LibsignalTripleRatchet.blackBoxSpec 16)`. -/
theorem hookOk_sessionBlackBox16K_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (blackBoxSpecK keep masterBlackBoxSpec)) :
    HookOk f (blackBoxSpecK keep
      (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16)) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ _ => emp) hh
    (fun _ _ => by
      dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec,
        masterBlackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterBlackBoxSpec, withStack,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun ⟨hx0, hst⟩ =>
    Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _)

/-- Lift `HookOk f masterBlackBoxSpec` to stack-parameterized
    `HookOk f (withStack LibsignalTripleRatchet.blackBoxSpec hookStack)` (`16 ≤ hookStack ≤ 2 ^ 64`). -/
theorem hookOk_sessionBlackBox_of_master {f : State → State} {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f masterBlackBoxSpec) :
    HookOk f (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack) := by
  refine hookOk_frame_pureAbort
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 16)) hh
    (fun _ s0 => by
      dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec,
        masterBlackBoxSpec]
      rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2]
      sep_entail)
    (fun _ s0 _ => ?_)
  dsimp only [masterBlackBoxSpec, withStack,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2, sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hst⟩ =>
    Entails.pure_right ⟨hx0, hst.2.1⟩ (by sep_entail)

/-- `K`-narrowed lift to
    `blackBoxSpecK keep (withStack LibsignalTripleRatchet.blackBoxSpec hookStack)`. -/
theorem hookOk_sessionBlackBoxK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    {hookStack : Nat} (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f (blackBoxSpecK keep masterBlackBoxSpec)) :
    HookOk f (blackBoxSpecK keep
      (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack)) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 16)) hh
    (fun _ s0 => by
      dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec,
        masterBlackBoxSpec]
      rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2]
      sep_entail)
    (fun _ s0 _ => ?_)
  dsimp only [masterBlackBoxSpec, withStack,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2, sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hst⟩ =>
    Entails.pure_right ⟨hx0, hst.2.1⟩ (by sep_entail)

/-- Lift `HookOk f masterBlackBoxSpec` to
    `HookOk f (withStack LibsignalTripleRatchet.blackBoxSpec hookStack).keepsFs`. -/
theorem hookOk_sessionBlackBox_keepsFs_of_master {f : State → State} {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f masterBlackBoxSpec) :
    HookOk f
      (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack).keepsFs := by
  refine hookOk_frame_pureAbort
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 16)) hh
    (fun _ s0 => by
      dsimp only [Arm64.Spec.keepsFs, withStack,
        CryptoVerification.LibsignalTripleRatchet.blackBoxSpec, masterBlackBoxSpec]
      rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2]
      sep_entail)
    (fun _ s0 _ => ?_)
  dsimp only [Arm64.Spec.keepsFs, masterBlackBoxSpec, withStack,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2, sepConj_assoc]
  exact Entails.pure_left fun ⟨hx0, hst⟩ =>
    Entails.pure_right hst.1 (Entails.pure_right ⟨hx0, hst.2.1⟩ (by sep_entail))

/-- Lift `HookOk f masterBlackBoxSpec` to `HookOk f (withStack blackBoxU8Spec hookStack)`
    (`16 ≤ hookStack ≤ 2 ^ 64`; matches `Mac/Verify.lean:278` and `Stage2ContractsExt.lean:301`
    at `hookStack = extHookStack`). -/
theorem hookOk_blackBoxU8_of_master {f : State → State} {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f masterBlackBoxSpec) :
    HookOk f (withStack blackBoxU8Spec hookStack) := by
  refine hookOk_frame_pureAbort (fun _ _ => emp)
    (hookOk_sessionBlackBox_of_master hstk hh)
    (fun _ _ => by
      dsimp only [withStack, blackBoxU8Spec,
        CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun v _ _ => ?_)
  dsimp only [withStack, blackBoxU8Spec,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun ⟨hx0, htr⟩ =>
    Entails.pure_right
      ⟨hx0 ▸ zeroExtend64_setWidth8_eq (v.setWidth 8), htr⟩ (Entails.refl _)

/-- `K`-narrowed lift to `blackBoxSpecK keep (withStack blackBoxU8Spec hookStack)`. -/
theorem hookOk_blackBoxU8K_of_master (keep : BitVec 64 → Bool) {f : State → State}
    {hookStack : Nat} (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f (blackBoxSpecK keep masterBlackBoxSpec)) :
    HookOk f (blackBoxSpecK keep (withStack blackBoxU8Spec hookStack)) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ _ => emp)
    (hookOk_sessionBlackBoxK_of_master keep hstk hh)
    (fun _ _ => by
      dsimp only [withStack, blackBoxU8Spec,
        CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun v _ _ => ?_)
  dsimp only [withStack, blackBoxU8Spec,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun ⟨hx0, htr⟩ =>
    Entails.pure_right
      ⟨hx0 ▸ zeroExtend64_setWidth8_eq (v.setWidth 8), htr⟩ (Entails.refl _)

/-- Lift `HookOk f masterBlackBoxSpec` to `HookOk f (cliBlackBoxSpec hookStack)`
    (`16 ≤ hookStack ≤ 2 ^ 64`). -/
theorem hookOk_cliBlackBox_of_master {f : State → State} {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f masterBlackBoxSpec) :
    HookOk f (cliBlackBoxSpec hookStack) := by
  refine hookOk_frame_pureAbort (fun _ _ => emp)
    (hookOk_sessionBlackBox_of_master hstk hh)
    (fun _ _ => by
      dsimp only [cliBlackBoxSpec, LibsignalBinary.Proofs.HookDischarge.Libc.Common.withStack,
        withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun v _ _ => ?_)
  dsimp only [cliBlackBoxSpec, LibsignalBinary.Proofs.HookDischarge.Libc.Common.withStack,
    withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun ⟨hx0, htr⟩ =>
    Entails.pure_right
      ⟨hx0 ▸ zeroExtend64_setWidth32_eq (v.setWidth 8), htr⟩ (Entails.refl _)

/-- `K`-narrowed lift to `blackBoxSpecK keep (cliBlackBoxSpec hookStack)`. -/
theorem hookOk_cliBlackBoxK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    {hookStack : Nat} (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f (blackBoxSpecK keep masterBlackBoxSpec)) :
    HookOk f (blackBoxSpecK keep (cliBlackBoxSpec hookStack)) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ _ => emp)
    (hookOk_sessionBlackBoxK_of_master keep hstk hh)
    (fun _ _ => by
      dsimp only [cliBlackBoxSpec, LibsignalBinary.Proofs.HookDischarge.Libc.Common.withStack,
        withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun v _ _ => ?_)
  dsimp only [cliBlackBoxSpec, LibsignalBinary.Proofs.HookDischarge.Libc.Common.withStack,
    withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun ⟨hx0, htr⟩ =>
    Entails.pure_right
      ⟨hx0 ▸ zeroExtend64_setWidth32_eq (v.setWidth 8), htr⟩ (Entails.refl _)

/-- Lift `HookOk f masterBlackBoxSpec` to `HookOk f CliExt.blackBoxSpec` (`extHookStack = 16384`;
    also `rfl`/defeq-equal by body to `CtEq.blackBoxSpec32`). -/
theorem hookOk_extBlackBox_of_master {f : State → State}
    (hh : HookOk f masterBlackBoxSpec) :
    HookOk f CryptoVerification.SignalSession.CliExt.blackBoxSpec :=
  cliBlackBoxSpec_extHookStack ▸ hookOk_cliBlackBox_of_master (by decide) hh

/-- `K`-narrowed lift to `blackBoxSpecK keep CliExt.blackBoxSpec`. -/
theorem hookOk_extBlackBoxK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (blackBoxSpecK keep masterBlackBoxSpec)) :
    HookOk f (blackBoxSpecK keep CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  cliBlackBoxSpec_extHookStack ▸ hookOk_cliBlackBoxK_of_master keep (by decide) hh

/-- Lift `HookOk f masterBlackBoxSpec` to `HookOk f CliExt.blackBoxSpec.keepsFs`. -/
theorem hookOk_extBlackBox_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterBlackBoxSpec) :
    HookOk f CryptoVerification.SignalSession.CliExt.blackBoxSpec.keepsFs := by
  refine hookOk_frame_pureAbort (fun _ _ => emp)
    (hookOk_sessionBlackBox_keepsFs_of_master (hookStack := extHookStack) (by decide) hh)
    (fun _ _ => by
      dsimp only [Arm64.Spec.keepsFs, CryptoVerification.SignalSession.CliExt.blackBoxSpec,
        CryptoVerification.SignalSession.CliExt.withStack, withStack,
        CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun v _ _ => ?_)
  dsimp only [Arm64.Spec.keepsFs, CryptoVerification.SignalSession.CliExt.blackBoxSpec,
    CryptoVerification.SignalSession.CliExt.withStack, withStack,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hfs =>
    Entails.pure_left fun ⟨hx0, htr⟩ =>
      Entails.pure_right hfs
        (Entails.pure_right ⟨hx0 ▸ zeroExtend64_setWidth32_eq (v.setWidth 8), htr⟩
          (Entails.refl _))

/-- Lift `HookOk f masterBlackBoxSpec` to `HookOk f (withFsPred Pfs CliExt.blackBoxSpec)`. -/
theorem hookOk_extBlackBox_withFsPred_of_master {f : State → State}
    (Pfs : FsState → Prop) (hh : HookOk f masterBlackBoxSpec) :
    HookOk f (withFsPred Pfs CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  hookOk_withFsPred_of_keepsFs Pfs (hookOk_extBlackBox_keepsFs_of_master hh)

/-! ### 4.1 Budget (`withVmPreserved`) Consumer Lifts -/

/-- Lift `HookOk f masterBlackBoxBudgetSpec` directly to minimal `16`-byte stack
    `HookOk f (withVmPreserved (withStack LibsignalTripleRatchet.blackBoxSpec 16))`. -/
theorem hookOk_sessionBlackBox16Budget_of_masterBudget {f : State → State}
    (hh : HookOk f masterBlackBoxBudgetSpec) :
    HookOk f
      (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16)) := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun _ _ => by
      dsimp only [withVmPreserved, withStack,
        CryptoVerification.LibsignalTripleRatchet.blackBoxSpec,
        masterBlackBoxBudgetSpec, masterBlackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterBlackBoxBudgetSpec, withVmPreserved, masterBlackBoxSpec,
    withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hvm =>
    Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right hvm (Entails.pure_right ⟨hx0, hst.2.1⟩ (Entails.refl _))

/-- Lift `HookOk f masterBlackBoxSpec` + pointwise `VmPreserved` to
    `HookOk f (withVmPreserved (withStack LibsignalTripleRatchet.blackBoxSpec 16))`. -/
theorem hookOk_sessionBlackBox16Budget_of_master {f : State → State}
    (hh : HookOk f masterBlackBoxSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f
      (withVmPreserved (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec 16)) :=
  hookOk_withVmPreserved (hookOk_sessionBlackBox16_of_master hh) hvm

/-- Lift `HookOk f masterBlackBoxBudgetSpec` to
    `HookOk f (withStack (withVmPreserved LibsignalTripleRatchet.blackBoxSpec) hookStack)`
    (`16 ≤ hookStack ≤ 2 ^ 64`). -/
theorem hookOk_sessionBlackBoxBudget_of_masterBudget {f : State → State} {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f masterBlackBoxBudgetSpec) :
    HookOk f
      (withStack (withVmPreserved CryptoVerification.LibsignalTripleRatchet.blackBoxSpec)
        hookStack) := by
  refine hookOk_frame_pureAbort
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - 16)) hh
    (fun _ s0 => by
      dsimp only [withStack, withVmPreserved,
        CryptoVerification.LibsignalTripleRatchet.blackBoxSpec,
        masterBlackBoxBudgetSpec, masterBlackBoxSpec]
      rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2]
      sep_entail)
    (fun _ s0 _ => ?_)
  dsimp only [masterBlackBoxBudgetSpec, withVmPreserved, masterBlackBoxSpec,
    withStack, CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [stackAt_shrink s0.sp hookStack 16 hstk.1 hstk.2]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun hvm =>
    Entails.pure_left fun ⟨hx0, hst⟩ =>
      Entails.pure_right hvm
        (Entails.pure_right ⟨hx0, hst.2.1⟩ (by sep_entail))

/-- Lift `HookOk f masterBlackBoxSpec` + pointwise `VmPreserved` to
    `HookOk f (withStack (withVmPreserved LibsignalTripleRatchet.blackBoxSpec) hookStack)`. -/
theorem hookOk_sessionBlackBoxBudget_of_master {f : State → State} {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f masterBlackBoxSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f
      (withStack (withVmPreserved CryptoVerification.LibsignalTripleRatchet.blackBoxSpec)
        hookStack) :=
  hookOk_sessionBlackBoxBudget_of_masterBudget hstk (hookOk_withVmPreserved hh hvm)

/-- Lift `HookOk f masterBlackBoxSpec` + pointwise `VmPreserved` to outer-wrapped
    `HookOk f (withVmPreserved (withStack LibsignalTripleRatchet.blackBoxSpec hookStack))`. -/
theorem hookOk_vmSessionBlackBox_of_master {f : State → State} {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f masterBlackBoxSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f
      (withVmPreserved
        (withStack CryptoVerification.LibsignalTripleRatchet.blackBoxSpec hookStack)) :=
  hookOk_withVmPreserved (hookOk_sessionBlackBox_of_master hstk hh) hvm

/-- Lift `HookOk f masterBlackBoxBudgetSpec` to
    `HookOk f (withStack (withVmPreserved blackBoxU8Spec) hookStack)` (`16 ≤ hookStack ≤ 2 ^ 64`;
    at `hookStack = extHookStack`, `rfl`/defeq-equal by body to
    `withStack Hooks2Budget.blackBoxU8BudgetSpec extHookStack` in
    `Mac/VerifyMacWithAddressesBudget.lean:1136`). -/
theorem hookOk_blackBoxU8Budget_of_masterBudget {f : State → State} {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f masterBlackBoxBudgetSpec) :
    HookOk f (withStack (withVmPreserved blackBoxU8Spec) hookStack) := by
  refine hookOk_frame_pureAbort (fun _ _ => emp)
    (hookOk_sessionBlackBoxBudget_of_masterBudget hstk hh)
    (fun _ _ => by
      dsimp only [withStack, withVmPreserved, blackBoxU8Spec,
        CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun v _ _ => ?_)
  dsimp only [withStack, withVmPreserved, blackBoxU8Spec,
    CryptoVerification.LibsignalTripleRatchet.blackBoxSpec]
  rw [sepConj_emp]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun hvm =>
    Entails.pure_left fun ⟨hx0, htr⟩ =>
      Entails.pure_right hvm
        (Entails.pure_right
          ⟨hx0 ▸ zeroExtend64_setWidth8_eq (v.setWidth 8), htr⟩ (Entails.refl _))

/-- Lift `HookOk f masterBlackBoxSpec` + pointwise `VmPreserved` to
    `HookOk f (withStack (withVmPreserved blackBoxU8Spec) hookStack)`. -/
theorem hookOk_blackBoxU8Budget_of_master {f : State → State} {hookStack : Nat}
    (hstk : 16 ≤ hookStack ∧ hookStack ≤ 2 ^ 64)
    (hh : HookOk f masterBlackBoxSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withStack (withVmPreserved blackBoxU8Spec) hookStack) :=
  hookOk_blackBoxU8Budget_of_masterBudget hstk (hookOk_withVmPreserved hh hvm)

/-- Lift `HookOk f masterBlackBoxSpec` + pointwise `VmPreserved` to
    `HookOk f (withVmPreserved CliExt.blackBoxSpec)` (`SpecBudget.lean:1104`). -/
theorem hookOk_extBlackBoxBudget_of_master {f : State → State}
    (hh : HookOk f masterBlackBoxSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec) :=
  hookOk_withVmPreserved (hookOk_extBlackBox_of_master hh) hvm

/-- `K`-narrowed lift to `blackBoxSpecK keep (withVmPreserved CliExt.blackBoxSpec)`. -/
theorem hookOk_extBlackBoxBudgetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (blackBoxSpecK keep masterBlackBoxSpec)) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f
      (blackBoxSpecK keep (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec)) :=
  hookOk_withVmPreserved (hookOk_extBlackBoxK_of_master keep hh) hvm

/-- Lift `HookOk f masterBlackBoxSpec` + pointwise `VmPreserved` to
    `HookOk f (withVmPreserved CliExt.blackBoxSpec).keepsFs`. -/
theorem hookOk_extBlackBoxBudget_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterBlackBoxSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec).keepsFs := by
  refine hookOk_frame_pureAbort (fun _ _ => emp)
    (hookOk_withVmPreserved (hookOk_extBlackBox_keepsFs_of_master hh) hvm)
    (fun _ _ => by
      dsimp only [Arm64.Spec.keepsFs, withVmPreserved]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [Arm64.Spec.keepsFs, withVmPreserved]
  rw [sepConj_emp]
  exact Entails.pure_left fun hvm' =>
    Entails.pure_left fun hfs =>
      Entails.pure_right hfs (Entails.pure_right hvm' (Entails.refl _))

/-- Lift `HookOk f masterBlackBoxSpec` + pointwise `VmPreserved` to
    `HookOk f (withFsPred Pfs (withVmPreserved CliExt.blackBoxSpec))`. -/
theorem hookOk_extBlackBoxBudget_withFsPred_of_master {f : State → State}
    (Pfs : FsState → Prop) (hh : HookOk f masterBlackBoxSpec)
    (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f
      (withFsPred Pfs (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec)) :=
  hookOk_withFsPred_of_keepsFs Pfs (hookOk_extBlackBoxBudget_keepsFs_of_master hh hvm)

/-- `blackBoxSpecK keep` commutes definitionally with `.keepsFs`, `withVmPreserved`, and
    `withOomPoolPreserved`. -/
theorem blackBoxSpecK_keepsFs (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    (blackBoxSpecK keep spec).keepsFs = blackBoxSpecK keep spec.keepsFs := rfl

theorem blackBoxSpecK_withVmPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withVmPreserved (blackBoxSpecK keep spec) = blackBoxSpecK keep (withVmPreserved spec) := rfl

theorem blackBoxSpecK_withOomPoolPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withOomPoolPreserved (blackBoxSpecK keep spec) =
      blackBoxSpecK keep (withOomPoolPreserved spec) := rfl

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BlackBoxCode
