/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.SepLogic.WP.StepsProcess
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import

/-!
# Region-Local `zeroize` Drop Code Verification & Master Spec (`HooksDehook.ZeroizeCode`)

Design-independent Stage `a1` (`D23-a1`) for de-hooking both `x25519-dalek` 32-byte zeroize drop
rows of `cliHookTablePlaced` (code identity on the stock binary comes from the untrusted Stage `a2`
card + K3(b), with no trusted placed-lib entry):
- **Row D2 (`<StaticSecret as Drop>::drop`, `lsStaticSecretDropSym`)**: `63` words = `252` bytes
  (`zeroize32Words`), `0` stack bytes, leaf body identical to `<MontgomeryPoint as Zeroize>::zeroize`.
- **Row D3 (`<SharedSecret as Drop>::drop`, `lsSharedSecretDropSym`)**: `1`-word unconditional tail
  branch `b (targetAddr - entry)` into `<MontgomeryPoint as Zeroize>::zeroize` (`zeroize32Words` at
  `targetAddr`), `0` stack bytes. In the stock `.text.lib2` layout, `<MontgomeryPoint as Zeroize>::zeroize`
  (`63` words = `252` bytes at `m`) is immediately followed at `m + 252#64` by `<SharedSecret as Drop>::drop`
  (`1` word `sharedSecretDropBackWord = 0x17ffffc1#32` = `b (m - (m + 252#64))`), forming the single
  contiguous `64`-word (`256`-byte) hull `sharedSecretDropHullWords`.

Contents (mirroring `HooksDehook.MemsetCode`):
1. **Permission-free master contract (`masterZeroizeSpec`), full-permission process contract
   (`processZeroizeSpec`), and `K`-narrowing (`zeroizeSpecK`)**:
   `ZeroizeStatePreserved` reuses `MemsetStatePreserved` (the 7 memory-permission-independent process
   fields `fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`, `physMemAvail`) via `abbrev`,
   omitting `mem.perm` so Stage `b` (`ZeroizeGhost`) can prove `SpecStripSInvariant`, while
   `processZeroizeSpec` has the identical `pre` and carries full `ProcessFieldsPreserved` (including
   `mem.perm`) so Stage `b` can derive `VmPreserved` on real runs (`activeRealRun_stdStatePreserved`).
2. **Placement-generic `pureWordsProg` `hasWords`, contiguous 64-word hull, and region-local `subroutine_ok`**:
   Covers single-block `StaticSecret::drop` (`P_sub.hasWords entry zeroize32Words`), general two-block
   `SharedSecret::drop`, and concrete single-hull `pureWordsProg m sharedSecretDropHullWords` at entry
   `m + 252#64` for `processZeroizeSpec`, `masterZeroizeSpec`, `zeroizeSpecK`, and `masterZeroizeBudgetSpec`.
3. **`W`-independent fallback idealized hook soundness (`zeroizeSecretHook_masterZeroize_ok`)**:
   Proves that `LibsignalTripleRatchet.zeroizeSecretHook` (with no `CliHooks` parameter) satisfies
   `processZeroizeSpec`, `masterZeroizeSpec`, `zeroizeSpecK keep masterZeroizeSpec`, and
   `masterZeroizeBudgetSpec`.
4. **`HookOk` consequence lifts to every consumer contract**:
   Covers `zeroizeSecretSpec`, `.keepsFs`, `withFsPred Pfs`, `withStack … stk`, `CliExt.zeroizeSpec`,
   and all `withVmPreserved` (`zeroizeSecretBudgetSpec`, `cliZeroizeBudgetSpec`) + `zeroizeSpecK`
   variants.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode

open Arm64 ProofLib SepProp
open ProofLib.StdStartup (hasInstrs)
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open CryptoVerification.LibsignalTripleRatchet (
  zeroizeSecretHook zeroizeSecretSpec withStack extHookStack
)
open CryptoVerification.SignalSession.CliExt (zeroizeSpec)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved)
open LibsignalBinary.Heap.Fine (
  hookOk_withVmPreserved zeroizeSecretHook_vmPreserved
)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (
  zeroize32Words zeroize32Instrs sharedSecretDropInstrs withFsPred
  zeroize32_zeroizeSecretProcessSpec_ok
  tailJump_subroutine_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  MemsetStatePreserved memsetSpecK
  pureWordsProg_externAt_none
  hookOk_frame_pureAbort hookOk_memsetSpecK_of_plain hookOk_memsetSpecK_frame_pureAbort
)

/-! ## 1. Master `zeroize` Specification & State Preservation -/

/-- Non-memory process/VM state fields preserved across real `StaticSecret::drop` /
    `SharedSecret::drop` (`zeroize32Words`) and fallback `zeroizeSecretHook`, reusing
    `MemsetStatePreserved` (`fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`,
    `physMemAvail`) and omitting `mem.perm` so Stage `b` (`ZeroizeGhost`) can prove
    `SpecStripSInvariant`. -/
abbrev ZeroizeStatePreserved : State → State → Prop := MemsetStatePreserved

theorem ZeroizeStatePreserved.refl (s : State) : ZeroizeStatePreserved s s :=
  MemsetStatePreserved.refl s

theorem ZeroizeStatePreserved.of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : ZeroizeStatePreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem ZeroizeStatePreserved.toProcessFieldsPreserved {s0 sf : State}
    (h : ZeroizeStatePreserved s0 sf) (hvm : VmPreserved s0 sf) :
    ProcessFieldsPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, hvm.2.2.1⟩

/-- Shared permission-free master specification for `StaticSecret::drop` and `SharedSecret::drop`:
    requires `0` stack bytes (`memRegion a 32` at `x0 = a`), writes `32` zero bytes at `a`,
    preserves `ZeroizeStatePreserved`, and never panics, exits, or OOMs. -/
@[expose] def masterZeroizeSpec : Spec (BitVec 64) where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a⌝ ∗ memRegion a 32
  post := fun a s0 sf =>
    ⌜ZeroizeStatePreserved s0 sf⌝ ∗ (a ↦ₛ List.replicate 32 0#8)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Full-permission process specification for `StaticSecret::drop` and `SharedSecret::drop`:
    identical `pre` to `masterZeroizeSpec`, strengthening `post` to full `ProcessFieldsPreserved`
    (`mem.perm` included) so Stage `b` (`ZeroizeGhost`) can derive `VmPreserved` on real runs. -/
@[expose] def processZeroizeSpec : Spec (BitVec 64) where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a⌝ ∗ memRegion a 32
  post := fun a s0 sf =>
    ⌜ProcessFieldsPreserved s0 sf⌝ ∗ (a ↦ₛ List.replicate 32 0#8)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- `processZeroizeSpec.pre` is definitionally `masterZeroizeSpec.pre`. -/
theorem processZeroize_pre_eq_masterZeroize_pre :
    processZeroizeSpec.pre = masterZeroizeSpec.pre := rfl

/-- Precondition identity helper matching `MemsetCode.stdMemset_pre_of_masterMemset_pre`. -/
theorem processZeroize_pre_of_masterZeroize_pre {a : BitVec 64} {R : SepProp} {s0 : State}
    (hp : s0.mem ⊨ masterZeroizeSpec.pre a s0 ∗ R) :
    s0.mem ⊨ processZeroizeSpec.pre a s0 ∗ R := hp

/-- `withVmPreserved` bundle of `masterZeroizeSpec` (`VmPreserved s0 sf` + `ZeroizeStatePreserved s0 sf`). -/
abbrev masterZeroizeBudgetSpec : Spec (BitVec 64) :=
  withVmPreserved masterZeroizeSpec

/-- `K`-route precondition narrowing (`⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre`), reusing
    `MemsetCode.memsetSpecK` via `abbrev`. -/
abbrev zeroizeSpecK (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) : Spec α :=
  memsetSpecK keep spec

/-! ## 2. Placement-Generic `pureWordsProg`, Contiguous Hull, & Region-Local `subroutine_ok` -/

/-- The `1`-word tail branch `b (pc - 252)` (`0x17ffffc1#32`) emitted for `<SharedSecret as Drop>::drop`
    in the stock `.text.lib2` layout, where `<MontgomeryPoint as Zeroize>::zeroize` (`63` words = `252` B)
    is immediately followed at `+252` by `<SharedSecret as Drop>::drop` (`1` word = `4` B). -/
@[expose] def sharedSecretDropBackWord : BitVec 32 := 0x17ffffc1#32

/-- Single contiguous `64`-word (`256`-byte) hull `zeroize32Words ++ [sharedSecretDropBackWord]`
    holding `<MontgomeryPoint as Zeroize>::zeroize` at `m` and `<SharedSecret as Drop>::drop` at
    `m + 252#64`. -/
@[expose] def sharedSecretDropHullWords : List (BitVec 32) :=
  zeroize32Words ++ [sharedSecretDropBackWord]

private theorem readWordOff_eq_of_code_eq {P Q : Program} (h : P.code = Q.code) (off : Nat) :
    P.readWordOff off = Q.readWordOff off := by
  unfold Program.readWordOff
  rw [h]

/-- Placement-generic `hasWords` witness for `pureWordsProg base zeroize32Words`. -/
theorem pureWordsProg_zeroize32_hasWords (base : BitVec 64) :
    (pureWordsProg base zeroize32Words).hasWords base zeroize32Words :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range zeroize32Words.length).all fun i =>
      (pureWordsProg 0#64 zeroize32Words).readWordOff (4 * i) == zeroize32Words[i]?) = true
    decide +kernel)

/-- Concrete `hasWords` witness for `zeroize32Words` at offset `0` (`m`) inside the `64`-word
    contiguous hull `pureWordsProg m sharedSecretDropHullWords`. -/
theorem pureWordsProg_sharedSecretDropHull_zeroize_hasWords (m : BitVec 64) :
    (pureWordsProg m sharedSecretDropHullWords).hasWords m zeroize32Words := by
  unfold Program.hasWords Program.hasWordsOff
  have hsub : (m - (pureWordsProg m sharedSecretDropHullWords).base).toNat = 0 := by
    change (m - m).toNat = 0; simp
  have hcheck : ((List.range zeroize32Words.length).all fun i =>
      (pureWordsProg 0#64 sharedSecretDropHullWords).readWordOff (4 * i) ==
        zeroize32Words[i]?) = true := by
    decide +kernel
  rw [hsub, Nat.zero_add]
  refine ⟨by decide, fun i hi => ?_, ⟨rfl, rfl⟩⟩
  have hmem : i ∈ List.range zeroize32Words.length := List.mem_range.mpr hi
  have hall := beq_iff_eq.mp (List.all_eq_true.mp hcheck i hmem)
  have hcode : (pureWordsProg m sharedSecretDropHullWords).code =
      (pureWordsProg 0#64 sharedSecretDropHullWords).code := rfl
  rw [Nat.zero_add, readWordOff_eq_of_code_eq hcode, hall, List.getElem?_eq_getElem hi]

/-- Concrete `hasWords` witness for `[sharedSecretDropBackWord]` at offset `252` (`m + 252#64`)
    inside the `64`-word contiguous hull `pureWordsProg m sharedSecretDropHullWords`. -/
theorem pureWordsProg_sharedSecretDropHull_drop_hasWords (m : BitVec 64) :
    (pureWordsProg m sharedSecretDropHullWords).hasWords (m + 252#64)
      [sharedSecretDropBackWord] := by
  unfold Program.hasWords Program.hasWordsOff
  have hsub : (m + 252#64 - (pureWordsProg m sharedSecretDropHullWords).base).toNat = 252 := by
    change (m + 252#64 - m).toNat = 252
    have hb : m + 252#64 - m = 252#64 := by bv_omega
    rw [hb]; rfl
  have hcheck : (pureWordsProg 0#64 sharedSecretDropHullWords).readWordOff 252 =
      some sharedSecretDropBackWord := by
    decide +kernel
  rw [hsub]
  refine ⟨by decide, fun i hi => ?_, ⟨rfl, rfl⟩⟩
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  have hcode : (pureWordsProg m sharedSecretDropHullWords).code =
      (pureWordsProg 0#64 sharedSecretDropHullWords).code := rfl
  simpa [readWordOff_eq_of_code_eq hcode] using hcheck

/-- `sharedSecretDropBackWord` (`0x17ffffc1#32`) decodes to `b (m - (m + 252#64))` for any `m`. -/
theorem decode_sharedSecretDropBackWord (m : BitVec 64) :
    decode sharedSecretDropBackWord = some (.b (m - (m + 252#64))) := by
  have hdiff : m - (m + 252#64) = -252#64 := by bv_omega
  have hdec0 : decode sharedSecretDropBackWord = some (.b (-252#64)) := by decide +kernel
  rw [hdiff]
  exact hdec0

/-- Decode a 1-word `hasWords` hypothesis at `entry` into `hasInstrs P_sub entry (sharedSecretDropInstrs entry targetAddr)`. -/
theorem hasInstrs_sharedSecretDrop_of_hasWords {P_sub : Program}
    {entry targetAddr : BitVec 64} {bWord : BitVec 32}
    (hb_words : P_sub.hasWords entry [bWord])
    (hdec : decode bWord = some (.b (targetAddr - entry))) :
    hasInstrs P_sub entry (sharedSecretDropInstrs entry targetAddr) := by
  intro i hi
  have hi0 : i = 0 := by
    dsimp only [sharedSecretDropInstrs, List.length_singleton] at hi
    omega
  subst hi0
  exact Program.fetch_of_hasWords_decodeAt 0 hb_words rfl hdec

/-- Concrete `hasInstrs` witness at `m + 252#64` inside `pureWordsProg m sharedSecretDropHullWords`. -/
theorem pureWordsProg_sharedSecretDropHull_drop_hasInstrs (m : BitVec 64) :
    hasInstrs (pureWordsProg m sharedSecretDropHullWords) (m + 252#64)
      (sharedSecretDropInstrs (m + 252#64) m) :=
  hasInstrs_sharedSecretDrop_of_hasWords
    (pureWordsProg_sharedSecretDropHull_drop_hasWords m)
    (decode_sharedSecretDropBackWord m)

/-- **Row D2 (`StaticSecret::drop` / `MontgomeryPoint::zeroize`)**: full-permission region-local
    `subroutine_ok` for `processZeroizeSpec` on any hook-free `P_sub` holding `zeroize32Words`. -/
theorem subroutine_ok_processZeroize_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry zeroize32Words) :
    subroutine_ok P_sub entry processZeroizeSpec := by
  refine subroutine_ok_mono (zeroize32_zeroizeSecretProcessSpec_ok hwords hsub_no)
    (fun _ _ _ hp => hp)
    (fun a R s0 sf hq => ?_)
  dsimp only [zeroizeSecretSpec, processZeroizeSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨hq.1, hq.2.2⟩

/-- **Row D2 (`StaticSecret::drop`)**: `K`-narrowed full-permission region-local `subroutine_ok`. -/
theorem subroutine_ok_processZeroizeK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry zeroize32Words) :
    subroutine_ok P_sub entry (zeroizeSpecK keep processZeroizeSpec) := by
  refine subroutine_ok_mono (subroutine_ok_processZeroize_of_hasWords hsub_no hwords)
    (fun _ R s0 hp => ?_)
    (fun _ _ _ _ hq => hq)
  dsimp only [zeroizeSpecK, memsetSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- **Row D2 (`StaticSecret::drop` / `MontgomeryPoint::zeroize`)**: region-local `subroutine_ok`
    for `masterZeroizeSpec` on any hook-free `P_sub` holding `zeroize32Words` at `entry`. -/
theorem subroutine_ok_masterZeroize_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry zeroize32Words) :
    subroutine_ok P_sub entry masterZeroizeSpec := by
  refine subroutine_ok_mono (subroutine_ok_processZeroize_of_hasWords hsub_no hwords)
    (fun _ _ _ hp => hp)
    (fun a R s0 sf hq => ?_)
  dsimp only [processZeroizeSpec, masterZeroizeSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨ZeroizeStatePreserved.of_processFieldsPreserved hq.1, hq.2⟩

/-- **Row D2 (`StaticSecret::drop`)**: region-local `subroutine_ok` for
    `zeroizeSpecK keep masterZeroizeSpec` on any hook-free `P_sub` holding `zeroize32Words`. -/
theorem subroutine_ok_masterZeroizeK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry zeroize32Words) :
    subroutine_ok P_sub entry (zeroizeSpecK keep masterZeroizeSpec) := by
  refine subroutine_ok_mono (subroutine_ok_masterZeroize_of_hasWords hsub_no hwords)
    (fun _ R s0 hp => ?_)
    (fun _ _ _ _ hq => hq)
  dsimp only [zeroizeSpecK, memsetSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- **Row D2 (`StaticSecret::drop`)**: region-local `subroutine_ok` for `masterZeroizeBudgetSpec`
    (`withVmPreserved masterZeroizeSpec`) on any hook-free `P_sub` holding `zeroize32Words`. -/
theorem subroutine_ok_masterZeroizeBudget_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry zeroize32Words) :
    subroutine_ok P_sub entry masterZeroizeBudgetSpec := by
  refine subroutine_ok_mono (subroutine_ok_processZeroize_of_hasWords hsub_no hwords)
    (fun _ _ _ hp => hp)
    (fun a R s0 sf hq => ?_)
  dsimp only [processZeroizeSpec, masterZeroizeBudgetSpec, withVmPreserved, masterZeroizeSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨hq.1.toVmPreserved, ZeroizeStatePreserved.of_processFieldsPreserved hq.1, hq.2⟩

/-- Placement-generic `pureWordsProg base zeroize32Words` satisfies `processZeroizeSpec`. -/
theorem pureWordsProg_zeroize32_processZeroize_ok (base : BitVec 64) :
    subroutine_ok (pureWordsProg base zeroize32Words) base processZeroizeSpec :=
  subroutine_ok_processZeroize_of_hasWords
    (pureWordsProg_externAt_none base zeroize32Words)
    (pureWordsProg_zeroize32_hasWords base)

/-- Placement-generic `pureWordsProg base zeroize32Words` satisfies `masterZeroizeSpec`. -/
theorem pureWordsProg_zeroize32_masterZeroize_ok (base : BitVec 64) :
    subroutine_ok (pureWordsProg base zeroize32Words) base masterZeroizeSpec :=
  subroutine_ok_masterZeroize_of_hasWords
    (pureWordsProg_externAt_none base zeroize32Words)
    (pureWordsProg_zeroize32_hasWords base)

/-- Placement-generic `pureWordsProg base zeroize32Words` satisfies
    `zeroizeSpecK keep masterZeroizeSpec`. -/
theorem pureWordsProg_zeroize32_masterZeroizeK_ok (keep : BitVec 64 → Bool) (base : BitVec 64) :
    subroutine_ok (pureWordsProg base zeroize32Words) base
      (zeroizeSpecK keep masterZeroizeSpec) :=
  subroutine_ok_masterZeroizeK_of_hasWords keep
    (pureWordsProg_externAt_none base zeroize32Words)
    (pureWordsProg_zeroize32_hasWords base)

/-- Placement-generic `pureWordsProg base zeroize32Words` satisfies `masterZeroizeBudgetSpec`. -/
theorem pureWordsProg_zeroize32_masterZeroizeBudget_ok (base : BitVec 64) :
    subroutine_ok (pureWordsProg base zeroize32Words) base masterZeroizeBudgetSpec :=
  subroutine_ok_masterZeroizeBudget_of_hasWords
    (pureWordsProg_externAt_none base zeroize32Words)
    (pureWordsProg_zeroize32_hasWords base)

/-- **Row D3 (`SharedSecret::drop`, two-block `P_sub`, `hasInstrs` branch form)**: full-permission
    region-local `subroutine_ok` for `processZeroizeSpec`. -/
theorem subroutine_ok_sharedSecret_processZeroize_of_hasInstrs_hasWords
    {P_sub : Program} {entry targetAddr : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb : hasInstrs P_sub entry (sharedSecretDropInstrs entry targetAddr))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry processZeroizeSpec :=
  tailJump_subroutine_ok hb (subroutine_ok_processZeroize_of_hasWords hsub_no htgt)

/-- **Row D3 (`SharedSecret::drop`, two-block `P_sub`, `hasWords` form)**: full-permission
    region-local `subroutine_ok` for `processZeroizeSpec`. -/
theorem subroutine_ok_sharedSecret_processZeroize_of_hasWords
    {P_sub : Program} {entry targetAddr : BitVec 64} {bWord : BitVec 32}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb_words : P_sub.hasWords entry [bWord])
    (hdec : decode bWord = some (.b (targetAddr - entry)))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry processZeroizeSpec :=
  subroutine_ok_sharedSecret_processZeroize_of_hasInstrs_hasWords hsub_no
    (hasInstrs_sharedSecretDrop_of_hasWords hb_words hdec) htgt

/-- **Row D3 (`SharedSecret::drop`)**: `K`-narrowed full-permission region-local `subroutine_ok`
    (`hasInstrs` branch form). -/
theorem subroutine_ok_sharedSecret_processZeroizeK_of_hasInstrs_hasWords
    (keep : BitVec 64 → Bool) {P_sub : Program} {entry targetAddr : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb : hasInstrs P_sub entry (sharedSecretDropInstrs entry targetAddr))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry (zeroizeSpecK keep processZeroizeSpec) :=
  tailJump_subroutine_ok hb (subroutine_ok_processZeroizeK_of_hasWords keep hsub_no htgt)

/-- **Row D3 (`SharedSecret::drop`)**: `K`-narrowed full-permission region-local `subroutine_ok`
    (`hasWords` form). -/
theorem subroutine_ok_sharedSecret_processZeroizeK_of_hasWords
    (keep : BitVec 64 → Bool) {P_sub : Program} {entry targetAddr : BitVec 64}
    {bWord : BitVec 32}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb_words : P_sub.hasWords entry [bWord])
    (hdec : decode bWord = some (.b (targetAddr - entry)))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry (zeroizeSpecK keep processZeroizeSpec) :=
  subroutine_ok_sharedSecret_processZeroizeK_of_hasInstrs_hasWords keep hsub_no
    (hasInstrs_sharedSecretDrop_of_hasWords hb_words hdec) htgt

/-- **Row D3 (`SharedSecret::drop`, two-block `P_sub`, `hasInstrs` branch form)**: region-local
    `subroutine_ok` for `masterZeroizeSpec` when `P_sub` holds `b (targetAddr - entry)` at `entry`
    and `zeroize32Words` at `targetAddr`. -/
theorem subroutine_ok_sharedSecret_masterZeroize_of_hasInstrs_hasWords
    {P_sub : Program} {entry targetAddr : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb : hasInstrs P_sub entry (sharedSecretDropInstrs entry targetAddr))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry masterZeroizeSpec :=
  tailJump_subroutine_ok hb (subroutine_ok_masterZeroize_of_hasWords hsub_no htgt)

/-- **Row D3 (`SharedSecret::drop`, two-block `P_sub`, `hasWords` form)**: region-local
    `subroutine_ok` for `masterZeroizeSpec` when `P_sub` holds `[bWord]` (`decode bWord = some (.b (targetAddr - entry))`)
    at `entry` and `zeroize32Words` at `targetAddr`. -/
theorem subroutine_ok_sharedSecret_masterZeroize_of_hasWords
    {P_sub : Program} {entry targetAddr : BitVec 64} {bWord : BitVec 32}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb_words : P_sub.hasWords entry [bWord])
    (hdec : decode bWord = some (.b (targetAddr - entry)))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry masterZeroizeSpec :=
  subroutine_ok_sharedSecret_masterZeroize_of_hasInstrs_hasWords hsub_no
    (hasInstrs_sharedSecretDrop_of_hasWords hb_words hdec) htgt

/-- **Row D3 (`SharedSecret::drop`)**: `K`-narrowed region-local `subroutine_ok` (`hasInstrs` branch form). -/
theorem subroutine_ok_sharedSecret_masterZeroizeK_of_hasInstrs_hasWords
    (keep : BitVec 64 → Bool) {P_sub : Program} {entry targetAddr : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb : hasInstrs P_sub entry (sharedSecretDropInstrs entry targetAddr))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry (zeroizeSpecK keep masterZeroizeSpec) :=
  tailJump_subroutine_ok hb (subroutine_ok_masterZeroizeK_of_hasWords keep hsub_no htgt)

/-- **Row D3 (`SharedSecret::drop`)**: `K`-narrowed region-local `subroutine_ok` (`hasWords` form). -/
theorem subroutine_ok_sharedSecret_masterZeroizeK_of_hasWords
    (keep : BitVec 64 → Bool) {P_sub : Program} {entry targetAddr : BitVec 64}
    {bWord : BitVec 32}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb_words : P_sub.hasWords entry [bWord])
    (hdec : decode bWord = some (.b (targetAddr - entry)))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry (zeroizeSpecK keep masterZeroizeSpec) :=
  subroutine_ok_sharedSecret_masterZeroizeK_of_hasInstrs_hasWords keep hsub_no
    (hasInstrs_sharedSecretDrop_of_hasWords hb_words hdec) htgt

/-- **Row D3 (`SharedSecret::drop`)**: `withVmPreserved` region-local `subroutine_ok` (`hasInstrs` branch form). -/
theorem subroutine_ok_sharedSecret_masterZeroizeBudget_of_hasInstrs_hasWords
    {P_sub : Program} {entry targetAddr : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb : hasInstrs P_sub entry (sharedSecretDropInstrs entry targetAddr))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry masterZeroizeBudgetSpec :=
  tailJump_subroutine_ok hb (subroutine_ok_masterZeroizeBudget_of_hasWords hsub_no htgt)

/-- **Row D3 (`SharedSecret::drop`)**: `withVmPreserved` region-local `subroutine_ok` (`hasWords` form). -/
theorem subroutine_ok_sharedSecret_masterZeroizeBudget_of_hasWords
    {P_sub : Program} {entry targetAddr : BitVec 64} {bWord : BitVec 32}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hb_words : P_sub.hasWords entry [bWord])
    (hdec : decode bWord = some (.b (targetAddr - entry)))
    (htgt : P_sub.hasWords targetAddr zeroize32Words) :
    subroutine_ok P_sub entry masterZeroizeBudgetSpec :=
  subroutine_ok_sharedSecret_masterZeroizeBudget_of_hasInstrs_hasWords hsub_no
    (hasInstrs_sharedSecretDrop_of_hasWords hb_words hdec) htgt

/-- Concrete `64`-word contiguous hull instance (`pureWordsProg m sharedSecretDropHullWords` at
    entry `m + 252#64`) satisfying full-permission `processZeroizeSpec`. -/
theorem pureWordsProg_sharedSecretDropHull_processZeroize_ok (m : BitVec 64) :
    subroutine_ok (pureWordsProg m sharedSecretDropHullWords) (m + 252#64) processZeroizeSpec :=
  subroutine_ok_sharedSecret_processZeroize_of_hasWords
    (pureWordsProg_externAt_none m sharedSecretDropHullWords)
    (pureWordsProg_sharedSecretDropHull_drop_hasWords m)
    (decode_sharedSecretDropBackWord m)
    (pureWordsProg_sharedSecretDropHull_zeroize_hasWords m)

/-- Concrete `64`-word contiguous hull instance satisfying `zeroizeSpecK keep processZeroizeSpec`. -/
theorem pureWordsProg_sharedSecretDropHull_processZeroizeK_ok
    (keep : BitVec 64 → Bool) (m : BitVec 64) :
    subroutine_ok (pureWordsProg m sharedSecretDropHullWords) (m + 252#64)
      (zeroizeSpecK keep processZeroizeSpec) :=
  subroutine_ok_sharedSecret_processZeroizeK_of_hasWords keep
    (pureWordsProg_externAt_none m sharedSecretDropHullWords)
    (pureWordsProg_sharedSecretDropHull_drop_hasWords m)
    (decode_sharedSecretDropBackWord m)
    (pureWordsProg_sharedSecretDropHull_zeroize_hasWords m)

/-- Concrete `64`-word contiguous hull instance (`pureWordsProg m sharedSecretDropHullWords` at
    entry `m + 252#64`) satisfying `masterZeroizeSpec`. -/
theorem pureWordsProg_sharedSecretDropHull_masterZeroize_ok (m : BitVec 64) :
    subroutine_ok (pureWordsProg m sharedSecretDropHullWords) (m + 252#64) masterZeroizeSpec :=
  subroutine_ok_sharedSecret_masterZeroize_of_hasWords
    (pureWordsProg_externAt_none m sharedSecretDropHullWords)
    (pureWordsProg_sharedSecretDropHull_drop_hasWords m)
    (decode_sharedSecretDropBackWord m)
    (pureWordsProg_sharedSecretDropHull_zeroize_hasWords m)

/-- Concrete `64`-word contiguous hull instance satisfying `zeroizeSpecK keep masterZeroizeSpec`. -/
theorem pureWordsProg_sharedSecretDropHull_masterZeroizeK_ok
    (keep : BitVec 64 → Bool) (m : BitVec 64) :
    subroutine_ok (pureWordsProg m sharedSecretDropHullWords) (m + 252#64)
      (zeroizeSpecK keep masterZeroizeSpec) :=
  subroutine_ok_sharedSecret_masterZeroizeK_of_hasWords keep
    (pureWordsProg_externAt_none m sharedSecretDropHullWords)
    (pureWordsProg_sharedSecretDropHull_drop_hasWords m)
    (decode_sharedSecretDropBackWord m)
    (pureWordsProg_sharedSecretDropHull_zeroize_hasWords m)

/-- Concrete `64`-word contiguous hull instance satisfying `masterZeroizeBudgetSpec`. -/
theorem pureWordsProg_sharedSecretDropHull_masterZeroizeBudget_ok (m : BitVec 64) :
    subroutine_ok (pureWordsProg m sharedSecretDropHullWords) (m + 252#64)
      masterZeroizeBudgetSpec :=
  subroutine_ok_sharedSecret_masterZeroizeBudget_of_hasWords
    (pureWordsProg_externAt_none m sharedSecretDropHullWords)
    (pureWordsProg_sharedSecretDropHull_drop_hasWords m)
    (decode_sharedSecretDropBackWord m)
    (pureWordsProg_sharedSecretDropHull_zeroize_hasWords m)

/-! ## 3. `W`-Independent Fallback `zeroizeSecretHook` Soundness -/

/-- The trusted-table idealized hook `LibsignalTripleRatchet.zeroizeSecretHook` (`W`-independent)
    satisfies `masterZeroizeSpec` (needed by the ghost hook's fallback branch). -/
theorem zeroizeSecretHook_masterZeroize_ok :
    HookOk zeroizeSecretHook masterZeroizeSpec := by
  unfold zeroizeSecretHook
  refine retHook_ok fun a R s0 _ hpre _ => ?_
  simp only [masterZeroizeSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨ha, hmem⟩
  subst ha
  let zeros := List.replicate 32 (0#8 : BitVec 8)
  have hlen : zeros.length ≤ 2 ^ 64 := by decide
  have hmem_rep : s0.mem ⊨ memRegion (s0.readReg64 .x0) zeros.length ∗ R := by
    simpa [zeros] using hmem
  refine ⟨keepsFrozen_writeBytes_of_memRegion zeros hlen hmem_rep,
    rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  change s0.mem.writeBytes (s0.readReg64 .x0) zeros ⊨
    (⌜ZeroizeStatePreserved s0 s0⌝ ∗ (s0.readReg64 .x0 ↦ₛ zeros)) ∗ R
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨ZeroizeStatePreserved.refl s0, satisfies_writeBytes zeros hlen hmem_rep⟩

/-- `zeroizeSecretHook` (`W`-independent) satisfies `zeroizeSpecK keep masterZeroizeSpec`. -/
theorem zeroizeSecretHook_masterZeroizeK_ok (keep : BitVec 64 → Bool) :
    HookOk zeroizeSecretHook (zeroizeSpecK keep masterZeroizeSpec) :=
  hookOk_memsetSpecK_of_plain keep zeroizeSecretHook_masterZeroize_ok

/-- `zeroizeSecretHook` (`W`-independent) satisfies `masterZeroizeBudgetSpec`
    (`withVmPreserved masterZeroizeSpec`). -/
theorem zeroizeSecretHook_masterZeroizeBudget_ok :
    HookOk zeroizeSecretHook masterZeroizeBudgetSpec :=
  hookOk_withVmPreserved zeroizeSecretHook_masterZeroize_ok zeroizeSecretHook_vmPreserved

/-- `zeroizeSecretHook` (`W`-independent) satisfies `zeroizeSpecK keep masterZeroizeBudgetSpec`. -/
theorem zeroizeSecretHook_masterZeroizeBudgetK_ok (keep : BitVec 64 → Bool) :
    HookOk zeroizeSecretHook (zeroizeSpecK keep masterZeroizeBudgetSpec) :=
  hookOk_memsetSpecK_of_plain keep zeroizeSecretHook_masterZeroizeBudget_ok

/-- `zeroizeSecretHook` (`W`-independent) also satisfies full-permission `processZeroizeSpec`. -/
theorem zeroizeSecretHook_processZeroize_ok :
    HookOk zeroizeSecretHook processZeroizeSpec := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) zeroizeSecretHook_masterZeroizeBudget_ok
    (fun _ _ => by
      dsimp only [processZeroizeSpec, masterZeroizeBudgetSpec, withVmPreserved, masterZeroizeSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterZeroizeBudgetSpec, withVmPreserved, masterZeroizeSpec, processZeroizeSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hvm =>
    Entails.pure_left fun hst =>
      Entails.pure_right (hst.toProcessFieldsPreserved hvm) (Entails.refl _)

/-! ## 4. Generic `HookOk` Consequence Lifts from `masterZeroizeSpec` -/

/-- Frame `stackAt s0.sp stk` onto any non-aborting `HookOk f spec`. -/
theorem hookOk_withStack_pureAbort {α : Type} {f : State → State} {spec : Spec α}
    (hh : HookOk f spec) (stk : Nat := extHookStack)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (withStack spec stk) :=
  hookOk_frame_pureAbort (fun _ s0 => stackAt s0.sp stk) hh
    (fun _ _ => Entails.refl _) (fun _ _ _ => Entails.refl _) hpan hex hoom

/-- Frame `stackAt s0.sp stk` across `zeroizeSpecK keep` onto any non-aborting `spec`. -/
theorem hookOk_zeroizeSpecK_withStack_pureAbort (keep : BitVec 64 → Bool)
    {α : Type} {f : State → State} {spec : Spec α}
    (hh : HookOk f (zeroizeSpecK keep spec)) (stk : Nat := extHookStack)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (zeroizeSpecK keep (withStack spec stk)) :=
  hookOk_memsetSpecK_frame_pureAbort keep (fun _ s0 => stackAt s0.sp stk) hh
    (fun _ _ => Entails.refl _) (fun _ _ _ => Entails.refl _) hpan hex hoom

/-- Lift any non-aborting `HookOk f spec.keepsFs` to `HookOk f (withFsPred Pfs spec)` without extra
    hypotheses on `f`. -/
theorem hookOk_withFsPred_of_keepsFs {α : Type} {f : State → State} {spec : Spec α}
    (Pfs : FsState → Prop) (hh : HookOk f spec.keepsFs)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (withFsPred Pfs spec) := by
  refine hookOk_frame_pureAbort (fun _ s0 => ⌜Pfs s0.fs⌝) hh
    (fun x s0 => by
      dsimp only [withFsPred, Arm64.Spec.keepsFs]
      exact Entails.of_eq (sepConj_comm _ _))
    (fun x s0 sf => ?_)
    hpan hex hoom
  dsimp only [withFsPred, Arm64.Spec.keepsFs]
  rw [sepConj_comm _ ⌜Pfs s0.fs⌝]
  exact Entails.pure_left fun hpfs =>
    Entails.pure_left fun (hfs : sf.fs = s0.fs) =>
      Entails.pure_right (hfs ▸ hpfs) (Entails.refl _)

/-- `K`-narrowed counterpart of `hookOk_withFsPred_of_keepsFs`. -/
theorem hookOk_zeroizeSpecK_withFsPred_of_keepsFs (keep : BitVec 64 → Bool)
    {α : Type} {f : State → State} {spec : Spec α}
    (Pfs : FsState → Prop) (hh : HookOk f (zeroizeSpecK keep spec.keepsFs))
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (zeroizeSpecK keep (withFsPred Pfs spec)) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ s0 => ⌜Pfs s0.fs⌝) hh
    (fun x s0 => by
      dsimp only [withFsPred, Arm64.Spec.keepsFs]
      exact Entails.of_eq (sepConj_comm _ _))
    (fun x s0 sf => ?_)
    hpan hex hoom
  dsimp only [withFsPred, Arm64.Spec.keepsFs]
  rw [sepConj_comm _ ⌜Pfs s0.fs⌝]
  exact Entails.pure_left fun hpfs =>
    Entails.pure_left fun (hfs : sf.fs = s0.fs) =>
      Entails.pure_right (hfs ▸ hpfs) (Entails.refl _)

/-- Lift `HookOk f masterZeroizeSpec` to `HookOk f zeroizeSecretSpec`. -/
theorem hookOk_zeroizeSecret_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) :
    HookOk f zeroizeSecretSpec := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun _ _ => by dsimp only [zeroizeSecretSpec, masterZeroizeSpec]; rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterZeroizeSpec, zeroizeSecretSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hst => Entails.pure_right hst.2.1 (Entails.refl _)

/-- Lift `HookOk f (zeroizeSpecK keep masterZeroizeSpec)` to `HookOk f (zeroizeSpecK keep zeroizeSecretSpec)`. -/
theorem hookOk_zeroizeSecretK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (zeroizeSpecK keep masterZeroizeSpec)) :
    HookOk f (zeroizeSpecK keep zeroizeSecretSpec) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ _ => emp) hh
    (fun _ _ => by dsimp only [zeroizeSecretSpec, masterZeroizeSpec]; rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterZeroizeSpec, zeroizeSecretSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hst => Entails.pure_right hst.2.1 (Entails.refl _)

/-- Lift `HookOk f masterZeroizeSpec` to `HookOk f zeroizeSecretSpec.keepsFs` (using `hst.1 : sf.fs = s0.fs`
    from `ZeroizeStatePreserved`). -/
theorem hookOk_zeroizeSecret_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) :
    HookOk f zeroizeSecretSpec.keepsFs := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun _ _ => by
      dsimp only [Arm64.Spec.keepsFs, zeroizeSecretSpec, masterZeroizeSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterZeroizeSpec, Arm64.Spec.keepsFs, zeroizeSecretSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hst =>
    Entails.pure_right hst.1 (Entails.pure_right hst.2.1 (Entails.refl _))

/-- Lift `HookOk f (zeroizeSpecK keep masterZeroizeSpec)` to `HookOk f (zeroizeSpecK keep zeroizeSecretSpec.keepsFs)`. -/
theorem hookOk_zeroizeSecretK_keepsFs_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (zeroizeSpecK keep masterZeroizeSpec)) :
    HookOk f (zeroizeSpecK keep zeroizeSecretSpec.keepsFs) := by
  refine hookOk_memsetSpecK_frame_pureAbort keep (fun _ _ => emp) hh
    (fun _ _ => by
      dsimp only [Arm64.Spec.keepsFs, zeroizeSecretSpec, masterZeroizeSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterZeroizeSpec, Arm64.Spec.keepsFs, zeroizeSecretSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hst =>
    Entails.pure_right hst.1 (Entails.pure_right hst.2.1 (Entails.refl _))

/-- Lift `HookOk f masterZeroizeSpec` to `HookOk f (withFsPred Pfs zeroizeSecretSpec)`. -/
theorem hookOk_zeroizeSecret_withFsPred_of_master {f : State → State}
    (Pfs : FsState → Prop) (hh : HookOk f masterZeroizeSpec) :
    HookOk f (withFsPred Pfs zeroizeSecretSpec) :=
  hookOk_withFsPred_of_keepsFs Pfs (hookOk_zeroizeSecret_keepsFs_of_master hh)

/-- Lift `HookOk f (zeroizeSpecK keep masterZeroizeSpec)` to
    `HookOk f (zeroizeSpecK keep (withFsPred Pfs zeroizeSecretSpec))`. -/
theorem hookOk_zeroizeSecretK_withFsPred_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (Pfs : FsState → Prop) (hh : HookOk f (zeroizeSpecK keep masterZeroizeSpec)) :
    HookOk f (zeroizeSpecK keep (withFsPred Pfs zeroizeSecretSpec)) :=
  hookOk_zeroizeSpecK_withFsPred_of_keepsFs keep Pfs (hookOk_zeroizeSecretK_keepsFs_of_master keep hh)

/-- Lift `HookOk f masterZeroizeSpec` to `HookOk f (withStack zeroizeSecretSpec stk)` for any `stk`. -/
theorem hookOk_withStack_zeroizeSecret_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) (stk : Nat := extHookStack) :
    HookOk f (withStack zeroizeSecretSpec stk) :=
  hookOk_withStack_pureAbort (hookOk_zeroizeSecret_of_master hh) stk

/-- Lift `HookOk f (zeroizeSpecK keep masterZeroizeSpec)` to
    `HookOk f (zeroizeSpecK keep (withStack zeroizeSecretSpec stk))`. -/
theorem hookOk_withStack_zeroizeSecretK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (zeroizeSpecK keep masterZeroizeSpec)) (stk : Nat := extHookStack) :
    HookOk f (zeroizeSpecK keep (withStack zeroizeSecretSpec stk)) :=
  hookOk_zeroizeSpecK_withStack_pureAbort keep (hookOk_zeroizeSecretK_of_master keep hh) stk

/-- Lift `HookOk f masterZeroizeSpec` to `HookOk f CliExt.zeroizeSpec` (`= withStack zeroizeSecretSpec extHookStack`). -/
theorem hookOk_cliZeroize_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) :
    HookOk f zeroizeSpec :=
  hookOk_withStack_zeroizeSecret_of_master hh extHookStack

/-- Lift `HookOk f (zeroizeSpecK keep masterZeroizeSpec)` to `HookOk f (zeroizeSpecK keep CliExt.zeroizeSpec)`. -/
theorem hookOk_cliZeroizeK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (zeroizeSpecK keep masterZeroizeSpec)) :
    HookOk f (zeroizeSpecK keep zeroizeSpec) :=
  hookOk_withStack_zeroizeSecretK_of_master keep hh extHookStack

/-- Lift `HookOk f masterZeroizeSpec` to `HookOk f CliExt.zeroizeSpec.keepsFs`. -/
theorem hookOk_cliZeroize_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) :
    HookOk f zeroizeSpec.keepsFs := by
  refine hookOk_frame_pureAbort (fun _ s0 => stackAt s0.sp extHookStack) hh
    (fun _ _ => Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterZeroizeSpec, Arm64.Spec.keepsFs, zeroizeSpec,
    CryptoVerification.SignalSession.CliExt.withStack, zeroizeSecretSpec]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun hst =>
    Entails.pure_right hst.1 (Entails.pure_right hst.2.1 (Entails.refl _))

/-! ### 4.1 Budget (`withVmPreserved`) Consumer Lifts -/

/-- Lift `HookOk f masterZeroizeBudgetSpec` directly to `HookOk f (withVmPreserved zeroizeSecretSpec)`
    (`rfl`/defeq-equal by body to `DhStepBudgetSteps.zeroizeSecretBudgetSpec`, the primary placed drop consumer spec). -/
theorem hookOk_zeroizeSecretBudget_of_masterBudget {f : State → State}
    (hh : HookOk f masterZeroizeBudgetSpec) :
    HookOk f (withVmPreserved zeroizeSecretSpec) := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun _ _ => by
      dsimp only [withVmPreserved, zeroizeSecretSpec, masterZeroizeBudgetSpec, masterZeroizeSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [masterZeroizeBudgetSpec, withVmPreserved, masterZeroizeSpec, zeroizeSecretSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hvm =>
    Entails.pure_left fun hst =>
      Entails.pure_right hvm (Entails.pure_right hst.2.1 (Entails.refl _))

/-- Lift `HookOk f masterZeroizeSpec` + pointwise `VmPreserved` to
    `HookOk f (withVmPreserved zeroizeSecretSpec)` (`= DhStepBudgetSteps.zeroizeSecretBudgetSpec`). -/
theorem hookOk_zeroizeSecretBudget_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withVmPreserved zeroizeSecretSpec) :=
  hookOk_withVmPreserved (hookOk_zeroizeSecret_of_master hh) hvm

/-- `K`-narrowed lift to `zeroizeSpecK keep (withVmPreserved zeroizeSecretSpec)`. -/
theorem hookOk_zeroizeSecretBudgetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (zeroizeSpecK keep masterZeroizeSpec)) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (zeroizeSpecK keep (withVmPreserved zeroizeSecretSpec)) :=
  hookOk_withVmPreserved (hookOk_zeroizeSecretK_of_master keep hh) hvm

/-- Lift `HookOk f masterZeroizeBudgetSpec` to `HookOk f (withVmPreserved zeroizeSecretSpec).keepsFs`. -/
theorem hookOk_zeroizeSecretBudget_keepsFs_of_masterBudget {f : State → State}
    (hh : HookOk f masterZeroizeBudgetSpec) :
    HookOk f (withVmPreserved zeroizeSecretSpec).keepsFs := by
  refine hookOk_frame_pureAbort (fun _ _ => emp) hh
    (fun _ _ => by
      dsimp only [Arm64.Spec.keepsFs, withVmPreserved, zeroizeSecretSpec,
        masterZeroizeBudgetSpec, masterZeroizeSpec]
      rw [sepConj_emp]; exact Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [Arm64.Spec.keepsFs, masterZeroizeBudgetSpec, withVmPreserved,
    masterZeroizeSpec, zeroizeSecretSpec]
  rw [sepConj_emp]
  exact Entails.pure_left fun hvm =>
    Entails.pure_left fun hst =>
      Entails.pure_right hst.1
        (Entails.pure_right hvm (Entails.pure_right hst.2.1 (Entails.refl _)))

/-- Lift `HookOk f masterZeroizeSpec` + pointwise `VmPreserved` to
    `HookOk f (withVmPreserved zeroizeSecretSpec).keepsFs`. -/
theorem hookOk_zeroizeSecretBudget_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withVmPreserved zeroizeSecretSpec).keepsFs :=
  hookOk_zeroizeSecretBudget_keepsFs_of_masterBudget (hookOk_withVmPreserved hh hvm)

/-- Lift `HookOk f masterZeroizeBudgetSpec` to
    `HookOk f (withFsPred Pfs (withVmPreserved zeroizeSecretSpec))` (exact consumer spec of
    `AgreeBudgetFd`, `CreateChainBudgetFd`, and `ResponderCore/CryptoBridgePlacedBudgetFd`). -/
theorem hookOk_zeroizeSecretBudget_withFsPred_of_masterBudget {f : State → State}
    (Pfs : FsState → Prop) (hh : HookOk f masterZeroizeBudgetSpec) :
    HookOk f (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)) :=
  hookOk_withFsPred_of_keepsFs Pfs (hookOk_zeroizeSecretBudget_keepsFs_of_masterBudget hh)

/-- Lift `HookOk f masterZeroizeSpec` + pointwise `VmPreserved` to
    `HookOk f (withFsPred Pfs (withVmPreserved zeroizeSecretSpec))`. -/
theorem hookOk_zeroizeSecretBudget_withFsPred_of_master {f : State → State}
    (Pfs : FsState → Prop) (hh : HookOk f masterZeroizeSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)) :=
  hookOk_zeroizeSecretBudget_withFsPred_of_masterBudget Pfs (hookOk_withVmPreserved hh hvm)

/-- Lift `HookOk f masterZeroizeSpec` + pointwise `VmPreserved` to
    `HookOk f (withStack (withVmPreserved zeroizeSecretSpec) stk)`. -/
theorem hookOk_withStack_zeroizeSecretBudget_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) (hvm : ∀ s, VmPreserved s (f s))
    (stk : Nat := extHookStack) :
    HookOk f (withStack (withVmPreserved zeroizeSecretSpec) stk) :=
  hookOk_withStack_pureAbort (hookOk_zeroizeSecretBudget_of_master hh hvm) stk

/-- Lift `HookOk f masterZeroizeSpec` + pointwise `VmPreserved` to
    `HookOk f (withVmPreserved CliExt.zeroizeSpec)` (`= SpecBudget.cliZeroizeBudgetSpec`). -/
theorem hookOk_cliZeroizeBudget_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withVmPreserved zeroizeSpec) :=
  hookOk_withVmPreserved (hookOk_cliZeroize_of_master hh) hvm

/-- `K`-narrowed lift to `zeroizeSpecK keep (withVmPreserved CliExt.zeroizeSpec)`. -/
theorem hookOk_cliZeroizeBudgetK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (zeroizeSpecK keep masterZeroizeSpec)) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (zeroizeSpecK keep (withVmPreserved zeroizeSpec)) :=
  hookOk_withVmPreserved (hookOk_cliZeroizeK_of_master keep hh) hvm

/-- Lift `HookOk f masterZeroizeSpec` + pointwise `VmPreserved` to
    `HookOk f (withVmPreserved CliExt.zeroizeSpec).keepsFs`. -/
theorem hookOk_cliZeroizeBudget_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterZeroizeSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (withVmPreserved zeroizeSpec).keepsFs := by
  refine hookOk_frame_pureAbort (fun _ s0 => stackAt s0.sp extHookStack)
    (hookOk_withVmPreserved hh hvm)
    (fun _ _ => Entails.refl _)
    (fun _ _ _ => ?_)
  dsimp only [Arm64.Spec.keepsFs, masterZeroizeBudgetSpec, withVmPreserved,
    masterZeroizeSpec, zeroizeSpec, CryptoVerification.SignalSession.CliExt.withStack,
    zeroizeSecretSpec]
  simp only [sepConj_assoc]
  exact Entails.pure_left fun hvm' =>
    Entails.pure_left fun hst =>
      Entails.pure_right hst.1
        (Entails.pure_right hvm' (Entails.pure_right hst.2.1 (Entails.refl _)))

/-- `zeroizeSpecK keep` commutes definitionally with `.keepsFs`, `withVmPreserved`, and
    `withOomPoolPreserved`. -/
theorem zeroizeSpecK_keepsFs (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    (zeroizeSpecK keep spec).keepsFs = zeroizeSpecK keep spec.keepsFs := rfl

theorem zeroizeSpecK_withVmPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withVmPreserved (zeroizeSpecK keep spec) = zeroizeSpecK keep (withVmPreserved spec) := rfl

theorem zeroizeSpecK_withOomPoolPreserved (keep : BitVec 64 → Bool) {α : Type} (spec : Spec α) :
    withOomPoolPreserved (zeroizeSpecK keep spec) =
      zeroizeSpecK keep (withOomPoolPreserved spec) := rfl

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode
