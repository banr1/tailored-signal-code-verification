/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import

/-!
# Closed-`lr` Trap & Subroutine-Outcome Suite for `StaticSecret::drop` & `SharedSecret::drop` (`HooksDehook.ZeroizeLrTrap`)

Rows 1 and 2 of Card **D-d** (`dd_dalek_lrtrap.md`):
1. **Row 1 (`StaticSecret::drop`, `zeroize32Words`, `63` words = `252` B at `entry`):**
   - Certifies `zeroize32_all_safe : checkWordsTrapSafe zeroize32Words [] = true` by `decide`
     and lifts to `RegionWordsSafe (staticSecretDropRegion entry)`.
2. **Row 2 (`SharedSecret::drop`, `sharedSecretDropHullWords`, `64` words = `256` B at `m`,
   hooked entry `m + sharedSecretDropEntryOff`):**
   - `<SharedSecret as Drop>::drop` at `m + sharedSecretDropEntryOff` is a 1-word unconditional
     tail branch `b` (`sharedSecretDropBackWord`, targeting `m`), NOT `bl` — it never writes `x30`.
   - Certifies `sharedSecretDropHull_all_safe : checkWordsTrapSafe sharedSecretDropHullWords [] = true`
     by `decide` and lifts to `RegionWordsSafe (sharedSecretDropHullRegion m)`.
3. **`TrapHook` Instances & Row 1 Card-`c` Post-Hook / At-Stub Corollaries:**
   - Stock `zeroizeSecretHook` (`∀ L`), plain `zeroizeGhostHook` / `f3EmptyZeroizeGhostHook` /
     `sharedSecretDropGhostHook` / `f3EmptySharedSecretDropGhostHook`, and `K`-narrowed counterparts.
   - Row 1 (`StaticSecret::drop`) post-hook (`P_sub.CodeLoaded u.mem` per `H1`) and at-stub
     `SubroutineOutcome` trap corollaries + entry-excluded (`F1`, `entries = [entry]`) `f3Empty*`
     wrappers. Row 2 (`SharedSecret::drop`) corollaries live in `HooksDehook.SharedSecretDropLrTrap`
     (both re-exported by `HooksDehook.DalekLrTrap`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap

open Arm64 ProofLib
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open CryptoVerification.LibsignalTripleRatchet (zeroizeSecretHook)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (zeroize32Words)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (keepFsTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (
  subroutineOutcome_running_pc_and_noFault
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapRegion keepBlock keepOf keepOf_singleton
  RegionWordsSafe RegionHasWords RegionCodeLoaded
  codeLoaded_stripExecOutside_of_keep
  TrapHook trapHook_of_exception_on_keepLr trapHook_linkedCallHook
  lr_trap_at_call_ret lr_trap_at_call TrapEntryGuard keepLr_false_at_stub_of_outcome
  checkWordsTrapSafe regionWordsSafe_single
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap (
  lr_trap_after_hook_ret
  keepLr_false_after_hook_of_outcome
  keepLr_false_after_hook_of_subroutineOutcome
  keepLr_false_at_stub_of_subroutineOutcome
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode (
  sharedSecretDropHullWords pureWordsProg_zeroize32_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost (
  sharedSecretDropEntryOff
  zeroizeGhostHook zeroizeGhostHookK
  f3EmptyZeroizeGhostHook f3EmptyZeroizeGhostHookK
  f3EmptyZeroizeGhostHook_eq f3EmptyZeroizeGhostHookK_eq
  sharedSecretDropGhostHook sharedSecretDropGhostHookK
  f3EmptySharedSecretDropGhostHook f3EmptySharedSecretDropGhostHookK
  keepFsTrace_zeroizeSecretHook_eq zeroizeGhostHookK_of_keepLr_true
)

/-! ## 1. Row 1 — 252 B `StaticSecret::drop` (`keepStaticSecretDrop`, `staticSecretDropRegion`) -/

/-- Byte length (`252 = 4 * 63`) of `<StaticSecret as Drop>::drop` (`zeroize32Words`). -/
@[expose] def staticSecretDropByteLen : Nat :=
  4 * zeroize32Words.length

theorem staticSecretDropByteLen_eq : staticSecretDropByteLen = 252 := rfl

theorem zeroize32Words_length : zeroize32Words.length = 63 := rfl

theorem four_mul_zeroize32Words_length :
    4 * zeroize32Words.length = staticSecretDropByteLen := rfl

/-- Kept-region byte predicate `[entry, entry + 252)` for `StaticSecret::drop`. -/
@[expose] def keepStaticSecretDrop (entry : BitVec 64) : BitVec 64 → Bool :=
  keepBlock entry staticSecretDropByteLen

theorem keepStaticSecretDrop_iff (entry pc : BitVec 64) :
    keepStaticSecretDrop entry pc = true ↔ (pc - entry).toNat < staticSecretDropByteLen := by
  simp [keepStaticSecretDrop, keepBlock, decide_eq_true_eq]

/-- `entry` lies inside `keepStaticSecretDrop entry`. -/
theorem keepStaticSecretDrop_entry (entry : BitVec 64) :
    keepStaticSecretDrop entry entry = true := by
  rw [keepStaticSecretDrop_iff, staticSecretDropByteLen_eq]
  have hsub : entry - entry = 0#64 := by bv_omega
  rw [hsub]
  decide

/-- Single-block `TrapRegion` for the 63-word `zeroize32Words` block at `entry`. -/
@[expose] def staticSecretDropRegion (entry : BitVec 64) : TrapRegion :=
  [(entry, zeroize32Words)]

theorem keepOf_staticSecretDropRegion (entry : BitVec 64) :
    keepOf (staticSecretDropRegion entry) = keepStaticSecretDrop entry := by
  funext pc
  dsimp only [staticSecretDropRegion]
  rw [keepOf_singleton, four_mul_zeroize32Words_length]
  rfl

theorem keepOf_staticSecretDropRegion_apply (entry pc : BitVec 64) :
    keepOf (staticSecretDropRegion entry) pc = keepStaticSecretDrop entry pc :=
  congrFun (keepOf_staticSecretDropRegion entry) pc

/-- All 63 words of `zeroize32Words` pass `checkWordsTrapSafe` with `allowed = []`. -/
theorem zeroize32_all_safe :
    checkWordsTrapSafe zeroize32Words [] = true := by
  decide

/-- `RegionWordsSafe` for `staticSecretDropRegion entry` at any `entry : BitVec 64`. -/
theorem staticSecretDrop_regionWordsSafe (entry : BitVec 64) :
    RegionWordsSafe (staticSecretDropRegion entry) :=
  regionWordsSafe_single entry zeroize32_all_safe

theorem staticSecretDropRegion_hasWords_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hHas : P_sub.hasWords entry zeroize32Words) :
    RegionHasWords [P_sub] (staticSecretDropRegion entry) := by
  intro blk hmem
  rw [staticSecretDropRegion, List.mem_singleton] at hmem
  subst hmem
  exact ⟨P_sub, List.mem_singleton.mpr rfl, hHas⟩

theorem staticSecretDropRegion_hasWords_pure (entry : BitVec 64) :
    RegionHasWords [pureWordsProg entry zeroize32Words] (staticSecretDropRegion entry) :=
  staticSecretDropRegion_hasWords_of_hasWords (pureWordsProg_zeroize32_hasWords entry)

theorem staticSecretDropRegion_codeLoaded_iff {P_sub : Program} {mem : Memory} :
    RegionCodeLoaded [P_sub] mem ↔ P_sub.CodeLoaded mem := by
  constructor
  · intro h; exact h P_sub (List.mem_singleton.mpr rfl)
  · intro h P hP; rw [List.mem_singleton] at hP; subst hP; exact h

theorem staticSecretDrop_codeLoaded_stripExecOutside {keep : BitVec 64 → Bool} {P_sub : Program}
    {mem : Memory}
    (hkeep : ∀ off : Nat, off < P_sub.code.length →
      keep (P_sub.base + BitVec.ofNat 64 off) = true)
    (hL : P_sub.CodeLoaded mem) :
    P_sub.CodeLoaded (ProofLib.stripExecOutside keep mem) :=
  codeLoaded_stripExecOutside_of_keep hkeep hL

/-- Entry-state `lr` guard at `s0` for `StaticSecret::drop` stub replay. -/
@[expose] def StaticSecretDropEntryGuard (entry stubPc : BitVec 64) (s0 : State) : Prop :=
  keepStaticSecretDrop entry (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

theorem staticSecretDropEntryGuard_iff_trapEntryGuard (entry stubPc : BitVec 64) (s0 : State) :
    StaticSecretDropEntryGuard entry stubPc s0 ↔
      TrapEntryGuard (staticSecretDropRegion entry) stubPc s0 := by
  simp only [StaticSecretDropEntryGuard, TrapEntryGuard, keepOf_staticSecretDropRegion_apply]

/-! ## 2. Row 2 — 256 B `SharedSecret::drop` Contiguous Hull (`keepSharedSecretDropHull`) -/

theorem sharedSecretDropEntryOff_eq : sharedSecretDropEntryOff = 252#64 := rfl

/-- Byte length (`256 = 4 * 64`) of the contiguous `zeroize32Words ++ [sharedSecretDropBackWord]`
    hull (`sharedSecretDropHullWords`). -/
@[expose] def sharedSecretDropHullByteLen : Nat :=
  4 * sharedSecretDropHullWords.length

theorem sharedSecretDropHullByteLen_eq : sharedSecretDropHullByteLen = 256 := rfl

theorem sharedSecretDropHullWords_length : sharedSecretDropHullWords.length = 64 := rfl

theorem four_mul_sharedSecretDropHullWords_length :
    4 * sharedSecretDropHullWords.length = sharedSecretDropHullByteLen := rfl

/-- Kept-region byte predicate `[m, m + 256)` for the contiguous 64-word `SharedSecret::drop` hull
    (`<MontgomeryPoint as Zeroize>::zeroize` at `m`, `<SharedSecret as Drop>::drop` at
    `m + sharedSecretDropEntryOff`). -/
@[expose] def keepSharedSecretDropHull (m : BitVec 64) : BitVec 64 → Bool :=
  keepBlock m sharedSecretDropHullByteLen

theorem keepSharedSecretDropHull_iff (m pc : BitVec 64) :
    keepSharedSecretDropHull m pc = true ↔ (pc - m).toNat < sharedSecretDropHullByteLen := by
  simp [keepSharedSecretDropHull, keepBlock, decide_eq_true_eq]

/-- `<MontgomeryPoint as Zeroize>::zeroize`'s base `m` lies inside `keepSharedSecretDropHull m`. -/
theorem keepSharedSecretDropHull_zeroize_entry (m : BitVec 64) :
    keepSharedSecretDropHull m m = true := by
  rw [keepSharedSecretDropHull_iff, sharedSecretDropHullByteLen_eq]
  have hsub : m - m = 0#64 := by bv_omega
  rw [hsub]
  decide

/-- The hooked `<SharedSecret as Drop>::drop` entry `m + sharedSecretDropEntryOff` lies inside
    `keepSharedSecretDropHull m`. -/
theorem keepSharedSecretDropHull_entry (m : BitVec 64) :
    keepSharedSecretDropHull m (m + sharedSecretDropEntryOff) = true := by
  rw [keepSharedSecretDropHull_iff, sharedSecretDropHullByteLen_eq]
  have hsub : m + sharedSecretDropEntryOff - m = sharedSecretDropEntryOff := by bv_omega
  rw [hsub, sharedSecretDropEntryOff_eq]
  decide

/-- Every byte in the 252 B `zeroize` subrange `[m, m + 252)` lies inside
    `keepSharedSecretDropHull m`. -/
theorem keepSharedSecretDropHull_of_zeroize {m pc : BitVec 64}
    (h : keepBlock m (4 * zeroize32Words.length) pc = true) :
    keepSharedSecretDropHull m pc = true := by
  simp only [keepBlock, decide_eq_true_eq] at h
  rw [keepSharedSecretDropHull_iff, sharedSecretDropHullByteLen_eq]
  have hlen : 4 * zeroize32Words.length = 252 := rfl
  omega

/-- Every byte in the 4 B `SharedSecret::drop` tail-branch subrange
    `[m + sharedSecretDropEntryOff, m + sharedSecretDropEntryOff + 4)` lies inside
    `keepSharedSecretDropHull m`. -/
theorem keepSharedSecretDropHull_of_drop {m pc : BitVec 64}
    (h : keepBlock (m + sharedSecretDropEntryOff) 4 pc = true) :
    keepSharedSecretDropHull m pc = true := by
  simp only [keepBlock, decide_eq_true_eq] at h
  rw [keepSharedSecretDropHull_iff, sharedSecretDropHullByteLen_eq]
  rw [sharedSecretDropEntryOff_eq] at h
  bv_omega

/-- Single-block `TrapRegion` for the 64-word `sharedSecretDropHullWords` block at `m`. -/
@[expose] def sharedSecretDropHullRegion (m : BitVec 64) : TrapRegion :=
  [(m, sharedSecretDropHullWords)]

theorem keepOf_sharedSecretDropHullRegion (m : BitVec 64) :
    keepOf (sharedSecretDropHullRegion m) = keepSharedSecretDropHull m := by
  funext pc
  dsimp only [sharedSecretDropHullRegion]
  rw [keepOf_singleton, four_mul_sharedSecretDropHullWords_length]
  rfl

theorem keepOf_sharedSecretDropHullRegion_apply (m pc : BitVec 64) :
    keepOf (sharedSecretDropHullRegion m) pc = keepSharedSecretDropHull m pc :=
  congrFun (keepOf_sharedSecretDropHullRegion m) pc

/-- All 64 words of `sharedSecretDropHullWords` (`63` words of `zeroize32Words` followed at `+252`
    by `b #-252` targeting `+0`) pass `checkWordsTrapSafe` with `allowed = []`. -/
theorem sharedSecretDropHull_all_safe :
    checkWordsTrapSafe sharedSecretDropHullWords [] = true := by
  decide

/-- `RegionWordsSafe` for `sharedSecretDropHullRegion m` at any `m : BitVec 64`. -/
theorem sharedSecretDropHull_regionWordsSafe (m : BitVec 64) :
    RegionWordsSafe (sharedSecretDropHullRegion m) :=
  regionWordsSafe_single m sharedSecretDropHull_all_safe

/-- Full 64-word `hasWords` witness for `pureWordsProg m sharedSecretDropHullWords`. -/
theorem pureWordsProg_sharedSecretDropHull_hasWords (m : BitVec 64) :
    (pureWordsProg m sharedSecretDropHullWords).hasWords m sharedSecretDropHullWords :=
  pureWordsProg_hasWords (by decide +kernel) (by
    change ((List.range sharedSecretDropHullWords.length).all fun i =>
      (pureWordsProg 0#64 sharedSecretDropHullWords).readWordOff (4 * i) ==
        sharedSecretDropHullWords[i]?) = true
    decide +kernel)

theorem sharedSecretDropHullRegion_hasWords_of_hasWords {P_sub : Program} {m : BitVec 64}
    (hHas : P_sub.hasWords m sharedSecretDropHullWords) :
    RegionHasWords [P_sub] (sharedSecretDropHullRegion m) := by
  intro blk hmem
  rw [sharedSecretDropHullRegion, List.mem_singleton] at hmem
  subst hmem
  exact ⟨P_sub, List.mem_singleton.mpr rfl, hHas⟩

theorem sharedSecretDropHullRegion_hasWords_pure (m : BitVec 64) :
    RegionHasWords [pureWordsProg m sharedSecretDropHullWords] (sharedSecretDropHullRegion m) :=
  sharedSecretDropHullRegion_hasWords_of_hasWords (pureWordsProg_sharedSecretDropHull_hasWords m)

theorem sharedSecretDropHullRegion_codeLoaded_iff {P_sub : Program} {mem : Memory} :
    RegionCodeLoaded [P_sub] mem ↔ P_sub.CodeLoaded mem := by
  constructor
  · intro h; exact h P_sub (List.mem_singleton.mpr rfl)
  · intro h P hP; rw [List.mem_singleton] at hP; subst hP; exact h

theorem sharedSecretDropHull_codeLoaded_stripExecOutside {keep : BitVec 64 → Bool} {P_sub : Program}
    {mem : Memory}
    (hkeep : ∀ off : Nat, off < P_sub.code.length →
      keep (P_sub.base + BitVec.ofNat 64 off) = true)
    (hL : P_sub.CodeLoaded mem) :
    P_sub.CodeLoaded (ProofLib.stripExecOutside keep mem) :=
  codeLoaded_stripExecOutside_of_keep hkeep hL

/-- Entry-state `lr` guard at `s0` for `SharedSecret::drop` stub replay
    (`stubPc = m + sharedSecretDropEntryOff` on stock/C2). -/
@[expose] def SharedSecretDropEntryGuard (m stubPc : BitVec 64) (s0 : State) : Prop :=
  keepSharedSecretDropHull m (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

theorem sharedSecretDropEntryGuard_iff_trapEntryGuard (m stubPc : BitVec 64) (s0 : State) :
    SharedSecretDropEntryGuard m stubPc s0 ↔
      TrapEntryGuard (sharedSecretDropHullRegion m) stubPc s0 := by
  simp only [SharedSecretDropEntryGuard, TrapEntryGuard, keepOf_sharedSecretDropHullRegion_apply]

/-! ## 3. `TrapHook` Instances (Stock `zeroizeSecretHook`, Plain Ghost, and `K` Ghost) -/

/-- Stock `zeroizeSecretHook` zeroes 32 bytes at `x0` and returns to `lr` while `.Running` with `lr`
    unchanged, so it satisfies `TrapHook L` for every `L : BitVec 64`. -/
theorem trapHook_zeroizeSecretHook (L : BitVec 64) :
    TrapHook L zeroizeSecretHook := by
  intro w hrun hlr
  unfold zeroizeSecretHook retHook
  exact Or.inr ⟨hrun, hlr, hlr⟩

theorem trapHook_keepFsTrace_zeroizeSecretHook (L : BitVec 64) :
    TrapHook L (keepFsTrace zeroizeSecretHook) := by
  intro w hrun hlr
  rw [keepFsTrace_zeroizeSecretHook_eq]
  exact trapHook_zeroizeSecretHook L w hrun hlr

/-- Plain `zeroizeGhostHook` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_zeroizeGhostHook {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (zeroizeGhostHook keepR P_real P_sub entryTarget) :=
  trapHook_linkedCallHook hkeepL (trapHook_keepFsTrace_zeroizeSecretHook L)

theorem trapHook_zeroizeGhostHook_of_cover_static {keepR : BitVec 64 → Bool} {entry L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hL : keepStaticSecretDrop entry L = true) :
    TrapHook L (zeroizeGhostHook keepR P_real P_sub entryTarget) :=
  trapHook_zeroizeGhostHook P_real P_sub entryTarget (hcover L hL)

theorem trapHook_zeroizeGhostHook_of_cover_shared {keepR : BitVec 64 → Bool} {m L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hL : keepSharedSecretDropHull m L = true) :
    TrapHook L (zeroizeGhostHook keepR P_real P_sub entryTarget) :=
  trapHook_zeroizeGhostHook P_real P_sub entryTarget (hcover L hL)

/-- Plain `W`-independent `f3EmptyZeroizeGhostHook` satisfies `TrapHook L` whenever
    `keepR L = true`. -/
theorem trapHook_f3EmptyZeroizeGhostHook {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (f3EmptyZeroizeGhostHook keepR P_sub entryTarget) := by
  rw [f3EmptyZeroizeGhostHook_eq]
  exact trapHook_zeroizeGhostHook _ P_sub entryTarget hkeepL

theorem trapHook_f3EmptyZeroizeGhostHook_of_cover_static {keepR : BitVec 64 → Bool}
    {entry L : BitVec 64} (P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hL : keepStaticSecretDrop entry L = true) :
    TrapHook L (f3EmptyZeroizeGhostHook keepR P_sub entryTarget) :=
  trapHook_f3EmptyZeroizeGhostHook P_sub entryTarget (hcover L hL)

theorem trapHook_f3EmptyZeroizeGhostHook_of_cover_shared {keepR : BitVec 64 → Bool}
    {m L : BitVec 64} (P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hL : keepSharedSecretDropHull m L = true) :
    TrapHook L (f3EmptyZeroizeGhostHook keepR P_sub entryTarget) :=
  trapHook_f3EmptyZeroizeGhostHook P_sub entryTarget (hcover L hL)

/-- `K`-narrowed `zeroizeGhostHookK` transitions to `.Exception` whenever `keepR L = true`, so it
    satisfies `TrapHook L`. -/
theorem trapHook_zeroizeGhostHookK {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (zeroizeGhostHookK keepR P_real P_sub entryTarget) :=
  trapHook_of_exception_on_keepLr fun w _ hlr =>
    ⟨"ghost-hook precondition violated", by rw [zeroizeGhostHookK_of_keepLr_true (hlr ▸ hkeepL)]⟩

theorem trapHook_zeroizeGhostHookK_of_cover_static {keepR : BitVec 64 → Bool} {entry L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hL : keepStaticSecretDrop entry L = true) :
    TrapHook L (zeroizeGhostHookK keepR P_real P_sub entryTarget) :=
  trapHook_zeroizeGhostHookK P_real P_sub entryTarget (hcover L hL)

theorem trapHook_zeroizeGhostHookK_of_cover_shared {keepR : BitVec 64 → Bool} {m L : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hL : keepSharedSecretDropHull m L = true) :
    TrapHook L (zeroizeGhostHookK keepR P_real P_sub entryTarget) :=
  trapHook_zeroizeGhostHookK P_real P_sub entryTarget (hcover L hL)

/-- `K`-narrowed `W`-independent `f3EmptyZeroizeGhostHookK` satisfies `TrapHook L` whenever
    `keepR L = true`. -/
theorem trapHook_f3EmptyZeroizeGhostHookK {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget) := by
  rw [f3EmptyZeroizeGhostHookK_eq]
  exact trapHook_zeroizeGhostHookK _ P_sub entryTarget hkeepL

theorem trapHook_f3EmptyZeroizeGhostHookK_of_cover_static {keepR : BitVec 64 → Bool}
    {entry L : BitVec 64} (P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hL : keepStaticSecretDrop entry L = true) :
    TrapHook L (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget) :=
  trapHook_f3EmptyZeroizeGhostHookK P_sub entryTarget (hcover L hL)

theorem trapHook_f3EmptyZeroizeGhostHookK_of_cover_shared {keepR : BitVec 64 → Bool}
    {m L : BitVec 64} (P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hL : keepSharedSecretDropHull m L = true) :
    TrapHook L (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget) :=
  trapHook_f3EmptyZeroizeGhostHookK P_sub entryTarget (hcover L hL)

/-- Explicit `SharedSecret::drop` aliases (`entryTarget := m + sharedSecretDropEntryOff`). -/
theorem trapHook_sharedSecretDropGhostHook {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (m : BitVec 64) (hkeepL : keepR L = true) :
    TrapHook L (sharedSecretDropGhostHook keepR P_real P_sub m) :=
  trapHook_zeroizeGhostHook P_real P_sub (m + sharedSecretDropEntryOff) hkeepL

theorem trapHook_sharedSecretDropGhostHook_of_cover {keepR : BitVec 64 → Bool} {m L : BitVec 64}
    (P_real P_sub : Program)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hL : keepSharedSecretDropHull m L = true) :
    TrapHook L (sharedSecretDropGhostHook keepR P_real P_sub m) :=
  trapHook_zeroizeGhostHook_of_cover_shared P_real P_sub (m + sharedSecretDropEntryOff) hcover hL

theorem trapHook_f3EmptySharedSecretDropGhostHook {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_sub : Program) (m : BitVec 64) (hkeepL : keepR L = true) :
    TrapHook L (f3EmptySharedSecretDropGhostHook keepR P_sub m) :=
  trapHook_f3EmptyZeroizeGhostHook P_sub (m + sharedSecretDropEntryOff) hkeepL

theorem trapHook_f3EmptySharedSecretDropGhostHook_of_cover {keepR : BitVec 64 → Bool}
    {m L : BitVec 64} (P_sub : Program)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hL : keepSharedSecretDropHull m L = true) :
    TrapHook L (f3EmptySharedSecretDropGhostHook keepR P_sub m) :=
  trapHook_f3EmptyZeroizeGhostHook_of_cover_shared P_sub (m + sharedSecretDropEntryOff) hcover hL

theorem trapHook_sharedSecretDropGhostHookK {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (m : BitVec 64) (hkeepL : keepR L = true) :
    TrapHook L (sharedSecretDropGhostHookK keepR P_real P_sub m) :=
  trapHook_zeroizeGhostHookK P_real P_sub (m + sharedSecretDropEntryOff) hkeepL

theorem trapHook_sharedSecretDropGhostHookK_of_cover {keepR : BitVec 64 → Bool} {m L : BitVec 64}
    (P_real P_sub : Program)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hL : keepSharedSecretDropHull m L = true) :
    TrapHook L (sharedSecretDropGhostHookK keepR P_real P_sub m) :=
  trapHook_zeroizeGhostHookK_of_cover_shared P_real P_sub (m + sharedSecretDropEntryOff) hcover hL

theorem trapHook_f3EmptySharedSecretDropGhostHookK {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_sub : Program) (m : BitVec 64) (hkeepL : keepR L = true) :
    TrapHook L (f3EmptySharedSecretDropGhostHookK keepR P_sub m) :=
  trapHook_f3EmptyZeroizeGhostHookK P_sub (m + sharedSecretDropEntryOff) hkeepL

theorem trapHook_f3EmptySharedSecretDropGhostHookK_of_cover {keepR : BitVec 64 → Bool}
    {m L : BitVec 64} (P_sub : Program)
    (hcover : ∀ pc, keepSharedSecretDropHull m pc = true → keepR pc = true)
    (hL : keepSharedSecretDropHull m L = true) :
    TrapHook L (f3EmptySharedSecretDropGhostHookK keepR P_sub m) :=
  trapHook_f3EmptyZeroizeGhostHookK_of_cover_shared P_sub (m + sharedSecretDropEntryOff) hcover hL

/-! ## 4. Row 1 (`StaticSecret::drop`) Post-Hook & At-Stub Trap Corollaries for Card `c` -/

theorem staticSecretDrop_lr_trap_after_hook_ret
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (htrap_u : keepStaticSecretDrop entry (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepStaticSecretDrop entry (u.readReg64 .lr) = true →
      ∀ pc, keepStaticSecretDrop entry pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hout_sf : sf.status = .Running → keepStaticSecretDrop entry sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  rw [← keepOf_staticSecretDropRegion_apply entry]
  exact lr_trap_after_hook_ret
    (staticSecretDrop_regionWordsSafe entry)
    (staticSecretDropRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_staticSecretDropRegion_apply entry _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_staticSecretDropRegion_apply entry _ ▸ hL) pc
        (keepOf_staticSecretDropRegion_apply entry _ ▸ hkp))
    (staticSecretDropRegion_codeLoaded_iff.mpr hCode_fu)
    hrest hrun_u
    (fun hr => (keepOf_staticSecretDropRegion_apply entry _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

theorem staticSecretDrop_lr_trap_after_hook_returned
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_u : State → State} {s0 u sf : State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (htrap_u : keepStaticSecretDrop entry (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepStaticSecretDrop entry (u.readReg64 .lr) = true →
      ∀ pc, keepStaticSecretDrop entry pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepStaticSecretDrop entry (s0.readReg64 .lr) = false) :
    keepStaticSecretDrop entry (u.readReg64 .lr) = false :=
  staticSecretDrop_lr_trap_after_hook_ret hHas htrap_u hreg_ext hCode_fu hrest hrun_u
    (fun _ => hpc_sf ▸ hlr_s0)
    (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- **Card-`c` `InvS u` post-hook theorem
    (`staticSecretDrop_keepLr_false_after_hook_of_codeLoaded_u`):**
    Consumes `P_sub.CodeLoaded u.mem` at `u` + `u.mem.KeepsFrozen (f_stub u).mem` (per `H1`). -/
theorem staticSecretDrop_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hreg_ext : ∀ pc : BitVec 64, keepStaticSecretDrop entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepStaticSecretDrop entry (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  intro u hc_u hsteps_fu_sf hrun_u hkf
  exact staticSecretDrop_lr_trap_after_hook_ret hHas
    (fun hL => htrap_stub _ hL)
    (fun hL pc hkp => (hreg_ext pc hkp).imp id fun ⟨f, hf, htf⟩ => ⟨f, hf, htf _ hL⟩)
    (hc_u.of_keepsFrozen hkf)
    hsteps_fu_sf hrun_u
    (fun hrun_sf => hret_pc hrun_sf ▸ hlr_s0)
    hnoex_sf hnhalt_sf

theorem staticSecretDrop_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hreg_ext : ∀ pc : BitVec 64, keepStaticSecretDrop entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepStaticSecretDrop entry (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact staticSecretDrop_keepLr_false_after_hook_of_codeLoaded_u hHas hreg_ext htrap_stub
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Trajectory post-hook theorem propagating `hc_codeLoaded : P_sub.CodeLoaded s0.mem`.
    Note (`H1`): `GhostRowReplayOn.replay_at_stub` provides `InvS u` (`P_sub.CodeLoaded u.mem`);
    prefer `staticSecretDrop_keepLr_false_after_hook_of_codeLoaded_u` there. -/
theorem staticSecretDrop_keepLr_false_after_hook_of_outcome
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hreg_ext : ∀ pc : BitVec 64, keepStaticSecretDrop entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepStaticSecretDrop entry (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_fu_sf hrun_u hkf
  rw [← keepOf_staticSecretDropRegion_apply entry]
  exact keepLr_false_after_hook_of_outcome
    (staticSecretDrop_regionWordsSafe entry)
    (staticSecretDropRegion_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_staticSecretDropRegion_apply entry _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ =>
          ⟨f, hf, fun L hL => htf L (keepOf_staticSecretDropRegion_apply entry _ ▸ hL)⟩)
    (fun L hL => htrap_stub L (keepOf_staticSecretDropRegion_apply entry _ ▸ hL))
    (staticSecretDropRegion_codeLoaded_iff.mpr hc_codeLoaded)
    ((keepOf_staticSecretDropRegion_apply entry _).trans hlr_s0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_fu_sf hrun_u hkf

theorem staticSecretDrop_keepLr_false_after_hook_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hreg_ext : ∀ pc : BitVec 64, keepStaticSecretDrop entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepStaticSecretDrop entry (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact staticSecretDrop_keepLr_false_after_hook_of_outcome hHas hreg_ext htrap_stub
    hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem staticSecretDrop_lr_trap_at_call_ret
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (htrap_u : keepStaticSecretDrop entry (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepStaticSecretDrop entry (u.readReg64 .lr) = true →
      ∀ pc, keepStaticSecretDrop entry pc = true →
        P_ghost.externAt? pc = none ∨
          ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hu_ne_sf : sf.status = .Running → sf.pc ≠ u.pc)
    (hout_sf : sf.status = .Running → keepStaticSecretDrop entry sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  rw [← keepOf_staticSecretDropRegion_apply entry]
  exact lr_trap_at_call_ret
    (staticSecretDrop_regionWordsSafe entry)
    (staticSecretDropRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_staticSecretDropRegion_apply entry _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_staticSecretDropRegion_apply entry _ ▸ hL) pc
        (keepOf_staticSecretDropRegion_apply entry _ ▸ hkp))
    hext_u
    (staticSecretDropRegion_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hu_ne_sf
    (fun hr => (keepOf_staticSecretDropRegion_apply entry _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

theorem staticSecretDrop_lr_trap_at_call
    {P_ghost P_sub : Program} {entry : BitVec 64} {f_u : State → State} {u sf : State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (htrap_u : keepStaticSecretDrop entry (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hno_ext : ∀ pc, keepStaticSecretDrop entry pc = true →
      P_ghost.externAt? pc = none ∨ P_ghost.externAt? pc = some f_u)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  rw [← keepOf_staticSecretDropRegion_apply entry]
  exact lr_trap_at_call
    (staticSecretDrop_regionWordsSafe entry)
    (staticSecretDropRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_staticSecretDropRegion_apply entry _ ▸ hL))
    (fun pc hkp => hno_ext pc (keepOf_staticSecretDropRegion_apply entry _ ▸ hkp))
    hext_u
    (staticSecretDropRegion_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hrun_sf hnoex_sf hnhalt_sf

theorem staticSecretDrop_keepLr_false_at_stub_of_outcome
    {P_ghost P_sub : Program} {entry stubPc : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hreg_ext : ∀ pc : BitVec 64, keepStaticSecretDrop entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : StaticSecretDropEntryGuard entry stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hpc_u
  rw [← keepOf_staticSecretDropRegion_apply entry]
  exact keepLr_false_at_stub_of_outcome
    (staticSecretDrop_regionWordsSafe entry)
    (staticSecretDropRegion_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_staticSecretDropRegion_apply entry _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ =>
          ⟨f, hf, fun L hL => htf L (keepOf_staticSecretDropRegion_apply entry _ ▸ hL)⟩)
    hext_stub
    (fun L hL => htrap_stub L (keepOf_staticSecretDropRegion_apply entry _ ▸ hL))
    (staticSecretDropRegion_codeLoaded_iff.mpr hc_codeLoaded)
    ((staticSecretDropEntryGuard_iff_trapEntryGuard entry stubPc s0).mp hGuard0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_u_sf hrun_u hpc_u

theorem staticSecretDrop_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {entry stubPc : BitVec 64} {f_stub : State → State}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hreg_ext : ∀ pc : BitVec 64, keepStaticSecretDrop entry pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepStaticSecretDrop entry L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : StaticSecretDropEntryGuard entry stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact staticSecretDrop_keepLr_false_at_stub_of_outcome hHas hreg_ext hext_stub htrap_stub
    hc_codeLoaded hGuard0 hret_pc hnoex_sf hnhalt_sf

/-- Parametric `∀ L` entry-excluded adapter for `keepStaticSecretDrop entry`. -/
theorem staticSecretDrop_reg_ext_of_entry_excluded {P_ghost : Program} {entry : BitVec 64}
    {entries : List (BitVec 64)}
    (hno_ext_outside : ∀ pc,
      keepStaticSecretDrop entry pc = true → pc ∉ entries → P_ghost.externAt? pc = none)
    (hentries : ∀ e ∈ entries, P_ghost.externAt? e = none ∨
      ∃ f, P_ghost.externAt? e = some f ∧ ∀ L, keepStaticSecretDrop entry L = true → TrapHook L f) :
    ∀ pc, keepStaticSecretDrop entry pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepStaticSecretDrop entry L = true → TrapHook L f := by
  intro pc hkp
  by_cases hmem : pc ∈ entries
  · exact hentries pc hmem
  · exact Or.inl (hno_ext_outside pc hkp hmem)

/-- Single-stub specialization (`entries := [stubPc]`; `stubPc = entry` on stock/C2). -/
theorem staticSecretDrop_reg_ext_of_stub_excluded {P_ghost : Program} {entry stubPc : BitVec 64}
    {f_stub : State → State}
    (hno_ext_outside : ∀ pc,
      keepStaticSecretDrop entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L, keepStaticSecretDrop entry L = true → TrapHook L f_stub) :
    ∀ pc, keepStaticSecretDrop entry pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepStaticSecretDrop entry L = true → TrapHook L f := by
  refine staticSecretDrop_reg_ext_of_entry_excluded (entries := [stubPc])
    (fun pc hkp hmem => hno_ext_outside pc hkp (fun hEq => hmem (List.mem_singleton.mpr hEq))) ?_
  intro e he
  rw [List.mem_singleton.mp he]
  exact Or.inr ⟨f_stub, hext_stub, htrap_stub⟩

/-- Entry-excluded card-`c` `InvS u` post-hook theorem for `StaticSecret::drop`
    (`f3EmptyZeroizeGhostHook`, `entries = [entry]` when `stubPc = entry`). -/
theorem f3EmptyStaticSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepStaticSecretDrop entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyZeroizeGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepStaticSecretDrop entry (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyZeroizeGhostHook keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyZeroizeGhostHook keepR P_sub entryTarget u).mem →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false :=
  staticSecretDrop_keepLr_false_after_hook_of_codeLoaded_u hHas
    (staticSecretDrop_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyZeroizeGhostHook_of_cover_static P_sub entryTarget hcover hL))
    (fun _ hL => trapHook_f3EmptyZeroizeGhostHook_of_cover_static P_sub entryTarget hcover hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem f3EmptyStaticSecretDropGhostHook_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepStaticSecretDrop entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyZeroizeGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepStaticSecretDrop entry (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyZeroizeGhostHook keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyZeroizeGhostHook keepR P_sub entryTarget u).mem →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact f3EmptyStaticSecretDropGhostHook_keepLr_false_after_hook_of_codeLoaded_u hHas hcover
    hno_ext_outside hext_stub hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem f3EmptyStaticSecretDropGhostHook_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepStaticSecretDrop entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyZeroizeGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : StaticSecretDropEntryGuard entry stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false :=
  staticSecretDrop_keepLr_false_at_stub_of_subroutineOutcome hHas
    (staticSecretDrop_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyZeroizeGhostHook_of_cover_static P_sub entryTarget hcover hL))
    hext_stub
    (fun _ hL => trapHook_f3EmptyZeroizeGhostHook_of_cover_static P_sub entryTarget hcover hL)
    hc_codeLoaded hGuard0 hout

theorem f3EmptyStaticSecretDropGhostHookK_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepStaticSecretDrop entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepStaticSecretDrop entry (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget u).mem →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false :=
  staticSecretDrop_keepLr_false_after_hook_of_codeLoaded_u hHas
    (staticSecretDrop_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyZeroizeGhostHookK_of_cover_static P_sub entryTarget hcover hL))
    (fun _ hL => trapHook_f3EmptyZeroizeGhostHookK_of_cover_static P_sub entryTarget hcover hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem f3EmptyStaticSecretDropGhostHookK_keepLr_false_after_hook_of_subroutineOutcome_u
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepStaticSecretDrop entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepStaticSecretDrop entry (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget u).mem →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact f3EmptyStaticSecretDropGhostHookK_keepLr_false_after_hook_of_codeLoaded_u hHas hcover
    hno_ext_outside hext_stub hlr_s0 hret_pc hnoex_sf hnhalt_sf

theorem f3EmptyStaticSecretDropGhostHookK_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {entry stubPc entryTarget : BitVec 64}
    (hHas : P_sub.hasWords entry zeroize32Words)
    (hcover : ∀ pc, keepStaticSecretDrop entry pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepStaticSecretDrop entry pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyZeroizeGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : StaticSecretDropEntryGuard entry stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepStaticSecretDrop entry (u.readReg64 .lr) = false :=
  staticSecretDrop_keepLr_false_at_stub_of_subroutineOutcome hHas
    (staticSecretDrop_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyZeroizeGhostHookK_of_cover_static P_sub entryTarget hcover hL))
    hext_stub
    (fun _ hL => trapHook_f3EmptyZeroizeGhostHookK_of_cover_static P_sub entryTarget hcover hL)
    hc_codeLoaded hGuard0 hout

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeLrTrap

