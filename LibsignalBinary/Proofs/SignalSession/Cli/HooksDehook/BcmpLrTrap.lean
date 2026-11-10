/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import

/-!
# Closed-`lr` Trap & Subroutine-Outcome `keepBcmpHull lr = false` Suite (`HooksDehook.BcmpLrTrap`)

Card **L1-d** of the `bcmp` de-hook row (`dehook_plan.md` §1, §5 L1-d; C11 §8.2): proves that
inside the 56-byte stock-order `memcmp ++ bcmp` hull at `m` (with `memcmp` at `m` and `bcmp` at
`m + memcmpByteLen`), no execution path writes `x30` (`lr`) or leaves the hull except via `ret x30`
to `lr`. Consequently, whenever a ghost run starting with `keepBcmpHull m (s0.readReg64 .lr) = false`
terminates without `.Exception`/`.Halted` and (if `.Running`) returns to `s0.readReg64 .lr`, every
intermediate call site `u` satisfies `keepBcmpHull m (u.readReg64 .lr) = false`.

## Summary of Exported Results
1. **Stock-Order 56 B `memcmp ++ bcmp` Hull (`keepBcmpHull`, `bcmpHullRegion`, `bcmpHull_regionWordsSafe`):**
   - Certifies `memcmp_bcmp_hull_all_safe : checkWordsTrapSafe (bcmpHullWords 0#64 (fun _ => 0#64)) [] = true`
     by reusing `TrapSafeWords.bcmp_memcmp_all_safe` (stock/2C order: 13-word `memcmp` followed by
     1-word `bcmp`), proves `m`-independence
     `bcmpHullWords_eq_canonical` for any `m` and `resolve "memcmp" = m`, and lifts to
     `RegionWordsSafe (bcmpHullRegion m resolve)`.
2. **`TrapHook` Instances (Idealized, Fallback, Plain Ghost, and `K` Ghost):**
   - `trapHook_cliBcmpHook`, `trapHook_keepFsTrace_cliBcmpHook`, `trapHook_hookBcmpFallback`,
     `trapHook_keepFsTrace_hookBcmpFallback` (`∀ L : BitVec 64`).
   - `trapHook_bcmpGhostFn`, `trapHook_f3EmptyBcmpGhostHook` (plain `linkedCallHook` / `f3LinkedCallHook`),
     and `trapHook_bcmpGhostFnK`, `trapHook_f3EmptyBcmpGhostHookK` (`K`-narrowed).
3. **Post-Hook Continuation & At-Stub `SubroutineOutcome` Trap Theorems for Card `c`:**
   - **Post-hook continuation form** (`Steps P_ghost (f_stub u) sf` + `u.mem.KeepsFrozen (f_stub u).mem`,
     matching `GhostRowReplayOn.replay_at_stub` Arm 2 directly without needing `s0.readReg64 .lr ≠ stubPc`):
     `bcmpHull_lr_trap_after_hook_ret` (consuming `P_sub.CodeLoaded (f_u u).mem` from `InvS u` + `KeepsFrozen`),
     `bcmpHull_keepLr_false_after_hook_of_codeLoaded_u` (consuming `P_sub.CodeLoaded u.mem` + `KeepsFrozen`),
     `bcmpHull_lr_trap_after_hook_returned`, `bcmpHull_keepLr_false_after_hook_of_outcome`,
     `bcmpHull_keepLr_false_after_hook_of_subroutineOutcome`, and entry-excluded
     `f3EmptyBcmpGhostHook{,K}` specializations (`pc ≠ stubPc`).
   - **At-stub trajectory form** (`Steps P_ghost s0 u` + `Steps P_ghost u sf` + `BcmpEntryGuard m stubPc s0`,
     matching `MemsetKeepLrOfOutcome.memset_keepLr_false_at_stub_of_{outcome,subroutineOutcome}`):
     `bcmpHull_lr_trap_at_call_ret`, `bcmpHull_lr_trap_at_call`,
     `bcmpHull_keepLr_false_at_stub_of_outcome`, `bcmpHull_keepLr_false_at_stub_of_subroutineOutcome`,
     and entry-excluded `f3EmptyBcmpGhostHook{,K}` specializations (`pc ≠ stubPc`).
   - **2-block `bcmpMemcmp2Region` (`keepBcmpMemcmp2`) wrappers** for non-adjacent placements within
     `Obj.BranchInRange bcmpBase memcmpBase`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap

open Arm64 ProofLib
open Arm64.Process (pureWordsProg)
open VerifiedLibraries.Musl (bcmpWords bcmpCalls memcmpLibcaWords)
open CryptoVerification.SignalSession (cliBcmpHook)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (keepFsTrace)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG (
  subroutineOutcome_running_pc_and_noFault
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapRegion keepBlock keepOf keepOf_singleton
  RegionWordsSafe RegionHasWords RegionCodeLoaded
  codeLoaded_stripExecOutside_of_keep
  TrapHook trapHook_of_exception_on_keepLr trapHook_linkedCallHook
  trap_impossible lr_trap_at_call_ret lr_trap_at_call
  TrapEntryGuard keepLr_false_at_stub_of_outcome
  checkWordsTrapSafe regionWordsSafe_single bcmp_memcmp_all_safe bcmp_memcmp_regionWordsSafe
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpCode (
  memcmpByteLen memcmpByteLen_eq bcmpHullWords pureWordsProg_bcmpHull_hasWords hookBcmpFallback
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhost (
  bcmpGhostFn bcmpGhostFnK bcmpGhostFnK_of_keepLr_true
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpGhostK (
  f3EmptyBcmpGhostHook f3EmptyBcmpGhostHookK f3EmptyBcmpGhostHook_eq f3EmptyBcmpGhostHookK_eq
)

/-! ## 1. Stock-Order 56 B `memcmp ++ bcmp` Hull (`keepBcmpHull`, `bcmpHullRegion`, `RegionWordsSafe`) -/

/-- Byte length (`56`) of the contiguous 14-word `memcmp ++ bcmp` stock `libc.a` hull
    (`13` words of `memcmpLibcaWords` + `1` word of `bcmpWords`). -/
@[expose] def bcmpHullByteLen : Nat :=
  4 * (memcmpLibcaWords.length + bcmpWords.length)

theorem bcmpHullByteLen_eq : bcmpHullByteLen = 56 := rfl

theorem bcmpHullWords_length (m : BitVec 64) (resolve : String → BitVec 64) :
    (bcmpHullWords m resolve).length = 14 := by
  simp [bcmpHullWords, Obj.patchCalls, memcmpLibcaWords, bcmpWords]

theorem four_mul_bcmpHullWords_length (m : BitVec 64)
    (resolve : String → BitVec 64) :
    4 * (bcmpHullWords m resolve).length = bcmpHullByteLen := by
  rw [bcmpHullWords_length, bcmpHullByteLen_eq]

/-- Kept-region byte predicate `[m, m + 56)` for the contiguous `memcmp ++ bcmp` hull at `m`
    (`memcmp` at `m`, `bcmp` entry at `m + memcmpByteLen`). -/
@[expose] def keepBcmpHull (m : BitVec 64) : BitVec 64 → Bool :=
  keepBlock m bcmpHullByteLen

theorem keepBcmpHull_iff (m pc : BitVec 64) :
    keepBcmpHull m pc = true ↔ (pc - m).toNat < bcmpHullByteLen := by
  simp [keepBcmpHull, keepBlock, decide_eq_true_eq]

/-- The `bcmp` entry `m + memcmpByteLen` lies inside `keepBcmpHull m`. -/
theorem keepBcmpHull_entry (m : BitVec 64) :
    keepBcmpHull m (m + memcmpByteLen) = true := by
  rw [keepBcmpHull_iff, bcmpHullByteLen_eq]
  have hsub : m + memcmpByteLen - m = memcmpByteLen := by bv_omega
  rw [hsub, memcmpByteLen_eq]
  decide

/-- Every byte in the 52 B `memcmp` subrange `[m, m + 52)` lies inside `keepBcmpHull m`. -/
theorem keepBcmpHull_of_memcmp {m pc : BitVec 64}
    (h : keepBlock m (4 * memcmpLibcaWords.length) pc = true) :
    keepBcmpHull m pc = true := by
  simp only [keepBlock, decide_eq_true_eq] at h
  rw [keepBcmpHull_iff, bcmpHullByteLen_eq]
  have hlen : 4 * memcmpLibcaWords.length = 52 := rfl
  omega

/-- Every byte in the 4 B `bcmp` subrange `[m + memcmpByteLen, m + memcmpByteLen + 4)` lies
    inside `keepBcmpHull m`. -/
theorem keepBcmpHull_of_bcmp {m pc : BitVec 64}
    (h : keepBlock (m + memcmpByteLen) (4 * bcmpWords.length) pc = true) :
    keepBcmpHull m pc = true := by
  simp only [keepBlock, decide_eq_true_eq] at h
  rw [keepBcmpHull_iff, bcmpHullByteLen_eq]
  have hlen : 4 * bcmpWords.length = 4 := rfl
  rw [hlen, memcmpByteLen_eq] at h
  bv_omega

/-- Single-block `TrapRegion` for the contiguous 56 B `memcmp ++ bcmp` hull at `m`. -/
@[expose] def bcmpHullRegion (m : BitVec 64) (resolve : String → BitVec 64 := fun _ => m) :
    TrapRegion :=
  [(m, bcmpHullWords m resolve)]

/-- `keepOf (bcmpHullRegion m resolve)` equals `keepBcmpHull m` (independent of `resolve`). -/
theorem keepOf_bcmpHullRegion (m : BitVec 64) (resolve : String → BitVec 64 := fun _ => m) :
    keepOf (bcmpHullRegion m resolve) = keepBcmpHull m := by
  funext pc
  dsimp only [bcmpHullRegion]
  rw [keepOf_singleton, four_mul_bcmpHullWords_length]
  rfl

theorem keepOf_bcmpHullRegion_apply (m : BitVec 64) (resolve : String → BitVec 64)
    (pc : BitVec 64) :
    keepOf (bcmpHullRegion m resolve) pc = keepBcmpHull m pc :=
  congrFun (keepOf_bcmpHullRegion m resolve) pc

private theorem branchWord_eq_of_sub_eq {w : BitVec 32} {p1 t1 p2 t2 : BitVec 64}
    (h : t1 - p1 = t2 - p2) :
    Obj.branchWord w p1 t1 = Obj.branchWord w p2 t2 := by
  unfold Obj.branchWord
  rw [h]

/-- Placement invariance of `bcmpHullWords`: whenever `resolve "memcmp" = m`, the relative branch
    displacement `m - (m + memcmpByteLen)` equals `0#64 - (0#64 + memcmpByteLen)`, so
    `bcmpHullWords m resolve` equals the fixed 14-word list `bcmpHullWords 0#64 (fun _ => 0#64)`. -/
theorem bcmpHullWords_eq_canonical {m : BitVec 64} {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m) :
    bcmpHullWords m resolve = bcmpHullWords 0#64 (fun _ => 0#64) := by
  simp only [bcmpHullWords, Obj.patchCalls, bcmpWords,
    List.mapIdx_cons, List.mapIdx_nil, Nat.mul_zero]
  dsimp only [bcmpCalls, List.find?]
  congr 2
  apply branchWord_eq_of_sub_eq
  rw [hres]
  bv_omega

/-- Stock-order 14-word `memcmp ++ bcmp` hull (`memcmp` at `+0`, `bcmp` `b #-52` at `+52`) passes
    `checkWordsTrapSafe` (directly reuses S2 M2's `TrapSafeWords.bcmp_memcmp_all_safe`). -/
theorem memcmp_bcmp_hull_all_safe :
    checkWordsTrapSafe (bcmpHullWords 0#64 (fun _ => 0#64)) [] = true :=
  bcmp_memcmp_all_safe

/-- For any base `m` and `resolve` with `resolve "memcmp" = m`, `bcmpHullWords m resolve` passes
    `checkWordsTrapSafe`. -/
theorem bcmpHull_all_safe {m : BitVec 64} {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m) :
    checkWordsTrapSafe (bcmpHullWords m resolve) [] = true := by
  rw [bcmpHullWords_eq_canonical hres]
  exact memcmp_bcmp_hull_all_safe

/-- `RegionWordsSafe` for the contiguous 56 B `memcmp ++ bcmp` stock hull at any `m` with
    `resolve "memcmp" = m`. -/
theorem bcmpHull_regionWordsSafe {m : BitVec 64} {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m) :
    RegionWordsSafe (bcmpHullRegion m resolve) :=
  regionWordsSafe_single m (bcmpHull_all_safe hres)

/-- `RegionHasWords [P_sub] (bcmpHullRegion m resolve)` from `P_sub.hasWords m (bcmpHullWords m resolve)`. -/
theorem bcmpHullRegion_hasWords_of_hasWords {P_sub : Program} {m : BitVec 64}
    {resolve : String → BitVec 64}
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve)) :
    RegionHasWords [P_sub] (bcmpHullRegion m resolve) := by
  intro blk hmem
  rw [bcmpHullRegion, List.mem_singleton] at hmem
  subst hmem
  exact ⟨P_sub, List.mem_singleton.mpr rfl, hHas⟩

/-- Unconditional `RegionHasWords` for `pureWordsProg m (bcmpHullWords m resolve)`. -/
theorem bcmpHullRegion_hasWords_pure (m : BitVec 64)
    (resolve : String → BitVec 64 := fun _ => m) :
    RegionHasWords [pureWordsProg m (bcmpHullWords m resolve)] (bcmpHullRegion m resolve) :=
  bcmpHullRegion_hasWords_of_hasWords (pureWordsProg_bcmpHull_hasWords m resolve)

theorem bcmpHullRegion_codeLoaded_iff {P_sub : Program} {mem : Memory} :
    RegionCodeLoaded [P_sub] mem ↔ P_sub.CodeLoaded mem := by
  constructor
  · intro h
    exact h P_sub (List.mem_singleton.mpr rfl)
  · intro h P hP
    rw [List.mem_singleton] at hP
    subst hP
    exact h

theorem bcmpHull_codeLoaded_stripExecOutside {keep : BitVec 64 → Bool} {P_sub : Program}
    {mem : Memory}
    (hkeep : ∀ off : Nat, off < P_sub.code.length →
      keep (P_sub.base + BitVec.ofNat 64 off) = true)
    (hL : P_sub.CodeLoaded mem) :
    P_sub.CodeLoaded (ProofLib.stripExecOutside keep mem) :=
  codeLoaded_stripExecOutside_of_keep hkeep hL

/-- Entry-state `lr` guard at `s0` for `bcmp` stub replay (`keepBcmpHull m lr = false ∧ lr ≠ stubPc`). -/
@[expose] def BcmpEntryGuard (m stubPc : BitVec 64) (s0 : State) : Prop :=
  keepBcmpHull m (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

theorem bcmpEntryGuard_iff_trapEntryGuard (m stubPc : BitVec 64)
    (resolve : String → BitVec 64) (s0 : State) :
    BcmpEntryGuard m stubPc s0 ↔ TrapEntryGuard (bcmpHullRegion m resolve) stubPc s0 := by
  simp only [BcmpEntryGuard, TrapEntryGuard, keepOf_bcmpHullRegion_apply]

/-! ## 2. `TrapHook` Instances (Idealized, Fallback, Plain Ghost, and `K` Ghost) -/

/-- `cliBcmpHook bcmpFn` returns to `lr` while `.Running` with `lr` unchanged, so it satisfies
    `TrapHook L` for every `L : BitVec 64`. -/
theorem trapHook_cliBcmpHook
    (bcmpFn : List (BitVec 8) → List (BitVec 8) → BitVec 64) (L : BitVec 64) :
    TrapHook L (cliBcmpHook bcmpFn) :=
  fun _ hrun hlr => Or.inr ⟨hrun, hlr, hlr⟩

theorem trapHook_keepFsTrace_cliBcmpHook
    (bcmpFn : List (BitVec 8) → List (BitVec 8) → BitVec 64) (L : BitVec 64) :
    TrapHook L (keepFsTrace (cliBcmpHook bcmpFn)) :=
  fun _ hrun hlr => Or.inr ⟨hrun, hlr, hlr⟩

theorem trapHook_hookBcmpFallback (L : BitVec 64) :
    TrapHook L hookBcmpFallback :=
  trapHook_cliBcmpHook _ L

theorem trapHook_keepFsTrace_hookBcmpFallback (L : BitVec 64) :
    TrapHook L (keepFsTrace hookBcmpFallback) :=
  trapHook_keepFsTrace_cliBcmpHook _ L

/-- Plain `bcmpGhostFn` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_bcmpGhostFn {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entry : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (bcmpGhostFn keepR P_real P_sub entry) :=
  trapHook_linkedCallHook hkeepL (trapHook_keepFsTrace_hookBcmpFallback L)

theorem trapHook_bcmpGhostFn_of_cover {keepR : BitVec 64 → Bool} {m L : BitVec 64}
    (P_real P_sub : Program) (entry : BitVec 64)
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hL : keepBcmpHull m L = true) :
    TrapHook L (bcmpGhostFn keepR P_real P_sub entry) :=
  trapHook_bcmpGhostFn P_real P_sub entry (hcover L hL)

/-- Plain `W`-independent `f3EmptyBcmpGhostHook` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_f3EmptyBcmpGhostHook {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (f3EmptyBcmpGhostHook keepR P_sub entryTarget) := by
  rw [f3EmptyBcmpGhostHook_eq]
  exact trapHook_bcmpGhostFn _ P_sub entryTarget hkeepL

theorem trapHook_f3EmptyBcmpGhostHook_of_cover {keepR : BitVec 64 → Bool} {m L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hL : keepBcmpHull m L = true) :
    TrapHook L (f3EmptyBcmpGhostHook keepR P_sub entryTarget) :=
  trapHook_f3EmptyBcmpGhostHook P_sub entryTarget (hcover L hL)

/-- `K`-narrowed `bcmpGhostFnK` transitions to `.Exception` whenever `keepR L = true`, so it
    satisfies `TrapHook L`. -/
theorem trapHook_bcmpGhostFnK {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_real P_sub : Program) (entry : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (bcmpGhostFnK keepR P_real P_sub entry) :=
  trapHook_of_exception_on_keepLr fun w _ hlr =>
    ⟨"ghost-hook precondition violated", by rw [bcmpGhostFnK_of_keepLr_true (hlr ▸ hkeepL)]⟩

theorem trapHook_bcmpGhostFnK_of_cover {keepR : BitVec 64 → Bool} {m L : BitVec 64}
    (P_real P_sub : Program) (entry : BitVec 64)
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hL : keepBcmpHull m L = true) :
    TrapHook L (bcmpGhostFnK keepR P_real P_sub entry) :=
  trapHook_bcmpGhostFnK P_real P_sub entry (hcover L hL)

/-- `K`-narrowed `W`-independent `f3EmptyBcmpGhostHookK` satisfies `TrapHook L` whenever
    `keepR L = true`. -/
theorem trapHook_f3EmptyBcmpGhostHookK {keepR : BitVec 64 → Bool} {L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hkeepL : keepR L = true) :
    TrapHook L (f3EmptyBcmpGhostHookK keepR P_sub entryTarget) := by
  rw [f3EmptyBcmpGhostHookK_eq]
  exact trapHook_bcmpGhostFnK _ P_sub entryTarget hkeepL

theorem trapHook_f3EmptyBcmpGhostHookK_of_cover {keepR : BitVec 64 → Bool} {m L : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hL : keepBcmpHull m L = true) :
    TrapHook L (f3EmptyBcmpGhostHookK keepR P_sub entryTarget) :=
  trapHook_f3EmptyBcmpGhostHookK P_sub entryTarget (hcover L hL)

/-! ## 3. Generic Post-Hook Continuation & `SubroutineOutcome` Trap Corollaries -/

theorem regionCodeLoaded_of_keepsFrozen {progs : List Program} {m m' : Memory}
    (hCode : RegionCodeLoaded progs m) (hkf : m.KeepsFrozen m') :
    RegionCodeLoaded progs m' :=
  fun P_sub hmem => (hCode P_sub hmem).of_keepsFrozen hkf

/-- **Post-hook continuation `keepOf region lr = false` (`lr_trap_after_hook_ret`):**
    Multi-block counterpart of `MemcpyLrTrapRet.blk20_lr_trap_after_hook_ret`. Consumes
    `hrest : Steps P_ghost (f_u u) sf` directly (requiring zero `sf.pc ≠ stubPc` inequality). -/
theorem lr_trap_after_hook_ret
    {P_ghost : Program} {progs : List Program} {region : TrapRegion} {f_u : State → State}
    {u sf : State}
    (hSafe : RegionWordsSafe region)
    (hHas : RegionHasWords progs region)
    (htrap_u : keepOf region (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepOf region (u.readReg64 .lr) = true → ∀ pc, keepOf region pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : RegionCodeLoaded progs (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hout_sf : sf.status = .Running → keepOf region sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepOf region (u.readReg64 .lr) = false := by
  cases hkeepL : keepOf region (u.readReg64 .lr) with
  | false => rfl
  | true =>
    exfalso
    rcases htrap_u hkeepL u hrun_u rfl with ⟨msg, hex⟩ | ⟨hrun_v, hpc_v, hlr_v⟩
    · have heq := ProofLib.Variant.Steps.eq_of_not_running hrest (by rw [hex]; nofun)
      exact hnoex_sf msg (by rw [heq, hex])
    · exact trap_impossible hSafe hHas hkeepL (hreg_ext hkeepL) hrest
        hout_sf hnoex_sf hnhalt_sf ⟨hrun_v, hpc_v ▸ hkeepL, hlr_v, hCode_fu⟩

/-- **Trajectory post-hook `keepOf region lr = false` from outcome facts
    (`keepLr_false_after_hook_of_outcome`):**
    Directly matches `GhostRowReplayOn.replay_at_stub` Arm 2 (`Steps P_ghost s0 u`,
    `Steps P_ghost (f_stub u) sf`, `u.status = .Running`, `u.mem.KeepsFrozen (f_stub u).mem`). -/
theorem keepLr_false_after_hook_of_outcome
    {P_ghost : Program} {progs : List Program} {region : TrapRegion}
    {f_stub : State → State}
    (hSafe : RegionWordsSafe region)
    (hHas : RegionHasWords progs region)
    (hreg_ext : ∀ pc : BitVec 64, keepOf region pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepOf region L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepOf region L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : RegionCodeLoaded progs s0.mem)
    (hlr_s0 : keepOf region (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepOf region (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_fu_sf hrun_u hkf
  exact lr_trap_after_hook_ret hSafe hHas
    (fun hL => htrap_stub _ hL)
    (fun hL pc hkp => (hreg_ext pc hkp).imp id fun ⟨f, hf, htf⟩ => ⟨f, hf, htf _ hL⟩)
    (regionCodeLoaded_of_keepsFrozen (hc_codeLoaded.steps hsteps_s0_u) hkf)
    hsteps_fu_sf hrun_u
    (fun hrun_sf => hret_pc hrun_sf ▸ hlr_s0)
    hnoex_sf hnhalt_sf

/-- Direct `SubroutineOutcome` wrapper for `keepLr_false_after_hook_of_outcome`. -/
theorem keepLr_false_after_hook_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost : Program} {progs : List Program} {region : TrapRegion}
    {f_stub : State → State}
    (hSafe : RegionWordsSafe region)
    (hHas : RegionHasWords progs region)
    (hreg_ext : ∀ pc : BitVec 64, keepOf region pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepOf region L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepOf region L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : RegionCodeLoaded progs s0.mem)
    (hlr_s0 : keepOf region (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepOf region (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact keepLr_false_after_hook_of_outcome hSafe hHas hreg_ext htrap_stub
    hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Direct `SubroutineOutcome` wrapper for `TrapSafeWords.keepLr_false_at_stub_of_outcome`. -/
theorem keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost : Program} {progs : List Program} {region : TrapRegion}
    {stubPc : BitVec 64} {f_stub : State → State}
    (hSafe : RegionWordsSafe region)
    (hHas : RegionHasWords progs region)
    (hreg_ext : ∀ pc : BitVec 64, keepOf region pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepOf region L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepOf region L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : RegionCodeLoaded progs s0.mem)
    (hGuard0 : TrapEntryGuard region stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepOf region (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact keepLr_false_at_stub_of_outcome hSafe hHas hreg_ext hext_stub htrap_stub
    hc_codeLoaded hGuard0 hret_pc hnoex_sf hnhalt_sf

/-! ## 4. Concrete 56 B `bcmp` Hull (`keepBcmpHull m`) & 2-Block Specializations for Card `c` -/

/-- Post-hook continuation `keepBcmpHull m (u.readReg64 .lr) = false` on the 56 B stock hull. -/
theorem bcmpHull_lr_trap_after_hook_ret
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_u : State → State} {u sf : State}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (htrap_u : keepBcmpHull m (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBcmpHull m (u.readReg64 .lr) = true → ∀ pc, keepBcmpHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hout_sf : sf.status = .Running → keepBcmpHull m sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepBcmpHull m (u.readReg64 .lr) = false := by
  rw [← keepOf_bcmpHullRegion_apply m resolve]
  exact lr_trap_after_hook_ret
    (bcmpHull_regionWordsSafe hres)
    (bcmpHullRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_bcmpHullRegion_apply m resolve _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_bcmpHullRegion_apply m resolve _ ▸ hL) pc
        (keepOf_bcmpHullRegion_apply m resolve _ ▸ hkp))
    (bcmpHullRegion_codeLoaded_iff.mpr hCode_fu)
    hrest hrun_u
    (fun hr => (keepOf_bcmpHullRegion_apply m resolve _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

/-- Post-hook `Returned`-case `keepBcmpHull m (u.readReg64 .lr) = false` when `sf` is `.Running` at
    `sf.pc = s0.readReg64 .lr`. -/
theorem bcmpHull_lr_trap_after_hook_returned
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_u : State → State} {s0 u sf : State}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (htrap_u : keepBcmpHull m (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBcmpHull m (u.readReg64 .lr) = true → ∀ pc, keepBcmpHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hCode_fu : P_sub.CodeLoaded (f_u u).mem)
    (hrest : Steps P_ghost (f_u u) sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status = .Running)
    (hpc_sf : sf.pc = s0.readReg64 .lr)
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false) :
    keepBcmpHull m (u.readReg64 .lr) = false :=
  bcmpHull_lr_trap_after_hook_ret hres hHas htrap_u hreg_ext hCode_fu hrest hrun_u
    (fun _ => hpc_sf ▸ hlr_s0)
    (fun _ h => by rw [hrun_sf] at h; cases h)
    (fun h => by rw [hrun_sf] at h; cases h)

/-- **Card-`c` post-hook trajectory theorem (`bcmpHull_keepLr_false_after_hook_of_outcome`):**
    Propagates `hc_codeLoaded : P_sub.CodeLoaded s0.mem` along `Steps P_ghost s0 u` and `KeepsFrozen`.
    Note (`H1`): `GhostRowReplayOn.replay_at_stub` Arm 2 provides `InvS u` (`P_sub.CodeLoaded u.mem`)
    rather than `P_sub.CodeLoaded s0.mem`; card `c` should therefore apply either
    `bcmpHull_lr_trap_after_hook_ret` (with `P_sub.CodeLoaded (f_stub u).mem` from `InvS u` +
    `u.mem.KeepsFrozen (f_stub u).mem`) or `bcmpHull_keepLr_false_after_hook_of_codeLoaded_u` below. -/
theorem bcmpHull_keepLr_false_after_hook_of_outcome
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_stub : State → State}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hreg_ext : ∀ pc : BitVec 64, keepBcmpHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepBcmpHull m (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_fu_sf hrun_u hkf
  rw [← keepOf_bcmpHullRegion_apply m resolve]
  exact keepLr_false_after_hook_of_outcome
    (bcmpHull_regionWordsSafe hres)
    (bcmpHullRegion_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_bcmpHullRegion_apply m resolve _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ => ⟨f, hf, fun L hL => htf L (keepOf_bcmpHullRegion_apply m resolve _ ▸ hL)⟩)
    (fun L hL => htrap_stub L (keepOf_bcmpHullRegion_apply m resolve _ ▸ hL))
    (bcmpHullRegion_codeLoaded_iff.mpr hc_codeLoaded)
    ((keepOf_bcmpHullRegion_apply m resolve _).trans hlr_s0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_fu_sf hrun_u hkf

/-- Direct `SubroutineOutcome` wrapper for `bcmpHull_keepLr_false_after_hook_of_outcome`. -/
theorem bcmpHull_keepLr_false_after_hook_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_stub : State → State}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hreg_ext : ∀ pc : BitVec 64, keepBcmpHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepBcmpHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact bcmpHull_keepLr_false_after_hook_of_outcome hres hHas hreg_ext htrap_stub
    hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- **Card-`c` `InvS u` post-hook theorem (`bcmpHull_keepLr_false_after_hook_of_codeLoaded_u`):**
    Variant of `bcmpHull_keepLr_false_after_hook_of_outcome` taking `P_sub.CodeLoaded u.mem` at the
    call state `u` (supplied by `InvS u` in `GhostRowReplayOn.replay_at_stub` Arm 2) instead of
    `P_sub.CodeLoaded s0.mem`. -/
theorem bcmpHull_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_stub : State → State}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hreg_ext : ∀ pc : BitVec 64, keepBcmpHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepBcmpHull m (u.readReg64 .lr) = false := by
  intro u hc_u hsteps_fu_sf hrun_u hkf
  exact bcmpHull_lr_trap_after_hook_ret hres hHas
    (fun hL => htrap_stub _ hL)
    (fun hL pc hkp => (hreg_ext pc hkp).imp id fun ⟨f, hf, htf⟩ => ⟨f, hf, htf _ hL⟩)
    (hc_u.of_keepsFrozen hkf)
    hsteps_fu_sf hrun_u
    (fun hrun_sf => hret_pc hrun_sf ▸ hlr_s0)
    hnoex_sf hnhalt_sf

/-- Call-point `keepBcmpHull m (u.readReg64 .lr) = false` on `Steps P_ghost u sf` covering both
    non-`.Running` and `Returned` outcomes. -/
theorem bcmpHull_lr_trap_at_call_ret
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_u : State → State} {u sf : State}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (htrap_u : keepBcmpHull m (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hreg_ext : keepBcmpHull m (u.readReg64 .lr) = true → ∀ pc, keepBcmpHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧ TrapHook (u.readReg64 .lr) f)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hu_ne_sf : sf.status = .Running → sf.pc ≠ u.pc)
    (hout_sf : sf.status = .Running → keepBcmpHull m sf.pc = false)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepBcmpHull m (u.readReg64 .lr) = false := by
  rw [← keepOf_bcmpHullRegion_apply m resolve]
  exact lr_trap_at_call_ret
    (bcmpHull_regionWordsSafe hres)
    (bcmpHullRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_bcmpHullRegion_apply m resolve _ ▸ hL))
    (fun hL pc hkp =>
      hreg_ext (keepOf_bcmpHullRegion_apply m resolve _ ▸ hL) pc
        (keepOf_bcmpHullRegion_apply m resolve _ ▸ hkp))
    hext_u
    (bcmpHullRegion_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hu_ne_sf
    (fun hr => (keepOf_bcmpHullRegion_apply m resolve _).trans (hout_sf hr))
    hnoex_sf hnhalt_sf

/-- Non-`.Running` terminal call-point `keepBcmpHull m (u.readReg64 .lr) = false`. -/
theorem bcmpHull_lr_trap_at_call
    {P_ghost P_sub : Program} {m : BitVec 64} {resolve : String → BitVec 64}
    {f_u : State → State} {u sf : State}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (htrap_u : keepBcmpHull m (u.readReg64 .lr) = true → TrapHook (u.readReg64 .lr) f_u)
    (hno_ext : ∀ pc, keepBcmpHull m pc = true →
      P_ghost.externAt? pc = none ∨ P_ghost.externAt? pc = some f_u)
    (hext_u : P_ghost.externAt? u.pc = some f_u)
    (hCode_u : P_sub.CodeLoaded u.mem)
    (hsteps_u_sf : Steps P_ghost u sf)
    (hrun_u : u.status = .Running)
    (hrun_sf : sf.status ≠ .Running)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    keepBcmpHull m (u.readReg64 .lr) = false := by
  rw [← keepOf_bcmpHullRegion_apply m resolve]
  exact lr_trap_at_call
    (bcmpHull_regionWordsSafe hres)
    (bcmpHullRegion_hasWords_of_hasWords hHas)
    (fun hL => htrap_u (keepOf_bcmpHullRegion_apply m resolve _ ▸ hL))
    (fun pc hkp => hno_ext pc (keepOf_bcmpHullRegion_apply m resolve _ ▸ hkp))
    hext_u
    (bcmpHullRegion_codeLoaded_iff.mpr hCode_u)
    hsteps_u_sf hrun_u hrun_sf hnoex_sf hnhalt_sf

/-- **Card-`c` at-stub trajectory theorem (`bcmpHull_keepLr_false_at_stub_of_outcome`):**
    56 B `bcmp` hull counterpart of `MemsetKeepLrOfOutcome.memset_keepLr_false_at_stub_of_outcome`. -/
theorem bcmpHull_keepLr_false_at_stub_of_outcome
    {P_ghost P_sub : Program} {m stubPc : BitVec 64} {resolve : String → BitVec 64}
    {f_stub : State → State}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hreg_ext : ∀ pc : BitVec 64, keepBcmpHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : BcmpEntryGuard m stubPc s0)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepBcmpHull m (u.readReg64 .lr) = false := by
  intro u hsteps_s0_u hsteps_u_sf hrun_u hpc_u
  rw [← keepOf_bcmpHullRegion_apply m resolve]
  exact keepLr_false_at_stub_of_outcome
    (bcmpHull_regionWordsSafe hres)
    (bcmpHullRegion_hasWords_of_hasWords hHas)
    (fun pc hkp =>
      (hreg_ext pc (keepOf_bcmpHullRegion_apply m resolve _ ▸ hkp)).imp id
        fun ⟨f, hf, htf⟩ => ⟨f, hf, fun L hL => htf L (keepOf_bcmpHullRegion_apply m resolve _ ▸ hL)⟩)
    hext_stub
    (fun L hL => htrap_stub L (keepOf_bcmpHullRegion_apply m resolve _ ▸ hL))
    (bcmpHullRegion_codeLoaded_iff.mpr hc_codeLoaded)
    ((bcmpEntryGuard_iff_trapEntryGuard m stubPc resolve s0).mp hGuard0)
    hret_pc hnoex_sf hnhalt_sf u hsteps_s0_u hsteps_u_sf hrun_u hpc_u

/-- **Card-`c` at-stub `SubroutineOutcome` theorem (`bcmpHull_keepLr_false_at_stub_of_subroutineOutcome`).** -/
theorem bcmpHull_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {m stubPc : BitVec 64} {resolve : String → BitVec 64}
    {f_stub : State → State}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hreg_ext : ∀ pc : BitVec 64, keepBcmpHull m pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepBcmpHull m L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : BcmpEntryGuard m stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepBcmpHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact bcmpHull_keepLr_false_at_stub_of_outcome hres hHas hreg_ext hext_stub htrap_stub
    hc_codeLoaded hGuard0 hret_pc hnoex_sf hnhalt_sf

/-- `∀ L` adapter bridging STARTUP's entry-excluded `externAt? pc = none` (`pc ∉ entries`) plus
    uniform per-entry `TrapHook` witnesses directly into `bcmpHull_keepLr_false_after_hook_of_outcome`,
    `bcmpHull_keepLr_false_after_hook_of_codeLoaded_u`, and
    `bcmpHull_keepLr_false_at_stub_of_{outcome,subroutineOutcome}`. -/
theorem bcmpHull_reg_ext_of_entry_excluded {P_ghost : Program} {m : BitVec 64}
    {entries : List (BitVec 64)}
    (hno_ext_outside : ∀ pc, keepBcmpHull m pc = true → pc ∉ entries → P_ghost.externAt? pc = none)
    (hentries : ∀ e ∈ entries, P_ghost.externAt? e = none ∨
      ∃ f, P_ghost.externAt? e = some f ∧ ∀ L, keepBcmpHull m L = true → TrapHook L f) :
    ∀ pc, keepBcmpHull m pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepBcmpHull m L = true → TrapHook L f := by
  intro pc hkp
  by_cases hmem : pc ∈ entries
  · exact hentries pc hmem
  · exact Or.inl (hno_ext_outside pc hkp hmem)

/-- Single-stub specialization of `bcmpHull_reg_ext_of_entry_excluded` (`entries := [stubPc]`; on the
    stock/2C route, `stubPc = m + memcmpByteLen` is the sole extern key in `keepBcmpHull m`). -/
theorem bcmpHull_reg_ext_of_stub_excluded {P_ghost : Program} {m stubPc : BitVec 64}
    {f_stub : State → State}
    (hno_ext_outside : ∀ pc, keepBcmpHull m pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L, keepBcmpHull m L = true → TrapHook L f_stub) :
    ∀ pc, keepBcmpHull m pc = true → P_ghost.externAt? pc = none ∨
      ∃ f, P_ghost.externAt? pc = some f ∧ ∀ L, keepBcmpHull m L = true → TrapHook L f := by
  refine bcmpHull_reg_ext_of_entry_excluded (entries := [stubPc])
    (fun pc hkp hmem => hno_ext_outside pc hkp (fun hEq => hmem (List.mem_singleton.mpr hEq))) ?_
  intro e he
  rw [List.mem_singleton.mp he]
  exact Or.inr ⟨f_stub, hext_stub, htrap_stub⟩

/-- Entry-excluded card-`c` `InvS u` post-hook theorem for `W`-independent `f3EmptyBcmpGhostHook`
    (`stubPc = m + memcmpByteLen` on stock/2C; consumes `P_sub.CodeLoaded u.mem` at `u`). -/
theorem f3EmptyBcmpGhostHook_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc entryTarget : BitVec 64}
    {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBcmpHull m pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBcmpGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyBcmpGhostHook keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBcmpGhostHook keepR P_sub entryTarget u).mem →
      keepBcmpHull m (u.readReg64 .lr) = false :=
  bcmpHull_keepLr_false_after_hook_of_codeLoaded_u hres hHas
    (bcmpHull_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBcmpGhostHook_of_cover P_sub entryTarget hcover hL))
    (fun _ hL => trapHook_f3EmptyBcmpGhostHook_of_cover P_sub entryTarget hcover hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` post-hook theorem for `W`-independent `f3EmptyBcmpGhostHook` when
    `P_ghost` has no externs inside `keepBcmpHull m` other than `stubPc` (`m + memcmpByteLen`). -/
theorem f3EmptyBcmpGhostHook_keepLr_false_after_hook_of_outcome
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc entryTarget : BitVec 64}
    {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBcmpHull m pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBcmpGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f3EmptyBcmpGhostHook keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBcmpGhostHook keepR P_sub entryTarget u).mem →
      keepBcmpHull m (u.readReg64 .lr) = false :=
  bcmpHull_keepLr_false_after_hook_of_outcome hres hHas
    (bcmpHull_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBcmpGhostHook_of_cover P_sub entryTarget hcover hL))
    (fun _ hL => trapHook_f3EmptyBcmpGhostHook_of_cover P_sub entryTarget hcover hL)
    hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` post-hook `SubroutineOutcome` theorem for `f3EmptyBcmpGhostHook`. -/
theorem f3EmptyBcmpGhostHook_keepLr_false_after_hook_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc entryTarget : BitVec 64}
    {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBcmpHull m pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBcmpGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f3EmptyBcmpGhostHook keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBcmpGhostHook keepR P_sub entryTarget u).mem →
      keepBcmpHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact f3EmptyBcmpGhostHook_keepLr_false_after_hook_of_outcome hres hHas hcover
    hno_ext_outside hext_stub hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` at-stub `SubroutineOutcome` theorem for `f3EmptyBcmpGhostHook`. -/
theorem f3EmptyBcmpGhostHook_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc entryTarget : BitVec 64}
    {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBcmpHull m pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBcmpGhostHook keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : BcmpEntryGuard m stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepBcmpHull m (u.readReg64 .lr) = false :=
  bcmpHull_keepLr_false_at_stub_of_subroutineOutcome hres hHas
    (bcmpHull_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBcmpGhostHook_of_cover P_sub entryTarget hcover hL))
    hext_stub
    (fun _ hL => trapHook_f3EmptyBcmpGhostHook_of_cover P_sub entryTarget hcover hL)
    hc_codeLoaded hGuard0 hout

/-- Entry-excluded card-`c` `InvS u` post-hook theorem for `K`-narrowed `f3EmptyBcmpGhostHookK`
    (`stubPc = m + memcmpByteLen` on stock/2C; consumes `P_sub.CodeLoaded u.mem` at `u`). -/
theorem f3EmptyBcmpGhostHookK_keepLr_false_after_hook_of_codeLoaded_u
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc entryTarget : BitVec 64}
    {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBcmpHull m pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBcmpGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      P_sub.CodeLoaded u.mem →
      Steps P_ghost (f3EmptyBcmpGhostHookK keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBcmpGhostHookK keepR P_sub entryTarget u).mem →
      keepBcmpHull m (u.readReg64 .lr) = false :=
  bcmpHull_keepLr_false_after_hook_of_codeLoaded_u hres hHas
    (bcmpHull_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBcmpGhostHookK_of_cover P_sub entryTarget hcover hL))
    (fun _ hL => trapHook_f3EmptyBcmpGhostHookK_of_cover P_sub entryTarget hcover hL)
    hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` post-hook theorem for `K`-narrowed `f3EmptyBcmpGhostHookK` when
    `P_ghost` has no externs inside `keepBcmpHull m` other than `stubPc` (`m + memcmpByteLen`). -/
theorem f3EmptyBcmpGhostHookK_keepLr_false_after_hook_of_outcome
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc entryTarget : BitVec 64}
    {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBcmpHull m pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBcmpGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f3EmptyBcmpGhostHookK keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBcmpGhostHookK keepR P_sub entryTarget u).mem →
      keepBcmpHull m (u.readReg64 .lr) = false :=
  bcmpHull_keepLr_false_after_hook_of_outcome hres hHas
    (bcmpHull_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBcmpGhostHookK_of_cover P_sub entryTarget hcover hL))
    (fun _ hL => trapHook_f3EmptyBcmpGhostHookK_of_cover P_sub entryTarget hcover hL)
    hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` post-hook `SubroutineOutcome` theorem for `f3EmptyBcmpGhostHookK`. -/
theorem f3EmptyBcmpGhostHookK_keepLr_false_after_hook_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc entryTarget : BitVec 64}
    {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBcmpHull m pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBcmpGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hlr_s0 : keepBcmpHull m (s0.readReg64 .lr) = false)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f3EmptyBcmpGhostHookK keepR P_sub entryTarget u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f3EmptyBcmpGhostHookK keepR P_sub entryTarget u).mem →
      keepBcmpHull m (u.readReg64 .lr) = false := by
  obtain ⟨hret_pc, hnoex_sf, hnhalt_sf⟩ := subroutineOutcome_running_pc_and_noFault hout
  exact f3EmptyBcmpGhostHookK_keepLr_false_after_hook_of_outcome hres hHas hcover
    hno_ext_outside hext_stub hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- Entry-excluded card-`c` at-stub `SubroutineOutcome` theorem for `f3EmptyBcmpGhostHookK`. -/
theorem f3EmptyBcmpGhostHookK_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost P_sub : Program} {keepR : BitVec 64 → Bool} {m stubPc entryTarget : BitVec 64}
    {resolve : String → BitVec 64}
    (hres : resolve "memcmp" = m)
    (hHas : P_sub.hasWords m (bcmpHullWords m resolve))
    (hcover : ∀ pc, keepBcmpHull m pc = true → keepR pc = true)
    (hno_ext_outside : ∀ pc : BitVec 64,
      keepBcmpHull m pc = true → pc ≠ stubPc → P_ghost.externAt? pc = none)
    (hext_stub : P_ghost.externAt? stubPc =
      some (f3EmptyBcmpGhostHookK keepR P_sub entryTarget))
    {s0 sf : State}
    (hc_codeLoaded : P_sub.CodeLoaded s0.mem)
    (hGuard0 : BcmpEntryGuard m stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepBcmpHull m (u.readReg64 .lr) = false :=
  bcmpHull_keepLr_false_at_stub_of_subroutineOutcome hres hHas
    (bcmpHull_reg_ext_of_stub_excluded hno_ext_outside hext_stub
      (fun _ hL => trapHook_f3EmptyBcmpGhostHookK_of_cover P_sub entryTarget hcover hL))
    hext_stub
    (fun _ hL => trapHook_f3EmptyBcmpGhostHookK_of_cover P_sub entryTarget hcover hL)
    hc_codeLoaded hGuard0 hout

/-- 2-block `TrapRegion` for non-adjacent `bcmp` (`bcmpBase`) + `memcmp` (`memcmpBase`) placements. -/
@[expose] def bcmpMemcmp2Region (bcmpBase memcmpBase : BitVec 64) : TrapRegion :=
  [(bcmpBase, Obj.patchCalls bcmpCalls bcmpWords bcmpBase (fun _ => memcmpBase)),
   (memcmpBase, memcmpLibcaWords)]

/-- Kept-region byte predicate for the 2-block `bcmpMemcmp2Region bcmpBase memcmpBase`. -/
@[expose] def keepBcmpMemcmp2 (bcmpBase memcmpBase : BitVec 64) : BitVec 64 → Bool :=
  keepOf (bcmpMemcmp2Region bcmpBase memcmpBase)

/-- Post-hook trajectory theorem on the 2-block `bcmp` + `memcmp` region. -/
theorem bcmpMemcmp2_keepLr_false_after_hook_of_outcome
    {P_ghost : Program} {progs : List Program} {bcmpBase memcmpBase : BitVec 64}
    {f_stub : State → State}
    (hrange : Obj.BranchInRange bcmpBase memcmpBase)
    (hHas : RegionHasWords progs (bcmpMemcmp2Region bcmpBase memcmpBase))
    (hreg_ext : ∀ pc : BitVec 64, keepBcmpMemcmp2 bcmpBase memcmpBase pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBcmpMemcmp2 bcmpBase memcmpBase L = true → TrapHook L f)
    (htrap_stub : ∀ L : BitVec 64, keepBcmpMemcmp2 bcmpBase memcmpBase L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : RegionCodeLoaded progs s0.mem)
    (hlr_s0 : keepBcmpMemcmp2 bcmpBase memcmpBase (s0.readReg64 .lr) = false)
    (hret_pc : sf.status = .Running → sf.pc = s0.readReg64 .lr)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost (f_stub u) sf →
      u.status = .Running →
      u.mem.KeepsFrozen (f_stub u).mem →
      keepBcmpMemcmp2 bcmpBase memcmpBase (u.readReg64 .lr) = false :=
  keepLr_false_after_hook_of_outcome
    (bcmp_memcmp_regionWordsSafe hrange) hHas hreg_ext htrap_stub
    hc_codeLoaded hlr_s0 hret_pc hnoex_sf hnhalt_sf

/-- At-stub `SubroutineOutcome` theorem on the 2-block `bcmp` + `memcmp` region. -/
theorem bcmpMemcmp2_keepLr_false_at_stub_of_subroutineOutcome
    {α : Type} {spec_ghost : Spec α} {x : α} {R : SepProp}
    {P_ghost : Program} {progs : List Program} {bcmpBase memcmpBase stubPc : BitVec 64}
    {f_stub : State → State}
    (hrange : Obj.BranchInRange bcmpBase memcmpBase)
    (hHas : RegionHasWords progs (bcmpMemcmp2Region bcmpBase memcmpBase))
    (hreg_ext : ∀ pc : BitVec 64, keepBcmpMemcmp2 bcmpBase memcmpBase pc = true →
      P_ghost.externAt? pc = none ∨
        ∃ f, P_ghost.externAt? pc = some f ∧
          ∀ L : BitVec 64, keepBcmpMemcmp2 bcmpBase memcmpBase L = true → TrapHook L f)
    (hext_stub : P_ghost.externAt? stubPc = some f_stub)
    (htrap_stub : ∀ L : BitVec 64, keepBcmpMemcmp2 bcmpBase memcmpBase L = true → TrapHook L f_stub)
    {s0 sf : State}
    (hc_codeLoaded : RegionCodeLoaded progs s0.mem)
    (hGuard0 : TrapEntryGuard (bcmpMemcmp2Region bcmpBase memcmpBase) stubPc s0)
    (hout : SubroutineOutcome spec_ghost x R s0 sf) :
    ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      u.pc = stubPc →
      keepBcmpMemcmp2 bcmpBase memcmpBase (u.readReg64 .lr) = false :=
  keepLr_false_at_stub_of_subroutineOutcome
    (bcmp_memcmp_regionWordsSafe hrange) hHas hreg_ext hext_stub htrap_stub
    hc_codeLoaded hGuard0 hout

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.BcmpLrTrap
