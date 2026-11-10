/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostReplays -- proof-setup: allow-public-import
import ProofLib.BV.Bits

/-!
# 956 B `.text.b_pre` Hull `RegionWordsSafe`, Pad Non-Fetch, & `C4` Universal-`L` `TrapHook`s (`HooksDehook.MemmoveLrTrapBase`)

Card **L3-d** of the `memmove` de-hook row: proves that over the full `956`-byte (`239`-word)
C2 `2C` `.text.b_pre` hull `keepBPreHull m` (`[m, m + 956)`: `memcpy` `99`w at `m`, `bPrePadWord =
0#32` `1`w at `m + 396`, `memset` `65`w at `m + 400`, and `memmove` `74`w at `m + 660` whose tail
branch at `+0x68` is an unconditional `b memcpy` back to `m` with zero `lr` writes), no execution
path writes `x30` (`lr`), executes through the `0#32` alignment pad, or leaves `[m, m + 956)` except
via `ret x30` to `lr`.

Consequently, whenever a ghost run starting with `keepBPreHull m (s0.readReg64 .lr) = false`
terminates without `.Exception`/`.Halted` and (if `.Running`) returns to `s0.readReg64 .lr`, every
intermediate call site `u` satisfies `keepBPreHull m (u.readReg64 .lr) = false`.

## Architecture & Review Guardrails (`C4 / H-REV2`, `F1`, `H1`, Pad Halt, `Lib2LayoutFacts` `@ a230f2671b`)

1. **Zero new word-list `decide` evaluations:**
   Reuses `TrapSafeWords.{memcpy_all_safe, memsetWords_all_safe, memmove_all_safe,
   blockSafe_of_checkWords, blockSafe_of_patchCalls, fetchMem_trapSafe, execInst_of_instrSafeInRegion}`
   to certify `RegionWordsSafe (bPreCodeRegion m resolve)` over the 3-block instruction sub-region
   (`memcpy` at `m`, `memset` at `m + bPreMemsetByteOff`, `memmove` at `m + bPreMemmoveByteOff`).
2. **Pad halt at `[m + 396, m + 400)` (`bPrePadWord = 0#32`, no nonexistent `Step.fetchFault`):**
   `Arm64.Step` (`Arm64/Trusted/ISA/Semantics.lean`) has four constructors (`exec`, `halt_unmapped`,
   `extern`, `extern_fault`). On the 4-byte zero pad `[m + 396, m + 400)` inside
   `bPreHullWords m resolve 0#32`, `bPrePad_fetchMem_none` proves `P_ghost.fetchMem mem pc = none`
   directly from `P_sub.CodeLoaded mem` + `decode 0#32 = none` (and 4-alignment at `off ∈ {397,
   398, 399}`): hence `Step.exec` is vacuous, `Step.halt_unmapped` sets `.Halted` (contradicting
   `sf.status ≠ .Halted`), `Step.extern_fault` sets `.Exception _` (contradicting `hnoex_sf`), and
   `Step.extern` is covered by `hreg_ext`. This yields `bPreHull_trap_impossible` over the **entire**
   contiguous `956` B `keepBPreHull m`.
3. **`F1` + `C4` (3-Entry Exclusion Set — NEVER Whole-Hull `externAt? = none`):**
   On `P_ghost`, `[m, m + 956)` contains `"memmove"` (`m + 660`) plus Stage A's `"memcpy"` (`m`) and
   `"memset"` (`m + 400`), where `P_ghost.externAt?` is `some _` when `g.memcpy` / `g.memset` are
   active (`BcmpHookPlaced.lean:251-258, 379-439`). Every ready-to-apply ghost corollary excludes
   `entries := ["memmove", "memcpy", "memset"].map resolve`, copying verbatim the premise shapes of
   `LibsignalBinary/Proofs/SpecLemmas/SignalSession/ElfF3Relink/Lib2LayoutFacts.lean` @ `a230f2671b`
   (`origin/stock-lld/c2-startup-dnm`, **NOT imported**):
   - Off-entry `externAt? pc = none`: `Lib2LayoutFacts.lean:392-402`
     `f3RowSyms_ghostProg617_externAt_none_of_ne_entries` (backed by `:346-353`
     `f3RxSeg_ghostProg617_externAt_none_of_ne_entries`, cf. `:316` `C2ExternTableFacts`, `:368`
     `f3Row_ghostProg617_externAt_none_of_ne_entry`, `:114` `keepTextBPre_sub_rxProg`);
   - 3-entry lookup: `Lib2LayoutFacts.lean:355-362` `f3RxSeg_ghostProg617_externAt_entry`;
   - Cross-block `C4` `TrapHook L` at `"memcpy"` & `"memset"`: §2 proves **universal-`L`
     (`∀ L : BitVec 64, TrapHook L f`)** for `hookMemcpy`, `hookMemset`, `memcpyGhostHook{,K}`,
     `memsetGhostHook{,K}`, `f3EmptyMemcpyGhostHook{,K}`, and `f3EmptyMemsetGhostHook{,K}` for
     **arbitrary** `keep_mc` / `keep_ms` (covering `keep_mc L = false` on `[m + 660, m + 956)`), via
     `MemmoveCode.trapRetHook_linkedCallHook_of_hookOk_and_lr` (`:1155`).
4. **Strict `H1` (`CodeLoaded` at `u.mem` / `(f u).mem` ONLY — Zero `s0.mem` Forms):**
   Every post-hook and at-stub theorem takes `P_sub.CodeLoaded (f u).mem` or `P_sub.CodeLoaded u.mem`
   (never `s0.mem`), matching `Lib2LayoutFacts.lean:203` `f3CodeInv_rxWords_codeLoaded_strip`
   (`hAlign : addr.toNat % 4 = 0`) and Stage A `GhostExternReplaysOn` (`MemmoveGhostReplays`
   `f3EmptyMemmoveGhostHook_replaysOn_of_lrOut`, citing `:428` `StepsVisitedIn` and `:444`
   `f3RxSeg_steps_realW_of_visitedIn`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrapBase

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open VerifiedLibraries.Musl (
  memcpySymWords memsetWordsSym memmoveLibcaWords memmoveLibcaCalls
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant ActiveRealPre ActiveRealRun
  keepFsTrace linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords (
  TrapRegion keepBlock keepOf keepOf_singleton keepOf_mem_offset
  InstrSafeInRegion execInst_of_instrSafeInRegion
  RegionWordsSafe RegionHasWords RegionCodeLoaded
  codeLoaded_stripExecOutside_of_keep
  fetchMem_trapSafe
  TrapHook TrapEntryGuard
  reg_ext_of_entry_excluded reg_ext_forall_of_entry_excluded
  blockSafe_of_checkWords blockSafe_of_patchCalls regionWordsSafe_single
  memcpy_all_safe memsetWords_all_safe memmove_all_safe
  memmove_memcpy_regionWordsSafe
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  masterMemcpySpec memcpySpecK
  subroutine_ok_masterMemcpy_of_hasWords subroutine_ok_masterMemcpyK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhost (
  memcpyGhostHook memcpyGhostHookK
  specStripSInvariant_masterMemcpy specStripSInvariant_masterMemcpyK
  masterMemcpy_pre_setPC masterMemcpyK_pre_setPC
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostReplaysOn (
  f3EmptyMemcpyGhostHook f3EmptyMemcpyGhostHookK
  f3EmptyMemcpyGhostHook_eq f3EmptyMemcpyGhostHookK_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  masterMemsetSpec memsetSpecK pureWordsProg_externAt_none
  subroutine_ok_masterMemset_of_hasWords subroutine_ok_masterMemsetK_of_hasWords
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  memsetGhostHook memsetGhostHookK
  specStripSInvariant_masterMemset specStripSInvariant_masterMemsetK
  masterMemset_pre_setPC masterMemsetK_pre_setPC
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg
  f3EmptyMemsetGhostHook f3EmptyMemsetGhostHookK
  f3EmptyMemsetGhostHook_eq f3EmptyMemsetGhostHookK_eq
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveCode (
  masterMemmoveSpec
  bPrePadWord bPreMemsetByteOff bPreMemmoveByteOff
  bPreMemsetByteOff_eq bPreMemmoveByteOff_eq
  bPreHullWords bPreHullWords_length
  hasWords_append_left hasWords_append_right
  bPreHull_hasWords_memcpy bPreHull_hasWords_memset bPreHull_hasWords_memmove
  branchInRange_bPreHull pureWordsProg_bPreHull_hasWords
  TrapRetHook trapRetHook_keepFsTrace
  trapRetHook_hookMemset trapRetHook_hookMemcpy trapRetHook_hookMemmove
  trapRetHook_linkedCallHook_of_hookOk_and_lr
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhost (
  keepBPreHull keepBPreHull_of_offset
  keepBPreHull_memcpyEntry keepBPreHull_memsetEntry keepBPreHull_memmoveEntry
  memmoveGhostFn memmoveGhostFnK memmoveGhostPure memmoveGhostPureK
  trapRetHook_memmoveGhostFn trapRetHook_memmoveGhostFnK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveGhostK (
  f3EmptyMemmoveGhostHook f3EmptyMemmoveGhostHookK
  f3PureMemmoveGhostHook f3PureMemmoveGhostHookK
  f3EmptyMemmoveGhostHook_eq f3EmptyMemmoveGhostHook_master_ok
  trapRetHook_f3EmptyMemmoveGhostHook trapRetHook_f3EmptyMemmoveGhostHookK
)

/-! ## 1. 956 B `.text.b_pre` Hull (`keepBPreHull`), 3-Block `bPreCodeRegion`, & Pad Non-Fetch -/

/-- Total byte length (`956` B = `4 * 239`) of the C2 `2C` `.text.b_pre` hull. -/
@[expose] def bPreHullByteLen : Nat := 956

theorem bPreHullByteLen_eq : bPreHullByteLen = 956 := rfl

/-- Byte offset (`396#64`) of the 1-word alignment pad (`bPrePadWord = 0#32`) after `99`-word `memcpy`. -/
@[expose] def bPrePadByteOff : BitVec 64 :=
  BitVec.ofNat 64 (4 * memcpySymWords.length)

theorem bPrePadByteOff_eq : bPrePadByteOff = BitVec.ofNat 64 396 := by decide

theorem keepBPreHull_eq_keepBlock (m : BitVec 64) :
    keepBPreHull m = keepBlock m bPreHullByteLen := rfl

theorem keepBPreHull_iff (m pc : BitVec 64) :
    keepBPreHull m pc = true ↔ (pc - m).toNat < 956 :=
  decide_eq_true_iff

/-- Sufficient coverage condition `keepBPreHull m ⊆ keepR` (`[m, m + 956)` covered by `keepR`). -/
@[expose] def KeepCoversBPreHull (keepR : BitVec 64 → Bool) (m : BitVec 64) : Prop :=
  ∀ pc : BitVec 64, keepBPreHull m pc = true → keepR pc = true

theorem keepCoversBPreHull_self (m : BitVec 64) :
    KeepCoversBPreHull (keepBPreHull m) m :=
  fun _ h => h

/-- 3-block instruction sub-region of `.text.b_pre` (`memcpy` `99`w at `m`, `memset` `65`w at
    `m + bPreMemsetByteOff`, and `memmove` `74`w at `m + bPreMemmoveByteOff`, omitting the 1-word
    `0#32` alignment pad at `m + bPrePadByteOff`). -/
@[expose] def bPreCodeRegion (m : BitVec 64)
    (resolve : String → BitVec 64 := fun _ => m) : TrapRegion :=
  [(m, memcpySymWords),
   (m + bPreMemsetByteOff, memsetWordsSym),
   (m + bPreMemmoveByteOff,
     Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords (m + bPreMemmoveByteOff) resolve)]

/-- Static word-level trap safety (`RegionWordsSafe`) of `bPreCodeRegion m resolve` when
    `resolve "memcpy" = m` (reuses `TrapSafeWords.{memcpy_all_safe, memsetWords_all_safe,
    memmove_all_safe}` with zero new word-list `decide` evaluations). -/
theorem bPreCodeRegion_wordsSafe {m : BitVec 64} {resolve : String → BitVec 64}
    (hres : resolve "memcpy" = m := by rfl) :
    RegionWordsSafe (bPreCodeRegion m resolve) := by
  intro blk hmem
  rcases List.mem_cons.mp hmem with rfl | hmem1
  · dsimp only; intro k hk
    exact blockSafe_of_checkWords memcpy_all_safe k hk
  · rcases List.mem_cons.mp hmem1 with rfl | hmem2
    · dsimp only; intro k hk
      exact blockSafe_of_checkWords memsetWords_all_safe k hk
    · rw [List.mem_singleton] at hmem2; subst hmem2
      dsimp only; intro k hk
      refine blockSafe_of_patchCalls (base := m + bPreMemmoveByteOff)
        (calls := memmoveLibcaCalls) (ws := memmoveLibcaWords) (resolve := resolve)
        memmove_all_safe (fun c hc => ?_) k hk
      rw [show memmoveLibcaCalls = [(104, "memcpy")] from rfl, List.mem_singleton] at hc
      subst hc
      refine ⟨branchInRange_bPreHull m hres, ?_⟩
      rw [hres]
      have h0 : keepOf (bPreCodeRegion m resolve) (m + BitVec.ofNat 64 0) = true :=
        keepOf_mem_offset (base := m) (ws := memcpySymWords) List.mem_cons_self
          (show 0 < 4 * memcpySymWords.length by decide)
      rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h0

/-- Every address in `bPreCodeRegion m resolve` lies inside the contiguous `956` B `keepBPreHull m`. -/
theorem keepBPreHull_of_bPreCodeRegion {m : BitVec 64} {resolve : String → BitVec 64}
    {pc : BitVec 64} (hkp : keepOf (bPreCodeRegion m resolve) pc = true) :
    keepBPreHull m pc = true := by
  have hlen_mc : 4 * memcpySymWords.length = 396 := by decide
  have hlen_ms : 4 * memsetWordsSym.length = 260 := by decide
  have hlen_mm : 4 * (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords
      (m + bPreMemmoveByteOff) resolve).length = 296 := by
    rw [Obj.patchCalls, List.length_mapIdx]; decide
  dsimp only [bPreCodeRegion, keepOf, List.any_cons, List.any_nil, Bool.or_false] at hkp
  rw [Bool.or_eq_true, Bool.or_eq_true] at hkp
  rw [keepBPreHull_iff]
  rcases hkp with hkb1 | hkb2 | hkb3
  · rw [hlen_mc] at hkb1
    have hlt : (pc - m).toNat < 396 := of_decide_eq_true hkb1
    omega
  · rw [hlen_ms] at hkb2
    have hlt : (pc - (m + bPreMemsetByteOff)).toNat < 260 := of_decide_eq_true hkb2
    have hsub : pc - m = (pc - (m + bPreMemsetByteOff)) + 400#64 := by
      rw [bPreMemsetByteOff_eq]; bv_omega
    rw [hsub, BitVec.toNat_add, show (400#64 : BitVec 64).toNat = 400 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [hlen_mm, Bool.or_false] at hkb3
    have hlt : (pc - (m + bPreMemmoveByteOff)).toNat < 296 := of_decide_eq_true hkb3
    have hsub : pc - m = (pc - (m + bPreMemmoveByteOff)) + 660#64 := by
      rw [bPreMemmoveByteOff_eq]; bv_omega
    rw [hsub, BitVec.toNat_add, show (660#64 : BitVec 64).toNat = 660 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- Decomposition of `keepBPreHull m pc = true`: either `pc` lies in the 3-block instruction
    sub-region `bPreCodeRegion m resolve` or in the 4-byte alignment pad `[m + 396, m + 400)`. -/
theorem keepBPreHull_cases {m : BitVec 64} (resolve : String → BitVec 64) {pc : BitVec 64}
    (hkp : keepBPreHull m pc = true) :
    keepOf (bPreCodeRegion m resolve) pc = true ∨
      (396 ≤ (pc - m).toNat ∧ (pc - m).toNat < 400) := by
  have hlen_mc : 4 * memcpySymWords.length = 396 := by decide
  have hlen_ms : 4 * memsetWordsSym.length = 260 := by decide
  have hoff : (pc - m).toNat < 956 := (keepBPreHull_iff m pc).mp hkp
  let off := (pc - m).toNat
  have hoff_lt : off < 956 := hoff
  have hpc_eq : pc = m + BitVec.ofNat 64 off := by
    dsimp only [off]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  by_cases h1 : off < 396
  · left
    rw [hpc_eq]
    exact keepOf_mem_offset (base := m) (ws := memcpySymWords) List.mem_cons_self (by omega)
  · by_cases h2 : off < 400
    · exact Or.inr ⟨by omega, h2⟩
    · left
      by_cases h3 : off < 660
      · let offMs := off - 400
        have hpc_ms : pc = (m + bPreMemsetByteOff) + BitVec.ofNat 64 offMs := by
          have hsplit : BitVec.ofNat 64 off = bPreMemsetByteOff + BitVec.ofNat 64 offMs := by
            rw [bPreMemsetByteOff_eq, show (400#64 : BitVec 64) = BitVec.ofNat 64 400 from rfl,
              ← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 64) (by omega)
          rw [hpc_eq, hsplit, ← BitVec.add_assoc]
        rw [hpc_ms]
        exact keepOf_mem_offset (base := m + bPreMemsetByteOff) (ws := memsetWordsSym)
          (List.mem_cons_of_mem _ List.mem_cons_self) (by omega)
      · let offMm := off - 660
        have hpc_mm : pc = (m + bPreMemmoveByteOff) + BitVec.ofNat 64 offMm := by
          have hsplit : BitVec.ofNat 64 off = bPreMemmoveByteOff + BitVec.ofNat 64 offMm := by
            rw [bPreMemmoveByteOff_eq, show (660#64 : BitVec 64) = BitVec.ofNat 64 660 from rfl,
              ← BitVec.ofNat_add]
            exact congrArg (BitVec.ofNat 64) (by omega)
          rw [hpc_eq, hsplit, ← BitVec.add_assoc]
        rw [hpc_mm]
        exact keepOf_mem_offset
          (base := m + bPreMemmoveByteOff)
          (ws := Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords (m + bPreMemmoveByteOff) resolve)
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))
          (by
            have : 4 * (Obj.patchCalls memmoveLibcaCalls memmoveLibcaWords
                (m + bPreMemmoveByteOff) resolve).length = 296 := by
              rw [Obj.patchCalls, List.length_mapIdx]; decide
            omega)

/-- Slice the 1-word alignment pad `[padWord]` at `m + bPrePadByteOff` (`m + 396`) out of a
    `239`-word `bPreHullWords` witness. -/
theorem bPreHull_hasWords_pad {prog : Program} {m : BitVec 64}
    {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hhull : prog.hasWords m (bPreHullWords m resolve padWord)) :
    prog.hasWords (m + bPrePadByteOff) [padWord] :=
  hasWords_append_right (hasWords_append_left (hasWords_append_left hhull)) (by simp)

/-- Lift `P_sub.hasWords m (bPreHullWords m resolve padWord)` to `RegionHasWords [P_sub]` for
    `bPreCodeRegion m resolve`. -/
theorem bPreCodeRegion_hasWords_of_bPreHull {P_sub : Program} {m : BitVec 64}
    {resolve : String → BitVec 64} {padWord : BitVec 32}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve padWord)) :
    RegionHasWords [P_sub] (bPreCodeRegion m resolve) := by
  intro blk hmem
  refine ⟨P_sub, List.mem_singleton.mpr rfl, ?_⟩
  rcases List.mem_cons.mp hmem with rfl | hmem1
  · dsimp only; exact bPreHull_hasWords_memcpy hhull
  · rcases List.mem_cons.mp hmem1 with rfl | hmem2
    · dsimp only; exact bPreHull_hasWords_memset hhull
    · rw [List.mem_singleton] at hmem2
      subst hmem2
      dsimp only
      exact bPreHull_hasWords_memmove hhull

theorem bPreCodeRegion_codeLoaded_iff {P_sub : Program} {mem : Memory} :
    RegionCodeLoaded [P_sub] mem ↔ P_sub.CodeLoaded mem :=
  ⟨fun h => h P_sub (List.mem_singleton.mpr rfl),
   fun h P hP => by rw [List.mem_singleton] at hP; subst hP; exact h⟩

/-- `CodeLoaded` under `stripExecOutside keepR mem` when `P_sub = pureWordsProg m (bPreHullWords ...)`
    and `KeepCoversBPreHull keepR m`. -/
theorem bPreHull_codeLoaded_stripExecOutside {keepR : BitVec 64 → Bool} {m : BitVec 64}
    {resolve : String → BitVec 64} {padWord : BitVec 32} {mem : Memory}
    (hcov : KeepCoversBPreHull keepR m)
    (hL : (pureWordsProg m (bPreHullWords m resolve padWord)).CodeLoaded mem) :
    (pureWordsProg m (bPreHullWords m resolve padWord)).CodeLoaded
      (ProofLib.stripExecOutside keepR mem) := by
  have hclen : (pureWordsProg m (bPreHullWords m resolve padWord)).code.length = 956 := by
    have hwlen := bPreHullWords_length m resolve padWord
    change ((bPreHullWords m resolve padWord).flatMap Program.wordToBytesLE).length = 956
    have hflat : ∀ ws : List (BitVec 32), (ws.flatMap Program.wordToBytesLE).length = 4 * ws.length := by
      intro ws; induction ws with
      | nil => rfl
      | cons _ tl ih => simp [Program.wordToBytesLE, ih]; omega
    rw [hflat, hwlen]
  exact codeLoaded_stripExecOutside_of_keep
    (fun off hoff => hcov _ (keepBPreHull_of_offset m (hclen ▸ hoff))) hL

/-- Inverse of `codeLoaded_stripExecOutside_of_keep`: because `stripExecOutside` only strips execute
    permission (`Perm.stripExec`) and never adds `Perm.rx`, `P_sub.CodeLoaded (stripExecOutside keep mem)`
    unconditionally implies `P_sub.CodeLoaded mem`. -/
theorem codeLoaded_of_stripExecOutside {keep : BitVec 64 → Bool} {prog : Program} {mem : Memory}
    (hL : prog.CodeLoaded (ProofLib.stripExecOutside keep mem)) :
    prog.CodeLoaded mem := by
  obtain ⟨hal, hnw, hbytes⟩ := Program.codeLoaded_iff.mp hL
  refine Program.codeLoaded_iff.mpr ⟨hal, hnw, fun i hi => ?_⟩
  obtain ⟨hr8, hperm, hlz⟩ := hbytes i hi
  rw [ProofLib.strip_read8] at hr8
  rw [ProofLib.strip_isLazyFree] at hlz
  refine ⟨hr8, ?_, hlz⟩
  rw [ProofLib.strip_perm] at hperm
  cases hk : keep (prog.base + BitVec.ofNat 64 i)
  · rw [hk] at hperm
    cases hp : mem.perm (prog.base + BitVec.ofNat 64 i) with
    | none => rw [hp] at hperm; cases hperm
    | some p =>
      rw [hp] at hperm
      rcases p with ⟨r, w, x, lf, an⟩
      cases x <;> simp [Option.map, ProofLib.stripPerm, Perm.rx] at hperm
  · rw [hk] at hperm
    cases hp : mem.perm (prog.base + BitVec.ofNat 64 i) with
    | none => rw [hp] at hperm; cases hperm
    | some p => rw [hp] at hperm; simpa [Option.map, ProofLib.stripPerm] using hperm

/-- **Pad non-fetch (`bPrePad_fetchMem_none`):** on the 4-byte zero pad `[m + 396, m + 400)`
    (`padWord = bPrePadWord = 0#32`), `P_ghost.fetchMem mem pc = none` unconditionally whenever
    `P_sub.hasWords m (bPreHullWords m resolve bPrePadWord)` and `P_sub.CodeLoaded mem` (at aligned
    `m + 396`, `mem.read32 pc = 0#32` and `decode 0#32 = none`; at `off ∈ {397, 398, 399}`,
    `pc.toNat % 4 ≠ 0`). -/
theorem bPrePad_fetchMem_none {P_ghost P_sub : Program} {m : BitVec 64}
    {resolve : String → BitVec 64} {mem : Memory} {pc : BitVec 64}
    (hhull : P_sub.hasWords m (bPreHullWords m resolve bPrePadWord))
    (hCode : P_sub.CodeLoaded mem)
    (hpad_lo : 396 ≤ (pc - m).toNat)
    (hpad_hi : (pc - m).toNat < 400) :
    P_ghost.fetchMem mem pc = none := by
  have hpad : P_sub.hasWords (m + bPrePadByteOff) [0#32] := bPreHull_hasWords_pad hhull
  obtain ⟨hbase_al, hbase_nw, hbytes⟩ := Program.codeLoaded_iff.mp hCode
  let padAddr := m + bPrePadByteOff
  let off := (padAddr - P_sub.base).toNat
  have hrw : P_sub.readWordOff off = some 0#32 := by
    have h0 := hpad.2.1 0 (by decide)
    rwa [Nat.mul_zero, Nat.add_zero] at h0
  unfold Program.readWordOff at hrw
  split at hrw
  · contradiction
  rename_i hal_neg
  have hoff_al : off % 4 = 0 := Classical.not_not.mp hal_neg
  split at hrw
  rotate_left
  · contradiction
  rename_i b0 b1 b2 b3 tl hdrop
  have hlen4 : off + 4 ≤ P_sub.code.length := by
    have hd := congrArg List.length hdrop
    rw [List.length_drop] at hd
    simp only [List.length_cons] at hd
    omega
  have hpadAddr_eq : padAddr = P_sub.base + BitVec.ofNat 64 off := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have hpadAddr_nat : padAddr.toNat = P_sub.base.toNat + off := by
    rw [hpadAddr_eq, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hpadAddr_al : padAddr.toNat % 4 = 0 := by omega
  have hpadAddr_nw : padAddr.toNat + 4 ≤ 2 ^ 64 := by omega
  let d := (pc - m).toNat - 396
  have hd_lt : d < 4 := by omega
  have hpc_pad : pc = padAddr + BitVec.ofNat 64 d := by
    have hpc_m : pc = m + BitVec.ofNat 64 (pc - m).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have hsplit : BitVec.ofNat 64 (pc - m).toNat = bPrePadByteOff + BitVec.ofNat 64 d := by
      rw [bPrePadByteOff_eq, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    rw [hpc_m, hsplit, ← BitVec.add_assoc]
  have hpc_nat : pc.toNat = padAddr.toNat + d := by
    rw [hpc_pad, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold Program.fetchMem
  split
  · rfl
  by_cases hpc_al : pc.toNat % 4 ≠ 0
  · simp [hpc_al]
  · simp only [hpc_al, ↓reduceIte]
    have hd_zero : d = 0 := by omega
    have hpc_eq_pad : pc = padAddr := by
      rw [hpc_pad, hd_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    subst hpc_eq_pad
    split
    · rfl
    have hb : ∀ k (hk : k < 4),
        mem.read8 (padAddr + BitVec.ofNat 64 k) = P_sub.code[off + k]'(by omega) := by
      intro k hk
      have he : padAddr + BitVec.ofNat 64 k = P_sub.base + BitVec.ofNat 64 (off + k) := by
        rw [hpadAddr_eq, BitVec.ofNat_add, BitVec.add_assoc]
      rw [he]
      exact (hbytes (off + k) (by omega)).1
    have hget : ∀ k (hk : k < 4),
        P_sub.code[off + k]'(by omega) = (b0 :: b1 :: b2 :: b3 :: tl)[k]'(by simp; omega) := by
      intro k hk
      simp only [← hdrop, List.getElem_drop]
    have hr32 : mem.read32 padAddr = b3 ++ b2 ++ b1 ++ b0 := by
      have h0 := hb 0 (by omega); have h1 := hb 1 (by omega)
      have h2 := hb 2 (by omega); have h3 := hb 3 (by omega)
      have g0 := hget 0 (by omega); have g1 := hget 1 (by omega)
      have g2 := hget 2 (by omega); have g3 := hget 3 (by omega)
      simp only [Memory.read32]
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at g0 g1 g2 g3
      rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, h0, g0,
        show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, h1, g1,
        show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, h2, g2,
        show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, h3, g3]
    have hword_eq : b3 ++ b2 ++ b1 ++ b0 = 0#32 := Option.some.inj hrw
    rw [hr32, hword_eq]
    exact (by decide : Arm64.decode 0#32 = none)

/-- Entry-state `lr` guard at `s0` for at-stub `memmove` closed-trap corollaries (discharged at C2
    assembly via `Lib2LayoutFacts.lean:485` `f3BatchLEntryGuard_of_startupLr` @ `a230f2671b`). -/
@[expose] def MemmoveEntryGuard (m stubPc : BitVec 64) (s0 : State) : Prop :=
  keepBPreHull m (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc

theorem memmoveEntryGuard_iff (m stubPc : BitVec 64) (s0 : State) :
    MemmoveEntryGuard m stubPc s0 ↔
      keepBPreHull m (s0.readReg64 .lr) = false ∧ s0.readReg64 .lr ≠ stubPc :=
  Iff.rfl

/-! ## 2. `TrapHook` Suite (Idealized, `memmove` Ghost, & Universal-`L` Cross-Block `C4` Ghosts) -/

/-- `TrapHook L hookMemmove` holds unconditionally for all `L : BitVec 64` (`TrapRetHook` and
    `TrapHook` are definitionally equal). -/
theorem trapHook_hookMemmove (L : BitVec 64) : TrapHook L hookMemmove :=
  trapRetHook_hookMemmove L

theorem trapHook_keepFsTrace_hookMemmove (L : BitVec 64) :
    TrapHook L (keepFsTrace hookMemmove) :=
  trapRetHook_keepFsTrace (trapRetHook_hookMemmove L)

theorem trapHook_hookMemcpy (L : BitVec 64) : TrapHook L hookMemcpy :=
  trapRetHook_hookMemcpy L

theorem trapHook_keepFsTrace_hookMemcpy (L : BitVec 64) :
    TrapHook L (keepFsTrace hookMemcpy) :=
  trapRetHook_keepFsTrace (trapRetHook_hookMemcpy L)

theorem trapHook_hookMemset (L : BitVec 64) : TrapHook L hookMemset :=
  trapRetHook_hookMemset L

theorem trapHook_keepFsTrace_hookMemset (L : BitVec 64) :
    TrapHook L (keepFsTrace hookMemset) :=
  trapRetHook_keepFsTrace (trapRetHook_hookMemset L)

/-- Plain `memmoveGhostFn` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_memmoveGhostFn {keepR : BitVec 64 → Bool}
    (P_real P_sub : Program) (entryTarget : BitVec 64) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (memmoveGhostFn keepR P_real P_sub entryTarget) :=
  trapRetHook_memmoveGhostFn hkeepL

theorem trapHook_memmoveGhostFn_of_cover {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hcov : KeepCoversBPreHull keepR m) {L : BitVec 64} (hL : keepBPreHull m L = true) :
    TrapHook L (memmoveGhostFn keepR P_real P_sub entryTarget) :=
  trapHook_memmoveGhostFn P_real P_sub entryTarget (hcov L hL)

/-- `K`-narrowed `memmoveGhostFnK` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_memmoveGhostFnK {keepR : BitVec 64 → Bool}
    (P_real P_sub : Program) (entryTarget : BitVec 64) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (memmoveGhostFnK keepR P_real P_sub entryTarget) :=
  trapRetHook_memmoveGhostFnK hkeepL

theorem trapHook_memmoveGhostFnK_of_cover {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (P_real P_sub : Program) (entryTarget : BitVec 64)
    (hcov : KeepCoversBPreHull keepR m) {L : BitVec 64} (hL : keepBPreHull m L = true) :
    TrapHook L (memmoveGhostFnK keepR P_real P_sub entryTarget) :=
  trapHook_memmoveGhostFnK P_real P_sub entryTarget (hcov L hL)

/-- `W`-independent `f3EmptyMemmoveGhostHook` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_f3EmptyMemmoveGhostHook {keepR : BitVec 64 → Bool}
    (P_sub : Program) (entryTarget : BitVec 64) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (f3EmptyMemmoveGhostHook keepR P_sub entryTarget) :=
  trapRetHook_f3EmptyMemmoveGhostHook hkeepL

theorem trapHook_f3EmptyMemmoveGhostHook_of_cover {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hcov : KeepCoversBPreHull keepR m) {L : BitVec 64} (hL : keepBPreHull m L = true) :
    TrapHook L (f3EmptyMemmoveGhostHook keepR P_sub entryTarget) :=
  trapHook_f3EmptyMemmoveGhostHook P_sub entryTarget (hcov L hL)

/-- `W`-independent `f3EmptyMemmoveGhostHookK` satisfies `TrapHook L` whenever `keepR L = true`. -/
theorem trapHook_f3EmptyMemmoveGhostHookK {keepR : BitVec 64 → Bool}
    (P_sub : Program) (entryTarget : BitVec 64) {L : BitVec 64}
    (hkeepL : keepR L = true) :
    TrapHook L (f3EmptyMemmoveGhostHookK keepR P_sub entryTarget) :=
  trapRetHook_f3EmptyMemmoveGhostHookK hkeepL

theorem trapHook_f3EmptyMemmoveGhostHookK_of_cover {keepR : BitVec 64 → Bool} {m : BitVec 64}
    (P_sub : Program) (entryTarget : BitVec 64)
    (hcov : KeepCoversBPreHull keepR m) {L : BitVec 64} (hL : keepBPreHull m L = true) :
    TrapHook L (f3EmptyMemmoveGhostHookK keepR P_sub entryTarget) :=
  trapHook_f3EmptyMemmoveGhostHookK P_sub entryTarget (hcov L hL)

private theorem fetchMem_none_of_perm_x_false {prog : Program} {mem : Memory} {pc : BitVec 64}
    (hperm : (mem.perm pc).x = false) :
    prog.fetchMem mem pc = none := by
  unfold Program.fetchMem
  split
  · rfl
  split
  · rfl
  have hnc : mem.canExec pc 4 = false := by
    unfold Memory.canExec Memory.allPerm
    rw [hperm, Bool.false_and]
  rw [hnc]
  rfl

private theorem stripExecOutside_perm_x_false {keep : BitVec 64 → Bool} {mem : Memory}
    {pc : BitVec 64} (hnk : keep pc = false) :
    ((ProofLib.stripExecOutside keep mem).perm pc).x = false := by
  cases hx : ((ProofLib.stripExecOutside keep mem).perm pc).x with
  | false => rfl
  | true =>
    have hk := (ProofLib.strip_perm_x_imp hx).2
    rw [hnk] at hk
    cases hk

/-- Leaf `lr`-preservation along any hook-free `Steps P_sub s1' sf'` inside a `RegionWordsSafe`
    region starting on `s1'.mem` with `(s1'.mem.perm L).x = false` (such as `stripExecOutside keep`
    when `keep L = false`): once `pc` reaches `L`, `fetchMem = none` prevents any further step
    without `.Halted`, so any `.Running` terminal state `sf'` preserves `sf'.readReg64 .lr = L`. -/
private theorem steps_lr_eq_of_regionWordsSafe_nonExecLr
    {P_sub : Program} {region : TrapRegion} {L : BitVec 64}
    (hSafe : RegionWordsSafe region)
    (hHas : RegionHasWords [P_sub] region)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    {s sf' : State}
    (hsteps : Steps P_sub s sf')
    (hrun_sf : sf'.status = .Running)
    (hrun_s : s.status = .Running)
    (hpc_s : s.pc = L ∨ keepOf region s.pc = true)
    (hlr_s : s.readReg64 .lr = L)
    (hCode_s : RegionCodeLoaded [P_sub] s.mem)
    (hperm_s : (s.mem.perm L).x = false) :
    sf'.readReg64 .lr = L := by
  induction hsteps with
  | refl _ => exact hlr_s
  | @step s1 s2 _ h1 hrest ih =>
    have hCode2 : RegionCodeLoaded [P_sub] s2.mem := hCode_s.step h1
    cases h1 with
    | halt_unmapped _ _ _ =>
      have heq := ProofLib.Variant.Steps.eq_of_not_running hrest nofun
      rw [heq] at hrun_sf; cases hrun_sf
    | extern_fault _ hext _ =>
      rw [hsub_no s1.pc] at hext; contradiction
    | extern _ hext _ _ =>
      rw [hsub_no s1.pc] at hext; contradiction
    | @exec inst _ hfm =>
      rcases hpc_s with hpc_eq_L | hkeep1
      · rw [hpc_eq_L, fetchMem_none_of_perm_x_false hperm_s] at hfm
        contradiction
      · obtain ⟨base, ws, off, hmem, _, hpc1, hsafe⟩ :=
          fetchMem_trapSafe hSafe hHas hCode_s hkeep1 hfm
        have hnsvc0 : inst.isSvc0 = false := hsafe.not_isSvc0
        have heval : P_sub.evalInst inst s1 = execInst inst s1 :=
          evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
        rcases execInst_of_instrSafeInRegion hmem hsafe hrun_s hpc1 with
          ⟨_, hex⟩ | ⟨hrun2, hlr2, hpc2⟩
        · have hex' : (P_sub.evalInst inst s1).status = .Exception _ := heval ▸ hex
          have heq := ProofLib.Variant.Steps.eq_of_not_running hrest (by rw [hex']; nofun)
          rw [heq, hex'] at hrun_sf; cases hrun_sf
        · rw [heval] at ih hCode2
          have hperm2 : ((execInst inst s1).mem.perm L).x = false := by
            rw [execInst_perm_apply_of_not_isSvc0 hnsvc0 s1 L]
            exact hperm_s
          exact ih hrun_sf hrun2 (hpc2.imp (fun h => h.trans hlr_s) id)
            (hlr2.trans hlr_s) hCode2 hperm2

/-- **Universal-`L` `TrapHook L` for `linkedCallHook` (`C4 / H-REV2` cross-block bridge):**
    Whenever `subroutine_ok P_sub entryTarget spec` is non-aborting (`onPanic`/`onExit`/`onOom` =
    `⌜False⌝`) over a `RegionWordsSafe` region containing `entryTarget`, `linkedCallHook` satisfies
    `TrapHook L` for **every** `L : BitVec 64` — both when `keep L = true` (fallback path) and when
    `keep L = false` (active real run lifted from `stripS keep`, e.g. `L` inside `memmove` while
    Stage A's `g.memcpy` / `g.memset` uses narrow `keepMemcpyBlk20` / `keepMemsetBlk21`). -/
theorem trapHook_linkedCallHook_of_regionWordsSafe {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {region : TrapRegion} {entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hStrip : SpecStripSInvariant keep spec)
    (hPrePC : ∀ x s, spec.pre x (s.setPC entryTarget) = spec.pre x s)
    (hSafe : RegionWordsSafe region)
    (hHas : RegionHasWords [P_sub] region)
    (hEntry_in : keepOf region entryTarget = true)
    (hfb : ∀ L : BitVec 64, TrapHook L fallback)
    (L : BitVec 64)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    TrapHook L (linkedCallHook keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro w hrun hlr
  by_cases hAct : ActiveRealPre spec w
  · by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget w
    · obtain ⟨_, hsp, x, R, hpre⟩ := id hAct
      let s1 := w.setPC entryTarget
      let s1' := stripS keep s1
      have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
        change w.mem ⊨ spec.pre x (w.setPC entryTarget) ∗ R
        rwa [hPrePC x w]
      have hs1'_pre : s1'.mem ⊨ spec.pre x s1' ∗ R := by
        have hsat := satisfies_stripExecOutside keep hs1_pre
        rwa [hStrip.pre_eq x s1]
      have hs1'_sp : s1'.spAligned = true := hsp
      obtain ⟨sf', hsteps', hout'⟩ :=
        subroutine_ok_elim_steps_outcome hOk x R s1' rfl hrun hs1'_pre hs1'_sp hReal.2.2.1
      rcases hout' with ⟨hret', _, _⟩ | ⟨_, hp_sat⟩ | ⟨code, _, he_sat⟩ | ⟨_, ho_sat⟩
      · have hstop0' : SubroutineStop w sf' := Or.inl hret'
        have hnhalt' : sf'.status ≠ .Halted := by rw [hret'.2.2]; nofun
        obtain ⟨sf, huntil, hstop_sf, hsf_eq, _⟩ :=
          stepsUntil_of_stripS_standard (s0 := w)
            hsvc_real hsvc_sub hreal_no
            (fun pc _ he => nomatch hsub_no pc ▸ he)
            hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
        have hchoose := Classical.choose_spec hReal.2.2.2
        have hdet : Classical.choose hReal.2.2.2 = sf :=
          StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
        have heq_lch :
            linkedCallHook keep P_real P_sub entryTarget spec fallback w = sf := by
          rw [← hdet]; unfold linkedCallHook; simp [hAct, hReal]
        have hkeepL_false : keep L = false := hlr ▸ hReal.2.1
        have hs1'_lr : s1'.readReg64 .lr = L := by cases w; exact hlr
        have hs1'_mem : s1'.mem = ProofLib.stripExecOutside keep w.mem := by cases w; rfl
        have hlr_sf' : sf'.readReg64 .lr = L :=
          steps_lr_eq_of_regionWordsSafe_nonExecLr hSafe hHas hsub_no hsteps' hret'.2.2
            hrun (Or.inr hEntry_in) hs1'_lr
            (fun P hmem => (List.mem_singleton.mp hmem) ▸ (hs1'_mem ▸ hReal.2.2.1))
            (hs1'_mem ▸ stripExecOutside_perm_x_false hkeepL_false)
        rw [hsf_eq] at hret' hlr_sf'
        have hsf_run : sf.status = .Running := by cases sf; exact hret'.2.2
        have hsf_pc : sf.pc = L := by
          have hpc0 : sf.pc = s1'.readReg64 .lr := by cases sf; exact hret'.1
          exact hpc0.trans hs1'_lr
        have hsf_lr : sf.readReg64 .lr = L := by cases sf; exact hlr_sf'
        rw [heq_lch]
        exact Or.inr ⟨hsf_run, hsf_pc, hsf_lr⟩
      · rw [hpan x s1' sf', satisfies_pure_sepConj] at hp_sat; exact False.elim hp_sat.1
      · rw [hex x code s1' sf', satisfies_pure_sepConj] at he_sat; exact False.elim he_sat.1
      · rw [hoom x s1' sf', satisfies_pure_sepConj] at ho_sat; exact False.elim ho_sat.1
    · unfold linkedCallHook
      simp only [hAct, hReal, ↓reduceDIte]
      exact trapRetHook_keepFsTrace (hfb L) w hrun hlr
  · exact Or.inl ⟨"ghost-hook precondition violated", by unfold linkedCallHook; simp [hAct]⟩

/-- **C4 universal-`L` `TrapHook L` for Stage A's plain `memcpyGhostHook`** (holds for **all**
    `keep` and **all** `L : BitVec 64`, including `L` inside `memmove` when `keep L = false`). -/
theorem trapHook_memcpyGhostHook
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (L : BitVec 64) :
    TrapHook L (memcpyGhostHook keep P_real P_sub entryTarget) := by
  have hEntry : keepOf [(entryTarget, memcpySymWords)] entryTarget = true := by
    have h0 : keepOf [(entryTarget, memcpySymWords)] (entryTarget + BitVec.ofNat 64 0) = true :=
      keepOf_mem_offset (List.mem_singleton.mpr rfl) (show 0 < 4 * memcpySymWords.length by decide)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h0
  exact trapHook_linkedCallHook_of_regionWordsSafe hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemcpy_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemcpy keep)
    (fun x s => masterMemcpy_pre_setPC x s entryTarget)
    (regionWordsSafe_single entryTarget memcpy_all_safe)
    (fun blk hm => by rw [List.mem_singleton] at hm; subst hm; exact ⟨P_sub, List.mem_singleton.mpr rfl, hwords⟩)
    hEntry trapHook_hookMemcpy L

/-- **C4 universal-`L` `TrapHook L` for Stage A's `K`-narrowed `memcpyGhostHookK`** (all `keep`, all `L`). -/
theorem trapHook_memcpyGhostHookK
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (L : BitVec 64) :
    TrapHook L (memcpyGhostHookK keep P_real P_sub entryTarget) := by
  have hEntry : keepOf [(entryTarget, memcpySymWords)] entryTarget = true := by
    have h0 : keepOf [(entryTarget, memcpySymWords)] (entryTarget + BitVec.ofNat 64 0) = true :=
      keepOf_mem_offset (List.mem_singleton.mpr rfl) (show 0 < 4 * memcpySymWords.length by decide)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h0
  exact trapHook_linkedCallHook_of_regionWordsSafe hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemcpyK_of_hasWords keep hsub_no hwords)
    (specStripSInvariant_masterMemcpyK keep)
    (fun x s => masterMemcpyK_pre_setPC keep x s entryTarget)
    (regionWordsSafe_single entryTarget memcpy_all_safe)
    (fun blk hm => by rw [List.mem_singleton] at hm; subst hm; exact ⟨P_sub, List.mem_singleton.mpr rfl, hwords⟩)
    hEntry trapHook_hookMemcpy L

/-- **C4 universal-`L` `TrapHook L` for `W`-independent `f3EmptyMemcpyGhostHook`** (`0` `P_real` premises). -/
theorem trapHook_f3EmptyMemcpyGhostHook
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (L : BitVec 64) :
    TrapHook L (f3EmptyMemcpyGhostHook keep P_sub entryTarget) := by
  rw [f3EmptyMemcpyGhostHook_eq]
  exact trapHook_memcpyGhostHook rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords L

/-- **C4 universal-`L` `TrapHook L` for `W`-independent `f3EmptyMemcpyGhostHookK`** (`0` `P_real` premises). -/
theorem trapHook_f3EmptyMemcpyGhostHookK
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memcpySymWords)
    (L : BitVec 64) :
    TrapHook L (f3EmptyMemcpyGhostHookK keep P_sub entryTarget) := by
  rw [f3EmptyMemcpyGhostHookK_eq]
  exact trapHook_memcpyGhostHookK rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords L

/-- **C4 universal-`L` `TrapHook L` for Stage A's plain `memsetGhostHook`** (all `keep`, all `L`). -/
theorem trapHook_memsetGhostHook
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (L : BitVec 64) :
    TrapHook L (memsetGhostHook keep P_real P_sub entryTarget) := by
  have hEntry : keepOf [(entryTarget, memsetWordsSym)] entryTarget = true := by
    have h0 : keepOf [(entryTarget, memsetWordsSym)] (entryTarget + BitVec.ofNat 64 0) = true :=
      keepOf_mem_offset (List.mem_singleton.mpr rfl) (show 0 < 4 * memsetWordsSym.length by decide)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h0
  exact trapHook_linkedCallHook_of_regionWordsSafe hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemset_of_hasWords hsub_no hwords)
    (specStripSInvariant_masterMemset keep)
    (fun x s => masterMemset_pre_setPC x s entryTarget)
    (regionWordsSafe_single entryTarget memsetWords_all_safe)
    (fun blk hm => by rw [List.mem_singleton] at hm; subst hm; exact ⟨P_sub, List.mem_singleton.mpr rfl, hwords⟩)
    hEntry trapHook_hookMemset L

/-- **C4 universal-`L` `TrapHook L` for Stage A's `K`-narrowed `memsetGhostHookK`** (all `keep`, all `L`). -/
theorem trapHook_memsetGhostHookK
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (L : BitVec 64) :
    TrapHook L (memsetGhostHookK keep P_real P_sub entryTarget) := by
  have hEntry : keepOf [(entryTarget, memsetWordsSym)] entryTarget = true := by
    have h0 : keepOf [(entryTarget, memsetWordsSym)] (entryTarget + BitVec.ofNat 64 0) = true :=
      keepOf_mem_offset (List.mem_singleton.mpr rfl) (show 0 < 4 * memsetWordsSym.length by decide)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h0
  exact trapHook_linkedCallHook_of_regionWordsSafe hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterMemsetK_of_hasWords keep hsub_no hwords)
    (specStripSInvariant_masterMemsetK keep)
    (fun x s => masterMemsetK_pre_setPC keep x s entryTarget)
    (regionWordsSafe_single entryTarget memsetWords_all_safe)
    (fun blk hm => by rw [List.mem_singleton] at hm; subst hm; exact ⟨P_sub, List.mem_singleton.mpr rfl, hwords⟩)
    hEntry trapHook_hookMemset L

/-- **C4 universal-`L` `TrapHook L` for `W`-independent `f3EmptyMemsetGhostHook`** (`0` `P_real` premises). -/
theorem trapHook_f3EmptyMemsetGhostHook
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (L : BitVec 64) :
    TrapHook L (f3EmptyMemsetGhostHook keep P_sub entryTarget) := by
  rw [f3EmptyMemsetGhostHook_eq]
  exact trapHook_memsetGhostHook rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords L

/-- **C4 universal-`L` `TrapHook L` for `W`-independent `f3EmptyMemsetGhostHookK`** (`0` `P_real` premises). -/
theorem trapHook_f3EmptyMemsetGhostHookK
    {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget memsetWordsSym)
    (L : BitVec 64) :
    TrapHook L (f3EmptyMemsetGhostHookK keep P_sub entryTarget) := by
  rw [f3EmptyMemsetGhostHookK_eq]
  exact trapHook_memsetGhostHookK rfl hsvc_sub (fun _ _ => rfl) hsub_no hwords L

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemmoveLrTrapBase
