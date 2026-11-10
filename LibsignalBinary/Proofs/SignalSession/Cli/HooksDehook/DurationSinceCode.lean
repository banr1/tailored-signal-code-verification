/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceBoundedVm -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceHullAux
import ProofLib.Hoare.Model
import ProofLib.SepLogic.WP.StepsProcess

/-!
# Region-Local `SystemTime::duration_since` Code Verification & Master Spec (`HooksDehook.DurationSinceCode`)

Untrusted (`Role::Proof`, `0` edits to `Specifications/`) Stage `a1` (`R3-a1`) de-hook module for
`<std::time::SystemTime>::duration_since` (`E2E.durationSinceName`), following the `MemsetCode` +
`LinkedCallHookG` (`roTableGuard`) template and incorporating all five `REV-PILOT` (`a1`) shape
rules:

1. **Permission-free `masterDurationSinceSpec` + permission-carrying `stdDurationSinceSpec` (§1, F1):**
   - `masterDurationSinceSpec` specifies valid `Timespec` inputs (`tv_nsec < 10^9` on both `&self`
     and `(x1, w2)`), `208` B stack (`stackAt s.sp 208`), exact `Result<Duration, SystemTimeError>`
     tag/seconds/nanoseconds at `ret + 0..20` with `(ret + 20) ↦₃₂ b20` preserved, and 7-field
     `DurationSinceStatePreserved` (`abbrev` of `MemsetStatePreserved`), so
     `SpecStripSInvariant keep masterDurationSinceSpec` holds definitionally.
   - `stdDurationSinceSpec` has the **definitionally identical `pre`** (`rfl`) and replaces
     `DurationSinceStatePreserved` with full `StdStatePreserved` (`mem.perm` preserved everywhere)
     so the ghost module derives `VmPreserved` on the active real branch via
     `activeRealRun_stdStatePreserved`.
   - Proves `SpecStripSInvariant`, `SpecPreservesFsTrace`, `masterDurationSince_pre_setPC`, and
     `masterDurationSince_outcome_setPC` directly in this file (F4).
2. **Region-local `subroutine_ok` & single 80-word contiguous hull witness (§2, F1 + F2):**
   - Proves `subroutine_ok` for both `withRoData cst16 timePlacedData0 stdDurationSinceSpec` and
     `withRoData cst16 timePlacedData0 masterDurationSinceSpec` (`= withStateGuard (roTableGuard …)`
     by `rfl`) on any hook-free `P_sub` (`P_sub.svc = Syscall.standard`, `P_sub.externAt? = none`)
     holding patched `Timespec::sub_timespec` (`60` words = `240` B) and patched
     `SystemTime::duration_since` (`20` words = `80` B) — **without** requiring `timeMultiLib`'s
     third block (`SystemTime::add`) in `s0.mem`.
   - Provides the concrete single-program `80`-word (`320` B) contiguous hull
     `durationSinceHullProg` (`pureWordsProg` over `sub_timespec` `60` words followed at `+240#64`
     by `duration_since` `20` words, matching the frozen C2 `.text.lib2` layout with zero gap and
     zero address literals), concrete `hasWords` instances at `+0` and `+240#64`, and concrete
     `subroutine_ok` witnesses at `mpl.base 0 + 240#64`. Block identity in the linked binary comes
     from the untrusted `a2` card plus `K3(b)` (GK6c: no trusted C2 placed-lib entry).
3. **`W`-independent fallback `durationSinceExactHook` soundness & `linkedCallHookG` (§3, F3):**
   - `durationSinceExactHook` is already `W`-free; proves `durationSinceExactHook_master_ok`,
     `keepFsTrace_durationSinceExactHook_eq`, `keepFsTrace_durationSinceExactHook_master_ok`, and
     ready-to-call `hookOk_linkedCallHookG_durationSince` via `hookOk_linkedCallHookG_roTable`.
4. **Consumer `HookOk` lifts (§4, F1 + F5):**
   - Lifts `HookOk f masterDurationSinceSpec` (plus `∀ s, VmPreserved s (f s)` for budget arms)
     to all bare and `withVmPreserved` consumer contracts (`durationSinceBounded*` and
     `durationSinceEpoch*`, including `.keepsFs` and `.inImage`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open VerifiedLibraries.RustStd (
  timespecNs timePlacedData0 timeMultiLib timeRodataCst16Sym
)
open CryptoVerification.SignalSession (durationSinceExactHook)
open CryptoVerification.SignalSession.CliExt (durationSinceEpochSpec)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (
  RoDataAt withRoData
)
open LibsignalBinary.Proofs.HookDischarge.RustStd.TimeDurationSince (
  durationSinceBoundedAtSpec durationSinceBoundedSpec
  durationSinceEpochAtSpec
)
open LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceVm (
  durationSinceEpochAllocSpec durationSinceEpochAllocBudgetSpec
)
open LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceBoundedVm (
  durationSinceBoundedBudgetAtSpec durationSinceBoundedBudgetSpec
  durationSinceBoundedAllocSpec durationSinceBoundedAllocBudgetSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  SpecPreservesFsTrace SpecStripSInvariant keepFsTrace
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG (
  linkedCallHookG roTableGuard roTableGuard_intro_sep_left
  withStateGuard withStateGuard_roTableGuard_eq_withRoData
  hookOk_linkedCallHookG_roTable roDataAt_stripExecOutside
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  MemsetStatePreserved pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceHullAux (
  DurCoreArgs durCore01Spec timeDurationSince_only01_ok
  keep01 strip_codeLoaded_of_imp fetch_in_block_not_svc0_msr steps_pureMem_lift_stripS_vm
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved durationSinceEpochBudgetSpec)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved)

/-! ## 1. Master & Full-Permission Process Specifications and `linkedCallHookG` Side Obligations -/

/-- Ghost argument bundle for `masterDurationSinceSpec` and `stdDurationSinceSpec`:
    - `p`: pointer to `&self` (`SystemTime` / `Timespec`: `s1 : i64 @ +0`, `n1 : u32 @ +8`),
    - `s2`, `n2`: register-passed `earlier` (`x1 = s2`, `(x2).truncate 32 = n2`),
    - `ret`: `24`-byte `sret` pointer in `x8` (`0..20` written, `20..24` preserved as `b20`). -/
structure DurationSinceGhost where
  p : BitVec 64
  s2 : BitVec 64
  n2 : BitVec 32
  ret : BitVec 64
  s1 : BitVec 64
  n1 : BitVec 32
  b20 : BitVec 32

/-- Non-memory process/VM state fields preserved across real `SystemTime::duration_since` and
    `durationSinceExactHook` (reuses `MemsetCode.MemsetStatePreserved`). Separating `mem.perm` out
    of `masterDurationSinceSpec.post` keeps `SpecStripSInvariant keep masterDurationSinceSpec`
    definitional for arbitrary `keep : BitVec 64 → Bool`, while `stdDurationSinceSpec` below carries
    full `StdStatePreserved` (`mem.perm` included) for deriving `VmPreserved` on the active real
    branch (`REV-PILOT` F1). -/
abbrev DurationSinceStatePreserved : State → State → Prop :=
  MemsetStatePreserved

/-- Strip-invariant master contract for `<std::time::SystemTime>::duration_since`:
    requires valid `Timespec` nanoseconds (`n1, n2 < 10^9`), `12` readable `&self` bytes at `p`,
    `20 + 4 = 24` writable `sret` bytes at `ret`, and `208` B stack (`stackAt s.sp 208`), writes
    the exact `Result<Duration, SystemTimeError>` `(tag, d / 10^9, d % 10^9)` to `ret + 0..20`
    while preserving `(ret + 20) ↦₃₂ b20`, `stackAt s0.sp 208`, and `DurationSinceStatePreserved`,
    and never panics, exits, or OOMs. -/
@[expose] def masterDurationSinceSpec : Spec DurationSinceGhost where
  pre := fun x s0 =>
    ⌜s0.readReg64 .x0 = x.p ∧
      s0.readReg64 .x1 = x.s2 ∧
      (s0.readReg64 .x2).truncate 32 = x.n2 ∧
      s0.readReg64 .x8 = x.ret ∧
      x.n1.toNat < 10 ^ 9 ∧
      x.n2.toNat < 10 ^ 9⌝ ∗
      (x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1) ∗
      memRegion x.ret 20 ∗ ((x.ret + 20#64) ↦₃₂ x.b20) ∗
      stackAt s0.sp 208
  post := fun x s0 sf =>
    let t1 := timespecNs x.s1 x.n1
    let t2 := timespecNs x.s2 x.n2
    let d := (t1 - t2).natAbs
    let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
    ⌜DurationSinceStatePreserved s0 sf⌝ ∗
      (x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1) ∗
      (x.ret ↦₆₄ tag) ∗
      ((x.ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
      ((x.ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗
      ((x.ret + 20#64) ↦₃₂ x.b20) ∗
      stackAt s0.sp 208
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Full-permission process specification for `<std::time::SystemTime>::duration_since`
    (`REV-PILOT` F1): shares the **exact same `pre`** (`rfl`) as `masterDurationSinceSpec` and
    strengthens `post` from `DurationSinceStatePreserved` to `StdStatePreserved` (`mem.perm`
    preserved everywhere), enabling the ghost module to prove `VmPreserved` on the active real-code
    branch via `activeRealRun_stdStatePreserved`. -/
@[expose] def stdDurationSinceSpec : Spec DurationSinceGhost where
  pre := masterDurationSinceSpec.pre
  post := fun x s0 sf =>
    let t1 := timespecNs x.s1 x.n1
    let t2 := timespecNs x.s2 x.n2
    let d := (t1 - t2).natAbs
    let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
    ⌜StdStatePreserved s0 sf⌝ ∗
      (x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1) ∗
      (x.ret ↦₆₄ tag) ∗
      ((x.ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
      ((x.ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗
      ((x.ret + 20#64) ↦₃₂ x.b20) ∗
      stackAt s0.sp 208
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- `stdDurationSinceSpec.pre` is definitionally `masterDurationSinceSpec.pre`. -/
theorem stdDurationSince_pre_eq (x : DurationSinceGhost) (s0 : State) :
    stdDurationSinceSpec.pre x s0 = masterDurationSinceSpec.pre x s0 :=
  rfl

/-- `withStateGuard (roTableGuard tbl timePlacedData0)` on `masterDurationSinceSpec` is
    definitionally `withRoData tbl timePlacedData0 masterDurationSinceSpec`. -/
theorem withStateGuard_roTableGuard_master_eq (tbl : BitVec 64) :
    withStateGuard (roTableGuard tbl timePlacedData0) masterDurationSinceSpec =
      withRoData tbl timePlacedData0 masterDurationSinceSpec :=
  withStateGuard_roTableGuard_eq_withRoData tbl timePlacedData0 masterDurationSinceSpec

/-- `withStateGuard (roTableGuard tbl timePlacedData0)` on `stdDurationSinceSpec` is
    definitionally `withRoData tbl timePlacedData0 stdDurationSinceSpec`. -/
theorem withStateGuard_roTableGuard_std_eq (tbl : BitVec 64) :
    withStateGuard (roTableGuard tbl timePlacedData0) stdDurationSinceSpec =
      withRoData tbl timePlacedData0 stdDurationSinceSpec :=
  withStateGuard_roTableGuard_eq_withRoData tbl timePlacedData0 stdDurationSinceSpec

/-- `masterDurationSinceSpec` is invariant under `stripExecOutside keep` for every `keep`. -/
theorem specStripSInvariant_masterDurationSince (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterDurationSinceSpec where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

/-- `masterDurationSinceSpec` preserves `fs` and `FsTraced` across every `SubroutineOutcome`. -/
theorem specPreservesFsTrace_masterDurationSince :
    SpecPreservesFsTrace masterDurationSinceSpec := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterDurationSinceSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs : sf.fs = s0.fs := hpost.1.1
    have htr : sf.trace = s0.trace := hpost.1.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · dsimp only [masterDurationSinceSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [masterDurationSinceSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [masterDurationSinceSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- `masterDurationSinceSpec.pre` is independent of `s.pc`. -/
theorem masterDurationSince_pre_setPC (x : DurationSinceGhost) (s : State) (pc : BitVec 64) :
    masterDurationSinceSpec.pre x (s.setPC pc) = masterDurationSinceSpec.pre x s := by
  cases s; rfl

/-- `SubroutineOutcome masterDurationSinceSpec` is independent of the initial `s0.pc`. -/
theorem masterDurationSince_outcome_setPC (x : DurationSinceGhost) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterDurationSinceSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterDurationSinceSpec x R s0 sf := by
  cases s0; cases sf; exact h

/-- `stdDurationSinceSpec.pre` is independent of `s.pc`. -/
theorem stdDurationSince_pre_setPC (x : DurationSinceGhost) (s : State) (pc : BitVec 64) :
    stdDurationSinceSpec.pre x (s.setPC pc) = stdDurationSinceSpec.pre x s := by
  cases s; rfl

/-- `SubroutineOutcome stdDurationSinceSpec` is independent of the initial `s0.pc`. -/
theorem stdDurationSince_outcome_setPC (x : DurationSinceGhost) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome stdDurationSinceSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome stdDurationSinceSpec x R s0 sf := by
  cases s0; cases sf; exact h

/-! ## 2. Region-Local `subroutine_ok` & Single `80`-Word Contiguous Hull Witness -/

/-- Relocation-patched 32-bit word list (`blk.code.length / 4` words) of `blk` at placement `pl`. -/
@[expose] def blockPatchedWords (blk : CodeBlock) (pl : Placement) : List (BitVec 32) :=
  (List.range (blk.code.length / 4)).map fun j => blk.patchedWord pl (4 * j)

/-- Relocation-patched `60` words (`240` B) of `Timespec::sub_timespec` (`timeMultiLib` block `0`)
    at `mpl`. -/
@[expose] def subTimespecPatchedWords (mpl : MultiPlacement) : List (BitVec 32) :=
  blockPatchedWords (timeMultiLib.blockLib 0).text (timeMultiLib.blockPlacement mpl 0)

/-- Relocation-patched `20` words (`80` B) of `SystemTime::duration_since` (`timeMultiLib` block `1`)
    at `mpl`. -/
@[expose] def durationSincePatchedWords (mpl : MultiPlacement) : List (BitVec 32) :=
  blockPatchedWords (timeMultiLib.blockLib 1).text (timeMultiLib.blockPlacement mpl 1)

/-- Contiguous `80`-word (`320` B) instruction hull for the `duration_since` row in `.text.lib2`
    (`REV-PILOT` F2): `sub_timespec` (`60` words at `+0`) immediately followed by `duration_since`
    (`20` words at `+240`). -/
@[expose] def durationSinceHullWords (mpl : MultiPlacement) : List (BitVec 32) :=
  subTimespecPatchedWords mpl ++ durationSincePatchedWords mpl

/-- Single-hull hook-free `Program` (`pureWordsProg`) holding `durationSinceHullWords mpl` (`80`
    words = `320` B) starting at `mpl.base 0`, with `duration_since` at `mpl.base 0 + 240#64`
    (`REV-PILOT` F2). -/
@[expose] def durationSinceHullProg (mpl : MultiPlacement) : Program :=
  pureWordsProg (mpl.base 0) (durationSinceHullWords mpl)

theorem subTimespecPatchedWords_length (mpl : MultiPlacement) :
    (subTimespecPatchedWords mpl).length = 60 := by
  have hlen : (timeMultiLib.blockLib 0).text.code.length = 240 := by decide +kernel
  simp [subTimespecPatchedWords, blockPatchedWords, hlen]

theorem durationSincePatchedWords_length (mpl : MultiPlacement) :
    (durationSincePatchedWords mpl).length = 20 := by
  have hlen : (timeMultiLib.blockLib 1).text.code.length = 80 := by decide +kernel
  simp [durationSincePatchedWords, blockPatchedWords, hlen]

theorem durationSinceHullWords_length (mpl : MultiPlacement) :
    (durationSinceHullWords mpl).length = 80 := by
  simp [durationSinceHullWords, subTimespecPatchedWords_length, durationSincePatchedWords_length]

private theorem bytesOfWordLE_eq_wordToBytesLE (w : BitVec 32) :
    bytesOfWordLE w = Program.wordToBytesLE w := by
  have hex (k : Nat) (hk : k + 8 ≤ 32) :
      BitVec.extractLsb' k 8 (BitVec.zeroExtend 64 w) = BitVec.extractLsb' k 8 w := by
    ext i hi
    simp
    omega
  unfold bytesOfWordLE bytesLE Program.wordToBytesLE
  simp only [List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.map_cons, List.map_nil, Nat.mul_zero, Nat.mul_one]
  rw [show 8 * 2 = 16 by rfl, show 8 * 3 = 24 by rfl,
    hex 0 (by decide), hex 8 (by decide), hex 16 (by decide), hex 24 (by decide)]

private theorem flatMap_wordToBytesLE_blockPatchedWords (blk : CodeBlock) (pl : Placement) :
    (blockPatchedWords blk pl).flatMap Program.wordToBytesLE = blk.patched pl := by
  unfold blockPatchedWords CodeBlock.patched
  simp only [List.flatMap_map, ← bytesOfWordLE_eq_wordToBytesLE]

/-- Prefix `hasWords` for `pureWordsProg base (wordsA ++ wordsB)` at `base`. -/
theorem pureWordsProg_hasWords_append_left (base : BitVec 64)
    (wordsA wordsB : List (BitVec 32))
    (hlen : 4 * (wordsA.length + wordsB.length) ≤ 2 ^ 64) :
    (pureWordsProg base (wordsA ++ wordsB)).hasWords base wordsA := by
  unfold Program.hasWords Program.hasWordsOff
  have hsub : (base - (pureWordsProg base (wordsA ++ wordsB)).base).toNat = 0 := by
    change (base - base).toNat = 0
    simp
  rw [hsub]
  have hcode_len : (pureWordsProg base (wordsA ++ wordsB)).code.length =
      4 * (wordsA.length + wordsB.length) := by
    unfold pureWordsProg Program.ofWords
    rw [Program.length_flatMap_wordToBytesLE, List.length_append]
  refine ⟨by omega, fun i hi => ?_, ⟨rfl, rfl⟩⟩
  have hi' : i < (wordsA ++ wordsB).length := by rw [List.length_append]; omega
  rw [Nat.zero_add, Program.readWordOff_eq_some_iff _ _ _ (by omega)]
  have h r (hr : r < 4) := Program.getElem?_flatMap_wordToBytesLE (wordsA ++ wordsB) i r hi' hr
  have hget : (wordsA ++ wordsB)[i]'hi' = wordsA[i]'hi := List.getElem_append_left hi
  simp only [hget] at h
  dsimp only [pureWordsProg, Program.ofWords]
  refine ⟨?_, h 1 (by omega), h 2 (by omega), h 3 (by omega)⟩
  have h0 := h 0 (by omega)
  simpa only [Nat.add_zero] using h0

/-- Suffix `hasWords` for `pureWordsProg base (wordsA ++ wordsB)` at
    `base + BitVec.ofNat 64 (4 * wordsA.length)`. -/
theorem pureWordsProg_hasWords_append_right (base : BitVec 64)
    (wordsA wordsB : List (BitVec 32))
    (hlen : 4 * (wordsA.length + wordsB.length) ≤ 2 ^ 64)
    (hoff_lt : 4 * wordsA.length < 2 ^ 64) :
    (pureWordsProg base (wordsA ++ wordsB)).hasWords
      (base + BitVec.ofNat 64 (4 * wordsA.length)) wordsB := by
  unfold Program.hasWords Program.hasWordsOff
  have hdiff : base + BitVec.ofNat 64 (4 * wordsA.length) -
      (pureWordsProg base (wordsA ++ wordsB)).base =
      BitVec.ofNat 64 (4 * wordsA.length) := by
    change base + BitVec.ofNat 64 (4 * wordsA.length) - base = _
    bv_omega
  have hsub : (base + BitVec.ofNat 64 (4 * wordsA.length) -
      (pureWordsProg base (wordsA ++ wordsB)).base).toNat = 4 * wordsA.length := by
    rw [hdiff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt]
  rw [hsub]
  have hcode_len : (pureWordsProg base (wordsA ++ wordsB)).code.length =
      4 * (wordsA.length + wordsB.length) := by
    unfold pureWordsProg Program.ofWords
    rw [Program.length_flatMap_wordToBytesLE, List.length_append]
  refine ⟨by omega, fun i hi => ?_, ⟨rfl, rfl⟩⟩
  have hi' : wordsA.length + i < (wordsA ++ wordsB).length := by
    rw [List.length_append]; omega
  have hmul : 4 * wordsA.length + 4 * i = 4 * (wordsA.length + i) := by omega
  rw [hmul, Program.readWordOff_eq_some_iff _ _ _ (by omega)]
  have h r (hr : r < 4) :=
    Program.getElem?_flatMap_wordToBytesLE (wordsA ++ wordsB) (wordsA.length + i) r hi' hr
  have hget : (wordsA ++ wordsB)[wordsA.length + i]'hi' = wordsB[i]'hi := by
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp
  simp only [hget] at h
  dsimp only [pureWordsProg, Program.ofWords]
  refine ⟨?_, h 1 (by omega), h 2 (by omega), h 3 (by omega)⟩
  have h0 := h 0 (by omega)
  simpa only [Nat.add_zero] using h0

/-- Concrete `hasWords` instance: `durationSinceHullProg mpl` holds `subTimespecPatchedWords mpl`
    (`60` words) at `mpl.base 0`. -/
theorem durationSinceHullProg_hasWords_subTimespec (mpl : MultiPlacement) :
    (durationSinceHullProg mpl).hasWords (mpl.base 0) (subTimespecPatchedWords mpl) := by
  refine pureWordsProg_hasWords_append_left (mpl.base 0)
    (subTimespecPatchedWords mpl) (durationSincePatchedWords mpl) ?_
  rw [subTimespecPatchedWords_length, durationSincePatchedWords_length]
  decide

/-- Concrete `hasWords` instance: `durationSinceHullProg mpl` holds `durationSincePatchedWords mpl`
    (`20` words) at `mpl.base 0 + 240#64`. -/
theorem durationSinceHullProg_hasWords_durationSince (mpl : MultiPlacement) :
    (durationSinceHullProg mpl).hasWords (mpl.base 0 + 240#64) (durationSincePatchedWords mpl) := by
  have h240 : BitVec.ofNat 64 (4 * (subTimespecPatchedWords mpl).length) = 240#64 := by
    rw [subTimespecPatchedWords_length]
  rw [← h240]
  refine pureWordsProg_hasWords_append_right (mpl.base 0)
    (subTimespecPatchedWords mpl) (durationSincePatchedWords mpl) ?_ ?_
  · rw [subTimespecPatchedWords_length, durationSincePatchedWords_length]; decide
  · rw [subTimespecPatchedWords_length]; decide

/-- `durationSinceHullProg mpl` has no external hooks (`externAt? pc = none`). -/
theorem durationSinceHullProg_externAt_none (mpl : MultiPlacement) (pc : BitVec 64) :
    (durationSinceHullProg mpl).externAt? pc = none :=
  pureWordsProg_externAt_none (mpl.base 0) (durationSinceHullWords mpl) pc

/-- `durationSinceHullProg mpl` uses `Syscall.standard`. -/
theorem durationSinceHullProg_svc (mpl : MultiPlacement) :
    (durationSinceHullProg mpl).svc = Syscall.standard :=
  rfl

/-- From `P_sub.CodeLoaded m` and `P_sub.hasWords (mpl.base j) (blockPatchedWords ...)`, the
    individual placed block `timeMultiLib.blockProgram mpl j` (`j < 3`) is `CodeLoaded` in `m`
    without requiring any other block of `timeMultiLib` to exist in `m`. -/
theorem blockProgram_codeLoaded_of_hasWords {P_sub : Program} {mpl : MultiPlacement}
    {j : Nat} (hj : j < timeMultiLib.blocks.length)
    (hpl : timeMultiLib.Placeable mpl)
    {m : Memory} (hcl : P_sub.CodeLoaded m)
    (hw : P_sub.hasWords (mpl.base j)
      (blockPatchedWords (timeMultiLib.blockLib j).text (timeMultiLib.blockPlacement mpl j))) :
    (timeMultiLib.blockProgram mpl j).CodeLoaded m := by
  have hbt := hpl.blocks_ok j hj
  have hbt' : (timeMultiLib.blockLib j).text.Placeable (timeMultiLib.blockPlacement mpl j) := by
    rwa [timeMultiLib.blockLib_text hj]
  have hcode_eq : (timeMultiLib.blockProgram mpl j).code =
      (timeMultiLib.blockLib j).text.patched (timeMultiLib.blockPlacement mpl j) := rfl
  have hplen : (timeMultiLib.blockProgram mpl j).code.length =
      (timeMultiLib.blockLib j).text.code.length := by
    rw [hcode_eq, CodeBlock.length_patched_of_aligned _ hbt'.len_aligned]
  have hbase_eq : (timeMultiLib.blockProgram mpl j).base = mpl.base j := rfl
  have hal_dvd : 4 ∣ (timeMultiLib.blockLib j).text.align := by
    have hj3 : j < 3 := hj
    rcases j with _ | _ | _ | j
    · decide
    · decide
    · decide
    · omega
  have hbase_al4 : (mpl.base j).toNat % 4 = 0 := by
    have h0 : (mpl.base j).toNat % (timeMultiLib.blockLib j).text.align = 0 := hbt'.base_aligned
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hal_dvd (Nat.dvd_of_mod_eq_zero h0))
  refine Program.CodeLoaded.intro
    (by rw [hbase_eq]; exact hbase_al4)
    (by rw [hbase_eq, hplen]; exact hbt'.no_wrap)
    fun k hk => ?_
  let ws := blockPatchedWords (timeMultiLib.blockLib j).text (timeMultiLib.blockPlacement mpl j)
  have hflat : ws.flatMap Program.wordToBytesLE = (timeMultiLib.blockProgram mpl j).code :=
    (flatMap_wordToBytesLE_blockPatchedWords _ _).trans hcode_eq.symm
  have hk_ws : k < 4 * ws.length := by
    have hfl_len := congrArg List.length hflat
    rw [Program.length_flatMap_wordToBytesLE] at hfl_len
    omega
  unfold Program.hasWords at hw
  let off := (mpl.base j - P_sub.base).toNat
  have hget := Program.code_getElem?_of_hasWordsOff hw k hk_ws
  rw [hflat, List.getElem?_eq_getElem hk] at hget
  have hoff_lt : off + k < P_sub.code.length := by
    cases h : P_sub.code[off + k]? with
    | none => rw [h] at hget; cases hget
    | some _ => exact (List.getElem?_eq_some_iff.mp h).1
  have hP_nw := hcl.no_wrap
  have haddr_eq : mpl.base j + BitVec.ofNat 64 k = P_sub.base + BitVec.ofNat 64 (off + k) := by
    have h1 : P_sub.base + BitVec.ofNat 64 off = mpl.base j := by
      dsimp [off]; bv_omega
    rw [← h1]
    bv_omega
  rw [hbase_eq, haddr_eq]
  have hb := hcl.byte_eq (off + k) hoff_lt
  have hbyte_eq : P_sub.code[off + k]'hoff_lt = (timeMultiLib.blockProgram mpl j).code[k]'hk := by
    rw [List.getElem?_eq_getElem hoff_lt] at hget
    exact Option.some.inj hget
  rw [hbyte_eq] at hb
  exact ⟨hb, hcl.perm_eq (off + k) hoff_lt, hcl.isLazyFree_eq (off + k) hoff_lt⟩

/-! ### 2b. Process-Level `StdStatePreserved` Lift & `80`-Word Hull `subroutine_ok` -/

/-- Region-local `subroutine_ok` for `withRoData ... stdDurationSinceSpec` (`StdStatePreserved`
    including `mem.perm`, `REV-PILOT` F1) on any hook-free `P_sub` (`P_sub.svc = Syscall.standard`,
    `P_sub.externAt? = none`) holding patched `sub_timespec` (`60` words) and `duration_since`
    (`20` words), without requiring `timeMultiLib` block `2` (`SystemTime::add`) in `s0.mem`. -/
theorem subroutine_ok_stdDurationSince_of_hasWords {P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl)) :
    subroutine_ok P_sub (mpl.base 1)
      (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 stdDurationSinceSpec) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp hLi
  have hcl0 : (timeMultiLib.blockProgram mpl 0).CodeLoaded s0.mem :=
    blockProgram_codeLoaded_of_hasWords (j := 0) (by decide) hpl hLi hw0
  have hcl1 : (timeMultiLib.blockProgram mpl 1).CodeLoaded s0.mem :=
    blockProgram_codeLoaded_of_hasWords (j := 1) (by decide) hpl hLi hw1
  dsimp only [withRoData, stdDurationSinceSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, hpre_m⟩
  let keep := keep01 mpl
  obtain ⟨R_view, hpre_strip, hunstrip⟩ := strip_frame keep hpre_m
  let s0' := stripS keep s0
  have hmem_s0' : s0'.mem = stripExecOutside keep s0.mem := by cases s0; rfl
  have hcl0' : (timeMultiLib.blockProgram mpl 0).CodeLoaded s0'.mem := by
    rw [hmem_s0']
    exact strip_codeLoaded_of_imp hcl0 fun a hk => by
      dsimp only [keep, keep01]; rw [hk]; rfl
  have hcl1' : (timeMultiLib.blockProgram mpl 1).CodeLoaded s0'.mem := by
    rw [hmem_s0']
    exact strip_codeLoaded_of_imp hcl1 fun a hk => by
      dsimp only [keep, keep01]; rw [hk, Bool.or_true]
  have hro' : roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0 s0' := by
    change RoDataAt s0'.mem (mpl.ρ timeRodataCst16Sym) timePlacedData0
    rw [hmem_s0']; exact roDataAt_stripExecOutside keep hro
  have hpre_s0' : s0'.mem ⊨ masterDurationSinceSpec.pre x s0' ∗ R_view := by
    have heq : masterDurationSinceSpec.pre x s0' = masterDurationSinceSpec.pre x s0 := by
      cases s0; rfl
    rw [heq, hmem_s0']; exact hpre_strip
  let xa : DurCoreArgs := (x.p, x.s2, x.n2, x.ret, x.s1, x.n1, x.b20)
  have hpre_core : s0'.mem ⊨ (durCore01Spec mpl).pre xa s0' ∗ R_view := by
    dsimp only [durCore01Spec, xa]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl0', roTableGuard_intro_sep_left hro' (by decide) hpre_s0'⟩
  obtain ⟨sf', hsteps_blk, hout'⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 (@timeDurationSince_only01_ok ⟨mpl, hpl⟩) xa R_view s0'
      (by cases s0; exact hpc) (by cases s0; exact hrun) hpre_core (by cases s0; exact hsp))
    hcl1'
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have h0 : ∀ L : List (String × Nat),
        L.findSome? (fun _ => (none : Option (State → State))) = none := by
      intro L; induction L <;> simp [*]
    have hsteps_pm' : Steps Program.pureMem s0' sf' :=
      Steps.of_sameHooks (P := Program.pureMem) (Q := timeMultiLib.blockProgram mpl 1)
        (by
          intro pc
          have hpure_ext : Program.pureMem.externAt? pc = none := rfl
          rw [hpure_ext]
          dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program,
            Program.externAt?, Program.hookAtOff?]
          simp only [ite_self, h0, Option.or_none]) rfl hsteps_blk
    obtain ⟨sf, hsf_eq, hsteps_P, hnsp, htp⟩ :=
      steps_pureMem_lift_stripS_vm keep (P := P_sub) hsvc (fun pc _ => hsub_no pc)
        (fun m pc inst hkf hk hfm => by
          dsimp only [keep, keep01] at hk
          cases hk0 : progKeep (timeMultiLib.blockProgram mpl 0) pc
          · rw [hk0, Bool.false_or] at hk
            exact fetch_in_block_not_svc0_msr (j := 1) (by decide) hpl hcl1 hkf hk hfm
          · exact fetch_in_block_not_svc0_msr (j := 0) (by decide) hpl hcl0 hkf hk0 hfm)
        rfl (Memory.KeepsFrozen.refl s0.mem) hsteps_pm' hret'.2.2
    dsimp only [durCore01Spec, xa] at hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    rcases hpost' with ⟨⟨hio, _⟩, hro_q⟩
    have hsig : sf.sigActions = s0.sigActions := by
      have hs : sf'.sigActions = s0'.sigActions := hio.2
      rw [hsf_eq] at hs
      cases s0; cases sf; exact hs
    have hstd : StdStatePreserved s0 sf :=
      ⟨hnsp.2.2.2.2.2.2, hnsp.1, htp, hsig, hnsp.2.2.1, hnsp.2.2.2.1, hnsp.2.2.2.2.1,
        fun a => congrFun hnsp.2.1 a⟩
    rw [sepConj_assoc] at hro_q
    have hq_strip : sf'.mem ⊨
        ((x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1) ∗
          (x.ret ↦₆₄ if timespecNs x.s2 x.n2 ≤ timespecNs x.s1 x.n1 then 0#64 else 1#64) ∗
          ((x.ret + 8#64) ↦₆₄ BitVec.ofNat 64 ((timespecNs x.s1 x.n1 - timespecNs x.s2 x.n2).natAbs / 10 ^ 9)) ∗
          ((x.ret + 16#64) ↦₃₂ BitVec.ofNat 32 ((timespecNs x.s1 x.n1 - timespecNs x.s2 x.n2).natAbs % 10 ^ 9)) ∗
          ((x.ret + 20#64) ↦₃₂ x.b20) ∗ stackAt s0.sp 208) ∗ R_view := by
      have hdrop := Satisfies.of_sep_right hro_q
      have hsp_eq : s0'.sp = s0.sp := by cases s0; rfl
      rw [hsp_eq] at hdrop
      simpa only [sepConj_assoc] using hdrop
    have hmem_sf' : sf'.mem = stripExecOutside keep sf.mem := by
      rw [hsf_eq]; cases sf; rfl
    rw [hmem_sf'] at hq_strip
    have hq_sf := hunstrip (fun a => congrFun hnsp.2.1 a) hq_strip
    refine ⟨sf, hsteps_P, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      rw [hsf_eq] at hr_pc hr_sp hr_st
      exact ⟨by cases s0; cases sf; exact hr_pc,
        by cases s0; cases sf; exact hr_sp,
        by cases sf; exact hr_st⟩
    · rw [hsf_eq] at hcc'
      rcases hcc' with ⟨hsp_cc, hcs⟩
      exact ⟨by cases s0; cases sf; exact hsp_cc, by cases s0; cases sf; exact hcs⟩
    · dsimp only [withRoData, stdDurationSinceSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hstd, by simpa only [sepConj_assoc] using hq_sf⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- Region-local `subroutine_ok` for `withRoData ... masterDurationSinceSpec` on any hook-free
    `P_sub` holding patched `sub_timespec` (`60` words) and `duration_since` (`20` words). -/
theorem subroutine_ok_masterDurationSince_of_hasWords {P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc : P_sub.svc = Syscall.standard)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl)) :
    subroutine_ok P_sub (mpl.base 1)
      (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 masterDurationSinceSpec) := by
  refine subroutine_ok_mono (subroutine_ok_stdDurationSince_of_hasWords hpl hsvc hsub_no hw0 hw1)
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => ?_)
  dsimp only [withRoData, stdDurationSinceSpec, masterDurationSinceSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨MemsetStatePreserved.of_stdStatePreserved hq.1, hq.2⟩

/-- Concrete `80`-word contiguous hull `subroutine_ok` for `stdDurationSinceSpec` at layout-generic
    entry `hullBase + 240#64` (`REV-PILOT` F1 + F2; in the C2 `.text.lib2` layout `sub_timespec`
    occupies `[hullBase, hullBase + 240)` and `duration_since` occupies
    `[hullBase + 240, hullBase + 320)`). -/
theorem durationSinceHullProg_stdDurationSince_ok {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl)
    (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + 240#64) :
    subroutine_ok (durationSinceHullProg mpl) (hullBase + 240#64)
      (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 stdDurationSinceSpec) := by
  rw [← hb1]
  refine subroutine_ok_stdDurationSince_of_hasWords hpl
    (durationSinceHullProg_svc mpl)
    (durationSinceHullProg_externAt_none mpl)
    (durationSinceHullProg_hasWords_subTimespec mpl) ?_
  rw [hb1, ← hb0]
  exact durationSinceHullProg_hasWords_durationSince mpl

/-- Concrete `80`-word contiguous hull `subroutine_ok` for `masterDurationSinceSpec` at
    layout-generic entry `hullBase + 240#64` (`REV-PILOT` F2). -/
theorem durationSinceHullProg_masterDurationSince_ok {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl)
    (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + 240#64) :
    subroutine_ok (durationSinceHullProg mpl) (hullBase + 240#64)
      (withRoData (mpl.ρ timeRodataCst16Sym) timePlacedData0 masterDurationSinceSpec) := by
  rw [← hb1]
  refine subroutine_ok_masterDurationSince_of_hasWords hpl
    (durationSinceHullProg_svc mpl)
    (durationSinceHullProg_externAt_none mpl)
    (durationSinceHullProg_hasWords_subTimespec mpl) ?_
  rw [hb1, ← hb0]
  exact durationSinceHullProg_hasWords_durationSince mpl

/-! ## 3. `W`-Independent Fallback `durationSinceExactHook` Soundness & `linkedCallHookG` -/

private theorem retHook_vm {f : State → State} {s : State} (h : VmPreserved s (f s)) :
    VmPreserved s (retHook f s) := h

private theorem setMem_vm (s : State) {m : Memory}
    (hp : ∀ a : BitVec 64, m.perm a = s.mem.perm a) :
    VmPreserved s (s.setMem m) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => by cases s; rfl⟩

/-- `durationSinceExactHook` preserves `VmPreserved` pointwise (`W`-free). -/
theorem durationSinceExactHook_vm (s : State) :
    VmPreserved s (durationSinceExactHook s) := by
  unfold durationSinceExactHook; try dsimp only
  split
  · exact LibsignalBinary.Heap.VmPreserved.refl s
  · try dsimp only
    split
    · refine retHook_vm (setMem_vm s fun a => ?_)
      simp only [LibsignalBinary.Heap.IfaceBudgetLemmas.perm_write32_norm,
        LibsignalBinary.Heap.IfaceBudgetLemmas.perm_write64_norm]
    · exact LibsignalBinary.Heap.VmPreserved.refl s

/-- `W`-independent fallback soundness (`REV-PILOT` F3): `durationSinceExactHook` satisfies
    `masterDurationSinceSpec`. -/
theorem durationSinceExactHook_master_ok :
    HookOk durationSinceExactHook masterDurationSinceSpec := by
  intro x R s0 hrun hpre _hsp
  dsimp only [masterDurationSinceSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx8, hn1, hn2⟩, hmem⟩
  have hm_p64 : s0.mem ⊨ (x.p ↦₆₄ x.s1) ∗ (((x.p + 8#64) ↦₃₂ x.n1) ∗ memRegion x.ret 20 ∗
      ((x.ret + 20#64) ↦₃₂ x.b20) ∗ stackAt s0.sp 208 ∗ R) := by ac_nf at hmem ⊢
  have hrd64 : s0.mem.read64 x.p = x.s1 := (IsBlock.pointsTo64 x.p x.s1).read hm_p64
  have hm_p32 : s0.mem ⊨ ((x.p + 8#64) ↦₃₂ x.n1) ∗ ((x.p ↦₆₄ x.s1) ∗ memRegion x.ret 20 ∗
      ((x.ret + 20#64) ↦₃₂ x.b20) ∗ stackAt s0.sp 208 ∗ R) := by ac_nf at hmem ⊢
  have hrd32 : s0.mem.read32 (x.p + 8#64) = x.n1 :=
    (IsBlock.pointsTo32 (x.p + 8#64) x.n1).read hm_p32
  have hm_p12 : s0.mem ⊨ memRegion x.p 12 ∗ (memRegion x.ret 20 ∗
      ((x.ret + 20#64) ↦₃₂ x.b20) ∗ stackAt s0.sp 208 ∗ R) := by
    have hgrp : s0.mem ⊨ ((x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1)) ∗ (memRegion x.ret 20 ∗
        ((x.ret + 20#64) ↦₃₂ x.b20) ∗ stackAt s0.sp 208 ∗ R) := by ac_nf at hmem ⊢
    have hent : ((x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1)) ⊢ memRegion x.p 12 := by
      rw [memRegion_split' (b := x.p) (n := 8) (k := 4) (b' := x.p + 8#64) rfl rfl (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion x.p x.s1)
        (pointsTo32_entails_memRegion (x.p + 8#64) x.n1)
    exact Satisfies.mono (sepConj_mono_left hent) hgrp
  have hcanR : s0.mem.canRead x.p 12 = true := (IsBlock.memRegion x.p 12).canRead (by decide) hm_p12
  have hm_ret24 : s0.mem ⊨ memRegion x.ret 24 ∗ ((x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1) ∗
      stackAt s0.sp 208 ∗ R) := by
    have hgrp : s0.mem ⊨ (memRegion x.ret 20 ∗ ((x.ret + 20#64) ↦₃₂ x.b20)) ∗
        ((x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1) ∗ stackAt s0.sp 208 ∗ R) := by ac_nf at hmem ⊢
    have hent : (memRegion x.ret 20 ∗ ((x.ret + 20#64) ↦₃₂ x.b20)) ⊢ memRegion x.ret 24 := by
      rw [memRegion_split' (b := x.ret) (n := 20) (k := 4) (b' := x.ret + 20#64) rfl rfl (by decide)]
      exact sepConj_mono_right (pointsTo32_entails_memRegion (x.ret + 20#64) x.b20)
    exact Satisfies.mono (sepConj_mono_left hent) hgrp
  have hcanW : s0.mem.canWrite x.ret 24 = true :=
    (IsBlock.memRegion x.ret 24).canWrite (by decide) hm_ret24
  have hsplit20 : memRegion x.ret 20 =
      (∃∗ w0 : BitVec 64, x.ret ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (x.ret + 8#64) ↦₆₄ w1) ∗
      (∃∗ lo : BitVec 32, (x.ret + 16#64) ↦₃₂ lo) := by
    rw [memRegion_split' (b := x.ret) (n := 8) (k := 12) (b' := x.ret + 8#64) rfl rfl (by decide),
      memRegion_split' (b := x.ret + 8#64) (n := 8) (k := 4) (b' := x.ret + 16#64) rfl
        (by bv_omega) (by decide),
      ProofLib.memRegion_eight x.ret, ProofLib.memRegion_eight (x.ret + 8#64),
      ProofLib.memRegion_four (x.ret + 16#64)]
  rw [hsplit20] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hmem
  rcases hmem with ⟨lo, w1, w0, hcells⟩
  let t1 := timespecNs x.s1 x.n1
  let t2 := timespecNs x.s2 x.n2
  let d := (t1 - t2).natAbs
  let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
  let secs := BitVec.ofNat 64 (d / 10 ^ 9)
  let nanos := BitVec.ofNat 32 (d % 10 ^ 9)
  have hc0 : s0.mem ⊨ (x.ret ↦₆₄ w0) ∗ (((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret + 16#64) ↦₃₂ lo) ∗
      ((x.ret + 20#64) ↦₃₂ x.b20) ∗ (x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1) ∗
      stackAt s0.sp 208 ∗ R) := by ac_nf at hcells ⊢
  have hkf1 := Memory.keepsFrozen_write64 ((IsBlock.pointsTo64 x.ret w0).canWrite (by decide) hc0) tag
  have hw1 := IsBlock.write64 (IsBlock.pointsTo64 x.ret w0) hc0 tag
  have hc1 : s0.mem.write64 x.ret tag ⊨ ((x.ret + 8#64) ↦₆₄ w1) ∗ ((x.ret ↦₆₄ tag) ∗
      ((x.ret + 16#64) ↦₃₂ lo) ∗ ((x.ret + 20#64) ↦₃₂ x.b20) ∗
      (x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1) ∗ stackAt s0.sp 208 ∗ R) := by ac_nf at hw1 ⊢
  have hkf2 := Memory.keepsFrozen_write64
    ((IsBlock.pointsTo64 (x.ret + 8#64) w1).canWrite (by decide) hc1) secs
  have hw2 := IsBlock.write64 (IsBlock.pointsTo64 (x.ret + 8#64) w1) hc1 secs
  have hc2 : (s0.mem.write64 x.ret tag).write64 (x.ret + 8#64) secs ⊨
      ((x.ret + 16#64) ↦₃₂ lo) ∗ ((x.ret ↦₆₄ tag) ∗ ((x.ret + 8#64) ↦₆₄ secs) ∗
        ((x.ret + 20#64) ↦₃₂ x.b20) ∗ (x.p ↦₆₄ x.s1) ∗ ((x.p + 8#64) ↦₃₂ x.n1) ∗
        stackAt s0.sp 208 ∗ R) := by ac_nf at hw2 ⊢
  have hkf3 := Memory.keepsFrozen_write32
    ((IsBlock.pointsTo32 (x.ret + 16#64) lo).canWrite (by decide) hc2) nanos
  have hw3 := IsBlock.write32 (IsBlock.pointsTo32 (x.ret + 16#64) lo) hc2 nanos
  have hx2_sw : (s0.readReg64 .x2).setWidth 32 = x.n2 := hx2
  have hn1' : x.n1.toNat < 1000000000 := hn1
  have hn2' : x.n2.toNat < 1000000000 := hn2
  have heval : durationSinceExactHook s0 =
      retHook (fun s => s.setMem (((s.mem.write64 x.ret tag).write64 (x.ret + 8#64) secs).write32
        (x.ret + 16#64) nanos)) s0 := by
    unfold durationSinceExactHook
    simp only [hx0, hx1, hx2_sw, hx8, hcanR, hcanW, Bool.true_and, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hrd32, hrd64, hn1', hn2', and_self]
    rfl
  rw [heval]
  refine ⟨hkf1.trans (hkf2.trans hkf3), rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  dsimp only [masterDurationSinceSpec, retHook, State.setMem, State.setPC]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  ac_nf at hw3 ⊢

/-- `keepFsTrace durationSinceExactHook` is pointwise equal to `durationSinceExactHook`. -/
theorem keepFsTrace_durationSinceExactHook_eq (s0 : State) :
    keepFsTrace durationSinceExactHook s0 = durationSinceExactHook s0 := by
  unfold keepFsTrace durationSinceExactHook
  dsimp only
  split
  · cases s0; rfl
  · split <;> (cases s0; rfl)

/-- `keepFsTrace durationSinceExactHook` satisfies `masterDurationSinceSpec` (`W`-free). -/
theorem keepFsTrace_durationSinceExactHook_master_ok :
    HookOk (keepFsTrace durationSinceExactHook) masterDurationSinceSpec := by
  have hfn : keepFsTrace durationSinceExactHook = durationSinceExactHook :=
    funext keepFsTrace_durationSinceExactHook_eq
  rw [hfn]
  exact durationSinceExactHook_master_ok

/-- Ready-to-call `HookOk` for `linkedCallHookG` specialized to `masterDurationSinceSpec`,
    `roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0`, and `durationSinceExactHook`. -/
theorem hookOk_linkedCallHookG_durationSince
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {mpl : MultiPlacement}
    (hpl : timeMultiLib.Placeable mpl)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hw0 : P_sub.hasWords (mpl.base 0) (subTimespecPatchedWords mpl))
    (hw1 : P_sub.hasWords (mpl.base 1) (durationSincePatchedWords mpl)) :
    HookOk (linkedCallHookG (roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0)
      keep P_real P_sub (mpl.base 1) masterDurationSinceSpec durationSinceExactHook)
      masterDurationSinceSpec :=
  hookOk_linkedCallHookG_roTable hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterDurationSince_of_hasWords hpl hsvc_sub hsub_no hw0 hw1)
    (specStripSInvariant_masterDurationSince keep)
    specPreservesFsTrace_masterDurationSince
    masterDurationSince_pre_setPC
    masterDurationSince_outcome_setPC
    keepFsTrace_durationSinceExactHook_master_ok

/-- Concrete `80`-word hull specialization of `hookOk_linkedCallHookG_durationSince` at
    layout-generic entry `hullBase + 240#64`. -/
theorem hookOk_linkedCallHookG_durationSinceHull
    {keep : BitVec 64 → Bool} {P_real : Program} {mpl : MultiPlacement} (hullBase : BitVec 64)
    (hpl : timeMultiLib.Placeable mpl)
    (hb0 : mpl.base 0 = hullBase)
    (hb1 : mpl.base 1 = hullBase + 240#64)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) :
    HookOk (linkedCallHookG (roTableGuard (mpl.ρ timeRodataCst16Sym) timePlacedData0)
      keep P_real (durationSinceHullProg mpl) (hullBase + 240#64)
      masterDurationSinceSpec durationSinceExactHook)
      masterDurationSinceSpec := by
  rw [← hb1]
  refine hookOk_linkedCallHookG_durationSince hpl hsvc_real
    (durationSinceHullProg_svc mpl) hreal_no (durationSinceHullProg_externAt_none mpl)
    (durationSinceHullProg_hasWords_subTimespec mpl) ?_
  rw [hb1, ← hb0]
  exact durationSinceHullProg_hasWords_durationSince mpl

/-! ## 4. Consumer `HookOk` Lifts (Bare, `keepsFs`, `withVmPreserved`, & `.inImage`) -/

/-- Drop `.keepsFs` from any `HookOk f spec.keepsFs`. -/
theorem hookOk_of_keepsFs {α : Type} {f : State → State} {spec : Spec α}
    (hh : HookOk f spec.keepsFs) : HookOk f spec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hh x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Any `HookOk f spec` weakens to `HookOk f (spec.inImage img)`. -/
theorem hookOk_inImage {α : Type} {f : State → State} {spec : Spec α} (img : Image)
    (hh : HookOk f spec) : HookOk f (spec.inImage img) := by
  intro x R s0 hrun hpre hsp
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hh x R s0 hrun hpre.2 hsp

private theorem systemTime_entails_memRegion16_local (p s1 : BitVec 64) (n1 : BitVec 32) :
    ((p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗ memRegion (p + 12#64) 4) ⊢ memRegion p 16 := by
  rw [memRegion_split3_ord p 16 8 4 (by decide) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion p s1)
    (sepConj_mono (pointsTo32_entails_memRegion (p + 8#64) n1) (Entails.refl _))

private theorem sret_entails_memRegion24_local (ret w0 w1 : BitVec 64) (r16 b20 : BitVec 32) :
    ((ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ w1) ∗ ((ret + 16#64) ↦₃₂ r16) ∗ ((ret + 20#64) ↦₃₂ b20)) ⊢
      memRegion ret 24 := by
  rw [memRegion_split3_ord ret 24 8 8 (by decide) (by decide)]
  have h8 : memRegion (ret + 16#64) 8 = memRegion (ret + 16#64) 4 ∗ memRegion (ret + 20#64) 4 :=
    memRegion_split' (b := ret + 16#64) (n := 4) (k := 4) (b' := ret + 20#64) rfl
      (by bv_omega) (by decide)
  rw [h8]
  exact sepConj_mono (pointsTo64_entails_memRegion ret w0)
    (sepConj_mono (pointsTo64_entails_memRegion (ret + 8#64) w1)
      (sepConj_mono (pointsTo32_entails_memRegion (ret + 16#64) r16)
        (pointsTo32_entails_memRegion (ret + 20#64) b20)))

/-- Lift `HookOk f masterDurationSinceSpec` to `(durationSinceBoundedAtSpec stk).keepsFs`
    for any stack budget `stk` with `208 ≤ stk ∧ stk ≤ 2 ^ 64`. -/
theorem hookOk_durationSinceBoundedAt_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) {stk : Nat}
    (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (durationSinceBoundedAtSpec stk).keepsFs := by
  intro ⟨p, ret⟩ R s0 hrun hpre hsp
  dsimp only [Arm64.Spec.keepsFs, durationSinceBoundedAtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hn2⟩, hmem⟩
  simp only [sepExists_sepConj_left, sepConj_assoc, satisfies_sepExists] at hmem
  rcases hmem with ⟨s1, n1, hmem⟩
  have hmem_p : s0.mem ⊨ ⌜n1.toNat < 1000000000⌝ ∗
      ((p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗ memRegion (p + 12#64) 4 ∗
        memRegion ret 24 ∗ stackAt s0.sp stk ∗ R) := by ac_nf at hmem ⊢
  rw [satisfies_pure_sepConj] at hmem_p
  rcases hmem_p with ⟨hn1, hmem_s⟩
  have hret24 : memRegion ret 24 = memRegion ret 20 ∗ ∃∗ b20 : BitVec 32, (ret + 20#64) ↦₃₂ b20 := by
    rw [memRegion_split' (b := ret) (n := 20) (k := 4) (b' := ret + 20#64) rfl rfl (by decide),
      ProofLib.memRegion_four (ret + 20#64)]
  have hstk_sp := stackAt_shrink s0.sp stk 208 hstk.1 hstk.2
  rw [hret24, hstk_sp] at hmem_s
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hmem_s
  rcases hmem_s with ⟨b20, hmem_b⟩
  let g : DurationSinceGhost :=
    ⟨p, s0.readReg64 .x1, (s0.readReg64 .x2).truncate 32, ret, s1, n1, b20⟩
  let F : SepProp :=
    memRegion (p + 12#64) 4 ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 208)
  have hpre_g : s0.mem ⊨ masterDurationSinceSpec.pre g s0 ∗ (F ∗ R) := by
    dsimp only [masterDurationSinceSpec, g, F]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, rfl, rfl, hx8, hn1, hn2⟩, ?_⟩
    ac_nf at hmem_b ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh g (F ∗ R) s0 hrun hpre_g hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [masterDurationSinceSpec, g, F] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hdsp, hq_m⟩
    dsimp only [Arm64.Spec.keepsFs, durationSinceBoundedAtSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hdsp.1, hdsp.2.1, ?_⟩
    rw [hstk_sp]
    let s2 : BitVec 64 := s0.readReg64 .x1
    let n2 : BitVec 32 := (s0.readReg64 .x2).truncate 32
    let tag : BitVec 64 := if timespecNs s2 n2 ≤ timespecNs s1 n1 then 0#64 else 1#64
    let d : Nat := (timespecNs s1 n1 - timespecNs s2 n2).natAbs
    have hgrp : (f s0).mem ⊨
        (((p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗ memRegion (p + 12#64) 4) ∗
          ((ret ↦₆₄ tag) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
            ((ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗ ((ret + 20#64) ↦₃₂ b20))) ∗
        (stackAt s0.sp 208 ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 208) ∗ R) := by
      dsimp only [tag, d, s2, n2]
      ac_nf at hq_m ⊢
    have hm1624 := Satisfies.mono (sepConj_mono_left
      (sepConj_mono (systemTime_entails_memRegion16_local p s1 n1)
        (sret_entails_memRegion24_local ret tag (BitVec.ofNat 64 (d / 10 ^ 9))
          (BitVec.ofNat 32 (d % 10 ^ 9)) b20))) hgrp
    ac_nf at hm1624 ⊢
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem hookOk_durationSinceBoundedAt_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (durationSinceBoundedAtSpec stk) :=
  hookOk_of_keepsFs (hookOk_durationSinceBoundedAt_keepsFs_of_master hh hstk)

/-- Lift `HookOk f masterDurationSinceSpec` to `(durationSinceEpochAtSpec stk).keepsFs`
    for any stack budget `stk` with `208 ≤ stk ∧ stk ≤ 2 ^ 64`. -/
theorem hookOk_durationSinceEpochAt_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) {stk : Nat}
    (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (durationSinceEpochAtSpec stk).keepsFs := by
  intro ⟨p, ret⟩ R s0 hrun hpre hsp
  dsimp only [Arm64.Spec.keepsFs, durationSinceEpochAtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hx1, hx2⟩, hmem⟩
  have hret24 : memRegion ret 24 = memRegion ret 20 ∗ ∃∗ b20 : BitVec 32, (ret + 20#64) ↦₃₂ b20 := by
    rw [memRegion_split' (b := ret) (n := 20) (k := 4) (b' := ret + 20#64) rfl rfl (by decide),
      ProofLib.memRegion_four (ret + 20#64)]
  have hstk_sp := stackAt_shrink s0.sp stk 208 hstk.1 hstk.2
  rw [hret24, hstk_sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hmem
  rcases hmem with ⟨b20, hmem_b⟩
  let g : DurationSinceGhost := ⟨p, 0#64, 0#32, ret, 0#64, 0#32, b20⟩
  let F : SepProp :=
    memRegion (p + 12#64) 4 ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 208)
  have hpre_g : s0.mem ⊨ masterDurationSinceSpec.pre g s0 ∗ (F ∗ R) := by
    dsimp only [masterDurationSinceSpec, g, F]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx8, by decide, by decide⟩, ?_⟩
    ac_nf at hmem_b ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh g (F ∗ R) s0 hrun hpre_g hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [masterDurationSinceSpec, g, F] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hdsp, hq_m⟩
    have hsec0 : BitVec.ofNat 64
        ((timespecNs 0#64 0#32 - timespecNs 0#64 0#32).natAbs / 10 ^ 9) = 0#64 := by decide
    have hnan0 : BitVec.ofNat 32
        ((timespecNs 0#64 0#32 - timespecNs 0#64 0#32).natAbs % 10 ^ 9) = 0#32 := by decide
    have htag0 : (if timespecNs 0#64 0#32 ≤ timespecNs 0#64 0#32 then 0#64 else 1#64) = 0#64 := by
      decide
    rw [hsec0, hnan0, htag0] at hq_m
    dsimp only [Arm64.Spec.keepsFs, durationSinceEpochAtSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hdsp.1, hdsp.2.1, ?_⟩
    rw [hstk_sp]
    have h20 : ret + 16#64 + 4#64 = ret + 20#64 := by bv_omega
    have hpair : (((ret + 16#64) ↦₃₂ 0#32) ∗ ((ret + 20#64) ↦₃₂ b20)) ⊢
        ((ret + 16#64) ↦₆₄ (b20 ++ 0#32)) := by
      rw [← h20, pointsTo32_pair (ret + 16#64) 0#32 b20]; exact Entails.refl _
    have hex_ret : ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗
        (((ret + 16#64) ↦₃₂ 0#32) ∗ ((ret + 20#64) ↦₃₂ b20))) ⊢
        (∃∗ w2 : BitVec 64, ∃∗ w0 : BitVec 64,
          (ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗ ((ret + 16#64) ↦₆₄ w2)) :=
      Entails.trans (sepConj_mono_right (sepConj_mono_right hpair))
        (Entails.sepExists_right (b20 ++ 0#32) (Entails.sepExists_right 0#64 (Entails.refl _)))
    have hgrp : (f s0).mem ⊨
        (((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₃₂ 0#32) ∗ memRegion (p + 12#64) 4) ∗
          ((ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ 0#64) ∗
            (((ret + 16#64) ↦₃₂ 0#32) ∗ ((ret + 20#64) ↦₃₂ b20)))) ∗
        (stackAt s0.sp 208 ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 208) ∗ R) := by
      ac_nf at hq_m ⊢
    have hm_ep := Satisfies.mono (sepConj_mono_left
      (sepConj_mono (systemTime_entails_memRegion16_local p 0#64 0#32) hex_ret)) hgrp
    ac_nf at hm_ep ⊢
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem hookOk_durationSinceEpochAt_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (durationSinceEpochAtSpec stk) :=
  hookOk_of_keepsFs (hookOk_durationSinceEpochAt_keepsFs_of_master hh hstk)

theorem hookOk_durationSinceBounded_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) : HookOk f durationSinceBoundedSpec :=
  hookOk_durationSinceBoundedAt_of_master hh (by decide)

theorem hookOk_durationSinceBounded_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) : HookOk f durationSinceBoundedSpec.keepsFs :=
  hookOk_durationSinceBoundedAt_keepsFs_of_master hh (by decide)

theorem hookOk_durationSinceBoundedAlloc_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) : HookOk f durationSinceBoundedAllocSpec :=
  hookOk_durationSinceBoundedAt_of_master hh (by decide)

theorem hookOk_durationSinceBoundedBudgetAt_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s))
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (durationSinceBoundedBudgetAtSpec stk) :=
  hookOk_withVmPreserved (hookOk_durationSinceBoundedAt_of_master hh hstk) hvm

theorem hookOk_durationSinceBoundedBudget_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f durationSinceBoundedBudgetSpec :=
  hookOk_durationSinceBoundedBudgetAt_of_master hh hvm (by decide)

theorem hookOk_durationSinceBoundedBudget_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f durationSinceBoundedBudgetSpec.keepsFs := by
  change HookOk f (withVmPreserved durationSinceBoundedSpec).keepsFs
  have heq : (withVmPreserved durationSinceBoundedSpec).keepsFs =
      withVmPreserved durationSinceBoundedSpec.keepsFs := by
    unfold Arm64.Spec.keepsFs withVmPreserved; congr 1; funext x s0 sf; simp [sepConj_left_comm]
  rw [heq]
  exact hookOk_withVmPreserved (hookOk_durationSinceBounded_keepsFs_of_master hh) hvm

theorem hookOk_durationSinceBoundedAllocBudget_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f durationSinceBoundedAllocBudgetSpec :=
  hookOk_durationSinceBoundedBudgetAt_of_master hh hvm (by decide)

theorem hookOk_durationSinceBounded_inImage_of_master {f : State → State}
    (img : Image) (hh : HookOk f masterDurationSinceSpec) :
    HookOk f (durationSinceBoundedSpec.inImage img) :=
  hookOk_inImage img (hookOk_durationSinceBounded_of_master hh)

theorem hookOk_durationSinceBoundedBudget_inImage_of_master {f : State → State}
    (img : Image) (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (durationSinceBoundedBudgetSpec.inImage img) :=
  hookOk_inImage img (hookOk_durationSinceBoundedBudget_of_master hh hvm)

theorem hookOk_durationSinceEpoch_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) : HookOk f durationSinceEpochSpec :=
  hookOk_durationSinceEpochAt_of_master hh (by decide)

theorem hookOk_durationSinceEpoch_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) : HookOk f durationSinceEpochSpec.keepsFs :=
  hookOk_durationSinceEpochAt_keepsFs_of_master hh (by decide)

theorem hookOk_durationSinceEpochAlloc_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) : HookOk f durationSinceEpochAllocSpec :=
  hookOk_durationSinceEpochAt_of_master hh (by decide)

theorem hookOk_durationSinceEpochBudgetAt_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s))
    {stk : Nat} (hstk : 208 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withVmPreserved (durationSinceEpochAtSpec stk)) :=
  hookOk_withVmPreserved (hookOk_durationSinceEpochAt_of_master hh hstk) hvm

theorem hookOk_durationSinceEpochBudget_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f durationSinceEpochBudgetSpec :=
  hookOk_durationSinceEpochBudgetAt_of_master hh hvm (by decide)

theorem hookOk_durationSinceEpochBudget_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f durationSinceEpochBudgetSpec.keepsFs := by
  change HookOk f (withVmPreserved durationSinceEpochSpec).keepsFs
  have heq : (withVmPreserved durationSinceEpochSpec).keepsFs =
      withVmPreserved durationSinceEpochSpec.keepsFs := by
    unfold Arm64.Spec.keepsFs withVmPreserved; congr 1; funext x s0 sf; simp [sepConj_left_comm]
  rw [heq]
  exact hookOk_withVmPreserved (hookOk_durationSinceEpoch_keepsFs_of_master hh) hvm

theorem hookOk_durationSinceEpochAllocBudget_of_master {f : State → State}
    (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f durationSinceEpochAllocBudgetSpec :=
  hookOk_durationSinceEpochBudgetAt_of_master hh hvm (by decide)

theorem hookOk_durationSinceEpoch_inImage_of_master {f : State → State}
    (img : Image) (hh : HookOk f masterDurationSinceSpec) :
    HookOk f (durationSinceEpochSpec.inImage img) :=
  hookOk_inImage img (hookOk_durationSinceEpoch_of_master hh)

theorem hookOk_durationSinceEpochBudget_inImage_of_master {f : State → State}
    (img : Image) (hh : HookOk f masterDurationSinceSpec) (hvm : ∀ s, VmPreserved s (f s)) :
    HookOk f (durationSinceEpochBudgetSpec.inImage img) :=
  hookOk_inImage img (hookOk_durationSinceEpochBudget_of_master hh hvm)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceCode
