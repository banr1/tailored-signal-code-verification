/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine

/-!
# Ghost `strlen` Hook & Consumer `HookOk` Suite (`HooksDehook.StrlenGhost`)

Card `L2-b` (`DEHOOK-PLAN` §1 row `b`, §2 `L2 strlen`) for de-hooking `strlen`
(`muslStrlenWords`, 22 words = 88 bytes in stock `:text_a`) using `linkedCallHook`
(`AllocGhostLinkTransfer.lean`) over `HooksDehook.StrlenCode`:

1. **Ghost `strlen` hooks (`strlenGhostHook`, `strlenGhostHookK`, `strlenGhostHookPure{,K}`)**:
   - `strlenGhostHook keep P_real P_sub entryTarget`: wraps `masterStrlenSpec` with `W`-free
     fallback `strlenHook`.
   - `strlenGhostHookK keep P_real P_sub entryTarget`: wraps `strlenSpecK keep masterStrlenSpec`
     (`⌜keep (s.readReg64 .lr) = false⌝ ∗ masterStrlenSpec.pre`) with fallback `strlenHook`.
   - `strlenGhostHookPure{,K} keep P_real entryTarget`: specializes `P_sub` to the single-hull
     `pureWordsProg entryTarget muslStrlenWords` (`GK6c`: stock block identity lives in `StrlenBlock`
     once C2 lands).
2. **`SpecStripSInvariant`, `SpecPreservesFsTrace`, & pointwise state preservation (`C11` §8.1/8.2)**:
   Proves `SpecStripSInvariant`, `SpecPreservesFsTrace`, `.fs = s.fs`, `HookFsTraced IsFsC`,
   `VmPreserved`, `OomPreserved ∧ PoolPreserved`, `.trace = s.trace`, `ExecFrozen` preservation,
   `strlenGhostHookK_keepLr_false_of_noException`, and `strlenGhostHook{,K}_of_keepLr_true` by
   combining `StrlenCode.processStrlenSpec`'s `ProcessFieldsPreserved` with `KeepsFrozen` +
   `ExecFrozen` across `stripS keep`.
3. **Complete `HookOk` suite for all 11 SWAR-padded `strlen` consumer contracts**:
   Covers `cliStrlenPaddedSpec`, `strlenPaddedSpecRO`, and the `withStrlenPadRO`,
   `withStrlenRoDataPad`, and `withStrlenAlignedEnd` wrappers of `M24.CalleesRO.strlenSpecRO`,
   `MainHops.strlenSpec`, and `CliExt.strlenSpec` across plain, `.keepsFs`, `withVmPreserved`
   (budget), `withVmPreserved` + `.keepsFs`, `strlenSpecK`, `.inImage`, `withExecFrozen`, and
   `withOomPoolPreserved` forms. (The K-convention `f3LinkedCallHook` `emptyStdProg` twin and
   stock-safe `h2fsgen_StepsVisitedIn` replay bridges live in `HooksDehook.StrlenGhostK`.)
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open ProofLib.StdStartup (StdStatePreserved muslStrlenWords)
open CryptoVerification.SignalSession (strlenHook unmodelled)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.Cli.MainHops (strlenSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (strlenSpecRO)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
  FdsHiFrame VmPreserved OomPreserved PoolPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (strlenHook_vmPreserved)
open LibsignalBinary.Heap.IfaceSimp (withOomPoolPreserved hookOk_withOomPoolPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (
  withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Strlen (
  StrlenSwarPadBound cliStrlenPaddedSpec strlenPaddedSpecRO
  withStrlenPadRO withStrlenRoDataPad withStrlenAlignedEnd
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen
  satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace
  ActiveRealPre ActiveRealRun
  linkedCallHook linkedCallHook_fs linkedCallHook_fsT linkedCallHook_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  pureWordsProg_externAt_none
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  memcpySpecK
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (
  withExecFrozen hookOk_withExecFrozen_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenCode (
  StrlenStatePreserved strlenSrc masterStrlenSpec processStrlenSpec masterStrlenROSpec
  processStrlenSpec_pre_eq strlenSpecK
  muslStrlenWords_length pureWordsProg_strlen_hasWords
  vmPreserved_of_processFieldsPreserved
  subroutine_ok_processStrlen_of_hasWords subroutine_ok_masterStrlen_of_hasWords
  subroutine_ok_masterStrlenK_of_hasWords
  hookStrlen_masterStrlen_ok hookStrlen_masterStrlenK_ok
  hookOk_masterStrlenRO_of_master hookOk_masterStrlenROK_of_master
  hookOk_strlenSpecK_of_plain hookOk_inImage hookOk_strlenSpecK_inImage
  hookOk_cliStrlenPadded_of_master hookOk_cliStrlenPaddedK_of_master
  hookOk_strlenPaddedRO_of_master hookOk_strlenPaddedROK_of_master
  hookOk_strlenSpecRO_padRO_of_master hookOk_strlenSpecRO_padROK_of_master
  hookOk_strlenSpecRO_roDataPad_of_master hookOk_strlenSpecRO_roDataPadK_of_master
  hookOk_strlenSpecRO_alignedEnd_of_master hookOk_strlenSpecRO_alignedEndK_of_master
  hookOk_mainStrlen_padRO_of_master hookOk_mainStrlen_padROK_of_master
  hookOk_mainStrlen_roDataPad_of_master hookOk_mainStrlen_roDataPadK_of_master
  hookOk_mainStrlen_alignedEnd_of_master hookOk_mainStrlen_alignedEndK_of_master
  hookOk_cliExtStrlen_padRO_of_master hookOk_cliExtStrlen_padROK_of_master
  hookOk_cliExtStrlen_roDataPad_of_master hookOk_cliExtStrlen_roDataPadK_of_master
  hookOk_cliExtStrlen_alignedEnd_of_master hookOk_cliExtStrlen_alignedEndK_of_master
  strlenSpecK_keepsFs strlenSpecK_withVmPreserved strlenSpecK_withOomPoolPreserved
)

/-! ## 1. Ghost `strlen` Hook Definitions & `keep` Coverage -/

/-- Plain ghost `strlen` hook wrapping `masterStrlenSpec` via `linkedCallHook` with `W`-free
    fallback `strlenHook`. Parametric in `keep`, `P_real`, `P_sub`, and `entryTarget`. -/
@[expose] noncomputable def strlenGhostHook
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    State → State :=
  linkedCallHook keep P_real P_sub entryTarget masterStrlenSpec strlenHook

/-- `K`-narrowed ghost `strlen` hook wrapping `strlenSpecK keep masterStrlenSpec` via
    `linkedCallHook` with fallback `strlenHook`. Outside `keep (s.readReg64 .lr) = false` (or when
    `masterStrlenSpec.pre` fails), transitions to `.Exception` so any non-`.Exception` ghost run
    automatically witnesses `keep (u.readReg64 .lr) = false`. -/
@[expose] noncomputable def strlenGhostHookK
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    State → State :=
  linkedCallHook keep P_real P_sub entryTarget (strlenSpecK keep masterStrlenSpec) strlenHook

/-- Specialization of `strlenGhostHook` to `P_sub := pureWordsProg entryTarget muslStrlenWords`. -/
noncomputable abbrev strlenGhostHookPure
    (keep : BitVec 64 → Bool) (P_real : Program) (entryTarget : BitVec 64) : State → State :=
  strlenGhostHook keep P_real (pureWordsProg entryTarget muslStrlenWords) entryTarget

/-- Specialization of `strlenGhostHookK` to `P_sub := pureWordsProg entryTarget muslStrlenWords`. -/
noncomputable abbrev strlenGhostHookPureK
    (keep : BitVec 64 → Bool) (P_real : Program) (entryTarget : BitVec 64) : State → State :=
  strlenGhostHookK keep P_real (pureWordsProg entryTarget muslStrlenWords) entryTarget

/-- Byte length (`88 = 4 * 22`) of the `muslStrlenWords` pure-instruction hull. -/
@[expose] def strlenByteLen : Nat := 4 * muslStrlenWords.length

theorem strlenByteLen_eq : strlenByteLen = 88 := by
  unfold strlenByteLen
  rw [muslStrlenWords_length]

/-- Minimal placement-generic `keep` predicate retaining only the `strlenByteLen`-byte (`22`-word)
    `strlen` instruction block starting at `entryTarget`. -/
@[expose] def keepStrlenRange (entryTarget a : BitVec 64) : Bool :=
  decide ((a - entryTarget).toNat < strlenByteLen)

/-- Coverage condition stating that `keep` retains all `strlenByteLen` bytes of `muslStrlenWords`
    starting at `entryTarget` (satisfied by `keepStrlenRange entryTarget` and `hole2_keepSub` on
    stock `:text_a`). -/
@[expose] def KeepCoversStrlen (keep : BitVec 64 → Bool) (entryTarget : BitVec 64) : Prop :=
  ∀ off : Nat, off < strlenByteLen → keep (entryTarget + BitVec.ofNat 64 off) = true

theorem keepCoversStrlen_keepStrlenRange (entryTarget : BitVec 64) :
    KeepCoversStrlen (keepStrlenRange entryTarget) entryTarget := by
  intro off hoff
  unfold keepStrlenRange
  have hsub : entryTarget + BitVec.ofNat 64 off - entryTarget = BitVec.ofNat 64 off := by
    bv_omega
  rw [strlenByteLen_eq] at hoff ⊢
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact decide_eq_true hoff

theorem keepCoversStrlen_of_inRegion
    {keep : BitVec 64 → Bool} {entryTarget : BitVec 64}
    (hin : ∀ a : BitVec 64, InRegion entryTarget strlenByteLen a → keep a = true) :
    KeepCoversStrlen keep entryTarget := by
  intro off hoff
  apply hin
  unfold InRegion
  have hsub : entryTarget + BitVec.ofNat 64 off - entryTarget = BitVec.ofNat 64 off := by
    bv_omega
  rw [strlenByteLen_eq] at hoff ⊢
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hoff

theorem keepCoversStrlen_of_range
    {keep : BitVec 64 → Bool} {entryTarget : BitVec 64} (lo hi : Nat)
    (hrange : ∀ a : BitVec 64, lo ≤ a.toNat → a.toNat < hi → keep a = true)
    (hlo : lo ≤ entryTarget.toNat)
    (hhi : entryTarget.toNat + strlenByteLen ≤ hi)
    (hnowrap : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64) :
    KeepCoversStrlen keep entryTarget := by
  intro off hoff
  rw [strlenByteLen_eq] at hoff hhi hnowrap
  have hadd : (entryTarget + BitVec.ofNat 64 off).toNat = entryTarget.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : off < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : entryTarget.toNat + off < 2 ^ 64)]
  exact hrange _ (by omega) (by omega)

/-! ## 2. `SpecStripSInvariant`, `SpecPreservesFsTrace`, & PC Invariance -/

theorem specStripSInvariant_masterStrlen (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterStrlenSpec where
  pre_eq := fun ⟨_, _, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specStripSInvariant_masterStrlenK (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (strlenSpecK keep masterStrlenSpec) where
  pre_eq := fun ⟨_, _, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specPreservesFsTrace_masterStrlen :
    SpecPreservesFsTrace masterStrlenSpec := by
  intro ⟨strRo, padRo, p, s, pad⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterStrlenSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.2.1, FsTraced.of_eq hpost.1.2.2.1 (congrArg FsState.files hpost.1.2.1)⟩
  · dsimp only [masterStrlenSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · dsimp only [masterStrlenSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
  · dsimp only [masterStrlenSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim

theorem specPreservesFsTrace_masterStrlenK (keep : BitVec 64 → Bool) :
    SpecPreservesFsTrace (strlenSpecK keep masterStrlenSpec) :=
  specPreservesFsTrace_masterStrlen

theorem masterStrlen_pre_setPC
    (x : Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s : State)
    (pc : BitVec 64) :
    masterStrlenSpec.pre x (s.setPC pc) = masterStrlenSpec.pre x s := by
  rcases x with ⟨_, _, _, _, _⟩; cases s; rfl
theorem masterStrlenK_pre_setPC (keep : BitVec 64 → Bool)
    (x : Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (s : State)
    (pc : BitVec 64) :
    (strlenSpecK keep masterStrlenSpec).pre x (s.setPC pc) =
      (strlenSpecK keep masterStrlenSpec).pre x s := by
  rcases x with ⟨_, _, _, _, _⟩; cases s; rfl

theorem masterStrlen_outcome_setPC
    (x : Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterStrlenSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterStrlenSpec x R s0 sf := by
  rcases x with ⟨_, _, _, _, _⟩; cases s0; cases sf; exact h
theorem masterStrlenK_outcome_setPC (keep : BitVec 64 → Bool)
    (x : Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8)) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (strlenSpecK keep masterStrlenSpec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (strlenSpecK keep masterStrlenSpec) x R s0 sf := by
  rcases x with ⟨_, _, _, _, _⟩; cases s0; cases sf; exact h

theorem keepFsTrace_strlenHook_eq (s0 : State) :
    keepFsTrace strlenHook s0 = strlenHook s0 := by
  unfold strlenHook retHook unmodelled keepFsTrace; dsimp only; split <;> (cases s0; rfl)
theorem keepFsTrace_strlenHook_master_ok :
    HookOk (keepFsTrace strlenHook) masterStrlenSpec := by
  rw [show keepFsTrace strlenHook = strlenHook from funext keepFsTrace_strlenHook_eq]
  exact hookStrlen_masterStrlen_ok
theorem keepFsTrace_strlenHook_masterK_ok (keep : BitVec 64 → Bool) :
    HookOk (keepFsTrace strlenHook) (strlenSpecK keep masterStrlenSpec) := by
  rw [show keepFsTrace strlenHook = strlenHook from funext keepFsTrace_strlenHook_eq]
  exact hookStrlen_masterStrlenK_ok keep

/-! ## 3. Master `HookOk` & Pointwise State Preservation (`VmPreserved`, `OomPreserved`, `fs`) -/

/-- `HookOk` of `strlenGhostHook` for `masterStrlenSpec` on any hook-free `P_sub` holding
    `muslStrlenWords` at `entryTarget`. -/
theorem strlenGhostHook_master_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) masterStrlenSpec :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterStrlen_of_hasWords hsub_no hwords (by simpa [strlenByteLen_eq] using haddr))
    (specStripSInvariant_masterStrlen keep)
    specPreservesFsTrace_masterStrlen
    masterStrlen_pre_setPC
    masterStrlen_outcome_setPC
    keepFsTrace_strlenHook_master_ok

/-- `HookOk` of `strlenGhostHookK` for `strlenSpecK keep masterStrlenSpec` on any hook-free `P_sub`
    holding `muslStrlenWords` at `entryTarget`. -/
theorem strlenGhostHookK_masterK_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep masterStrlenSpec) :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterStrlenK_of_hasWords keep hsub_no hwords
      (by simpa [strlenByteLen_eq] using haddr))
    (specStripSInvariant_masterStrlenK keep)
    (specPreservesFsTrace_masterStrlenK keep)
    (masterStrlenK_pre_setPC keep)
    (masterStrlenK_outcome_setPC keep)
    (keepFsTrace_strlenHook_masterK_ok keep)

/-- `HookOk` of `strlenGhostHook` for `masterStrlenROSpec`. -/
theorem strlenGhostHook_masterRO_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) masterStrlenROSpec :=
  hookOk_masterStrlenRO_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

/-- `HookOk` of `strlenGhostHookK` for `strlenSpecK keep masterStrlenROSpec`. -/
theorem strlenGhostHookK_masterROK_ok
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep masterStrlenROSpec) :=
  hookOk_masterStrlenROK_of_master keep
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHook_fs
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (strlenGhostHook keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget masterStrlenSpec strlenHook s0

theorem strlenGhostHookK_fs
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (strlenGhostHookK keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget (strlenSpecK keep masterStrlenSpec) strlenHook s0

theorem strlenGhostHook_fsT
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (strlenGhostHook keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget masterStrlenSpec strlenHook

theorem strlenGhostHookK_fsT
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (strlenGhostHookK keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget (strlenSpecK keep masterStrlenSpec) strlenHook

private theorem perm_eq_of_stripExecOutside_keepsFrozen
    {keep : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keep mf).perm a = (stripExecOutside keep m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  have hst := hstrip a; rw [strip_perm, strip_perm] at hst
  have hfr0_a := hfr0 a; have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a with
    | none =>
      cases hpf : mf.perm a with
      | none => rfl
      | some pf => rw [hp0, hpf] at hst; simp [Option.map] at hst
    | some p0 =>
      cases hpf : mf.perm a with
      | none => rw [hp0, hpf] at hst; simp [Option.map] at hst
      | some pf =>
        rw [hp0] at hfr0_a hfrozen0 hst; rw [hpf] at hfrf_a hst
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩; rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hst
        cases hk : keep a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;> simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem subroutineStop_of_processStrlenOutcome
    {x : Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8)}
    {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome processStrlenSpec x R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · exact ⟨Or.inl hret, by rw [hret.2.2]; decide⟩
  · dsimp only [processStrlenSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · dsimp only [processStrlenSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
  · dsimp only [processStrlenSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim

/-- Shared real-run `ProcessFieldsPreserved` (`= StdStatePreserved`, including pointwise `mem.perm`)
    extractor when `s0` satisfies `masterStrlenSpec.pre` and
    `ActiveRealRun keep P_real P_sub entryTarget s0`. -/
private theorem activeRealRun_processFieldsPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    {x : Bool × Bool × BitVec 64 × List (BitVec 8) × List (BitVec 8)}
    {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpreM : s0.mem ⊨ masterStrlenSpec.pre x s0 ∗ R)
    (hReal : ActiveRealRun keep P_real P_sub entryTarget s0) :
    ProcessFieldsPreserved s0 (Classical.choose hReal.2.2.2) := by
  have hpre : s0.mem ⊨ processStrlenSpec.pre x s0 ∗ R := hpreM
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ processStrlenSpec.pre x s1 ∗ R := by
    rcases x with ⟨_, _, _, _, _⟩; cases s0; exact hpre
  have hs1'_pre : s1'.mem ⊨ processStrlenSpec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    have heq : processStrlenSpec.pre x s1' = processStrlenSpec.pre x s1 := by
      dsimp only [s1']
      rcases x with ⟨_, _, _, _, _⟩; cases s1; rfl
    rwa [heq]
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome
      (subroutine_ok_processStrlen_of_hasWords (entry := entryTarget) hsub_no hwords
        (by simpa [strlenByteLen_eq] using haddr))
      x R s1' (by cases s0; rfl) hrun hs1'_pre hsp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_processStrlenOutcome hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he)
      hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : Classical.choose hReal.2.2.2 = sf :=
    StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hdet]
  rcases hout' with ⟨_, _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [processStrlenSpec] at hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hstd' : ProcessFieldsPreserved s1' sf' := hpost'.1.2
    rw [hsf_eq] at hstd'
    have hperm : ∀ a, sf.mem.perm a = s0.mem.perm a :=
      perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen
        hstd'.2.2.2.2.2.2.2
    refine ⟨by cases s0; cases sf; exact hstd'.1,
            by cases s0; cases sf; exact hstd'.2.1,
            by cases s0; cases sf; exact hstd'.2.2.1,
            by cases s0; cases sf; exact hstd'.2.2.2.1,
            by cases s0; cases sf; exact hstd'.2.2.2.2.1,
            by cases s0; cases sf; exact hstd'.2.2.2.2.2.1,
            by cases s0; cases sf; exact hstd'.2.2.2.2.2.2.1,
            hperm⟩
  · dsimp only [processStrlenSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · dsimp only [processStrlenSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
  · dsimp only [processStrlenSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim

private theorem oomPoolPreserved_of_processFieldsPreserved {s0 sf : State}
    (h : ProcessFieldsPreserved s0 sf) : OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

private theorem strlenHook_preserves_oom_pool (s0 : State) :
    OomPreserved s0 (strlenHook s0) ∧ PoolPreserved s0 (strlenHook s0) := by
  unfold strlenHook retHook unmodelled; dsimp only; split <;> exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
private theorem strlenHook_trace_eq (s0 : State) : (strlenHook s0).trace = s0.trace := by
  unfold strlenHook retHook unmodelled; dsimp only; split <;> rfl
private theorem strlenHook_mem_eq (s0 : State) : (strlenHook s0).mem = s0.mem := by
  unfold strlenHook retHook unmodelled; dsimp only; split <;> rfl

/-- Pointwise `VmPreserved` for `strlenGhostHook` across all three branches (`ActiveRealRun`,
    fallback `strlenHook`, and `.Exception`). -/
theorem strlenGhostHook_vmPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (s0 : State) :
    VmPreserved s0 (strlenGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold strlenGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact vmPreserved_of_processFieldsPreserved
        (activeRealRun_processFieldsPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
          hrun hsp hpre hReal)
    · rw [keepFsTrace_strlenHook_eq]
      exact strlenHook_vmPreserved s0
  · exact VmPreserved.refl s0

/-- Pointwise `VmPreserved` for `strlenGhostHookK` across all three branches. -/
theorem strlenGhostHookK_vmPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (s0 : State) :
    VmPreserved s0 (strlenGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold strlenGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [strlenSpecK, memcpySpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact vmPreserved_of_processFieldsPreserved
        (activeRealRun_processFieldsPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
          hrun hsp hpre.2 hReal)
    · rw [keepFsTrace_strlenHook_eq]
      exact strlenHook_vmPreserved s0
  · exact VmPreserved.refl s0

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `strlenGhostHook`. -/
theorem strlenGhostHook_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (s0 : State) :
    OomPreserved s0 (strlenGhostHook keep P_real P_sub entryTarget s0) ∧
      PoolPreserved s0 (strlenGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold strlenGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact oomPoolPreserved_of_processFieldsPreserved
        (activeRealRun_processFieldsPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
          hrun hsp hpre hReal)
    · rw [keepFsTrace_strlenHook_eq]
      exact strlenHook_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `OomPreserved ∧ PoolPreserved` for `strlenGhostHookK`. -/
theorem strlenGhostHookK_oomPoolPreserved
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (s0 : State) :
    OomPreserved s0 (strlenGhostHookK keep P_real P_sub entryTarget s0) ∧
      PoolPreserved s0 (strlenGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold strlenGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [strlenSpecK, memcpySpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact oomPoolPreserved_of_processFieldsPreserved
        (activeRealRun_processFieldsPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
          hrun hsp hpre.2 hReal)
    · rw [keepFsTrace_strlenHook_eq]
      exact strlenHook_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- Pointwise `trace` preservation for `strlenGhostHook`. -/
theorem strlenGhostHook_trace
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (s0 : State) :
    (strlenGhostHook keep P_real P_sub entryTarget s0).trace = s0.trace := by
  classical
  unfold strlenGhostHook linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      exact (activeRealRun_processFieldsPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
        hrun hsp hpre hReal).2.1
    · rw [keepFsTrace_strlenHook_eq]
      exact strlenHook_trace_eq s0
  · rfl

/-- Pointwise `trace` preservation for `strlenGhostHookK`. -/
theorem strlenGhostHookK_trace
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget muslStrlenWords)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)
    (s0 : State) :
    (strlenGhostHookK keep P_real P_sub entryTarget s0).trace = s0.trace := by
  classical
  unfold strlenGhostHookK linkedCallHook
  split
  · rename_i hActPre
    split
    · rename_i hReal
      rcases hActPre with ⟨hrun, hsp, x, R, hpre⟩
      dsimp only [strlenSpecK, memcpySpecK] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact (activeRealRun_processFieldsPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
        hrun hsp hpre.2 hReal).2.1
    · rw [keepFsTrace_strlenHook_eq]
      exact strlenHook_trace_eq s0
  · rfl

/-- Pointwise `ExecFrozen` + `.fs` preservation for `strlenGhostHook` (discharging
    `GhostRowReplayOn.preserves_execFrozen` with zero `P_real`/`P_sub` hypotheses). -/
theorem strlenGhostHook_preserves_execFrozen
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hFr : ExecFrozen u.mem) :
    ExecFrozen (strlenGhostHook keep P_real P_sub entryTarget u).mem ∧
      (strlenGhostHook keep P_real P_sub entryTarget u).fs = u.fs := by
  refine ⟨?_, strlenGhostHook_fs keep P_real P_sub entryTarget u⟩
  classical
  unfold strlenGhostHook linkedCallHook
  split
  · split
    · rename_i _ hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · rw [keepFsTrace_strlenHook_eq, strlenHook_mem_eq]
      exact hFr
  · exact hFr

/-- Pointwise `ExecFrozen` + `.fs` preservation for `strlenGhostHookK`. -/
theorem strlenGhostHookK_preserves_execFrozen
    (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64)
    {u : State} (hFr : ExecFrozen u.mem) :
    ExecFrozen (strlenGhostHookK keep P_real P_sub entryTarget u).mem ∧
      (strlenGhostHookK keep P_real P_sub entryTarget u).fs = u.fs := by
  refine ⟨?_, strlenGhostHookK_fs keep P_real P_sub entryTarget u⟩
  classical
  unfold strlenGhostHookK linkedCallHook
  split
  · split
    · rename_i _ hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · rw [keepFsTrace_strlenHook_eq, strlenHook_mem_eq]
      exact hFr
  · exact hFr

/-- Along any non-`.Exception` call step of `strlenGhostHookK`, `keep (u.readReg64 .lr) = false`
    holds automatically (the `K`-route `lr ∉ keep` extractor). -/
theorem strlenGhostHookK_keepLr_false_of_noException
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
    {u : State}
    (hnoex : ∀ msg,
      (strlenGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  classical
  have hActPre : ActiveRealPre (strlenSpecK keep masterStrlenSpec) u := by
    by_contra hnAct
    have hex : (strlenGhostHookK keep P_real P_sub entryTarget u).status =
        .Exception "ghost-hook precondition violated" := by
      unfold strlenGhostHookK linkedCallHook
      simp [hnAct]
    exact hnoex _ hex
  rcases hActPre with ⟨_, _, x, R, hpre⟩
  dsimp only [strlenSpecK, memcpySpecK] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1

/-- Behavior of **plain** `strlenGhostHook` when `keep (s0.readReg64 .lr) = true` and
    `ActiveRealPre masterStrlenSpec s0` holds: `ActiveRealRun` is false, so `linkedCallHook`
    delegates to `keepFsTrace strlenHook s0 = strlenHook s0` (the fallback, not `.Exception`). -/
theorem strlenGhostHook_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hActPre : ActiveRealPre masterStrlenSpec s0)
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    strlenGhostHook keep P_real P_sub entryTarget s0 = strlenHook s0 := by
  classical
  have hnReal : ¬ ActiveRealRun keep P_real P_sub entryTarget s0 := by
    intro hReal
    have hfalse : keep (s0.readReg64 .lr) = false := hReal.2.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold strlenGhostHook linkedCallHook
  simp only [hActPre, hnReal, ↓reduceDIte]
  exact keepFsTrace_strlenHook_eq s0

/-- Behavior of **`K`-narrowed** `strlenGhostHookK` when `keep (s0.readReg64 .lr) = true`:
    `ActiveRealPre (strlenSpecK keep masterStrlenSpec) s0` is false, so `linkedCallHook` returns
    `{ s0 with status := .Exception "ghost-hook precondition violated" }`. -/
theorem strlenGhostHookK_of_keepLr_true
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {s0 : State}
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    strlenGhostHookK keep P_real P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (strlenSpecK keep masterStrlenSpec) s0 := by
    rintro ⟨_, _, x, R, hpre⟩
    dsimp only [strlenSpecK, memcpySpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hfalse : keep (s0.readReg64 .lr) = false := hpre.1
    rw [hlr_in] at hfalse
    exact Bool.noConfusion hfalse
  unfold strlenGhostHookK linkedCallHook
  simp only [hnAct, ↓reduceDIte]

/-! ## 4. Complete `HookOk` Suite for All 11 SWAR-Padded `strlen` Consumer Contracts -/

section GenericHookOkSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
variable (hsvc_real : P_real.svc = Syscall.standard)
variable (hsvc_sub : P_sub.svc = Syscall.standard)
variable (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
variable (hsub_no : ∀ pc, P_sub.externAt? pc = none)
variable (hwords : P_sub.hasWords entryTarget muslStrlenWords)
variable (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64)

include hsvc_real hsvc_sub hreal_no hsub_no hwords haddr

-- 4.0 Master `withVmPreserved` & generic wrapper combinators:

theorem strlenGhostHook_masterVm_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withVmPreserved masterStrlenSpec) :=
  hookOk_withVmPreserved
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
    (strlenGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHookK_masterVmK_ok :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withVmPreserved masterStrlenSpec)) := by
  rw [← strlenSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (strlenGhostHookK_masterK_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
    (strlenGhostHookK_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHook_any_keepsFs_ok {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) spec.keepsFs :=
  hh.keepsFs (strlenGhostHook_fs keep P_real P_sub entryTarget)

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHookK_any_keepsFs_ok {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHookK keep P_real P_sub entryTarget) (strlenSpecK keep spec)) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget) (strlenSpecK keep spec.keepsFs) := by
  rw [← strlenSpecK_keepsFs]
  exact hh.keepsFs (strlenGhostHookK_fs keep P_real P_sub entryTarget)

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHook_any_inImage_ok (img : Obj.Image) {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (spec.inImage img) :=
  hookOk_inImage img hh

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHookK_any_inImage_ok (img : Obj.Image) {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHookK keep P_real P_sub entryTarget) (strlenSpecK keep spec)) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (spec.inImage img)) :=
  hookOk_strlenSpecK_inImage keep img hh

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHook_any_withExecFrozen_ok {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHookK_any_withExecFrozen_ok {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHookK keep P_real P_sub entryTarget) spec) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget) (withExecFrozen spec) :=
  hookOk_withExecFrozen_of_plain hh

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHook_any_strlenSpecK_ok {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (strlenSpecK keep spec) :=
  hookOk_strlenSpecK_of_plain keep hh

theorem strlenGhostHook_any_withOomPoolPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withOomPoolPreserved spec) :=
  hookOk_withOomPoolPreserved hh
    (strlenGhostHook_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHookK_any_withOomPoolPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHookK keep P_real P_sub entryTarget) (strlenSpecK keep spec)) :
    HookOk (strlenGhostHookK keep P_real P_sub entryTarget)
      (strlenSpecK keep (withOomPoolPreserved spec)) := by
  rw [← strlenSpecK_withOomPoolPreserved]
  exact hookOk_withOomPoolPreserved hh
    (strlenGhostHookK_oomPoolPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

-- 4.1 Plain contracts (`_ok` and `_keepsFs_ok`) on `strlenGhostHook`:

theorem strlenGhostHook_cliStrlenPadded_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (cliStrlenPaddedSpec stk) :=
  hookOk_cliStrlenPadded_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHook_cliStrlenPadded_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (cliStrlenPaddedSpec stk).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_cliStrlenPadded_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_strlenPaddedRO_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (strlenPaddedSpecRO stk) :=
  hookOk_strlenPaddedRO_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHook_strlenPaddedRO_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (strlenPaddedSpecRO stk).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_strlenPaddedRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_strlenSpecRO_padRO_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withStrlenPadRO (strlenSpecRO stk)) :=
  hookOk_strlenSpecRO_padRO_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHook_strlenSpecRO_padRO_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenPadRO (strlenSpecRO stk)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_strlenSpecRO_padRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_strlenSpecRO_roDataPad_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenRoDataPad (strlenSpecRO stk)) :=
  hookOk_strlenSpecRO_roDataPad_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHook_strlenSpecRO_roDataPad_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenRoDataPad (strlenSpecRO stk)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_strlenSpecRO_roDataPad_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_strlenSpecRO_alignedEnd_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenAlignedEnd (strlenSpecRO stk)) :=
  hookOk_strlenSpecRO_alignedEnd_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHook_strlenSpecRO_alignedEnd_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenAlignedEnd (strlenSpecRO stk)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_strlenSpecRO_alignedEnd_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_mainStrlen_padRO_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withStrlenPadRO (strlenSpec stk)) :=
  hookOk_mainStrlen_padRO_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHook_mainStrlen_padRO_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenPadRO (strlenSpec stk)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_mainStrlen_padRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_mainStrlen_roDataPad_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withStrlenRoDataPad (strlenSpec stk)) :=
  hookOk_mainStrlen_roDataPad_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHook_mainStrlen_roDataPad_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenRoDataPad (strlenSpec stk)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_mainStrlen_roDataPad_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_mainStrlen_alignedEnd_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenAlignedEnd (strlenSpec stk)) :=
  hookOk_mainStrlen_alignedEnd_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr) stk
theorem strlenGhostHook_mainStrlen_alignedEnd_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenAlignedEnd (strlenSpec stk)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_mainStrlen_alignedEnd_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_cliExtStrlen_padRO_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec) :=
  hookOk_cliExtStrlen_padRO_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHook_cliExtStrlen_padRO_keepsFs_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_cliExtStrlen_padRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHook_cliExtStrlen_roDataPad_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec) :=
  hookOk_cliExtStrlen_roDataPad_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHook_cliExtStrlen_roDataPad_keepsFs_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_cliExtStrlen_roDataPad_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHook_cliExtStrlen_alignedEnd_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec) :=
  hookOk_cliExtStrlen_alignedEnd_of_master
    (strlenGhostHook_master_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHook_cliExtStrlen_alignedEnd_keepsFs_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_cliExtStrlen_alignedEnd_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

-- 4.2 Budget (`withVmPreserved`) & `.keepsFs` contracts on `strlenGhostHook`:

theorem strlenGhostHook_any_withVmPreserved_ok {α : Type} {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withVmPreserved spec) :=
  hookOk_withVmPreserved hh
    (strlenGhostHook_vmPreserved hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHook_cliStrlenPadded_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (cliStrlenPaddedSpec stk)) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_cliStrlenPadded_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_cliStrlenPadded_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (cliStrlenPaddedSpec stk)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_cliStrlenPadded_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_strlenPaddedRO_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (strlenPaddedSpecRO stk)) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_strlenPaddedRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_strlenPaddedRO_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (strlenPaddedSpecRO stk)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_strlenPaddedRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_strlenSpecRO_padRO_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenPadRO (strlenSpecRO stk))) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_strlenSpecRO_padRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_strlenSpecRO_padRO_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenPadRO (strlenSpecRO stk))).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_strlenSpecRO_padRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_strlenSpecRO_roDataPad_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenRoDataPad (strlenSpecRO stk))) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_strlenSpecRO_roDataPad_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_strlenSpecRO_roDataPad_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenRoDataPad (strlenSpecRO stk))).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_strlenSpecRO_roDataPad_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_strlenSpecRO_alignedEnd_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenAlignedEnd (strlenSpecRO stk))) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_strlenSpecRO_alignedEnd_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_strlenSpecRO_alignedEnd_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenAlignedEnd (strlenSpecRO stk))).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_strlenSpecRO_alignedEnd_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_mainStrlen_padRO_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenPadRO (strlenSpec stk))) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_mainStrlen_padRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_mainStrlen_padRO_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenPadRO (strlenSpec stk))).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_mainStrlen_padRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_mainStrlen_roDataPad_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenRoDataPad (strlenSpec stk))) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_mainStrlen_roDataPad_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_mainStrlen_roDataPad_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenRoDataPad (strlenSpec stk))).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_mainStrlen_roDataPad_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_mainStrlen_alignedEnd_budget_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenAlignedEnd (strlenSpec stk))) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_mainStrlen_alignedEnd_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_mainStrlen_alignedEnd_budget_keepsFs_ok (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenAlignedEnd (strlenSpec stk))).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_mainStrlen_alignedEnd_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)

theorem strlenGhostHook_cliExtStrlen_padRO_budget_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_cliExtStrlen_padRO_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHook_cliExtStrlen_padRO_budget_keepsFs_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved
        (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_cliExtStrlen_padRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHook_cliExtStrlen_roDataPad_budget_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_cliExtStrlen_roDataPad_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHook_cliExtStrlen_roDataPad_budget_keepsFs_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved
        (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_cliExtStrlen_roDataPad_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

theorem strlenGhostHook_cliExtStrlen_alignedEnd_budget_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec)) :=
  strlenGhostHook_any_withVmPreserved_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr
    (strlenGhostHook_cliExtStrlen_alignedEnd_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHook_cliExtStrlen_alignedEnd_budget_keepsFs_ok :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withVmPreserved
        (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec)).keepsFs :=
  strlenGhostHook_any_keepsFs_ok
    (strlenGhostHook_cliExtStrlen_alignedEnd_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

-- 4.3 C11 `withAlloc` pool-threaded budget lifts (`WithAlloc.withAlloc`) on `strlenGhostHook`:

omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHook_any_withAlloc_of_withVmPreserved_ok {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withVmPreserved spec)) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withAlloc (M := M) A lim spec) :=
  hookOk_withAlloc_of_withVmPreserved A lim hh
omit hsvc_real hsvc_sub hreal_no hsub_no hwords haddr in
theorem strlenGhostHook_any_withAlloc_withVmPreserved_ok {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {spec : Spec α}
    (hh : HookOk (strlenGhostHook keep P_real P_sub entryTarget) (withVmPreserved spec)) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved spec)) :=
  hookOk_withAlloc_withVmPreserved A lim hh

theorem strlenGhostHook_cliStrlenPadded_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (cliStrlenPaddedSpec stk))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_cliStrlenPadded_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_strlenPaddedRO_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (strlenPaddedSpecRO stk))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_strlenPaddedRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_strlenSpecRO_padRO_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStrlenPadRO (strlenSpecRO stk)))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_strlenSpecRO_padRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_strlenSpecRO_roDataPad_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStrlenRoDataPad (strlenSpecRO stk)))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_strlenSpecRO_roDataPad_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_strlenSpecRO_alignedEnd_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStrlenAlignedEnd (strlenSpecRO stk)))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_strlenSpecRO_alignedEnd_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_mainStrlen_padRO_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStrlenPadRO (strlenSpec stk)))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_mainStrlen_padRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_mainStrlen_roDataPad_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStrlenRoDataPad (strlenSpec stk)))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_mainStrlen_roDataPad_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_mainStrlen_alignedEnd_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (stk : Nat := 4096) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved (withStrlenAlignedEnd (strlenSpec stk)))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_mainStrlen_alignedEnd_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr stk)
theorem strlenGhostHook_cliExtStrlen_padRO_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim
        (withVmPreserved (withStrlenPadRO CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_cliExtStrlen_padRO_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHook_cliExtStrlen_roDataPad_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim
        (withVmPreserved (withStrlenRoDataPad CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_cliExtStrlen_roDataPad_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)
theorem strlenGhostHook_cliExtStrlen_alignedEnd_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (strlenGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim
        (withVmPreserved (withStrlenAlignedEnd CryptoVerification.SignalSession.CliExt.strlenSpec))) :=
  hookOk_withAlloc_withVmPreserved A lim
    (strlenGhostHook_cliExtStrlen_alignedEnd_budget_ok hsvc_real hsvc_sub hreal_no hsub_no hwords haddr)

end GenericHookOkSuite

/-! ## 5. `pureWordsProg` Specializations (`P_sub` Hypotheses Discharged Unconditionally) -/

theorem strlenGhostHookPure_master_ok
    {keep : BitVec 64 → Bool} {P_real : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64) :
    HookOk (strlenGhostHookPure keep P_real entryTarget) masterStrlenSpec :=
  strlenGhostHook_master_ok hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entryTarget muslStrlenWords)
    (pureWordsProg_strlen_hasWords entryTarget) haddr

theorem strlenGhostHookPureK_masterK_ok
    {keep : BitVec 64 → Bool} {P_real : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64) :
    HookOk (strlenGhostHookPureK keep P_real entryTarget)
      (strlenSpecK keep masterStrlenSpec) :=
  strlenGhostHookK_masterK_ok hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entryTarget muslStrlenWords)
    (pureWordsProg_strlen_hasWords entryTarget) haddr

theorem strlenGhostHookPure_vmPreserved
    {keep : BitVec 64 → Bool} {P_real : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64) (s0 : State) :
    VmPreserved s0 (strlenGhostHookPure keep P_real entryTarget s0) :=
  strlenGhostHook_vmPreserved hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entryTarget muslStrlenWords)
    (pureWordsProg_strlen_hasWords entryTarget) haddr s0

theorem strlenGhostHookPureK_vmPreserved
    {keep : BitVec 64 → Bool} {P_real : Program} {entryTarget : BitVec 64}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (haddr : entryTarget.toNat + strlenByteLen ≤ 2 ^ 64) (s0 : State) :
    VmPreserved s0 (strlenGhostHookPureK keep P_real entryTarget s0) :=
  strlenGhostHookK_vmPreserved hsvc_real rfl hreal_no
    (pureWordsProg_externAt_none entryTarget muslStrlenWords)
    (pureWordsProg_strlen_hasWords entryTarget) haddr s0

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.StrlenGhost
