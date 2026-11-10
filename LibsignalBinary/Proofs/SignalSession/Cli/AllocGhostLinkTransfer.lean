/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.Process.PureMem
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.MallocngBridge
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetBaseBridges
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Heap.Fine.AllocZeroedFine
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev
import ProofLib.SepLogic.WPp

/-!
# Ghost-Hook Overlay and Link-Transfer Bridge for `mallocng`

Connects `HookOk` / `HookSat`-parameterized `RustCliAllocBudget` proofs to linked binaries in which
`__rust_{alloc,dealloc,realloc,alloc_zeroed}` execute real `mallocng` machine code:

1. **Executable-memory restriction (`ExecFrozen`, `stripExecOutside`):** proves `SepProp.Satisfies`
   invariance and commutation of `allocMallocng` and `Syscall.standard` with `stripS keep`, lifting
   `Steps` on restricted code to first-stop `StepsUntil P_real (SubroutineStop s0)` traces when the
   caller `lr` lies outside `keep`.
2. **Linked allocator budget (`linkedGhostBudget`):** combines an auxiliary code-RO witness with
   `fineHookRustCliAllocBudget`, lifts the `mallocng` crypto and `String::clone` hooks, and splits
   out `((__libc + 3) ↦₈ 0#8)` (`need_locks`) for `exit` cleanup.
3. **Ghost-to-real link transfer (`linkedCallHook`, `cliGhostExterns`, `subroutine_ok_transfer_allocGhost`):**
   constructs total ghost hooks that replay as real `Steps P_real` traces on reachable calls (falling
   back to `codeROSubroutineHook` outside `ActiveRealRun`) and transfers `Steps`, `SepWPp`, and
   `subroutine_ok` from `cliGhostExterns g baseExt` to `baseExt`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic ProofLib.StdStartup
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries
open VerifiedLibraries.Mallocng hiding AllocCostModel MallocngModelEnv
open VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.RustStd (
  RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs
)
open CryptoGames.CBC (AesKey Block)
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement)
open CryptoVerification.E2E (
  aesDecFrameBytes aesDecHookMallocng aesDecOut
  aesEncFrameBytes aesEncHookMallocng
  libcruxHmacFrameBytes libcruxHmacHookMallocng
  stepRustAlloc1 stepRustDealloc1
)
open CryptoVerification.LibsignalPublicApi.StoreKit (TraceFsSound)
open CryptoVerification.LibsignalSpqrV1 (libcruxHmacName)
open CryptoVerification.LibsignalTripleRatchet (
  AesCall extHookStack framelessMemcpySpec memcpyName memmoveName memsetName
  noAllocShimSpec noAllocShim_hookOk sessionMemcpyRegionSpec sessionMemcpySpec
  sessionMemsetRegionSpec sessionMemsetSpec sessionShim_hookOk
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced
  lsAesDecSym lsAesEncSym lsFormatInnerSym lsFromUtf8Sym lsMemcpySym lsMemrchrSym lsMemsetSym
  lsReadFileSym lsReadStdinSym
  lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli
  lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym
)
open CryptoVerification.SignalSession.Cli.MainHops (
  hookMemmove_fs hookNoop_fs
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  FsTHooks IsFsC cliExternsPlaced_row cliGhostExterns_memcpy_some cliGhostExterns_memset_some
  fsTHooks_cliExternsPlaced fsTHooks_none fsT_externAt
  hookNoop_fsT panicked_fsT traceFsSound_of_fsTHooks
)
open CryptoVerification.SignalSession.Cli.Slots (
  memmove_row_placed
)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (
  CliPanicHooksPlaced cliPanicHooksPlaced_cli
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits
  MallocngCostModelIface MallocngModelEnv
  OomPreserved RustAllocAddrs RustCliAllocBudget RustCliAllocBudgetEntries
  RustCliAllocBudgetEntriesBase
  StaticMappedCover VmPreserved
  allocMemcpyVmSpec
  hookOk_rustCliAllocBudget_of_base hookOk_rustCliDeallocBudget_of_base
  hookOk_rustCliReallocBudget_of_base
  mallocngBudgetPoolAt mallocngBudgetPoolAt_split_runtime mallocngBudgetPoolInv
  rustAllocZeroedBudgetSpecBase
  rustCliAllocBudgetSpec rustCliAllocBudgetSpecBase
  rustCliDeallocBudgetSpec rustCliDeallocBudgetSpecBase
  rustCliReallocBudgetSpec rustCliReallocBudgetSpecBase
  subroutine_ok_rustCliAllocBudget_of_base
)
open LibsignalBinary.Heap.SpecBudget (
  aesCallPreBudget aesDecBudgetSpec aesDecFnBudgetSpec aesDecWeakBudgetSpec
  aesEncBudgetSpec formatInnerBudgetSpec libcruxHmacBudgetSpec rustAllocZeroedBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  RustStdAllocAuxEntries stringCloneBudgetSpec
)
open LibsignalBinary.Heap.Fine (
  FineBudget allocMemsetVmSpec fineCostModel fineCostModelIface fineCostModelSound
  fineRustCliAllocBudget rdlAllocZeroedInstrs
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX CodeBlocksPermRXMem fineHookRustCliAllocBudget
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudget (
  fineAesDecWeak_budget_hookOk fineAesDec_budget_hookOk fineAesEnc_budget_hookOk
  fineHookRustCliAllocBudgetEntries_thunks fineHookRustCliAllocZeroedBudget_thunk_ok
  fineHookStringCloneBudget_of_hasInstrs_ok fineLibcruxHmac_budget_hookOk
  fineStringClone_budget_hookOk stringCloneHookMallocng
)
open LibsignalBinary.Proofs.Placed.StringCloneMallocngPlaced (
  rustStringCloneBudget_of_hasInstrs_ok rustStringCloneInstrs
)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (PublicApiDecHooksPlaced)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget (Stage2ContractsMinPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsFsPlaced AllocContractsXCliPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  allocContractsFsPlaced_of_hookSat allocContractsXCliPlaced_of_hookSat
  cliExternsPlaced_bcmp_budget_sat cliExternsPlaced_fromUtf8_budget_sat
  cliExternsPlaced_memmove_budget_sat cliExternsPlaced_memrchr_budget_sat
  cliExternsPlaced_noAllocShim_budget_sat
  cliExternsPlaced_sessionMemmove_budget_sat cliExternsPlaced_shim_budget_sat
  cliGhostExterns_framelessMemcpy_budget_sat cliGhostExterns_memcpyRegionRO_budget_sat
  cliGhostExterns_memcpyRegion_budget_sat cliGhostExterns_memcpy_budget_sat
  cliGhostExterns_memsetRegion_budget_sat cliGhostExterns_memset_budget_sat
  cliGhostExterns_sessionMemcpyRegion_budget_sat cliGhostExterns_sessionMemcpy_budget_sat
  cliGhostExterns_sessionMemsetRegion_budget_sat cliGhostExterns_sessionMemset_budget_sat
  codecHooksPlaced_of_hookSat publicApiDecHooksPlaced_of_hookSat
  stage2ContractsMinPlaced_of_hookSat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)

/-! ## 1. `ExecFrozen`, `stripExecOutside` Satisfaction Equivalence, & `allocMallocng` Commutation -/

/-- Every executable byte in `m` is readable and non-writable (`Perm.rx`, hence frozen). Holds on
    every `ElfImage.loadState` memory and is preserved by all non-`SVC` instructions and all
    Linux VM syscalls (`brk`, `mmap`, `munmap`, `mprotect`, `mremap`, `madvise`). -/
def ExecFrozen (m : Memory) : Prop :=
  ∀ a : BitVec 64, (m.perm a).x = true → (m.perm a).r = true ∧ (m.perm a).w = false

theorem ExecFrozen.of_perm_eq {m m' : Memory} (h : ExecFrozen m)
    (hp : ∀ a, m'.perm a = m.perm a) : ExecFrozen m' := by
  intro a hx
  rw [hp a] at hx ⊢
  exact h a hx

theorem ExecFrozen.of_keepsFrozen_noNewX {m m' : Memory} (h : ExecFrozen m)
    (hno : ∀ a, (m'.perm a).x = true → (m.perm a).x = true)
    (hkf : m.KeepsFrozen m') : ExecFrozen m' := by
  intro a hx'
  have hx := hno a hx'
  obtain ⟨hr, hw⟩ := h a hx
  have hfr : m.Frozen a := by
    unfold Memory.Frozen Option.frozen
    cases hp : m.perm a with
    | none => simp [hp] at hx
    | some p =>
      rcases p with ⟨r, w, x, lf, an⟩
      simp only [hp, Option.r, Option.w, Option.x] at hx hr hw ⊢
      subst hx hr hw; rfl
  have hpeq : m'.perm a = m.perm a := (hkf a hfr).2.1
  rw [hpeq]
  exact ⟨hr, hw⟩

private theorem perm_rwx_props {m : Memory} {a : BitVec 64} {p : Perm}
    (hp : m.perm a = some p) : p.lazyFree = false ∧ p.anon = true := by
  unfold Memory.perm at hp
  cases hc : m.cells a with
  | none => simp [hc] at hp
  | some cb =>
    rcases cb with ⟨_ | q, _⟩ <;> simp [hc, Perm.rwx] at hp
    subst hp; exact ⟨rfl, rfl⟩

/-- Forward `SepProp.Satisfies` preservation under `stripExecOutside keep` (unconditional). -/
theorem satisfies_stripExecOutside (keep : BitVec 64 → Bool) {m : Memory} {P : SepProp}
    (hsat : m ⊨ P) :
    stripExecOutside keep m ⊨ P := by
  refine Arm64.Satisfies.of_perm_mono
    (fun a => strip_read8 keep m a)
    (fun a hrw => (strip_perm_props keep m a).2.2.2.mpr hrw)
    (fun a hpn => ?_)
    (fun a hr => (strip_perm_props keep m a).1.trans hr)
    (fun a hm => (strip_perm_props keep m a).2.2.1.trans hm)
    (fun a hlf => (strip_isLazyFree keep m a).trans hlf)
    (fun a han => (strip_isAnon keep m a).trans han)
    hsat
  rw [strip_perm, hpn]
  unfold stripPerm Perm.protNone
  cases keep a <;> rfl

/-- Backward `SepProp.Satisfies` recovery from `stripExecOutside keep m` under `ExecFrozen m`. -/
theorem satisfies_of_stripExecOutside {keep : BitVec 64 → Bool} {m : Memory} {P : SepProp}
    (hfr : ExecFrozen m) (hsat : stripExecOutside keep m ⊨ P) :
    m ⊨ P := by
  refine Arm64.Satisfies.of_perm_mono
    (fun a => (strip_read8 keep m a).symm)
    (fun a hrw => (strip_perm_props keep m a).2.2.2.mp hrw)
    (fun a hpn => ?_)
    (fun a hr => (strip_perm_props keep m a).1.symm.trans hr)
    (fun a hm => (strip_perm_props keep m a).2.2.1.symm.trans hm)
    (fun a hlf => (strip_isLazyFree keep m a).symm.trans hlf)
    (fun a han => (strip_isAnon keep m a).symm.trans han)
    hsat
  rw [strip_perm] at hpn
  cases hp : m.perm a with
  | none => simp [hp] at hpn
  | some p =>
    obtain ⟨hlf, han⟩ := perm_rwx_props hp
    have hfr_a := hfr a
    rw [hp] at hpn hfr_a
    rcases p with ⟨r, w, x, lf, an⟩
    dsimp only at hlf han
    subst hlf han
    unfold stripPerm Perm.protNone at hpn
    unfold Perm.protNone
    cases hk : keep a <;> cases r <;> cases w <;> cases x <;>
      simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem strip_perm_w {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) (a : BitVec 64) :
    ((stripExecOutside keep m).perm a).w = (m.perm a).w := by
  rw [strip_perm]
  have hfr_a := hfr a
  cases hp : m.perm a with
  | none => rfl
  | some p =>
    rw [hp] at hfr_a
    rcases p with ⟨r, w, x, lf, an⟩
    unfold stripPerm
    cases hk : keep a <;> cases r <;> cases w <;> cases x <;>
      simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem strip_perm_frozen {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) (a : BitVec 64) :
    ((stripExecOutside keep m).perm a).frozen = (m.perm a).frozen := by
  rw [strip_perm]
  have hfr_a := hfr a
  cases hp : m.perm a with
  | none => rfl
  | some p =>
    rw [hp] at hfr_a
    rcases p with ⟨r, w, x, lf, an⟩
    unfold stripPerm Option.frozen Perm.frozen
    cases keep a <;> cases r <;> cases w <;> cases x <;>
      simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem strip_canMap (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (n : Nat) :
    (stripExecOutside keep m).canMap a n = m.canMap a n :=
  strip_allPerm_eq (p := fun q => !q.mapped)
    (fun x => congrArg Bool.not (strip_perm_props keep m x).2.2.1) a n

private theorem strip_allAnon (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat),
      (stripExecOutside keep m).allAnon a n = m.allAnon a n
  | _, 0 => rfl
  | a, n + 1 => by
    simp only [Memory.allAnon, strip_isAnon, strip_allAnon keep m (a + 1#64) n]

private theorem strip_countPerm_rw (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat),
      (stripExecOutside keep m).countPerm (· == some Perm.rw) a n =
        m.countPerm (· == some Perm.rw) a n
  | _, 0 => rfl
  | a, n + 1 => by
    have hrw :
        ((stripExecOutside keep m).perm a == some Perm.rw) = (m.perm a == some Perm.rw) := by
      cases h1 : (stripExecOutside keep m).perm a == some Perm.rw <;>
        cases h2 : m.perm a == some Perm.rw
      · rfl
      · exfalso
        exact Bool.eq_false_iff.mp h1
          (beq_iff_eq.mpr ((strip_perm_props keep m a).2.2.2.mpr (beq_iff_eq.mp h2)))
      · exfalso
        exact Bool.eq_false_iff.mp h2
          (beq_iff_eq.mpr ((strip_perm_props keep m a).2.2.2.mp (beq_iff_eq.mp h1)))
      · rfl
    simp only [Memory.countPerm, hrw, strip_countPerm_rw keep m (a + 1#64) n]

private theorem strip_countRw (keep : BitVec 64 → Bool) (m : Memory)
    (a : BitVec 64) (n : Nat) :
    (stripExecOutside keep m).countRw a n = m.countRw a n :=
  strip_countPerm_rw keep m a n

private theorem strip_findMappedByte (keep : BitVec 64 → Bool) (m : Memory)
    (base : BitVec 64) :
    ∀ (curOff rem : Nat),
      findMappedByte (stripExecOutside keep m) base curOff rem =
        findMappedByte m base curOff rem
  | _, 0 => rfl
  | curOff, rem + 1 => by
    simp only [findMappedByte, (strip_perm_props keep m _).2.2.1,
      strip_findMappedByte keep m base (curOff + 1) rem]

private theorem strip_findUnmappedAreaLoop (keep : BitVec 64 → Bool) (m : Memory) (size : Nat) :
    ∀ (fuel addr : Nat),
      findUnmappedAreaLoop (stripExecOutside keep m) size fuel addr =
        findUnmappedAreaLoop m size fuel addr
  | 0, _ => rfl
  | fuel + 1, addr => by
    unfold findUnmappedAreaLoop
    dsimp only
    rw [strip_findMappedByte]
    split
    · rfl
    · cases findMappedByte m (BitVec.ofNat 64 addr) 0 size with
      | none => rfl
      | some off => exact strip_findUnmappedAreaLoop keep m size fuel _

private theorem strip_sanitizeMmapAddr (keep : BitVec 64 → Bool) (m : Memory)
    (cand : BitVec 64) (size : Nat) :
    sanitizeMmapAddr (stripExecOutside keep m) cand size = sanitizeMmapAddr m cand size := by
  unfold sanitizeMmapAddr findUnmappedArea
  rw [strip_canMap, strip_findUnmappedAreaLoop]

private theorem perm_mk_cells (f : BitVec 64 → Option (Option Perm × BitVec 8)) (a : BitVec 64) :
    (Memory.mk f).perm a =
      match f a with
      | some (some p, _) => some p.rwx
      | _ => none := rfl

private theorem strip_mapZero (keep : BitVec 64 → Bool) (m : Memory)
    (base : BitVec 64) (len : Nat) :
    (stripExecOutside keep m).mapZero base len = stripExecOutside keep (m.mapZero base len) := by
  have hmp : ∀ a, ((stripExecOutside keep m).perm a).mapped = (m.perm a).mapped :=
    fun a => (strip_perm_props keep m a).2.2.1
  dsimp only [Memory.mapZero]
  simp only [hmp]
  dsimp only [stripExecOutside]
  congr 1; funext a
  cases (decide ((a - base).toNat < len) && !(m.perm a).mapped)
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte, stripPerm, Perm.rw]; cases keep a <;> rfl

private theorem execFrozen_mapZero {m : Memory} (hfr : ExecFrozen m)
    (base : BitVec 64) (len : Nat) :
    ExecFrozen (m.mapZero base len) := by
  intro a hx
  unfold Memory.mapZero at hx ⊢
  rw [perm_mk_cells] at hx ⊢
  by_cases hc : (decide ((a - base).toNat < len) && !(m.perm a).mapped) = true
  · simp only [hc, ↓reduceIte, Perm.rwx, Perm.rw, Option.x] at hx
    cases hx
  · simp only [hc] at hx ⊢
    exact hfr a hx

private theorem strip_unmapWritable {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) (base : BitVec 64) (len : Nat) :
    (stripExecOutside keep m).unmapWritable base len =
      stripExecOutside keep (m.unmapWritable base len) := by
  have hw : ∀ a, ((stripExecOutside keep m).perm a).w = (m.perm a).w := strip_perm_w hfr
  dsimp only [Memory.unmapWritable]
  simp only [hw]
  dsimp only [stripExecOutside]
  congr 1; funext a
  cases (decide ((a - base).toNat < len) && (m.perm a).w) <;>
    simp only [Bool.false_eq_true, ↓reduceIte]

private theorem execFrozen_unmapWritable {m : Memory} (hfr : ExecFrozen m)
    (base : BitVec 64) (len : Nat) :
    ExecFrozen (m.unmapWritable base len) := by
  intro a hx
  unfold Memory.unmapWritable at hx ⊢
  rw [perm_mk_cells] at hx ⊢
  by_cases hc : (decide ((a - base).toNat < len) && (m.perm a).w) = true
  · simp only [hc, ↓reduceIte, Option.x] at hx
    cases hx
  · simp only [hc] at hx ⊢
    exact hfr a hx

private theorem strip_unmapNonFrozen {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) (base : BitVec 64) (len : Nat) :
    (stripExecOutside keep m).unmapNonFrozen base len =
      stripExecOutside keep (m.unmapNonFrozen base len) := by
  have hfz : ∀ a, ((stripExecOutside keep m).perm a).frozen = (m.perm a).frozen :=
    strip_perm_frozen hfr
  dsimp only [Memory.unmapNonFrozen]
  simp only [hfz]
  dsimp only [stripExecOutside]
  congr 1; funext a
  cases (decide ((a - base).toNat < len) && !(m.perm a).frozen) <;>
    simp only [Bool.false_eq_true, ↓reduceIte]

private theorem execFrozen_unmapNonFrozen {m : Memory} (hfr : ExecFrozen m)
    (base : BitVec 64) (len : Nat) :
    ExecFrozen (m.unmapNonFrozen base len) := by
  intro a hx
  unfold Memory.unmapNonFrozen at hx ⊢
  rw [perm_mk_cells] at hx ⊢
  by_cases hc : (decide ((a - base).toNat < len) && !(m.perm a).frozen) = true
  · simp only [hc, ↓reduceIte, Option.x] at hx
    cases hx
  · simp only [hc] at hx ⊢
    exact hfr a hx

private theorem strip_setPermNonFrozen {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) (base : BitVec 64) (len : Nat) (p : Perm) (hpx : p.x = false) :
    (stripExecOutside keep m).setPermNonFrozen base len p =
      stripExecOutside keep (m.setPermNonFrozen base len p) := by
  have hfz : ∀ a, ((stripExecOutside keep m).perm a).frozen = (m.perm a).frozen :=
    strip_perm_frozen hfr
  have hmp : ∀ a, ((stripExecOutside keep m).perm a).mapped = (m.perm a).mapped :=
    fun a => (strip_perm_props keep m a).2.2.1
  have hlf := strip_isLazyFree keep m
  have han := strip_isAnon keep m
  have hr8 := strip_read8 keep m
  dsimp only [Memory.setPermNonFrozen]
  simp only [hfz, hmp, hlf, han, hr8]
  dsimp only [stripExecOutside]
  congr 1; funext a
  cases (decide ((a - base).toNat < len) && (m.perm a).mapped && !(m.perm a).frozen)
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · rcases p with ⟨r, w, x, lf, an⟩
    dsimp only at hpx
    subst hpx
    simp only [↓reduceIte, stripPerm]
    cases keep a <;> rfl

private theorem execFrozen_setPermNonFrozen {m : Memory} (hfr : ExecFrozen m)
    (base : BitVec 64) (len : Nat) (p : Perm) (hpx : p.x = false) :
    ExecFrozen (m.setPermNonFrozen base len p) := by
  intro a hx
  unfold Memory.setPermNonFrozen at hx ⊢
  rw [perm_mk_cells] at hx ⊢
  by_cases hc : (decide ((a - base).toNat < len) && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [hc, ↓reduceIte, Perm.rwx, Option.x, hpx] at hx
    cases hx
  · simp only [hc] at hx ⊢
    exact hfr a hx

private theorem strip_remapRw {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) :
    (stripExecOutside keep m).remapRw oldBase oldSize newBase newSize =
      stripExecOutside keep (m.remapRw oldBase oldSize newBase newSize) := by
  have hfz : ∀ a, ((stripExecOutside keep m).perm a).frozen = (m.perm a).frozen :=
    strip_perm_frozen hfr
  have hlf := strip_isLazyFree keep m
  have han := strip_isAnon keep m
  have hr8 := strip_read8 keep m
  dsimp only [Memory.remapRw]
  simp only [hfz, hlf, han, hr8]
  dsimp only [stripExecOutside]
  congr 1; funext a
  cases (m.perm a).frozen
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hn : (a - newBase).toNat < newSize
    · simp only [hn, ↓reduceIte, stripPerm, Perm.rw]
      by_cases ho : (a - newBase).toNat < oldSize
      · simp only [ho, ↓reduceIte]; cases keep a <;> rfl
      · simp only [ho, ↓reduceIte]; cases keep a <;> rfl
    · simp only [hn, ↓reduceIte]
      by_cases ho2 : (a - oldBase).toNat < oldSize
      · simp only [ho2, ↓reduceIte]
      · simp only [ho2, ↓reduceIte]
  · simp only [↓reduceIte]

private theorem execFrozen_remapRw {m : Memory} (hfr : ExecFrozen m)
    (oldBase : BitVec 64) (oldSize : Nat) (newBase : BitVec 64) (newSize : Nat) :
    ExecFrozen (m.remapRw oldBase oldSize newBase newSize) := by
  intro a hx
  unfold Memory.remapRw at hx ⊢
  rw [perm_mk_cells] at hx ⊢
  by_cases hf : (m.perm a).frozen = true
  · simp only [hf, ↓reduceIte] at hx ⊢
    exact hfr a hx
  · simp only [hf] at hx ⊢
    by_cases hn : (a - newBase).toNat < newSize
    · simp only [hn, ↓reduceIte] at hx
      by_cases ho : (a - newBase).toNat < oldSize
      · simp only [ho, ↓reduceIte, Perm.rwx, Perm.rw, Option.x] at hx; cases hx
      · simp only [ho, ↓reduceIte, Perm.rwx, Perm.rw, Option.x] at hx; cases hx
    · simp only [hn, ↓reduceIte] at hx ⊢
      by_cases ho2 : (a - oldBase).toNat < oldSize
      · simp only [ho2, ↓reduceIte, Option.x] at hx; cases hx
      · simp only [ho2, ↓reduceIte] at hx ⊢
        exact hfr a hx

private theorem nonFrozen_perm_x_false {m : Memory} (hfr : ExecFrozen m) {a : BitVec 64}
    (hnf : (m.perm a).frozen = false) :
    (m.perm a).x = false := by
  apply Bool.eq_false_iff.mpr
  intro hx
  obtain ⟨hr, hw⟩ := hfr a hx
  cases hp : m.perm a with
  | none => simp [hp] at hx
  | some p =>
    rcases p with ⟨r, w, x, lf, an⟩
    simp only [hp, Option.x, Option.r, Option.w, Option.frozen, Perm.frozen] at hx hr hw hnf
    subst hx hr hw
    cases hnf

private theorem strip_zeroNonFrozen {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) (base : BitVec 64) (len : Nat) :
    (stripExecOutside keep m).zeroNonFrozen base len =
      stripExecOutside keep (m.zeroNonFrozen base len) := by
  have hfz : ∀ a, ((stripExecOutside keep m).perm a).frozen = (m.perm a).frozen :=
    strip_perm_frozen hfr
  have hmp : ∀ a, ((stripExecOutside keep m).perm a).mapped = (m.perm a).mapped :=
    fun a => (strip_perm_props keep m a).2.2.1
  have han := strip_isAnon keep m
  have hp := strip_perm keep m
  dsimp only [Memory.zeroNonFrozen]
  simp only [hfz, hmp, han]
  simp only [hp]
  dsimp only [stripExecOutside]
  congr 1; funext a
  cases hc : (decide ((a - base).toNat < len) && (m.perm a).mapped && !(m.perm a).frozen)
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · have hnf : (m.perm a).frozen = false := by
      rcases Bool.and_eq_true_iff.mp hc with ⟨_, hnf'⟩
      simpa using hnf'
    have hx0 := nonFrozen_perm_x_false hfr hnf
    cases hpa : m.perm a with
    | none => simp [hpa, Option.mapped] at hc
    | some p =>
      rw [hpa] at hx0
      rcases p with ⟨r, w, x, lf, an⟩
      simp only [Option.x] at hx0
      subst hx0
      simp only [↓reduceIte, Option.map, stripPerm]
      cases keep a <;> rfl

private theorem execFrozen_zeroNonFrozen {m : Memory} (hfr : ExecFrozen m)
    (base : BitVec 64) (len : Nat) :
    ExecFrozen (m.zeroNonFrozen base len) := by
  intro a hx
  unfold Memory.zeroNonFrozen at hx ⊢
  rw [perm_mk_cells] at hx ⊢
  by_cases hc : (decide ((a - base).toNat < len) && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [hc, ↓reduceIte] at hx
    have hnf : (m.perm a).frozen = false := by
      rcases Bool.and_eq_true_iff.mp hc with ⟨_, hnf'⟩
      simpa using hnf'
    have hx0 := nonFrozen_perm_x_false hfr hnf
    cases hpa : m.perm a with
    | none => simp [hpa, Option.mapped] at hc
    | some p =>
      rw [hpa] at hx0 hx
      rcases p with ⟨r, w, x, lf, an⟩
      dsimp only [Option.x] at hx0
      subst hx0
      dsimp only [Option.map, Perm.rwx, Option.x] at hx
      cases hx
  · simp only [hc] at hx ⊢
    exact hfr a hx

private theorem strip_madvFreeNonFrozen {keep : BitVec 64 → Bool} {m : Memory}
    (hfr : ExecFrozen m) (base : BitVec 64) (len : Nat) :
    (stripExecOutside keep m).madvFreeNonFrozen base len =
      stripExecOutside keep (m.madvFreeNonFrozen base len) := by
  have hfz : ∀ a, ((stripExecOutside keep m).perm a).frozen = (m.perm a).frozen :=
    strip_perm_frozen hfr
  have hmp : ∀ a, ((stripExecOutside keep m).perm a).mapped = (m.perm a).mapped :=
    fun a => (strip_perm_props keep m a).2.2.1
  have han := strip_isAnon keep m
  have hr8 := strip_read8 keep m
  have hp := strip_perm keep m
  dsimp only [Memory.madvFreeNonFrozen]
  simp only [hfz, hmp, han, hr8]
  simp only [hp]
  dsimp only [stripExecOutside]
  congr 1; funext a
  cases hc : (decide ((a - base).toNat < len) && (m.perm a).mapped && !(m.perm a).frozen)
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · have hnf : (m.perm a).frozen = false := by
      rcases Bool.and_eq_true_iff.mp hc with ⟨_, hnf'⟩
      simpa using hnf'
    have hx0 := nonFrozen_perm_x_false hfr hnf
    cases hpa : m.perm a with
    | none => simp [hpa, Option.mapped] at hc
    | some p =>
      rw [hpa] at hx0
      rcases p with ⟨r, w, x, lf, an⟩
      simp only [Option.x] at hx0
      subst hx0
      simp only [↓reduceIte, Option.map, stripPerm]
      cases keep a <;> rfl

private theorem execFrozen_madvFreeNonFrozen {m : Memory} (hfr : ExecFrozen m)
    (base : BitVec 64) (len : Nat) :
    ExecFrozen (m.madvFreeNonFrozen base len) := by
  intro a hx
  unfold Memory.madvFreeNonFrozen at hx ⊢
  rw [perm_mk_cells] at hx ⊢
  by_cases hc : (decide ((a - base).toNat < len) && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [hc, ↓reduceIte] at hx
    have hnf : (m.perm a).frozen = false := by
      rcases Bool.and_eq_true_iff.mp hc with ⟨_, hnf'⟩
      simpa using hnf'
    have hx0 := nonFrozen_perm_x_false hfr hnf
    cases hpa : m.perm a with
    | none => simp [hpa, Option.mapped] at hc
    | some p =>
      rw [hpa] at hx0 hx
      rcases p with ⟨r, w, x, lf, an⟩
      dsimp only [Option.x] at hx0
      subst hx0
      dsimp only [Option.map, Perm.rwx, Option.x] at hx
      cases hx
  · simp only [hc] at hx ⊢
    exact hfr a hx

private theorem stripS_mem (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).mem = stripExecOutside keep s.mem := by cases s; rfl
private theorem stripS_r64 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem stripS_brk (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).brk = s.brk := by cases s; rfl
private theorem stripS_brkStart (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).brkStart = s.brkStart := by cases s; rfl
private theorem stripS_pma (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).physMemAvail = s.physMemAvail := by cases s; rfl
private theorem stripS_orc (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).oracle = s.oracle := by cases s; rfl
private theorem stripS_oi (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).oracleIdx = s.oracleIdx := by cases s; rfl
private theorem stripS_status (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).status = s.status := by cases s; rfl
private theorem stripS_pc (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).pc = s.pc := by cases s; rfl
private theorem stripS_sp (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sp = s.sp := by cases s; rfl
private theorem stripS_fs (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).fs = s.fs := by cases s; rfl
private theorem stripS_w64 (keep : BitVec 64 → Bool) (s : State) (r : Reg) (v : BitVec 64) :
    (stripS keep s).writeReg64 r v = stripS keep (s.writeReg64 r v) := by
  cases s; cases r <;> rfl
private theorem stripS_adv (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).advancePC = stripS keep s.advancePC := by cases s; rfl
private theorem stripS_sst (keep : BitVec 64 → Bool) (s : State) (st : ExecStatus) :
    (stripS keep s).setStatus st = stripS keep (s.setStatus st) := by cases s; rfl
private theorem stripS_sbrk (keep : BitVec 64 → Bool) (s : State) (b : BitVec 64) :
    (stripS keep s).setBrk b = stripS keep (s.setBrk b) := by cases s; rfl
private theorem stripS_spma (keep : BitVec 64 → Bool) (s : State) (n : Nat) :
    (stripS keep s).setPhysMemAvail n = stripS keep (s.setPhysMemAvail n) := by cases s; rfl
private theorem stripS_norc (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).nextOracle = stripS keep s.nextOracle := by cases s; rfl
private theorem stripS_smem (keep : BitVec 64 → Bool) (s : State) (m : Memory) :
    (stripS keep s).setMem (stripExecOutside keep m) = stripS keep (s.setMem m) := by cases s; rfl
private theorem stripS_ite (keep : BitVec 64 → Bool) (c : Prop) [Decidable c] (a b : State) :
    (if c then stripS keep a else stripS keep b) = stripS keep (if c then a else b) := by
  split <;> rfl
private theorem state_mem_ite (c : Prop) [Decidable c] (a b : State) :
    (if c then a else b).mem = if c then a.mem else b.mem :=
  apply_ite State.mem c a b
private theorem state_fs_ite (c : Prop) [Decidable c] (a b : State) :
    (if c then a else b).fs = if c then a.fs else b.fs :=
  apply_ite State.fs c a b
private theorem execFrozen_ite {c : Prop} [Decidable c] {a b : State}
    (ha : ExecFrozen a.mem) (hb : ExecFrozen b.mem) :
    ExecFrozen (if c then a else b).mem := by
  split <;> assumption

private theorem execBrk_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execBrk (stripS keep s) = stripS keep (execBrk s) ∧
    ExecFrozen (execBrk s).mem ∧ (execBrk s).fs = s.fs := by
  unfold execBrk
  have hmap := strip_allPerm_eq (keep := keep) (m := s.mem)
    (fun a => (strip_perm_props keep s.mem a).2.2.1)
  simp only [stripS_r64, stripS_brkStart, stripS_brk, stripS_mem, stripS_pma,
    hmap, strip_countRw, strip_canMap, strip_unmapWritable hfr, strip_mapZero]
  split
  · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
  · split
    · split
      · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
      · exact ⟨by simp [stripS_sbrk, stripS_smem, stripS_spma, stripS_w64, stripS_adv],
          by simpa using execFrozen_unmapWritable hfr _ _, rfl⟩
    · split
      · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
      · split
        · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
        · exact ⟨by simp [stripS_sbrk, stripS_smem, stripS_spma, stripS_w64, stripS_adv],
            by simpa using execFrozen_mapZero hfr _ _, rfl⟩

private theorem execMunmap_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execMunmap (stripS keep s) = stripS keep (execMunmap s) ∧
    ExecFrozen (execMunmap s).mem ∧ (execMunmap s).fs = s.fs := by
  unfold execMunmap
  have hnf := strip_allPerm_eq (keep := keep) (m := s.mem) (p := fun q => !q.frozen)
    (fun a => congrArg Bool.not (strip_perm_frozen (keep := keep) hfr a))
  simp only [stripS_r64, stripS_mem, stripS_pma, hnf, strip_countRw, strip_unmapNonFrozen hfr]
  split
  · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
  · split
    · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
    · exact ⟨by simp [stripS_smem, stripS_spma, stripS_w64, stripS_adv],
        by simpa using execFrozen_unmapNonFrozen hfr _ _, rfl⟩

private theorem execMmap_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execMmap (stripS keep s) = stripS keep (execMmap s) ∧
    ExecFrozen (execMmap s).mem ∧ (execMmap s).fs = s.fs := by
  unfold execMmap
  have hnf := strip_allPerm_eq (keep := keep) (m := s.mem) (p := fun q => !q.frozen)
    (fun a => congrArg Bool.not (strip_perm_frozen (keep := keep) hfr a))
  simp only [stripS_r64, stripS_mem, stripS_pma, stripS_orc, stripS_oi, hnf, strip_countRw,
    strip_sanitizeMmapAddr]
  split
  · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
  · split
    · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
    · split
      · split
        · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
        · split
          · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
          · have hunf := execFrozen_unmapNonFrozen hfr (s.readReg64 Reg.x0)
              (pageAlignUp (s.readReg64 Reg.x1).toNat)
            have hmz := execFrozen_mapZero hunf (s.readReg64 Reg.x0)
              (pageAlignUp (s.readReg64 Reg.x1).toNat)
            split
            · rw [strip_unmapNonFrozen hfr, strip_mapZero,
                  strip_setPermNonFrozen hmz _ _ Perm.protNone rfl]
              exact ⟨by simp [stripS_smem, stripS_spma, stripS_w64, stripS_adv],
                by simpa using execFrozen_setPermNonFrozen hmz _ _ Perm.protNone rfl, rfl⟩
            · split
              · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
              · rw [strip_unmapNonFrozen hfr, strip_mapZero]
                exact ⟨by simp [stripS_smem, stripS_spma, stripS_w64, stripS_adv],
                  by simpa using hmz, rfl⟩
      · cases sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
            (pageAlignUp (s.readReg64 Reg.x1).toNat) with
        | none =>
          exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
        | some base =>
          have hmz := execFrozen_mapZero hfr base (pageAlignUp (s.readReg64 Reg.x1).toNat)
          dsimp only
          split
          · rw [strip_mapZero, strip_setPermNonFrozen hmz _ _ Perm.protNone rfl]
            exact ⟨by simp [stripS_smem, stripS_norc, stripS_w64, stripS_adv],
              by simpa using execFrozen_setPermNonFrozen hmz _ _ Perm.protNone rfl, rfl⟩
          · split
            · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
            · rw [strip_mapZero]
              exact ⟨by simp [stripS_smem, stripS_spma, stripS_norc, stripS_w64, stripS_adv],
                by simpa using hmz, rfl⟩

private theorem execMprotect_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) :
    execMprotect (stripS keep s) = stripS keep (execMprotect s) ∧
    ExecFrozen (execMprotect s).mem ∧ (execMprotect s).fs = s.fs := by
  unfold execMprotect
  have hnf := strip_allPerm_eq (keep := keep) (m := s.mem) (p := fun q => !q.frozen)
    (fun a => congrArg Bool.not (strip_perm_frozen (keep := keep) hfr a))
  have hmp := strip_allPerm_eq (keep := keep) (m := s.mem)
    (fun a => (strip_perm_props keep s.mem a).2.2.1)
  simp only [stripS_r64, stripS_mem, stripS_pma, hnf, hmp, strip_canMap, strip_countRw]
  split
  · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
  · split
    · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
    · split
      · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
      · split
        · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
        · split
          · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
          · split
            · split
              · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
              · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
            · split
              · rw [strip_setPermNonFrozen hfr _ _ Perm.protNone rfl]
                exact ⟨by simp [stripS_smem, stripS_w64, stripS_adv],
                  by simpa using execFrozen_setPermNonFrozen hfr _ _ Perm.protNone rfl, rfl⟩
              · split
                · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
                · rw [strip_setPermNonFrozen hfr _ _ Perm.rw rfl]
                  exact ⟨by simp [stripS_smem, stripS_spma, stripS_w64, stripS_adv],
                    by simpa using execFrozen_setPermNonFrozen hfr _ _ Perm.rw rfl, rfl⟩

private theorem execMremap_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execMremap (stripS keep s) = stripS keep (execMremap s) ∧
    ExecFrozen (execMremap s).mem ∧ (execMremap s).fs = s.fs := by
  have hnf := strip_allPerm_eq (keep := keep) (m := s.mem) (p := fun q => !q.frozen)
    (fun a => congrArg Bool.not (strip_perm_frozen (keep := keep) hfr a))
  have hrw := strip_allPerm_eq (keep := keep) (m := s.mem) (p := (· == some Perm.rw))
    (fun a => by
      cases h1 : ((stripExecOutside keep s.mem).perm a == some Perm.rw) <;>
        cases h2 : (s.mem.perm a == some Perm.rw)
      · rfl
      · exfalso
        exact Bool.eq_false_iff.mp h1
          (beq_iff_eq.mpr ((strip_perm_props keep s.mem a).2.2.2.mpr (beq_iff_eq.mp h2)))
      · exfalso
        exact Bool.eq_false_iff.mp h2
          (beq_iff_eq.mpr ((strip_perm_props keep s.mem a).2.2.2.mp (beq_iff_eq.mp h1)))
      · rfl)
  refine ⟨?_, ?_, ?_⟩
  · unfold execMremap
    dsimp only
    simp (config := { instances := true }) only
      [stripS_r64, stripS_mem, stripS_pma, stripS_orc, stripS_oi, hnf, hrw,
       strip_canMap, strip_allAnon, strip_unmapNonFrozen hfr, strip_sanitizeMmapAddr,
       strip_remapRw hfr, stripS_smem, stripS_spma, stripS_norc, stripS_w64, stripS_adv,
       stripS_sst, stripS_ite]
    cases sanitizeMmapAddr
        (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat))
        (s.oracle.mmap s.oracleIdx)
        (pageAlignUp (s.readReg64 Reg.x2).toNat) with
    | none =>
      dsimp only
      simp (config := { instances := true }) only [stripS_ite]
    | some _ =>
      dsimp only
      simp (config := { instances := true }) only [stripS_ite]
  · unfold execMremap
    dsimp only
    repeat' apply execFrozen_ite (by simpa using hfr)
    cases sanitizeMmapAddr
        (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat))
        (s.oracle.mmap s.oracleIdx)
        (pageAlignUp (s.readReg64 Reg.x2).toNat) with
    | none => simpa using hfr
    | some newBase =>
      dsimp only
      exact execFrozen_ite (by simpa using hfr)
        (by dsimp only [State.advancePC, State.writeReg64, State.nextOracle, State.setPhysMemAvail,
              State.setMem]; exact execFrozen_remapRw hfr _ _ _ _)
  · unfold execMremap
    dsimp only
    cases sanitizeMmapAddr
        (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat))
        (s.oracle.mmap s.oracleIdx)
        (pageAlignUp (s.readReg64 Reg.x2).toNat) <;>
      simp [state_fs_ite]

private theorem execMadvise_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execMadvise (stripS keep s) = stripS keep (execMadvise s) ∧
    ExecFrozen (execMadvise s).mem ∧ (execMadvise s).fs = s.fs := by
  unfold execMadvise
  have hnf := strip_allPerm_eq (keep := keep) (m := s.mem) (p := fun q => !q.frozen)
    (fun a => congrArg Bool.not (strip_perm_frozen (keep := keep) hfr a))
  have hmp := strip_allPerm_eq (keep := keep) (m := s.mem)
    (fun a => (strip_perm_props keep s.mem a).2.2.1)
  simp only [stripS_r64, stripS_mem, hnf, hmp, strip_canMap, strip_allAnon,
    strip_zeroNonFrozen hfr, strip_madvFreeNonFrozen hfr]
  split
  · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
  · split
    · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
    · split
      · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
      · split
        · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
        · split
          · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
          · split
            · split
              · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩
              · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
            · split
              · exact ⟨by simp [stripS_sst], by simpa using hfr, rfl⟩
              · split
                · exact ⟨by simp [stripS_smem, stripS_w64, stripS_adv],
                    by simpa using execFrozen_zeroNonFrozen hfr _ _, rfl⟩
                · split
                  · exact ⟨by simp [stripS_smem, stripS_w64, stripS_adv],
                      by simpa using execFrozen_madvFreeNonFrozen hfr _ _, rfl⟩
                  · exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr, rfl⟩

/-- `allocMallocng` (`brk`, `munmap`, `mremap`, `mmap`, `mprotect(PROT_RW)`, `madvise`) commutes
    with `stripS keep`, preserves `ExecFrozen`, and preserves `State.fs`. -/
theorem allocMallocng_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    allocMallocng (stripS keep s) = stripS keep (allocMallocng s) ∧
    ExecFrozen (allocMallocng s).mem ∧ (allocMallocng s).fs = s.fs := by
  unfold allocMallocng
  simp only [stripS_r64]
  split
  · exact ⟨stripS_sst keep s _, by simpa using hfr, rfl⟩
  · unfold Syscall.alloc Syscall.dispatch Syscall.allocTable
    simp only [List.find?_cons, stripS_r64]
    by_cases h1 : (SYS_BRK == s.readReg64 Reg.x8) = true
    · simp only [h1]; exact execBrk_stripS hfr
    · simp only [h1]
      by_cases h2 : (SYS_MUNMAP == s.readReg64 Reg.x8) = true
      · simp only [h2]; exact execMunmap_stripS hfr
      · simp only [h2]
        by_cases h3 : (SYS_MREMAP == s.readReg64 Reg.x8) = true
        · simp only [h3]; exact execMremap_stripS hfr
        · simp only [h3]
          by_cases h4 : (SYS_MMAP == s.readReg64 Reg.x8) = true
          · simp only [h4]; exact execMmap_stripS hfr
          · simp only [h4]
            by_cases h5 : (SYS_MPROTECT == s.readReg64 Reg.x8) = true
            · simp only [h5]; exact execMprotect_stripS hfr
            · simp only [h5]
              by_cases h6 : (SYS_MADVISE == s.readReg64 Reg.x8) = true
              · simp only [h6]; exact execMadvise_stripS hfr
              · simp only [h6, List.find?_nil]
                exact ⟨stripS_sst keep s _, by simpa using hfr, rfl⟩

private theorem execInst_preserves_execFrozen {inst : Instr} (h : inst.isSvc0 = false)
    {s : State} (hfr : ExecFrozen s.mem) :
    ExecFrozen (execInst inst s).mem ∧ (execInst inst s).fs = s.fs := by
  have hpf := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 h s
  exact ⟨ExecFrozen.of_perm_eq hfr (congrFun hpf.2.1), hpf.2.2.2.2.2.2⟩

/-! ## 2. Lifting `Steps (P_alloc.withSvc allocMallocng)` on `stripS` to `StepsUntil P_real` -/

private theorem codeLoaded_strip_progKeep {prog : Program} {m : Memory}
    (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside (progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hin : progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [strip_read8, strip_perm_of_keep hin, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem step_running {P : Program} {s s' : State} (h : Step P s s') :
    s.status = .Running := by
  cases h <;> assumption

private theorem steps_start_running_or_oom {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running ∨ sf.status = .OutOfMemory) :
    s.status = .Running ∨ s.status = .OutOfMemory := by
  cases h with
  | refl => exact hr
  | step h1 _ => exact Or.inl (step_running h1)

private theorem strip_read16 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read16 a = m.read16 a := by
  simp [Memory.read16, strip_read8]

private theorem strip_read32 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read32 a = m.read32 a := by
  simp [Memory.read32, strip_read8]

private theorem strip_read64 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read64 a = m.read64 a := by
  simp [Memory.read64, strip_read8]

private theorem strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat),
      (stripExecOutside keep m).readBytes a n = m.readBytes a n
  | _, 0 => rfl
  | a, n + 1 => by
    simp only [Memory.readBytes, strip_read8, strip_readBytes keep m (a + 1#64) n]

private theorem strip_readCStringAux (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (ptr : BitVec 64) (fuel : Nat) (acc : List Char),
      readCStringAux (stripExecOutside keep m) ptr fuel acc = readCStringAux m ptr fuel acc
  | _, 0, _ => rfl
  | ptr, fuel + 1, acc => by
    simp only [readCStringAux, (strip_perm_props keep m ptr).1, strip_canRead, strip_read8]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · exact strip_readCStringAux keep m (ptr + 1#64) fuel _

private theorem strip_readCString (keep : BitVec 64 → Bool) (m : Memory) (ptr : BitVec 64) :
    readCString (stripExecOutside keep m) ptr = readCString m ptr :=
  strip_readCStringAux keep m ptr _ []

private theorem execFrozen_write8 {m : Memory} (hfr : ExecFrozen m)
    (addr : BitVec 64) (val : BitVec 8) :
    ExecFrozen (m.write8 addr val) := by
  intro a hx
  unfold Memory.write8 Memory.rawPerm at hx ⊢
  rw [perm_mk_cells] at hx ⊢
  by_cases ha : a = addr
  · subst ha
    simp only [↓reduceIte] at hx ⊢
    have hfr_a := hfr a
    unfold Memory.perm at hfr_a
    cases hc : m.cells a with
    | none => simp [hc, Option.x] at hx
    | some cb =>
      rw [hc] at hx hfr_a
      rcases cb with ⟨_ | p, b⟩
      · simp [Option.x] at hx
      · rcases p with ⟨r, w, x, lf, an⟩
        dsimp only [Perm.rwx, Option.x, Option.r, Option.w] at hx hfr_a ⊢
        exact hfr_a hx
  · simp only [ha, ↓reduceIte] at hx ⊢
    exact hfr a hx

private theorem execFrozen_write16 {m : Memory} (hfr : ExecFrozen m)
    (addr : BitVec 64) (val : BitVec 16) :
    ExecFrozen (m.write16 addr val) :=
  execFrozen_write8 (execFrozen_write8 hfr _ _) _ _

private theorem strip_writeBytes (keep : BitVec 64 → Bool) :
    ∀ (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)),
      (stripExecOutside keep m).writeBytes base bs = stripExecOutside keep (m.writeBytes base bs)
  | _, _, [] => rfl
  | m, base, b :: rest => by
    simp only [Memory.writeBytes, strip_write8, strip_writeBytes keep (m.write8 base b) _ rest]

private theorem execFrozen_writeBytes :
    ∀ {m : Memory}, ExecFrozen m → ∀ (base : BitVec 64) (bs : List (BitVec 8)),
      ExecFrozen (m.writeBytes base bs)
  | _, hfr, _, [] => hfr
  | _, hfr, base, b :: rest =>
    execFrozen_writeBytes (execFrozen_write8 hfr base b) (base + 1#64) rest

private theorem strip_evalPpollEntries (keep : BitVec 64 → Bool) (fs : FsState)
    (ufds : BitVec 64) :
    ∀ (rem : Nat) (m : Memory) (idx count : Nat),
      evalPpollEntries fs (stripExecOutside keep m) ufds rem idx count =
        (evalPpollEntries fs m ufds rem idx count).map
          (fun mc => (stripExecOutside keep mc.1, mc.2))
  | 0, _, _, _ => rfl
  | rem + 1, m, idx, count => by
    simp only [evalPpollEntries, strip_read32, strip_read16]
    split
    · rfl
    · cases fs.fds _ with
      | none =>
        dsimp only
        rw [strip_write16]
        exact strip_evalPpollEntries keep fs ufds rem _ _ _
      | some desc =>
        dsimp only
        split
        · rw [strip_write16]
          exact strip_evalPpollEntries keep fs ufds rem _ _ _
        · rfl

private theorem execFrozen_evalPpollEntries (fs : FsState) (ufds : BitVec 64) :
    ∀ (rem : Nat) {m m' : Memory} (idx count count' : Nat),
      ExecFrozen m →
      evalPpollEntries fs m ufds rem idx count = some (m', count') →
      ExecFrozen m'
  | 0, _, _, _, _, _, hfr, h => by
    cases h; exact hfr
  | rem + 1, m, m', idx, count, count', hfr, h => by
    unfold evalPpollEntries at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · exact execFrozen_evalPpollEntries fs ufds rem _ _ _ (execFrozen_write16 hfr _ _) h
      · split at h
        · exact execFrozen_evalPpollEntries fs ufds rem _ _ _ (execFrozen_write16 hfr _ _) h
        · cases h

private theorem stripS_r32 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (stripS keep s).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem stripS_sfs (keep : BitVec 64 → Bool) (s : State) (fs : FsState) :
    (stripS keep s).setFs fs = stripS keep (s.setFs fs) := by cases s; rfl
private theorem stripS_appTr (keep : BitVec 64 → Bool) (s : State) (evs : List TraceEvent) :
    (stripS keep s).appendTrace evs = stripS keep (s.appendTrace evs) := by cases s; rfl
private theorem stripS_gsa (keep : BitVec 64 → Bool) (s : State) (sig : BitVec 32) :
    (stripS keep s).getSigAction sig = s.getSigAction sig := by cases s; rfl
private theorem stripS_ssa (keep : BitVec 64 → Bool) (s : State) (sig : BitVec 32) (sa : SigAction) :
    (stripS keep s).setSigAction sig sa = stripS keep (s.setSigAction sig sa) := by cases s; rfl
private theorem stripS_sas (keep : BitVec 64 → Bool) (s : State) :
    (stripS keep s).sigAltStack = s.sigAltStack := by cases s; rfl
private theorem stripS_ssas (keep : BitVec 64 → Bool) (s : State) (sas : SigAltStack) :
    (stripS keep s).setSigAltStack sas = stripS keep (s.setSigAltStack sas) := by cases s; rfl

private theorem execReadCommon_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) (usePos : Bool) :
    execReadCommon (stripS keep s) usePos = stripS keep (execReadCommon s usePos) ∧
    ExecFrozen (execReadCommon s usePos).mem := by
  refine ⟨?_, ?_⟩
  · dsimp (config := { zetaHave := true }) only [execReadCommon]
    simp (config := { instances := true }) only
      [stripS_r32, stripS_r64, stripS_fs, stripS_mem, strip_canWrite, strip_writeBytes,
       stripS_w64, stripS_adv, stripS_sst, stripS_smem, stripS_sfs, stripS_ite]
    cases s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) <;>
      (dsimp only; simp (config := { instances := true }) only [stripS_ite])
  · have hite : ∀ {c : Prop} [inst : Decidable c] {a b : Memory},
        ExecFrozen a → ExecFrozen b → ExecFrozen (if c then a else b) := by
      intro c inst a b ha hb; cases inst <;> assumption
    dsimp (config := { zetaHave := true }) only [execReadCommon]
    cases s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) <;>
      (dsimp only
       simp [state_mem_ite]
       repeat' apply hite
       all_goals first
         | exact hfr
         | exact execFrozen_writeBytes hfr _ _)

private theorem execRead_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execRead (stripS keep s) = stripS keep (execRead s) ∧ ExecFrozen (execRead s).mem :=
  execReadCommon_stripS hfr false

private theorem execPread64_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execPread64 (stripS keep s) = stripS keep (execPread64 s) ∧ ExecFrozen (execPread64 s).mem :=
  execReadCommon_stripS hfr true

private theorem execWrite_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execWrite (stripS keep s) = stripS keep (execWrite s) ∧ ExecFrozen (execWrite s).mem := by
  have hr := strip_allPerm_eq (keep := keep) (m := s.mem) (p := (·.r))
    (fun a => (strip_perm_props keep s.mem a).1)
  refine ⟨?_, ?_⟩
  · dsimp (config := { zetaHave := true }) only [execWrite]
    simp (config := { instances := true }) only
      [stripS_r32, stripS_r64, stripS_fs, stripS_mem, hr, strip_canRead, strip_readBytes,
       stripS_sfs, stripS_appTr, stripS_w64, stripS_adv, stripS_sst, stripS_ite]
    cases s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
    | none =>
      dsimp only
      simp (config := { instances := true }) only [stripS_ite]
    | some _ =>
      dsimp only
      simp (config := { instances := true }) only
        [stripS_ite]
  · suffices (execWrite s).mem = s.mem by rw [this]; exact hfr
    dsimp (config := { zetaHave := true }) only [execWrite]
    cases s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) <;>
      simp [state_mem_ite]

private theorem rwvMapInv_stripS (keep : BitVec 64 → Bool) :
    LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.RwvMapInv
      (stripS keep) (fun s => ExecFrozen s.mem) where
  readReg64 := stripS_r64 keep
  readReg32 := stripS_r32 keep
  status := stripS_status keep
  fs := stripS_fs keep
  allPermR s a n := by
    rw [stripS_mem]
    exact strip_allPerm_eq (keep := keep) (m := s.mem) (p := (·.r))
      (fun x => (strip_perm_props keep s.mem x).1) a n
  canRead s a n := by
    rw [stripS_mem]
    exact strip_canRead keep s.mem a n
  read64 s a := by
    rw [stripS_mem]
    exact strip_read64 keep s.mem a
  writeReg64 := stripS_w64 keep
  advancePC := stripS_adv keep
  setStatus := stripS_sst keep
  regsPc s s0 := by cases s; cases s0; rfl
  inv_writeReg64 := fun {s} r _ hfr => by cases s; cases r <;> exact hfr
  inv_advancePC := fun {s} hfr => by cases s; exact hfr
  inv_setStatus := fun {s} _ hfr => by cases s; exact hfr
  inv_regsPc := fun {s} _ _ hfr => by cases s; exact hfr

private theorem execReadv_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execReadv (stripS keep s) = stripS keep (execReadv s) ∧ ExecFrozen (execReadv s).mem :=
  LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execReadv_map_inv
    (rwvMapInv_stripS keep) (fun _ hx => execRead_stripS hx) s hfr

private theorem execWritev_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execWritev (stripS keep s) = stripS keep (execWritev s) ∧ ExecFrozen (execWritev s).mem :=
  LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execWritev_map_inv
    (rwvMapInv_stripS keep) (fun _ hx => execWrite_stripS hx) s hfr

private theorem execLseek_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execLseek (stripS keep s) = stripS keep (execLseek s) ∧ ExecFrozen (execLseek s).mem := by
  dsimp (config := { zetaHave := true }) only [execLseek]
  simp only [stripS_r32, stripS_r64, stripS_fs]
  repeat' split
  repeat' split
  all_goals exact ⟨by simp [stripS_w64, stripS_adv, stripS_sst, stripS_sfs], by simpa using hfr⟩

private theorem execFcntl_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execFcntl (stripS keep s) = stripS keep (execFcntl s) ∧ ExecFrozen (execFcntl s).mem := by
  unfold execFcntl
  dsimp only
  simp only [stripS_r32, stripS_r64, stripS_fs]
  repeat' split
  all_goals exact ⟨by simp [stripS_w64, stripS_adv, stripS_sst, stripS_sfs], by simpa using hfr⟩

private theorem execIoctl_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execIoctl (stripS keep s) = stripS keep (execIoctl s) ∧ ExecFrozen (execIoctl s).mem := by
  unfold execIoctl
  dsimp only
  simp only [stripS_r32, stripS_r64, stripS_fs, stripS_mem, strip_canWrite, strip_writeBytes]
  repeat' split
  all_goals first
    | exact ⟨by simp [stripS_w64, stripS_adv, stripS_sst, stripS_sfs], by simpa using hfr⟩
    | exact ⟨by simp [stripS_smem, stripS_w64, stripS_adv],
        by simpa using execFrozen_writeBytes hfr _ _⟩

private theorem applyOpenVerdict_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) (v : OpenVerdict) :
    applyOpenVerdict (stripS keep s) v = stripS keep (applyOpenVerdict s v) ∧
    ExecFrozen (applyOpenVerdict s v).mem := by
  cases v with
  | opened fd fs' ch? =>
    cases ch? <;>
      exact ⟨by simp [applyOpenVerdict, stripS_sfs, stripS_appTr, stripS_w64, stripS_adv],
        by simpa [applyOpenVerdict] using hfr⟩
  | errno err =>
    exact ⟨by simp [applyOpenVerdict, stripS_w64, stripS_adv], by simpa [applyOpenVerdict] using hfr⟩
  | trap msg =>
    exact ⟨by simp [applyOpenVerdict, stripS_sst], by simpa [applyOpenVerdict] using hfr⟩

private theorem execOpenat_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execOpenat (stripS keep s) = stripS keep (execOpenat s) ∧ ExecFrozen (execOpenat s).mem := by
  unfold execOpenat
  dsimp only
  simp only [stripS_r32, stripS_r64, stripS_mem, stripS_fs, strip_readCString]
  cases checkOpenFlags (s.readReg32 Reg.x2) with
  | some v => exact applyOpenVerdict_stripS hfr v
  | none =>
    cases readCString s.mem (s.readReg64 Reg.x1) with
    | trap msg => exact ⟨by simp [stripS_sst], by simpa using hfr⟩
    | errno err => exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr⟩
    | ok rawPath => exact applyOpenVerdict_stripS hfr _

private theorem execClose_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execClose (stripS keep s) = stripS keep (execClose s) ∧ ExecFrozen (execClose s).mem := by
  unfold execClose
  dsimp only
  simp only [stripS_r32, stripS_fs]
  repeat' split
  all_goals exact ⟨by simp [stripS_w64, stripS_adv, stripS_sst, stripS_sfs], by simpa using hfr⟩

private theorem execFstat_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execFstat (stripS keep s) = stripS keep (execFstat s) ∧ ExecFrozen (execFstat s).mem := by
  unfold execFstat
  dsimp only
  simp only [stripS_r32, stripS_r64, stripS_fs, stripS_mem, strip_canWrite, strip_writeBytes]
  repeat' split
  all_goals first
    | exact ⟨by simp [stripS_w64, stripS_adv, stripS_sst], by simpa using hfr⟩
    | exact ⟨by simp [stripS_smem, stripS_w64, stripS_adv],
        by simpa using execFrozen_writeBytes hfr _ _⟩

private theorem execPpoll_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execPpoll (stripS keep s) = stripS keep (execPpoll s) ∧ ExecFrozen (execPpoll s).mem := by
  have hr := strip_allPerm_eq (keep := keep) (m := s.mem) (p := (·.r))
    (fun a => (strip_perm_props keep s.mem a).1)
  refine ⟨?_, ?_⟩
  · unfold execPpoll
    dsimp only
    simp (config := { instances := true }) only
      [stripS_r64, stripS_r32, stripS_fs, stripS_mem, hr, strip_canRead, strip_read64,
       strip_canWrite, strip_evalPpollEntries, stripS_w64, stripS_adv,
       stripS_sst]
    cases evalPpollEntries s.fs s.mem (s.readReg64 Reg.x0) (s.readReg32 Reg.x1).toNat 0 0 with
    | none =>
      dsimp only [Option.map]
      simp (config := { instances := true }) only [stripS_ite]
    | some mc =>
      rcases mc with ⟨m', count⟩
      dsimp only [Option.map]
      simp (config := { instances := true }) only
        [stripS_smem, stripS_w64, stripS_adv, stripS_ite]
  · unfold execPpoll
    dsimp only
    repeat' apply execFrozen_ite (by simpa using hfr)
    cases hev : evalPpollEntries s.fs s.mem (s.readReg64 Reg.x0) (s.readReg32 Reg.x1).toNat 0 0 with
    | none => simpa using hfr
    | some mc =>
      rcases mc with ⟨m', count⟩
      dsimp only
      exact execFrozen_ite (by simpa using hfr)
        (by dsimp only [State.advancePC, State.writeReg64, State.setMem]
            exact execFrozen_evalPpollEntries s.fs _ _ 0 0 count hfr hev)

private theorem execExit_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execExit (stripS keep s) = stripS keep (execExit s) ∧ ExecFrozen (execExit s).mem := by
  unfold execExit
  exact ⟨by simp [stripS_r64, stripS_sst], by simpa using hfr⟩

private theorem execTkill_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execTkill (stripS keep s) = stripS keep (execTkill s) ∧ ExecFrozen (execTkill s).mem := by
  unfold execTkill
  dsimp only
  simp only [stripS_r32, stripS_gsa]
  repeat' split
  all_goals exact ⟨by simp [stripS_w64, stripS_adv, stripS_sst], by simpa using hfr⟩

private theorem execTgkill_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    execTgkill (stripS keep s) = stripS keep (execTgkill s) ∧ ExecFrozen (execTgkill s).mem := by
  unfold execTgkill
  dsimp only
  simp only [stripS_r32, stripS_gsa]
  repeat' split
  all_goals exact ⟨by simp [stripS_w64, stripS_adv, stripS_sst], by simpa using hfr⟩

private theorem execRtSigprocmask_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) :
    execRtSigprocmask (stripS keep s) = stripS keep (execRtSigprocmask s) ∧
    ExecFrozen (execRtSigprocmask s).mem := by
  have hr := strip_allPerm_eq (keep := keep) (m := s.mem) (p := (·.r))
    (fun a => (strip_perm_props keep s.mem a).1)
  refine ⟨?_, ?_⟩
  · unfold execRtSigprocmask
    dsimp only
    simp (config := { instances := true }) only
      [stripS_r32, stripS_r64, stripS_mem, hr, strip_canRead, strip_read64, strip_canWrite,
       strip_writeBytes, stripS_smem, stripS_w64, stripS_adv, stripS_sst, stripS_ite]
  · unfold execRtSigprocmask
    dsimp only
    repeat' apply execFrozen_ite (by simpa using hfr)
    dsimp only [State.advancePC, State.writeReg64, State.setMem]
    exact execFrozen_writeBytes hfr _ _

private theorem execSigaltstack_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) :
    execSigaltstack (stripS keep s) = stripS keep (execSigaltstack s) ∧
    ExecFrozen (execSigaltstack s).mem := by
  have hr := strip_allPerm_eq (keep := keep) (m := s.mem) (p := (·.r))
    (fun a => (strip_perm_props keep s.mem a).1)
  have hmem_ssas : ∀ sas, (s.setSigAltStack sas).mem = s.mem := fun _ => rfl
  refine ⟨?_, ?_⟩
  · unfold execSigaltstack
    dsimp only
    simp (config := { instances := true }) only
      [stripS_r64, stripS_mem, stripS_sas, stripS_sp, hr, strip_canRead, strip_read64,
       strip_read32, stripS_ssas, strip_canWrite, strip_writeBytes, stripS_smem,
       stripS_w64, stripS_adv, stripS_sst, stripS_ite]
  · unfold execSigaltstack
    dsimp only
    repeat' apply execFrozen_ite (by simpa [state_mem_ite, hmem_ssas] using hfr)
    dsimp only [State.advancePC, State.writeReg64, State.setMem]
    simp only [state_mem_ite, hmem_ssas, ite_self]
    exact execFrozen_writeBytes hfr _ _

private theorem execRtSigaction_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) :
    execRtSigaction (stripS keep s) = stripS keep (execRtSigaction s) ∧
    ExecFrozen (execRtSigaction s).mem := by
  have hr := strip_allPerm_eq (keep := keep) (m := s.mem) (p := (·.r))
    (fun a => (strip_perm_props keep s.mem a).1)
  have hmem_ssa : ∀ sig sa, (s.setSigAction sig sa).mem = s.mem := fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · unfold execRtSigaction
    dsimp only
    simp (config := { instances := true }) only
      [stripS_r32, stripS_r64, stripS_mem, stripS_gsa, hr, strip_canRead, strip_read64,
       stripS_ssa, strip_canWrite, strip_writeBytes, stripS_smem,
       stripS_w64, stripS_adv, stripS_sst, stripS_ite]
  · unfold execRtSigaction
    dsimp only
    repeat' apply execFrozen_ite (by simpa [state_mem_ite, hmem_ssa] using hfr)
    dsimp only [State.advancePC, State.writeReg64, State.setMem]
    simp only [state_mem_ite, hmem_ssa, ite_self]
    exact execFrozen_writeBytes hfr _ _

private theorem execClockGettime_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) :
    execClockGettime (stripS keep s) = stripS keep (execClockGettime s) ∧
    ExecFrozen (execClockGettime s).mem := by
  unfold execClockGettime
  dsimp only
  simp only [stripS_r32, stripS_r64, stripS_mem, stripS_orc, stripS_oi,
    strip_canWrite, strip_writeBytes]
  repeat' split
  all_goals first
    | exact ⟨by simp [stripS_w64, stripS_adv, stripS_sst], by simpa using hfr⟩
    | exact ⟨by simp [stripS_smem, stripS_norc, stripS_w64, stripS_adv],
        by simpa using execFrozen_writeBytes hfr _ _⟩

private theorem execGetrandom_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) :
    execGetrandom (stripS keep s) = stripS keep (execGetrandom s) ∧
    ExecFrozen (execGetrandom s).mem := by
  unfold execGetrandom
  dsimp only
  simp only [stripS_r32, stripS_r64, stripS_mem, stripS_orc, stripS_oi,
    strip_canWrite, strip_writeBytes]
  repeat' split
  all_goals first
    | exact ⟨by simp [stripS_w64, stripS_adv], by simpa using hfr⟩
    | exact ⟨by simp [stripS_smem, stripS_norc, stripS_w64, stripS_adv],
        by simpa using execFrozen_writeBytes hfr _ _⟩

private theorem execSetTidAddress_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) :
    execSetTidAddress (stripS keep s) = stripS keep (execSetTidAddress s) ∧
    ExecFrozen (execSetTidAddress s).mem :=
  ⟨by simp [execSetTidAddress, stripS_w64, stripS_adv], by simpa [execSetTidAddress] using hfr⟩

private theorem execGetpid_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) :
    execGetpid (stripS keep s) = stripS keep (execGetpid s) ∧
    ExecFrozen (execGetpid s).mem :=
  ⟨by simp [execGetpid, stripS_w64, stripS_adv], by simpa [execGetpid] using hfr⟩

private theorem execSchedGetaffinity_stripS {keep : BitVec 64 → Bool} {s : State}
    (hfr : ExecFrozen s.mem) :
    execSchedGetaffinity (stripS keep s) = stripS keep (execSchedGetaffinity s) ∧
    ExecFrozen (execSchedGetaffinity s).mem := by
  unfold execSchedGetaffinity
  dsimp only
  simp only [stripS_r32, stripS_r64, stripS_mem, strip_canWrite, strip_writeBytes]
  repeat' split
  all_goals first
    | exact ⟨by simp [stripS_w64, stripS_adv, stripS_sst], by simpa using hfr⟩
    | exact ⟨by simp [stripS_smem, stripS_w64, stripS_adv],
        by simpa using execFrozen_writeBytes hfr _ _⟩

private theorem dispatch_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    ∀ (tbl : List (BitVec 64 × (State → State))),
      (∀ p ∈ tbl, p.2 (stripS keep s) = stripS keep (p.2 s) ∧ ExecFrozen (p.2 s).mem) →
      Syscall.dispatch tbl (stripS keep s) = stripS keep (Syscall.dispatch tbl s) ∧
      ExecFrozen (Syscall.dispatch tbl s).mem
  | [], _ => ⟨stripS_sst keep s _, by simpa [Syscall.dispatch] using hfr⟩
  | (nr, fn) :: rest, htbl => by
    unfold Syscall.dispatch
    simp only [List.find?_cons, stripS_r64]
    by_cases h : (nr == s.readReg64 Reg.x8) = true
    · simp only [h]
      exact htbl (nr, fn) (List.mem_cons_self ..)
    · simp only [h]
      exact dispatch_stripS hfr rest (fun p hp => htbl p (List.mem_cons_of_mem _ hp))

/-- All 31 modeled Linux AArch64 syscalls (`Syscall.standard`) commute with `stripS keep` and
    preserve `ExecFrozen`. -/
theorem standard_stripS {keep : BitVec 64 → Bool} {s : State} (hfr : ExecFrozen s.mem) :
    Syscall.standard (stripS keep s) = stripS keep (Syscall.standard s) ∧
    ExecFrozen (Syscall.standard s).mem := by
  unfold Syscall.standard
  refine dispatch_stripS hfr Syscall.standardTable ?_
  intro p hp
  simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
    Syscall.randomTable, Syscall.miscTable, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with ((((((hp | hp) | hp) | hp) | hp) | hp) | hp) | hp
  · rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact execRead_stripS hfr
    · exact execWrite_stripS hfr
    · exact execReadv_stripS hfr
    · exact execWritev_stripS hfr
    · exact execExit_stripS hfr
    · exact execExit_stripS hfr
  · rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact execFcntl_stripS hfr
    · exact execIoctl_stripS hfr
    · exact execOpenat_stripS hfr
    · exact execClose_stripS hfr
    · exact execLseek_stripS hfr
    · exact execPread64_stripS hfr
    · exact execFstat_stripS hfr
  · subst hp; exact execPpoll_stripS hfr
  · rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(execBrk_stripS (keep := keep) hfr).1, (execBrk_stripS (keep := keep) hfr).2.1⟩
    · exact ⟨(execMunmap_stripS (keep := keep) hfr).1, (execMunmap_stripS (keep := keep) hfr).2.1⟩
    · exact ⟨(execMremap_stripS (keep := keep) hfr).1, (execMremap_stripS (keep := keep) hfr).2.1⟩
    · exact ⟨(execMmap_stripS (keep := keep) hfr).1, (execMmap_stripS (keep := keep) hfr).2.1⟩
    · exact ⟨(execMprotect_stripS (keep := keep) hfr).1, (execMprotect_stripS (keep := keep) hfr).2.1⟩
    · exact ⟨(execMadvise_stripS (keep := keep) hfr).1, (execMadvise_stripS (keep := keep) hfr).2.1⟩
  · rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact execTkill_stripS hfr
    · exact execTgkill_stripS hfr
    · exact execSigaltstack_stripS hfr
    · exact execRtSigaction_stripS hfr
    · exact execRtSigprocmask_stripS hfr
  · subst hp; exact execClockGettime_stripS hfr
  · subst hp; exact execGetrandom_stripS hfr
  · rcases hp with rfl | rfl | rfl | rfl
    · exact execSetTidAddress_stripS hfr
    · exact execSchedGetaffinity_stripS hfr
    · exact execGetpid_stripS hfr
    · exact execGetpid_stripS hfr

private theorem subroutineStop_stripS_iff {keep : BitVec 64 → Bool} {s0 s : State} :
    SubroutineStop s0 (stripS keep s) ↔ SubroutineStop s0 s := by
  simp [SubroutineStop, Returned, stripS_pc, stripS_sp, stripS_status]

private theorem steps_preserves_halted {P : Program} {u v : State}
    (hs : Steps P u v) (hu : u.status = .Halted) : v.status = .Halted := by
  induction hs with
  | refl => exact hu
  | step hs1 _ ihs => cases hs1 <;> simp_all

private theorem steps_preserves_exception {P : Program} {u v : State} {msg : String}
    (hs : Steps P u v) (hu : u.status = .Exception msg) : v.status = .Exception msg := by
  induction hs with
  | refl => exact hu
  | step hs1 _ ihs => cases hs1 <;> simp_all

/-- Lift a `Steps P_sub` trace from `stripS keep s1` ending in `SubroutineStop s0 sf'` (with
    `sf'.status ≠ .Halted`) to a **first-stop** `StepsUntil P_real (SubroutineStop s0) s1 sf`
    trace on unmodified `s1` whenever `keep (s0.readReg64 .lr) = false`, `P_sub.svc = Syscall.standard`,
    `P_real.svc = Syscall.standard`, `P_real` has no extern hooks inside `keep`, and any extern hook
    of `P_sub` also sits at the same address in `P_real`, differs from `lr`, and commutes with
    `stripS keep` while preserving `ExecFrozen`, `KeepsFrozen`, and `symtab`. -/
theorem stepsUntil_of_stripS_standard
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {s0 : State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hext_comm : ∀ (pc : BitVec 64) (f : State → State),
      P_sub.externAt? pc = some f →
      P_real.externAt? pc = some f ∧
      pc ≠ s0.readReg64 .lr ∧
      (∀ st : State, ExecFrozen st.mem →
        f (stripS keep st) = stripS keep (f st) ∧
        ExecFrozen (f st).mem ∧
        st.mem.KeepsFrozen (f st).mem ∧
        (f st).symtab = st.symtab))
    (hlr_out : keep (s0.readReg64 .lr) = false)
    {s1' sf' : State}
    (hsteps : Steps P_sub s1' sf')
    (hstop' : SubroutineStop s0 sf')
    (hnhalt' : sf'.status ≠ .Halted) :
    ∀ s1 : State,
      s1' = stripS keep s1 →
      ExecFrozen s1.mem →
      ∃ sf : State,
        StepsUntil P_real (SubroutineStop s0) s1 sf ∧
        SubroutineStop s0 sf ∧
        sf' = stripS keep sf ∧
        ExecFrozen sf.mem := by
  induction hsteps with
  | refl s' =>
    intro s1 hs1 hfr1
    have hstop1 : SubroutineStop s0 s1 := subroutineStop_stripS_iff.mp (hs1 ▸ hstop')
    exact ⟨s1, StepsUntil.refl s1, hstop1, hs1, hfr1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro sa hsa hfra
    by_cases hstop_sa : SubroutineStop s0 sa
    · rcases hstop_sa with ⟨hpc_lr, _⟩ | hpan | ⟨_, hex⟩ | hoom
      · cases h1 with
        | @exec inst hr' hfm' =>
          rw [hsa, stripS_pc, stripS_mem] at hfm'
          unfold Program.fetchMem at hfm'
          cases he : P_sub.externAt? sa.pc with
          | some f => simp [he] at hfm'
          | none =>
            simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
            by_cases hal : sa.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
              by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
              · have hx0 : ((stripExecOutside keep sa.mem).perm sa.pc).x = true := by
                  have h4 :
                      ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                      ((stripExecOutside keep sa.mem).allPerm (·.x) (sa.pc + 1#64) 3) = true := by
                    simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true] using hce'
                  exact h4.1
                have hkp := (strip_perm_x_imp hx0).2
                rw [hpc_lr, hlr_out] at hkp
                cases hkp
              · simp [hce'] at hfm'
            · simp [hal] at hfm'
        | halt_unmapped _ _ _ =>
          exact False.elim (hnhalt' (steps_preserves_halted hrest rfl))
        | extern _ he _ _ =>
          rw [hsa, stripS_pc] at he
          exact False.elim ((hext_comm sa.pc _ he).2.1 hpc_lr)
        | extern_fault _ he _ =>
          rw [hsa, stripS_pc] at he
          exact False.elim ((hext_comm sa.pc _ he).2.1 hpc_lr)
      · have hr_sa : sa.status = .Running := by
          have h := step_running h1
          rwa [hsa, stripS_status] at h
        rw [hpan] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := step_running h1
          rwa [hsa, stripS_status] at h
        rw [hex] at hr_sa; cases hr_sa
      · have hr_sa : sa.status = .Running := by
          have h := step_running h1
          rwa [hsa, stripS_status] at h
        rw [hoom] at hr_sa; cases hr_sa
    · cases h1 with
      | halt_unmapped _ _ _ =>
        exact False.elim (hnhalt' (steps_preserves_halted hrest rfl))
      | @extern f hr' he' _ _ =>
        have hra : sa.status = .Running := by rw [hsa, stripS_status] at hr'; exact hr'
        rw [hsa, stripS_pc] at he'
        obtain ⟨he_real, _, hf_comm⟩ := hext_comm sa.pc f he'
        obtain ⟨hf_eq, hfr_f, hkf_f, hsym_f⟩ := hf_comm sa hfra
        have hstep_real : Step P_real sa (f sa) := Step.extern hra he_real hkf_f hsym_f
        rw [hsa, hf_eq] at hrest ih
        obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
          ih hstop' hnhalt' (f sa) rfl hfr_f
        exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest,
          hstop_sf, hsf_eq, hfr_sf⟩
      | extern_fault _ _ _ =>
        have hsf_ex := steps_preserves_exception hrest rfl
        rcases hstop' with ⟨_, _, hr_sf⟩ | hpan | ⟨_, hex⟩ | hoom
        · rw [hsf_ex] at hr_sf; cases hr_sf
        · rw [hsf_ex] at hpan; cases hpan
        · rw [hsf_ex] at hex; cases hex
        · rw [hsf_ex] at hoom; cases hoom
      | @exec inst hr' hfm' =>
        have hra : sa.status = .Running := by
          rw [hsa, stripS_status] at hr'; exact hr'
        rw [hsa, stripS_pc, stripS_mem] at hfm'
        unfold Program.fetchMem at hfm'
        cases he_sub : P_sub.externAt? sa.pc with
        | some f => simp [he_sub] at hfm'
        | none =>
          simp only [he_sub, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
          by_cases hal_pc : sa.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
            by_cases hce' : (stripExecOutside keep sa.mem).canExec sa.pc 4 = true
            · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
              have hx4 :
                  ((stripExecOutside keep sa.mem).perm sa.pc).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 1#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 2#64)).x = true ∧
                  ((stripExecOutside keep sa.mem).perm (sa.pc + 3#64)).x = true := by
                simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
              obtain ⟨hx0, hkp0⟩ := strip_perm_x_imp hx4.1
              obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
              obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
              obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
              have hce : sa.mem.canExec sa.pc 4 = true := by
                simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
              rw [strip_read32] at hfm'
              have hext_real : P_real.externAt? sa.pc = none := hreal_no sa.pc hkp0
              have hfm_real : P_real.fetchMem sa.mem sa.pc = some inst := by
                unfold Program.fetchMem
                simp [hext_real, hal_pc, hce, hfm']
              by_cases hsvc0 : inst.isSvc0 = true
              · have hinst : inst = .system false 0#16 := by
                  cases inst <;> simp [Instr.isSvc0] at hsvc0
                  rcases hsvc0 with ⟨rfl, rfl⟩; rfl
                subst hinst
                obtain ⟨hcomm, hfr_sb⟩ := standard_stripS (keep := keep) hfra
                have hev_strip :
                    P_sub.evalInst (.system false 0#16) (stripS keep sa) =
                      stripS keep (Syscall.standard sa) := by
                  simp [Program.evalInst, execInstWithSvc, hsvc_sub, hcomm]
                have hev_real :
                    P_real.evalInst (.system false 0#16) sa = Syscall.standard sa := by
                  simp [Program.evalInst, execInstWithSvc, hsvc_real]
                have hstep_real : Step P_real sa (Syscall.standard sa) :=
                  hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                  ih hstop' hnhalt' (Syscall.standard sa) rfl hfr_sb
                exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest,
                  hstop_sf, hsf_eq, hfr_sf⟩
              · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
                have hev_strip :
                    P_sub.evalInst inst (stripS keep sa) =
                      stripS keep (execInst inst sa) := by
                  rw [evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0, execInst_stripS hnsvc0]
                have hev_real : P_real.evalInst inst sa = execInst inst sa :=
                  evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 sa
                obtain ⟨hfr_sb, _⟩ := execInst_preserves_execFrozen hnsvc0 hfra
                have hstep_real : Step P_real sa (execInst inst sa) :=
                  hev_real ▸ Step.exec hra hfm_real
                rw [hsa, hev_strip] at hrest ih
                obtain ⟨sf, huntil_rest, hstop_sf, hsf_eq, hfr_sf⟩ :=
                  ih hstop' hnhalt' (execInst inst sa) rfl hfr_sb
                exact ⟨sf, StepsUntil.step hstop_sa hstep_real huntil_rest,
                  hstop_sf, hsf_eq, hfr_sf⟩
            · simp [hce'] at hfm'
          · simp [hal_pc] at hfm'

/-! ## 3. `linkedGhostBudget`, `*Mallocng` Hook Lifts, & `need_locks` Split -/

/-- Unified `fineCostModel` `RustCliAllocBudget` combining an arbitrary auxiliary code-RO witness
    `allocLib.codeRO allocMpl` (for `rdl_shim` / thunk span fallback hooks) with
    `fineHookRustCliAllocBudget γ mmpl tp brkStart` (`VerifiedLibraries.mallocngLib.codeRO mmpl` +
    `fineRustCliAllocBudget` + `CodeBlocksPermRX`). Its `repAlloc` is `rfl`-equal to
    `fineRustCliAllocBudget γ mmpl tp brkStart`, so all `vecU8At` / `vecGhostAt` / store-kit
    invariants match `fineRustCliAllocBudget` definitionally. -/
noncomputable def linkedGhostBudget (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    RustCliAllocBudget fineCostModel :=
  let base := fineHookRustCliAllocBudget γ mmpl tp brkStart
  { pool := fun lim st s => allocLib.codeRO allocMpl ∗ base.pool lim st s
    live := base.live
    block_valid := base.block_valid
    pool_transport := fun lim st s s' hvm =>
      congrArg (allocLib.codeRO allocMpl ∗ ·) (base.pool_transport lim st s s' hvm)
    pool_zero_transport := fun st s s' hp =>
      congrArg (allocLib.codeRO allocMpl ∗ ·) (base.pool_zero_transport st s s' hp) }

@[simp]
theorem linkedGhostBudget_repAlloc (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart).repAlloc =
      (fineRustCliAllocBudget γ mmpl tp brkStart).repAlloc :=
  rfl

/-- `(mallocngAddrsOfPlacement mmpl).libc` is definitionally `mmpl.ρ "__libc"`. -/
theorem mallocngAddrsOfPlacement_libc_eq (mmpl : Obj.MultiPlacement) :
    (mallocngAddrsOfPlacement mmpl).libc = mmpl.ρ "__libc" :=
  rfl

/-- Projects `(((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗ anyHeap` out of
    `(linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart).pool lim st s` for `exit` cleanup. -/
theorem linkedGhostPool_entails_needLocks_anyHeap
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : FineBudget) (s : State) :
    (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart).pool lim st s ⊢
      (((mallocngAddrsOfPlacement mmpl).libc + 3#64) ↦₈ 0#8) ∗ anyHeap := by
  let A := mallocngAddrsOfPlacement mmpl
  change allocLib.codeRO allocMpl ∗
      (VerifiedLibraries.mallocngLib.codeRO mmpl ∗
        mallocngBudgetPoolAt fineCostModel fineCostModelIface γ A tp brkStart lim st s ∗
        ⌜lim.enforced = true → CodeBlocksPermRX mmpl s⌝) ⊢
    ((A.libc + 3#64) ↦₈ 0#8) ∗ anyHeap
  rw [mallocngBudgetPoolAt_split_runtime fineCostModelSound γ A tp brkStart lim st s]
  unfold MallocngRuntime
  have hEq :
      allocLib.codeRO allocMpl ∗
        (VerifiedLibraries.mallocngLib.codeRO mmpl ∗
          ((∃∗ staticIvs : List (BitVec 64 × Nat),
            ∃∗ ivs : List (BitVec 64 × Nat),
              ⌜mallocngBudgetPoolInv lim staticIvs ivs s ∧ s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
              fineCostModelIface.CoreM γ A brkStart s.brk st ivs) ∗
            ((∃∗ errnoVal : BitVec 32, (tp - 0xa4#64) ↦₃₂ errnoVal) ∗
              ((A.libc + 3#64) ↦₈ 0#8) ∗
              ((A.libc + 48#64) ↦₆₄ 4096#64))) ∗
          ⌜lim.enforced = true → CodeBlocksPermRX mmpl s⌝) =
      ((A.libc + 3#64) ↦₈ 0#8) ∗
        (allocLib.codeRO allocMpl ∗ VerifiedLibraries.mallocngLib.codeRO mmpl ∗
          ((∃∗ staticIvs : List (BitVec 64 × Nat),
            ∃∗ ivs : List (BitVec 64 × Nat),
              ⌜mallocngBudgetPoolInv lim staticIvs ivs s ∧ s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
              fineCostModelIface.CoreM γ A brkStart s.brk st ivs) ∗
            (∃∗ errnoVal : BitVec 32, (tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            ((A.libc + 48#64) ↦₆₄ 4096#64)) ∗
          ⌜lim.enforced = true → CodeBlocksPermRX mmpl s⌝) := by
    sep_ac_rfl
  rw [hEq]
  exact sepConj_mono_right (entails_anyHeap _)

private theorem strip_rwBytes (keep : BitVec 64 → Bool) (m : Memory) :
    rwBytes (stripExecOutside keep m) = rwBytes m := by
  unfold ProofLib.rwBytes
  exact strip_countRw keep m 0#64 (2 ^ 64)

private theorem strip_physPlusRw (keep : BitVec 64 → Bool) (s : State) :
    physPlusRw (stripS keep s) = physPlusRw s := by
  unfold ProofLib.physPlusRw
  simp only [stripS_pma, stripS_mem, strip_rwBytes]

private theorem strip_staticMappedCover (keep : BitVec 64 → Bool)
    (lim : BudgetLimits) (staticIvs ivs : List (BitVec 64 × Nat)) (m : Memory) :
    StaticMappedCover lim staticIvs ivs (stripExecOutside keep m) =
      StaticMappedCover lim staticIvs ivs m := by
  apply propext
  unfold StaticMappedCover
  simp only [(strip_perm_props keep m _).2.2.1]

private theorem strip_mallocngBudgetPoolAt (keep : BitVec 64 → Bool)
    (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (A : VerifiedLibraries.Mallocng.MallocngAddrs) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    mallocngBudgetPoolAt M I γ A tp brkStart lim st (stripS keep s) =
      mallocngBudgetPoolAt M I γ A tp brkStart lim st s := by
  have hinv : ∀ staticIvs ivs,
      mallocngBudgetPoolInv lim staticIvs ivs (stripS keep s) =
        mallocngBudgetPoolInv lim staticIvs ivs s := by
    intro staticIvs ivs
    apply propext
    unfold mallocngBudgetPoolInv
    simp only [stripS_mem, strip_staticMappedCover, strip_physPlusRw]
  unfold mallocngBudgetPoolAt MallocngModelEnv
  simp only [hinv, stripS_brkStart, stripS_brk]
  cases s; rfl

/-- Under `keep` retaining all `mallocngLib` code-block bytes (`mmpl`), `CodeBlocksPermRX mmpl`
    is invariant under `stripS keep`, so `linkedGhostBudget.pool` is equal on `stripS keep s`
    and `s`. -/
theorem linkedGhostBudget_pool_stripS
    {keep : BitVec 64 → Bool}
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) (st : fineCostModel.σ) (s : State) :
    (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart).pool lim st (stripS keep s) =
      (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart).pool lim st s := by
  have hPermRX : CodeBlocksPermRX mmpl (stripS keep s) = CodeBlocksPermRX mmpl s := by
    apply propext
    unfold CodeBlocksPermRX CodeBlocksPermRXMem
    constructor <;> intro h a ha
    · have ha' := h a ha
      rwa [stripS_mem, strip_perm_of_keep (hKeepMallocng a ha)] at ha'
    · rw [stripS_mem, strip_perm_of_keep (hKeepMallocng a ha)]
      exact h a ha
  change allocLib.codeRO allocMpl ∗
      (VerifiedLibraries.mallocngLib.codeRO mmpl ∗
        mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
          tp brkStart lim st (stripS keep s) ∗
        ⌜lim.enforced = true → CodeBlocksPermRX mmpl (stripS keep s)⌝) =
    allocLib.codeRO allocMpl ∗
      (VerifiedLibraries.mallocngLib.codeRO mmpl ∗
        mallocngBudgetPoolAt fineCostModel fineCostModelIface γ (mallocngAddrsOfPlacement mmpl)
          tp brkStart lim st s ∗
        ⌜lim.enforced = true → CodeBlocksPermRX mmpl s⌝)
  rw [strip_mallocngBudgetPoolAt, hPermRX]

/-- Generic `HookOk` framing lemma adding an invariant read-only assertion `Extra` to `A.pool`
    whenever `spec`'s `onPanic`, `onExit`, and `onOom` branches do not retain `Extra`. -/
theorem hookOk_frame_extra {α : Type} {f : State → State}
    {spec0 spec1 : Spec α} (Extra : SepProp)
    (h0 : HookOk f spec0)
    (hpre : ∀ x s, spec1.pre x s ⊢ spec0.pre x s ∗ Extra)
    (hpost : ∀ x s0 sf, spec0.post x s0 sf ∗ Extra ⊢ spec1.post x s0 sf)
    (hpan : ∀ x s0 sf, spec0.onPanic x s0 sf ⊢ spec1.onPanic x s0 sf)
    (hexit : ∀ x c s0 sf, spec0.onExit x c s0 sf ⊢ spec1.onExit x c s0 sf)
    (hoom : ∀ x s0 sf, spec0.onOom x s0 sf ⊢ spec1.onOom x s0 sf) :
    HookOk f spec1 := by
  intro x R s0 hrun hm0 hsp
  have hm0' : s0.mem ⊨ spec0.pre x s0 ∗ (Extra ∗ R) :=
    Satisfies.mono (Entails.trans (sepConj_mono_left (hpre x s0)) (Entails.of_eq (by sep_ac_rfl))) hm0
  obtain ⟨hkf, hsym, hout⟩ := h0 x (Extra ∗ R) s0 hrun hm0' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hst, hp⟩ | ⟨c, hst, hp⟩ | ⟨hst, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    exact Satisfies.mono
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left (hpost x s0 (f s0)))) hp
  · refine Or.inr (Or.inl ⟨hst, ?_⟩)
    have hp' : (f s0).mem ⊨ (spec0.onPanic x s0 (f s0) ∗ R) ∗ Extra :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 (f s0))) (Satisfies.of_sep_left hp')
  · refine Or.inr (Or.inr (Or.inl ⟨c, hst, ?_⟩))
    have hp' : (f s0).mem ⊨ (spec0.onExit x c s0 (f s0) ∗ R) ∗ Extra :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
    exact Satisfies.mono (sepConj_mono_left (hexit x c s0 (f s0))) (Satisfies.of_sep_left hp')
  · refine Or.inr (Or.inr (Or.inr ⟨hst, ?_⟩))
    have hp' : (f s0).mem ⊨ (spec0.onOom x s0 (f s0) ∗ R) ∗ Extra :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
    exact Satisfies.mono (sepConj_mono_left (hoom x s0 (f s0))) (Satisfies.of_sep_left hp')

/-- Generic `subroutine_ok` framing lemma adding an invariant read-only assertion `Extra` to
    `A.pool` whenever `spec`'s `onPanic`, `onExit`, and `onOom` branches do not retain `Extra`. -/
theorem subroutine_ok_frame_extra {α : Type} {P : Program} {entry : BitVec 64}
    {spec0 spec1 : Spec α} (Extra : SepProp)
    (h0 : subroutine_ok P entry spec0)
    (hpre : ∀ x s, spec1.pre x s ⊢ spec0.pre x s ∗ Extra)
    (hpost : ∀ x s0 sf, spec0.post x s0 sf ∗ Extra ⊢ spec1.post x s0 sf)
    (hpan : ∀ x s0 sf, spec0.onPanic x s0 sf ⊢ spec1.onPanic x s0 sf)
    (hexit : ∀ x c s0 sf, spec0.onExit x c s0 sf ⊢ spec1.onExit x c s0 sf)
    (hoom : ∀ x s0 sf, spec0.onOom x s0 sf ⊢ spec1.onOom x s0 sf) :
    subroutine_ok P entry spec1 := by
  apply subroutine_ok_of_steps_outcome
  intro x R s0 hpc hrun hm0 hsp hcl
  have hm0' : s0.mem ⊨ spec0.pre x s0 ∗ (Extra ∗ R) :=
    Satisfies.mono (Entails.trans (sepConj_mono_left (hpre x s0)) (Entails.of_eq (by sep_ac_rfl))) hm0
  obtain ⟨sf, hsteps, hout⟩ := subroutine_ok_elim_steps_outcome h0 x (Extra ∗ R) s0 hpc hrun hm0' hsp hcl
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hret, hcc, hp⟩ | ⟨hst, hp⟩ | ⟨c, hst, hp⟩ | ⟨hst, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    exact Satisfies.mono
      (Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono_left (hpost x s0 sf))) hp
  · refine Or.inr (Or.inl ⟨hst, ?_⟩)
    have hp' : sf.mem ⊨ (spec0.onPanic x s0 sf ∗ R) ∗ Extra :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) (Satisfies.of_sep_left hp')
  · refine Or.inr (Or.inr (Or.inl ⟨c, hst, ?_⟩))
    have hp' : sf.mem ⊨ (spec0.onExit x c s0 sf ∗ R) ∗ Extra :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
    exact Satisfies.mono (sepConj_mono_left (hexit x c s0 sf)) (Satisfies.of_sep_left hp')
  · refine Or.inr (Or.inr (Or.inr ⟨hst, ?_⟩))
    have hp' : sf.mem ⊨ (spec0.onOom x s0 sf ∗ R) ∗ Extra :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
    exact Satisfies.mono (sepConj_mono_left (hoom x s0 sf)) (Satisfies.of_sep_left hp')

/-- Frame `allocLib.codeRO allocMpl` onto `rustCliAllocBudgetSpecBase` (`zeroed = false`/`true`). -/
theorem linkedGhostAlloc_subroutine_ok
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    {P : Program} {entry : BitVec 64} (lim : BudgetLimits) (zeroed : Bool)
    (h0 : subroutine_ok P entry
      (rustCliAllocBudgetSpecBase fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim zeroed)) :
    subroutine_ok P entry
      (rustCliAllocBudgetSpecBase fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim zeroed) := by
  refine subroutine_ok_frame_extra (allocLib.codeRO allocMpl) h0
    (fun ⟨sz, al, st⟩ s => Entails.of_eq (by
      dsimp [rustCliAllocBudgetSpecBase, linkedGhostBudget]; sep_ac_rfl))
    (fun ⟨sz, al, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
  dsimp [rustCliAllocBudgetSpecBase, linkedGhostBudget]
  refine Entails.of_eq ?_
  by_cases h0z : sf.readReg64 .x0 = 0#64
  · simp only [h0z, ↓reduceIte]; sep_ac_rfl
  · simp only [h0z, ↓reduceIte]; sep_ac_rfl

/-- Frame `allocLib.codeRO allocMpl` onto `rustCliDeallocBudgetSpecBase`. -/
theorem linkedGhostDealloc_subroutine_ok
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    {P : Program} {entry : BitVec 64} (lim : BudgetLimits)
    (h0 : subroutine_ok P entry
      (rustCliDeallocBudgetSpecBase fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :
    subroutine_ok P entry
      (rustCliDeallocBudgetSpecBase fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) :=
  subroutine_ok_frame_extra (allocLib.codeRO allocMpl) h0
    (fun ⟨ptr, sz, al, st⟩ s => Entails.of_eq (by
      dsimp [rustCliDeallocBudgetSpecBase, linkedGhostBudget]; sep_ac_rfl))
    (fun ⟨ptr, sz, al, st⟩ s0 sf => Entails.of_eq (by
      dsimp [rustCliDeallocBudgetSpecBase, linkedGhostBudget]; sep_ac_rfl))
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)

/-- Frame `allocLib.codeRO allocMpl` onto `rustCliReallocBudgetSpecBase`. -/
theorem linkedGhostRealloc_subroutine_ok
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    {P : Program} {entry : BitVec 64} (lim : BudgetLimits)
    (h0 : subroutine_ok P entry
      (rustCliReallocBudgetSpecBase fineCostModel (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim)) :
    subroutine_ok P entry
      (rustCliReallocBudgetSpecBase fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) := by
  refine subroutine_ok_frame_extra (allocLib.codeRO allocMpl) h0
    (fun ⟨ptr, oldSz, al, newSz, bs, st⟩ s => Entails.of_eq (by
      dsimp [rustCliReallocBudgetSpecBase, linkedGhostBudget]; sep_ac_rfl))
    (fun ⟨ptr, oldSz, al, newSz, bs, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
  dsimp [rustCliReallocBudgetSpecBase, linkedGhostBudget]
  refine Entails.of_eq ?_
  by_cases h0z : sf.readReg64 .x0 = 0#64
  · simp only [h0z, ↓reduceIte]; sep_ac_rfl
  · simp only [h0z, ↓reduceIte]; sep_ac_rfl

/-- Lift `fineHookRustCliAllocBudgetEntries_thunks` (`__rust_{alloc,dealloc,realloc}`) to
    `linkedGhostBudget`. -/
theorem linkedGhostAllocEntries_thunks
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    {P : Program} {mmpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mmpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mmpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) P thunkAddrs := by
  have hBase := fineHookRustCliAllocBudgetEntries_thunks hP γ tp brkStart hThunks hShims hMemcpy
  exact
    { alloc := fun lim =>
        linkedGhostAlloc_subroutine_ok allocLib allocMpl γ mmpl tp brkStart lim false
          (hBase.alloc lim)
      dealloc := fun lim =>
        linkedGhostDealloc_subroutine_ok allocLib allocMpl γ mmpl tp brkStart lim
          (hBase.dealloc lim)
      realloc := fun lim =>
        linkedGhostRealloc_subroutine_ok allocLib allocMpl γ mmpl tp brkStart lim
          (hBase.realloc lim) }

/-- Lift `fineHookRustCliAllocZeroedBudget_thunk_ok` (`__rust_alloc_zeroed`) to
    `linkedGhostBudget`. -/
theorem linkedGhostAllocZeroed_thunk_ok
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    {P : Program} {mmpl : Obj.MultiPlacement}
    (hP : ProgContainsMallocng P mmpl)
    (γ : GhostName) (tp brkStart thunkAddr rdlAddr memsetAddr : BitVec 64)
    (lim : BudgetLimits)
    (hThunk : hasInstrs P thunkAddr [ .b (rdlAddr - thunkAddr) ])
    (hCode : hasInstrs P rdlAddr
      (rdlAllocZeroedInstrs rdlAddr (VerifiedLibraries.mallocngLib.fnAddr mmpl "calloc")
        (mallocngPlacedCAddrs mmpl).posixMemalign memsetAddr))
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec) :
    subroutine_ok P thunkAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) :=
  linkedGhostAlloc_subroutine_ok allocLib allocMpl γ mmpl tp brkStart lim true
    (fineHookRustCliAllocZeroedBudget_thunk_ok hP γ tp brkStart thunkAddr rdlAddr memsetAddr lim
      hThunk hCode hMemset)

/-- Swapped F3 crypto hook `aesEncHookMallocng mmpl E` lifted to `linkedGhostBudget`. -/
theorem linkedGhostAesEnc_hookOk
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (E : AesKey → Block → Block) :
    HookOk (aesEncHookMallocng mmpl E)
      (aesEncBudgetSpec E fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) := by
  refine hookOk_frame_extra (allocLib.codeRO allocMpl)
    (fineAesEnc_budget_hookOk γ tp brkStart lim hPl E)
    (fun ⟨c, st⟩ s => Entails.of_eq (by
      dsimp [aesEncBudgetSpec, aesCallPreBudget, linkedGhostBudget]; sep_ac_rfl))
    (fun ⟨c, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
  dsimp [aesEncBudgetSpec, linkedGhostBudget]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Swapped F3 crypto hook `aesDecHookMallocng mmpl D` lifted to `linkedGhostBudget`. -/
theorem linkedGhostAesDec_hookOk
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mmpl D)
      (aesDecBudgetSpec D fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) := by
  refine hookOk_frame_extra (allocLib.codeRO allocMpl)
    (fineAesDec_budget_hookOk γ tp brkStart lim hPl D)
    (fun ⟨c, st⟩ s => Entails.of_eq (by
      dsimp [aesDecBudgetSpec, aesCallPreBudget, linkedGhostBudget]; sep_ac_rfl))
    (fun ⟨c, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
  dsimp [aesDecBudgetSpec, linkedGhostBudget]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Swapped F3 crypto hook `aesDecHookMallocng mmpl D` (`aesDecWeakBudgetSpec`) lifted to
    `linkedGhostBudget`. -/
theorem linkedGhostAesDecWeak_hookOk
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (D : AesKey → Block → Block) :
    HookOk (aesDecHookMallocng mmpl D)
      (aesDecWeakBudgetSpec D fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) := by
  refine hookOk_frame_extra (allocLib.codeRO allocMpl)
    (fineAesDecWeak_budget_hookOk γ tp brkStart lim hPl D)
    (fun ⟨c, st⟩ s => Entails.of_eq (by
      dsimp [aesDecWeakBudgetSpec, aesDecFnBudgetSpec, aesCallPreBudget, linkedGhostBudget]
      sep_ac_rfl))
    (fun ⟨c, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
  dsimp [aesDecWeakBudgetSpec, aesDecFnBudgetSpec, linkedGhostBudget]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Swapped F3 crypto hook `libcruxHmacHookMallocng mmpl F` lifted to `linkedGhostBudget`. -/
theorem linkedGhostLibcruxHmac_hookOk
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (F : ShaState → List (BitVec 8) → ShaState) :
    HookOk (libcruxHmacHookMallocng mmpl F)
      (libcruxHmacBudgetSpec F fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) := by
  refine hookOk_frame_extra (allocLib.codeRO allocMpl)
    (fineLibcruxHmac_budget_hookOk γ tp brkStart lim hPl F)
    (fun ⟨c, st⟩ s => Entails.of_eq (by
      dsimp [libcruxHmacBudgetSpec, linkedGhostBudget]; sep_ac_rfl))
    (fun ⟨c, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
  dsimp [libcruxHmacBudgetSpec, linkedGhostBudget]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Hook-mode `stringCloneHookMallocng mmpl` lifted to `linkedGhostBudget`. -/
theorem linkedGhostStringClone_hookOk [LibsignalPlacement]
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mmpl) :
    HookOk (stringCloneHookMallocng mmpl)
      (stringCloneBudgetSpec fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) := by
  refine hookOk_frame_extra (allocLib.codeRO allocMpl)
    (fineStringClone_budget_hookOk γ tp brkStart lim hPl)
    (fun ⟨p, ret, g, st⟩ s => Entails.of_eq (by
      dsimp [stringCloneBudgetSpec, linkedGhostBudget]; sep_ac_rfl))
    (fun ⟨p, ret, g, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
  dsimp [stringCloneBudgetSpec, linkedGhostBudget]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Program-mode `<String as Clone>::clone` (`libsignalSessionLib` block `623`) lifted to
    `linkedGhostBudget`. -/
theorem linkedGhostStringClone_of_hasInstrs_ok [LibsignalPlacement]
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) {mmpl : Obj.MultiPlacement} (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {P : Program} {allocAddrs : RustAllocAddrs}
    {fnAddr shimAddr memcpyAddr handleErrorAddr : BitVec 64}
    (hCode : hasInstrs P fnAddr
      (rustStringCloneInstrs fnAddr shimAddr allocAddrs.alloc memcpyAddr handleErrorAddr))
    (hAlloc : RustCliAllocBudgetEntriesBase fineCostModel
      (fineHookRustCliAllocBudget γ mmpl tp brkStart) P allocAddrs)
    (hAux : RustStdAllocAuxEntries P shimAddr memcpyAddr handleErrorAddr) :
    subroutine_ok P fnAddr
      (stringCloneBudgetSpec fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) := by
  refine subroutine_ok_frame_extra (allocLib.codeRO allocMpl)
    (rustStringCloneBudget_of_hasInstrs_ok (fineHookRustCliAllocBudget γ mmpl tp brkStart) lim
      hCode hAlloc hAux)
    (fun ⟨p, ret, g, st⟩ s => Entails.of_eq (by
      dsimp [stringCloneBudgetSpec, linkedGhostBudget]; sep_ac_rfl))
    (fun ⟨p, ret, g, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.refl _)
    (fun _ _ _ _ => Entails.refl _)
    (fun _ _ _ => Entails.refl _)
  dsimp [stringCloneBudgetSpec, linkedGhostBudget]
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 4. Terminating `linkedCallHook`, Ghost-Hook Overlay `cliGhostExterns`, & Bundle Constructors -/

/-- Specification invariance under `stripS keep`: holds for `rustCliAllocBudgetSpec`,
    `rustCliDeallocBudgetSpec`, `rustCliReallocBudgetSpec`, `rustAllocZeroedBudgetSpec`, and
    `stringCloneBudgetSpec` at `linkedGhostBudget` whenever `keep` retains `mallocngLib`'s code
    bytes (`linkedGhostBudget_pool_stripS`). -/
structure SpecStripSInvariant {α : Type} (keep : BitVec 64 → Bool) (spec : Spec α) : Prop where
  pre_eq : ∀ x s, spec.pre x (stripS keep s) = spec.pre x s
  post_eq : ∀ x s0 sf, spec.post x (stripS keep s0) (stripS keep sf) = spec.post x s0 sf
  onPanic_eq : ∀ x s0 sf, spec.onPanic x (stripS keep s0) (stripS keep sf) = spec.onPanic x s0 sf
  onExit_eq : ∀ x c s0 sf, spec.onExit x c (stripS keep s0) (stripS keep sf) = spec.onExit x c s0 sf
  onOom_eq : ∀ x s0 sf, spec.onOom x (stripS keep s0) (stripS keep sf) = spec.onOom x s0 sf

/-- `SpecStripSInvariant` for `rustCliAllocBudgetSpec` (`zeroed = false`/`true`) at
    `linkedGhostBudget`. -/
theorem specStripSInvariant_alloc [LibsignalPlacement] {keep : BitVec 64 → Bool}
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) (zeroed : Bool) :
    SpecStripSInvariant keep
      (rustCliAllocBudgetSpec fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim zeroed) where
  pre_eq := fun ⟨_, _, _⟩ s => by
    dsimp [rustCliAllocBudgetSpec]
    rw [linkedGhostBudget_pool_stripS allocLib allocMpl γ mmpl tp brkStart hKeepMallocng]
    cases s; rfl
  post_eq := fun ⟨_, _, _⟩ s0 sf => by
    dsimp [rustCliAllocBudgetSpec]
    simp only [stripS_r64,
      linkedGhostBudget_pool_stripS allocLib allocMpl γ mmpl tp brkStart hKeepMallocng]
    cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun ⟨_, _, _⟩ s0 sf => by
    dsimp [rustCliAllocBudgetSpec]
    cases s0; cases sf; rfl

/-- `SpecStripSInvariant` for `rustCliDeallocBudgetSpec` at `linkedGhostBudget`. -/
theorem specStripSInvariant_dealloc [LibsignalPlacement] {keep : BitVec 64 → Bool}
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) :
    SpecStripSInvariant keep
      (rustCliDeallocBudgetSpec fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) where
  pre_eq := fun ⟨_, _, _, _⟩ s => by
    dsimp [rustCliDeallocBudgetSpec]
    rw [linkedGhostBudget_pool_stripS allocLib allocMpl γ mmpl tp brkStart hKeepMallocng]
    cases s; rfl
  post_eq := fun ⟨_, _, _, _⟩ s0 sf => by
    dsimp [rustCliDeallocBudgetSpec]
    rw [linkedGhostBudget_pool_stripS allocLib allocMpl γ mmpl tp brkStart hKeepMallocng]
    cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

/-- `SpecStripSInvariant` for `rustCliReallocBudgetSpec` at `linkedGhostBudget`. -/
theorem specStripSInvariant_realloc [LibsignalPlacement] {keep : BitVec 64 → Bool}
    (allocLib : Obj.MultiPlacedLib) (allocMpl : Obj.MultiPlacement)
    (γ : GhostName) (mmpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (lim : BudgetLimits) :
    SpecStripSInvariant keep
      (rustCliReallocBudgetSpec fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim) where
  pre_eq := fun ⟨_, _, _, _, _, _⟩ s => by
    dsimp [rustCliReallocBudgetSpec]
    rw [linkedGhostBudget_pool_stripS allocLib allocMpl γ mmpl tp brkStart hKeepMallocng]
    cases s; rfl
  post_eq := fun ⟨_, _, _, _, _, _⟩ s0 sf => by
    dsimp [rustCliReallocBudgetSpec]
    simp only [stripS_r64,
      linkedGhostBudget_pool_stripS allocLib allocMpl γ mmpl tp brkStart hKeepMallocng]
    cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun ⟨_, _, _, _, _, _⟩ s0 sf => by
    dsimp [rustCliReallocBudgetSpec]
    cases s0; cases sf; rfl

theorem specPreservesFsTraceExact_allocBase {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) :
    ∀ x R s0 sf,
      SubroutineOutcome (rustCliAllocBudgetSpecBase M A lim zeroed) x R s0 sf →
        sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  intro ⟨sz, al, st⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp [rustCliAllocBudgetSpecBase] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.1, hpost.1.2.1⟩
  · dsimp [rustCliAllocBudgetSpecBase] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp [rustCliAllocBudgetSpecBase] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp [rustCliAllocBudgetSpecBase] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact ⟨hoom.1.2.1, hoom.1.2.2.1⟩

theorem specPreservesFsTraceExact_deallocBase {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    ∀ x R s0 sf,
      SubroutineOutcome (rustCliDeallocBudgetSpecBase M A lim) x R s0 sf →
        sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  intro ⟨ptr, sz, al, st⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp [rustCliDeallocBudgetSpecBase] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.1.1, hpost.1.1.2.1⟩
  · dsimp [rustCliDeallocBudgetSpecBase] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp [rustCliDeallocBudgetSpecBase] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp [rustCliDeallocBudgetSpecBase] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem specPreservesFsTraceExact_reallocBase {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    ∀ x R s0 sf,
      SubroutineOutcome (rustCliReallocBudgetSpecBase M A lim) x R s0 sf →
        sf.fs = s0.fs ∧ sf.trace = s0.trace := by
  intro ⟨ptr, oldSz, al, newSz, bs, st⟩ R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp [rustCliReallocBudgetSpecBase] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.1, hpost.1.2.1⟩
  · dsimp [rustCliReallocBudgetSpecBase] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp [rustCliReallocBudgetSpecBase] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp [rustCliReallocBudgetSpecBase] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact ⟨hoom.1.2.1, hoom.1.2.2.1⟩

theorem specPreservesFsTraceExact_alloc [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (zeroed : Bool) :
    ∀ x R s0 sf,
      SubroutineOutcome (rustCliAllocBudgetSpec M A lim zeroed) x R s0 sf →
        sf.fs = s0.fs ∧ sf.trace = s0.trace :=
  specPreservesFsTraceExact_allocBase A lim zeroed

theorem specPreservesFsTraceExact_dealloc [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    ∀ x R s0 sf,
      SubroutineOutcome (rustCliDeallocBudgetSpec M A lim) x R s0 sf →
        sf.fs = s0.fs ∧ sf.trace = s0.trace :=
  specPreservesFsTraceExact_deallocBase A lim

theorem specPreservesFsTraceExact_realloc [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    ∀ x R s0 sf,
      SubroutineOutcome (rustCliReallocBudgetSpec M A lim) x R s0 sf →
        sf.fs = s0.fs ∧ sf.trace = s0.trace :=
  specPreservesFsTraceExact_reallocBase A lim

/-- Every `SubroutineOutcome` of `spec` preserves `State.fs` and `FsTraced IsFsC`. -/
def SpecPreservesFsTrace {α : Type} (spec : Spec α) : Prop :=
  ∀ (x : α) (R : SepProp) (s0 sf : State),
    SubroutineOutcome spec x R s0 sf → sf.fs = s0.fs ∧ FsTraced IsFsC s0 sf

theorem specPreservesFsTrace_alloc [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (zeroed : Bool) :
    SpecPreservesFsTrace (rustCliAllocBudgetSpec M A lim zeroed) := by
  intro x R s0 sf hout
  obtain ⟨hfs, htr⟩ := specPreservesFsTraceExact_alloc A lim zeroed x R s0 sf hout
  exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩

theorem specPreservesFsTrace_dealloc [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    SpecPreservesFsTrace (rustCliDeallocBudgetSpec M A lim) := by
  intro x R s0 sf hout
  obtain ⟨hfs, htr⟩ := specPreservesFsTraceExact_dealloc A lim x R s0 sf hout
  exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩

theorem specPreservesFsTrace_realloc [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    SpecPreservesFsTrace (rustCliReallocBudgetSpec M A lim) := by
  intro x R s0 sf hout
  obtain ⟨hfs, htr⟩ := specPreservesFsTraceExact_realloc A lim x R s0 sf hout
  exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩

/-- Terminating fallback wrapper preserving `s0.fs` and `s0.trace` unconditionally for
    `HookFsTraced IsFsC` and `AllocContractsFsPlaced`, while agreeing with `fallback s0` whenever
    `(fallback s0).fs = s0.fs ∧ (fallback s0).trace = s0.trace` (which holds on every valid
    `SubroutineOutcome` of `rustCli{Alloc,Dealloc,Realloc}BudgetSpec`). -/
def keepFsTrace (fallback : State → State) (s0 : State) : State :=
  let sf := fallback s0
  { sf with fs := s0.fs, trace := s0.trace }

theorem keepFsTrace_fs (fallback : State → State) (s0 : State) :
    (keepFsTrace fallback s0).fs = s0.fs := rfl

theorem keepFsTrace_trace (fallback : State → State) (s0 : State) :
    (keepFsTrace fallback s0).trace = s0.trace := rfl

theorem keepFsTrace_fsT (fallback : State → State) :
    HookFsTraced IsFsC (keepFsTrace fallback) :=
  fun _ => FsTraced.of_eq rfl rfl

theorem keepFsTrace_ok {α : Type} {fallback : State → State} {spec : Spec α}
    (hfb : HookOk fallback spec)
    (hFsTrace : ∀ x R s0,
      SubroutineOutcome spec x R s0 (fallback s0) →
        (fallback s0).fs = s0.fs ∧ (fallback s0).trace = s0.trace) :
    HookOk (keepFsTrace fallback) spec := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hfb x R s0 hrun hpre hsp
  obtain ⟨hfs, htr⟩ := hFsTrace x R s0 hout
  have heq : keepFsTrace fallback s0 = fallback s0 := by
    unfold keepFsTrace
    cases h : fallback s0
    rw [h] at hfs htr
    dsimp only at hfs htr ⊢
    subst hfs htr
    rfl
  rw [heq]
  exact ⟨hkf, hsym, hout⟩

/-- Entry precondition witness for `linkedCallHook`. -/
def ActiveRealPre {α : Type} (spec : Spec α) (s0 : State) : Prop :=
  s0.status = .Running ∧ s0.spAligned = true ∧ ∃ (x : α) (R : SepProp), s0.mem ⊨ spec.pre x s0 ∗ R

/-- Active real-code execution witness for `linkedCallHook`: `s0.mem` is `ExecFrozen`, caller `lr`
    lies outside `keep` (`keep (s0.readReg64 .lr) = false`), `P_sub` is loaded inside `keep`, and
    the real program `P_real` reaches a first `SubroutineStop s0` state `sf` from `s0.setPC entryTarget`
    while preserving `State.fs`, `FsTraced IsFsC`, and `ExecFrozen`. -/
def ActiveRealRun (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (s0 : State) : Prop :=
  ExecFrozen s0.mem ∧ keep (s0.readReg64 .lr) = false ∧
  P_sub.CodeLoaded (stripExecOutside keep s0.mem) ∧
  ∃ sf : State,
    StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
    SubroutineStop s0 sf ∧ sf.fs = s0.fs ∧ FsTraced IsFsC s0 sf ∧ ExecFrozen sf.mem

open Classical in
/-- Total ghost-hook constructor for an unhooked real-code subroutine at `entryTarget`:
    - When `ActiveRealPre spec s0` and `ActiveRealRun keep P_real P_sub entryTarget s0` hold, returns
      the deterministic first-stop state of `P_real` from `s0.setPC entryTarget`.
    - When `ActiveRealPre spec s0` holds outside `ActiveRealRun` (e.g., `lr ∈ keep` or non-`ExecFrozen`
      memory), delegates to `keepFsTrace fallback` (`codeROSubroutineHook`) so `HookOk` holds
      unconditionally.
    - Outside `ActiveRealPre spec s0`, sets `.Exception`, so `steps_preserves_exception` establishes
      `ActiveRealPre spec s0` at every call along non-faulting ghost traces. -/
noncomputable def linkedCallHook {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State) (s0 : State) : State :=
  if _ : ActiveRealPre spec s0 then
    if hReal : ActiveRealRun keep P_real P_sub entryTarget s0 then
      Classical.choose hReal.2.2.2
    else
      keepFsTrace fallback s0
  else
    { s0 with status := .Exception "ghost-hook precondition violated" }

theorem linkedCallHook_fs {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State) (s0 : State) :
    (linkedCallHook keep P_real P_sub entryTarget spec fallback s0).fs = s0.fs := by
  classical
  unfold linkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.1
    · rfl
  · rfl

theorem linkedCallHook_fsT {α : Type}
    (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) (spec : Spec α) (fallback : State → State) :
    HookFsTraced IsFsC (linkedCallHook keep P_real P_sub entryTarget spec fallback) := by
  classical
  intro s0
  unfold linkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.1
    · exact FsTraced.of_eq rfl rfl
  · exact FsTraced.of_eq rfl rfl

private theorem subroutineOutcome_not_halted {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : sf.status ≠ .Halted := by
  rcases h with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
  · rw [hr]; decide
  · rw [hp]; decide
  · rw [he]; nofun
  · rw [ho]; decide

private theorem subroutineOutcome_to_stop {α : Type} {spec : Spec α} {x : α} {R : SepProp}
    {s0 sf : State} (h : SubroutineOutcome spec x R s0 sf) : SubroutineStop s0 sf := by
  rcases h with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, he, _⟩ | ⟨ho, _⟩
  · exact Or.inl hret
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he⟩))
  · exact Or.inr (Or.inr (Or.inr ho))

private theorem subroutineStop_setPC (s0 : State) (pc : BitVec 64) (sf : State) :
    SubroutineStop (s0.setPC pc) sf ↔ SubroutineStop s0 sf := Iff.rfl

/-- Lift `subroutine_ok P_sub entryTarget spec` across `stripS keep` to a first-stop real execution
    `StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf` whenever `ExecFrozen s0.mem`,
    `keep (s0.readReg64 .lr) = false`, and `P_sub.CodeLoaded (stripExecOutside keep s0.mem)`. -/
theorem real_subroutine_run_of_stripS {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64} {spec : Spec α}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {x : α} {R : SepProp} {s0 : State}
    (hRun : s0.status = .Running)
    (hSp : s0.spAligned = true)
    (hPre : s0.mem ⊨ spec.pre x s0 ∗ R)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    ∃ sf : State,
      StepsUntil P_real (SubroutineStop s0) (s0.setPC entryTarget) sf ∧
      SubroutineStop s0 sf ∧
      SubroutineOutcome spec x R s0 sf ∧
      sf.fs = s0.fs ∧
      FsTraced IsFsC s0 sf ∧
      ExecFrozen sf.mem := by
  let s1 := s0.setPC entryTarget
  let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ spec.pre x s1 ∗ R := by
    change s0.mem ⊨ spec.pre x (s0.setPC entryTarget) ∗ R
    rwa [hPrePC x s0 entryTarget]
  have hs1'_pre : s1'.mem ⊨ spec.pre x s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    rwa [← hInv.pre_eq x s1] at hsat
  have hs1'_sp : s1'.spAligned = true := hSp
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hOk x R s1' rfl hRun hs1'_pre hs1'_sp hCodeSub
  have hstop1' : SubroutineStop s1' sf' := subroutineOutcome_to_stop hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  have hnhalt' : sf'.status ≠ .Halted := subroutineOutcome_not_halted hout'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0)
      hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he)
      hlr_out hsteps' hstop0' hnhalt' s1 rfl hFr
  have hout1 : SubroutineOutcome spec x R s1 sf := by
    rw [hsf_eq] at hout'
    rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨hp', hpan'⟩ | ⟨c, he', hex'⟩ | ⟨ho', hoom'⟩
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · exact ⟨hret'.1, hret'.2.1, hret'.2.2⟩
      · cases s0; cases sf; exact hcc'
      · rw [hInv.post_eq x s1 sf] at hpost'
        exact satisfies_of_stripExecOutside hfr_sf hpost'
    · refine Or.inr (Or.inl ⟨hp', ?_⟩)
      rw [hInv.onPanic_eq x s1 sf] at hpan'
      exact satisfies_of_stripExecOutside hfr_sf hpan'
    · refine Or.inr (Or.inr (Or.inl ⟨c, he', ?_⟩))
      rw [hInv.onExit_eq x c s1 sf] at hex'
      exact satisfies_of_stripExecOutside hfr_sf hex'
    · refine Or.inr (Or.inr (Or.inr ⟨ho', ?_⟩))
      rw [hInv.onOom_eq x s1 sf] at hoom'
      exact satisfies_of_stripExecOutside hfr_sf hoom'
  have hout0 : SubroutineOutcome spec x R s0 sf := hOutPC x R s0 sf entryTarget hout1
  obtain ⟨hfs, hfst⟩ := hFsT x R s0 sf hout0
  exact ⟨sf, huntil, hstop_sf, hout0, hfs, hfst, hfr_sf⟩

/-- Unconditional `HookOk` for `linkedCallHook` (real execution under `ActiveRealRun`,
    `keepFsTrace fallback` otherwise). -/
theorem linkedCallHook_ok {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) spec) :
    HookOk (linkedCallHook keep P_real P_sub entryTarget spec fallback) spec := by
  classical
  intro x R s0 hrun hpre hsp
  have hActPre : ActiveRealPre spec s0 := ⟨hrun, hsp, x, R, hpre⟩
  unfold linkedCallHook
  simp only [hActPre, ↓reduceDIte]
  by_cases hReal : ActiveRealRun keep P_real P_sub entryTarget s0
  · simp only [hReal, ↓reduceDIte]
    obtain ⟨sf, huntil, hstop, hout, _, _, _⟩ :=
      real_subroutine_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hOk hInv hFsT
        hPrePC hOutPC hrun hsp hpre hReal.1 hReal.2.1 hReal.2.2.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop
    rw [hdet]
    exact ⟨huntil.toSteps.keepsFrozen, huntil.toSteps.symtab_eq, hout⟩
  · simp only [hReal, ↓reduceDIte]
    exact hFallbackOk x R s0 hrun hpre hsp

/-- On any ghost call step where `ActiveRealPre spec s0` holds (automatically established along any
    non-`.Exception` ghost trace via `steps_preserves_exception`), `ExecFrozen s0.mem` holds,
    `keep (s0.readReg64 .lr) = false`, and `P_sub.CodeLoaded (stripExecOutside keep s0.mem)` holds,
    `linkedCallHook` executes the real machine-code trace `Steps P_real (s0.setPC entryTarget) sf`
    and preserves `ExecFrozen`. -/
theorem linkedCallHook_active_steps {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf)
    {s0 : State}
    (hActPre : ActiveRealPre spec s0)
    (hFr : ExecFrozen s0.mem)
    (hlr_out : keep (s0.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep s0.mem)) :
    Steps P_real (s0.setPC entryTarget)
        (linkedCallHook keep P_real P_sub entryTarget spec fallback s0) ∧
      ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback s0).mem := by
  classical
  have ⟨hrun, hsp, x, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf⟩ :=
    real_subroutine_run_of_stripS hsvc_real hsvc_sub hreal_no hsub_no hOk hInv hFsT
      hPrePC hOutPC hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep P_real P_sub entryTarget s0 :=
    ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  unfold linkedCallHook
  simp only [hActPre, hReal, ↓reduceDIte]
  have hchoose := Classical.choose_spec hReal.2.2.2
  exact ⟨hchoose.1.toSteps, hchoose.2.2.2.2⟩

export CryptoVerification.SignalSession.Cli.RunGlue (
  codeROSubroutineHook_fsT stepRustAlloc1_fsT stepRustDealloc1_fsT
  aesEncHookMallocng_fsT aesDecHookMallocng_fsT libcruxHmacHookMallocng_fsT
)

/-- `HookFsTraced IsFsC` for `stringCloneHookMallocng mmpl`. -/
theorem stringCloneHookMallocng_fsT (mpl : Obj.MultiPlacement) :
    HookFsTraced IsFsC (stringCloneHookMallocng mpl) := by
  intro s0
  unfold stringCloneHookMallocng
  dsimp only
  split
  · exact FsTraced.of_eq rfl rfl
  · apply stepRustAlloc1_fsT
    intro _ _
    exact FsTraced.of_eq rfl rfl

export CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns
  cliGhostExterns_alloc cliGhostExterns_dealloc cliGhostExterns_realloc
  cliGhostExterns_allocZeroed cliGhostExterns_shim
  cliGhostExterns_stringClone_some cliGhostExterns_memset_some cliGhostExterns_memset_none
  cliGhostExterns_memcpy_some cliGhostExterns_memcpy_none cliGhostExterns_other hookSat_of_eq
)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks CliGhostSpqrAllocHooks
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookExactMemcpy)

/-- Construct `CliGhostSpqrAllocHooks` for a tuple of `linkedCallHook`s directly from `subroutine_ok`
    witnesses (`linkedGhostAllocEntries_thunks` + `linkedGhostAllocZeroed_thunk_ok`) and terminating
    `keepFsTrace` fallbacks. -/
theorem cliGhostSpqrAllocHooks_of_linked [LibsignalPlacement]
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {allocLib : Obj.MultiPlacedLib} {allocMpl : Obj.MultiPlacement}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits}
    {thunkAddrs : RustAllocAddrs} {allocZeroedAddr : BitVec 64}
    {fbAlloc fbDealloc fbRealloc fbAllocZeroed : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hKeepMallocng : ∀ a : BitVec 64,
      (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hEntries : RustCliAllocBudgetEntriesBase fineCostModel
      (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) P_sub thunkAddrs)
    (hZeroed : subroutine_ok P_sub allocZeroedAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim))
    (hFbAlloc : HookOk fbAlloc
      (rustCliAllocBudgetSpecBase fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim false))
    (hFbDealloc : HookOk fbDealloc
      (rustCliDeallocBudgetSpecBase fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim))
    (hFbRealloc : HookOk fbRealloc
      (rustCliReallocBudgetSpecBase fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim))
    (hFbZeroed : HookOk fbAllocZeroed
      (rustCliAllocBudgetSpecBase fineCostModel
        (linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart) lim true))
    (strClone : Option (State → State) := none)
    (fMemset : Option (State → State))
    (fMemcpy : Option (State → State))
    (hMemset : ∃ f, fMemset = some f ∧
      (∀ stk, 0 < stk → HookOk f (libcMemsetSpec stk)) ∧
      (∀ stk, 0 < stk → HookOk f (sessionMemsetSpec stk)) ∧
      HookOk f memsetRegionSpec ∧
      HookOk f sessionMemsetRegionSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpy : ∃ f, fMemcpy = some f ∧
      (∀ stk, HookOk f (libcMemcpySpec stk)) ∧
      (∀ stk, HookOk f (sessionMemcpySpec stk)) ∧
      HookOk f memcpyRegionSpec ∧
      HookOk f sessionMemcpyRegionSpec ∧
      HookOk f framelessMemcpySpec ∧
      HookOk f CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec ∧
      (∀ s : State, VmPreserved s (f s)) ∧
      (∀ s : State, (f s).fs = s.fs) ∧
      HookFsTraced IsFsC f)
    (hMemcpyExact : ∀ f, fMemcpy = some f → HookExactMemcpy f)
    (hMemsetAcp : ∀ f, fMemset = some f →
      ∀ s : State, (f s).sigActions = s.sigActions ∧ (f s).oracle = s.oracle) :
    let A := linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart
    let spAlloc := rustCliAllocBudgetSpec fineCostModel A lim false
    let spDealloc := rustCliDeallocBudgetSpec fineCostModel A lim
    let spRealloc := rustCliReallocBudgetSpec fineCostModel A lim
    let spZeroed := rustCliAllocBudgetSpec fineCostModel A lim true
    CliGhostSpqrAllocHooks fineCostModel A lim
      { alloc := linkedCallHook keep P_real P_sub thunkAddrs.alloc spAlloc fbAlloc
        dealloc := linkedCallHook keep P_real P_sub thunkAddrs.dealloc spDealloc fbDealloc
        realloc := linkedCallHook keep P_real P_sub thunkAddrs.realloc spRealloc fbRealloc
        allocZeroed := linkedCallHook keep P_real P_sub allocZeroedAddr spZeroed fbAllocZeroed
        shim := hookNoop
        stringClone := strClone
        memset := fMemset
        memcpy := fMemcpy } := by
  dsimp only
  let A := linkedGhostBudget allocLib allocMpl γ mmpl tp brkStart
  have hEntriesP := hEntries.toPlaced
  have hZeroedP := subroutine_ok_rustCliAllocBudget_of_base hZeroed
  have hFbAllocP := hookOk_rustCliAllocBudget_of_base hFbAlloc
  have hFbDeallocP := hookOk_rustCliDeallocBudget_of_base hFbDealloc
  have hFbReallocP := hookOk_rustCliReallocBudget_of_base hFbRealloc
  have hFbZeroedP := hookOk_rustCliAllocBudget_of_base hFbZeroed
  have hOutAlloc : ∀ (z : Bool) x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (rustCliAllocBudgetSpec fineCostModel A lim z) x R (s0.setPC pc) sf →
      SubroutineOutcome (rustCliAllocBudgetSpec fineCostModel A lim z) x R s0 sf := by
    intro z ⟨sz, al, st⟩ R s0 sf pc hout
    exact hout
  have hOutDealloc : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (rustCliDeallocBudgetSpec fineCostModel A lim) x R (s0.setPC pc) sf →
      SubroutineOutcome (rustCliDeallocBudgetSpec fineCostModel A lim) x R s0 sf := by
    intro ⟨ptr, sz, al, st⟩ R s0 sf pc hout
    exact hout
  have hOutRealloc : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome (rustCliReallocBudgetSpec fineCostModel A lim) x R (s0.setPC pc) sf →
      SubroutineOutcome (rustCliReallocBudgetSpec fineCostModel A lim) x R s0 sf := by
    intro ⟨ptr, oldSz, al, newSz, bs, st⟩ R s0 sf pc hout
    exact hout
  refine
    { alloc := linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no (hEntriesP.alloc lim)
        (specStripSInvariant_alloc allocLib allocMpl γ mmpl tp brkStart hKeepMallocng lim false)
        (specPreservesFsTrace_alloc A lim false)
        (fun _ _ _ => rfl) (hOutAlloc false)
        (keepFsTrace_ok hFbAllocP fun x R s0 hout =>
          specPreservesFsTraceExact_alloc A lim false x R s0 (fbAlloc s0) hout)
      dealloc := linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no (hEntriesP.dealloc lim)
        (specStripSInvariant_dealloc allocLib allocMpl γ mmpl tp brkStart hKeepMallocng lim)
        (specPreservesFsTrace_dealloc A lim)
        (fun _ _ _ => rfl) hOutDealloc
        (keepFsTrace_ok hFbDeallocP fun x R s0 hout =>
          specPreservesFsTraceExact_dealloc A lim x R s0 (fbDealloc s0) hout)
      realloc := linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no (hEntriesP.realloc lim)
        (specStripSInvariant_realloc allocLib allocMpl γ mmpl tp brkStart hKeepMallocng lim)
        (specPreservesFsTrace_realloc A lim)
        (fun _ _ _ => rfl) hOutRealloc
        (keepFsTrace_ok hFbReallocP fun x R s0 hout =>
          specPreservesFsTraceExact_realloc A lim x R s0 (fbRealloc s0) hout)
      alloc_fs := linkedCallHook_fs _ _ _ _ _ _
      dealloc_fs := linkedCallHook_fs _ _ _ _ _ _
      realloc_fs := linkedCallHook_fs _ _ _ _ _ _
      alloc_fsT := linkedCallHook_fsT _ _ _ _ _ _
      dealloc_fsT := linkedCallHook_fsT _ _ _ _ _ _
      realloc_fsT := linkedCallHook_fsT _ _ _ _ _ _
      shim_eq := rfl
      memset := hMemset
      memcpy := hMemcpy
      memcpy_exact := hMemcpyExact
      memset_acp := hMemsetAcp
      allocZeroed := linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no hZeroedP
        (specStripSInvariant_alloc allocLib allocMpl γ mmpl tp brkStart hKeepMallocng lim true)
        (specPreservesFsTrace_alloc A lim true)
        (fun _ _ _ => rfl) (hOutAlloc true)
        (keepFsTrace_ok hFbZeroedP fun x R s0 hout =>
          specPreservesFsTraceExact_alloc A lim true x R s0 (fbAllocZeroed s0) hout)
      allocZeroed_fs := linkedCallHook_fs _ _ _ _ _ _
      allocZeroed_fsT := linkedCallHook_fsT _ _ _ _ _ _ }

/-- `FsTHooks` for `cliGhostExterns g baseExt` whenever `FsTHooks baseExt` and `g`'s overlaid hooks
    are `HookFsTraced IsFsC`. -/
theorem fsTHooks_cliGhostExterns [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {g : CliGhostHooks} {baseExt : LibsignalHooks}
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hBase : FsTHooks baseExt) :
    FsTHooks (cliGhostExterns g baseExt) := by
  intro sym f h
  unfold cliGhostExterns at h
  split at h
  · cases h; exact hG.alloc_fsT
  · split at h
    · cases h; exact hG.dealloc_fsT
    · split at h
      · cases h; exact hG.realloc_fsT
      · split at h
        · cases h; exact hG.allocZeroed_fsT
        · split at h
          · cases h; rw [hG.shim_eq]; exact hookNoop_fsT
          · split at h
            · cases hsc : g.stringClone with
              | some fc =>
                rw [hsc] at h; cases h; exact hStrFsT f hsc
              | none =>
                rw [hsc] at h; exact hBase sym f h
            · split at h
              · cases hrf : g.readFile with
                | some rf =>
                  rw [hrf] at h; cases h; exact rf.2
                | none =>
                  rw [hrf] at h; exact hBase sym f h
              · split at h
                · cases hrs : g.readStdin with
                  | some rs =>
                    rw [hrs] at h; cases h; exact rs.2
                  | none =>
                    rw [hrs] at h; exact hBase sym f h
                · split at h
                  · obtain ⟨fm, hfm, _, _, _, _, _, _, hfmT⟩ := hG.memset
                    rw [hfm] at h; cases h; exact hfmT
                  · split at h
                    · obtain ⟨fc, hfc, _, _, _, _, _, _, _, _, hfcT⟩ := hG.memcpy
                      rw [hfc] at h; cases h; exact hfcT
                    · exact hBase sym f h

/-- `TraceFsSound` on any `IsLsBlockProg prog i (cliGhostExterns g baseExt)`. -/
theorem traceFsSound_lsProg_ghost [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {g : CliGhostHooks} {baseExt : LibsignalHooks}
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hBase : FsTHooks baseExt)
    (prog : Program) (i : Nat) [hprog : IsLsBlockProg prog i (cliGhostExterns g baseExt)] :
    TraceFsSound prog := by
  rw [hprog.eq_blockProgram]
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
  exact traceFsSound_of_fsTHooks (fsTHooks_cliGhostExterns hG hStrFsT hBase) fsTHooks_none rfl


/-- Table-parametric hypothesis bundle for the non-allocator helper and panic rows of `baseExt`
    against the `37`-row `cliExternsPlaced mmpl W` (`memset` and `memcpy` come from `CliGhostAllocHooks`). -/
structure BaseHelperRows (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks) :
    Prop where
  memmove_eq : baseExt memmoveName = cliExternsPlaced mmpl W memmoveName
  bcmp_eq : baseExt "bcmp" = cliExternsPlaced mmpl W "bcmp"
  utf8_eq : baseExt lsFromUtf8Sym = cliExternsPlaced mmpl W lsFromUtf8Sym
  memrchr_eq : baseExt lsMemrchrSym = cliExternsPlaced mmpl W lsMemrchrSym
  panics : CliPanicHooksPlaced baseExt

theorem cliGhostExterns_memmove_eq (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {baseExt : LibsignalHooks} (g : CliGhostHooks) (hBase : BaseHelperRows mmpl W baseExt) :
    cliGhostExterns g baseExt memmoveName = cliExternsPlaced mmpl W memmoveName :=
  (cliGhostExterns_other g baseExt (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hBase.memmove_eq

theorem shim_budget_sat_of_eq (baseExt : LibsignalHooks) {g : CliGhostHooks}
    (hShim : g.shim = hookNoop) :
    HookSat (cliGhostExterns g baseExt) lsRustNoAllocShimSymCli sessionShimBudgetSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g baseExt).trans (congrArg some hShim),
    hookOk_withVmPreserved sessionShim_hookOk (fun s => LibsignalBinary.Heap.VmPreserved.refl s)⟩

theorem noAllocShim_budget_sat_of_eq (baseExt : LibsignalHooks) {g : CliGhostHooks}
    (hShim : g.shim = hookNoop) :
    HookSat (cliGhostExterns g baseExt) lsRustNoAllocShimSymCli
      (withVmPreserved noAllocShimSpec) :=
  ⟨hookNoop, (cliGhostExterns_shim g baseExt).trans (congrArg some hShim),
    hookOk_withVmPreserved noAllocShim_hookOk (fun s => LibsignalBinary.Heap.VmPreserved.refl s)⟩

theorem cliGhostExterns_panics {baseExt : LibsignalHooks} (g : CliGhostHooks)
    (hPan : CliPanicHooksPlaced baseExt) :
    CliPanicHooksPlaced (cliGhostExterns g baseExt) := by
  intro sym hmem
  have h1 : sym ≠ lsRustAllocSymCli := by intro he; subst he; exact nomatch hmem
  have h2 : sym ≠ lsRustDeallocSymCli := by intro he; subst he; exact nomatch hmem
  have h3 : sym ≠ lsRustReallocSymCli := by intro he; subst he; exact nomatch hmem
  have h4 : sym ≠ lsRustAllocZeroedSymCli := by intro he; subst he; exact nomatch hmem
  have h5 : sym ≠ lsRustNoAllocShimSymCli := by intro he; subst he; exact nomatch hmem
  have h6 : sym ≠ lsStringCloneSym := by intro he; subst he; exact nomatch hmem
  have h7 : sym ≠ lsReadFileSym := by intro he; subst he; exact nomatch hmem
  have h8 : sym ≠ lsReadStdinSym := by intro he; subst he; exact nomatch hmem
  have h9 : sym ≠ lsMemsetSym := by intro he; subst he; exact nomatch hmem
  have h10 : sym ≠ lsMemcpySym := by intro he; subst he; exact nomatch hmem
  rw [cliGhostExterns_other g baseExt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]
  exact hPan sym hmem

theorem allocContractsXCliPlaced_of_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (hBase : BaseHelperRows mmpl W baseExt)
    (hG : CliGhostAllocHooks M A lim g) :
    AllocContractsXCliPlaced A lim (cliGhostExterns g baseExt) :=
  allocContractsXCliPlaced_of_hookSat
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    ⟨g.realloc, cliGhostExterns_realloc g baseExt, hG.realloc⟩
    (shim_budget_sat_of_eq baseExt hG.shim_eq)
    (cliGhostExterns_memcpy_budget_sat baseExt hG)
    (cliGhostExterns_sessionMemcpy_budget_sat baseExt hG)
    (cliGhostExterns_memcpyRegion_budget_sat baseExt hG)
    (cliGhostExterns_sessionMemcpyRegion_budget_sat baseExt hG)
    (fun stk => hookSat_of_eq (cliGhostExterns_memmove_eq mmpl W g hBase)
      (cliExternsPlaced_memmove_budget_sat mmpl W stk))
    (fun stk => hookSat_of_eq (cliGhostExterns_memmove_eq mmpl W g hBase)
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W stk))
    (cliGhostExterns_memset_budget_sat baseExt hG)
    (cliGhostExterns_sessionMemset_budget_sat baseExt hG)
    (cliGhostExterns_memsetRegion_budget_sat baseExt hG)
    (cliGhostExterns_sessionMemsetRegion_budget_sat baseExt hG)

theorem allocContractsFsPlaced_of_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (hBase : BaseHelperRows mmpl W baseExt)
    (hG : CliGhostAllocHooks M A lim g) :
    AllocContractsFsPlaced A lim (cliGhostExterns g baseExt) := by
  refine allocContractsFsPlaced_of_hookSat
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    ⟨g.realloc, cliGhostExterns_realloc g baseExt, hG.realloc⟩
    (shim_budget_sat_of_eq baseExt hG.shim_eq)
    (cliGhostExterns_memcpy_budget_sat baseExt hG)
    (cliGhostExterns_sessionMemcpy_budget_sat baseExt hG)
    (cliGhostExterns_memcpyRegion_budget_sat baseExt hG)
    (cliGhostExterns_sessionMemcpyRegion_budget_sat baseExt hG)
    (cliGhostExterns_memcpyRegionRO_budget_sat baseExt hG)
    (fun stk => hookSat_of_eq (cliGhostExterns_memmove_eq mmpl W g hBase)
      (cliExternsPlaced_memmove_budget_sat mmpl W stk))
    (fun stk => hookSat_of_eq (cliGhostExterns_memmove_eq mmpl W g hBase)
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W stk))
    (cliGhostExterns_memset_budget_sat baseExt hG)
    (cliGhostExterns_sessionMemset_budget_sat baseExt hG)
    (cliGhostExterns_memsetRegion_budget_sat baseExt hG)
    (cliGhostExterns_sessionMemsetRegion_budget_sat baseExt hG)
    ?_
  intro sym hmem f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cliGhostExterns_alloc] at hf; cases hf; exact hG.alloc_fs
  · rw [cliGhostExterns_dealloc] at hf; cases hf; exact hG.dealloc_fs
  · rw [cliGhostExterns_realloc] at hf; cases hf; exact hG.realloc_fs
  · rw [cliGhostExterns_shim, hG.shim_eq] at hf; cases hf; exact hookNoop_fs
  · obtain ⟨fc, hfc, _, _, _, _, _, _, _, hfs, _⟩ := hG.memcpy
    rw [cliGhostExterns_memcpy_some g baseExt hfc] at hf
    cases hf; exact hfs
  · rw [cliGhostExterns_memmove_eq mmpl W g hBase,
        cliExternsPlaced_row mmpl W (memmove_row_placed mmpl W)] at hf
    cases hf; exact hookMemmove_fs
  · obtain ⟨fm, hfm, _, _, _, _, _, hfs, _⟩ := hG.memset
    rw [cliGhostExterns_memset_some g baseExt hfm] at hf
    cases hf; exact hfs

theorem stage2ContractsMinPlaced_of_ghost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (baseExt : LibsignalHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (g : CliGhostHooks) (hBase : BaseHelperRows mmpl W baseExt)
    (hG : CliGhostAllocHooks M A lim g) :
    Stage2ContractsMinPlaced M A lim (cliGhostExterns g baseExt) :=
  stage2ContractsMinPlaced_of_hookSat
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    ⟨g.realloc, cliGhostExterns_realloc g baseExt, hG.realloc⟩
    (shim_budget_sat_of_eq baseExt hG.shim_eq)
    (cliGhostExterns_sessionMemcpy_budget_sat baseExt hG extHookStack)
    (hookSat_of_eq (cliGhostExterns_memmove_eq mmpl W g hBase)
      (cliExternsPlaced_sessionMemmove_budget_sat mmpl W extHookStack))

theorem codecHooksPlaced_of_ghost [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (baseExt : LibsignalHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (g : CliGhostHooks) (hBase : BaseHelperRows mmpl W baseExt)
    (hG : CliGhostAllocHooks M A lim g) :
    CodecHooksPlaced M A lim (cliGhostExterns g baseExt) :=
  codecHooksPlaced_of_hookSat
    (noAllocShim_budget_sat_of_eq baseExt hG.shim_eq)
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.realloc, cliGhostExterns_realloc g baseExt, hG.realloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    (cliGhostExterns_framelessMemcpy_budget_sat baseExt hG)
    (cliGhostExterns_panics g hBase.panics _ (by decide))
    (cliGhostExterns_panics g hBase.panics _ (by decide))

theorem publicApiDecHooksPlaced_of_ghost [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (baseExt : LibsignalHooks) {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (g : CliGhostHooks) (hBase : BaseHelperRows mmpl W baseExt)
    (hG : CliGhostAllocHooks M A lim g)
    (hStrClone : HookSat (cliGhostExterns g baseExt) lsStringCloneSym
      (stringCloneBudgetSpec M A lim)) :
    PublicApiDecHooksPlaced A lim (cliGhostExterns g baseExt) :=
  publicApiDecHooksPlaced_of_hookSat
    (shim_budget_sat_of_eq baseExt hG.shim_eq)
    ⟨g.alloc, cliGhostExterns_alloc g baseExt, hG.alloc⟩
    ⟨g.dealloc, cliGhostExterns_dealloc g baseExt, hG.dealloc⟩
    (cliGhostExterns_sessionMemcpyRegion_budget_sat baseExt hG)
    hStrClone
    (cliGhostExterns_panics g hBase.panics _ (by decide))
    (cliGhostExterns_panics g hBase.panics _ (by decide))

/-- Canonical `BaseHelperRows` witness for the `37`-row `cliExternsPlaced mmpl W`. -/
theorem cliExternsPlaced_baseHelperRows (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    BaseHelperRows mmpl W (cliExternsPlaced mmpl W) where
  memmove_eq := rfl
  bcmp_eq := rfl
  utf8_eq := rfl
  memrchr_eq := rfl
  panics := cliPanicHooksPlaced_cli mmpl W

/-! ## 5. Ghost-to-Real Link Transfer (`steps_transfer_allocGhost`, `sepWPp_transfer_allocGhost`, `subroutine_ok_transfer_allocGhost`) & `lr ∉ keep` Discharge -/

/-- A stub address `stubPc` reaches `entryTarget` under `P_real` (`0` steps when `stubPc = entryTarget`,
    or `1` `Step.exec` hop across a branch-stub `B` instruction). -/
def StubReachesTarget (P_real : Program) (stubPc entryTarget : BitVec 64) : Prop :=
  ∀ u : State,
    u.pc = stubPc →
    u.status = .Running →
    ExecFrozen u.mem →
    Steps P_real u (u.setPC entryTarget)

theorem StubReachesTarget.refl (P_real : Program) (entryTarget : BitVec 64) :
    StubReachesTarget P_real entryTarget entryTarget := by
  intro u hpc _ _
  have heq : u.setPC entryTarget = u := by
    cases u; dsimp [State.setPC] at hpc ⊢; subst hpc; rfl
  rw [heq]
  exact Steps.refl _

/-- Every extern hook in `P_ghost` either:
    - (`Or.inl`) is already an identical real extern hook in `P_real` preserving `ExecFrozen`, or
    - (`Or.inr`) is an overlaid ghost hook (`P_real.externAt? pc = none`) that replays as a real
      multi-step execution `Steps P_real u (f u)` preserving `ExecFrozen` whenever `f u` does not
      fault (`∀ msg, (f u).status ≠ .Exception msg`), `ExecFrozen u.mem`, `keep (u.readReg64 .lr) = false`,
      and `Inv u.mem` holds. -/
def GhostExternReplays (keep : BitVec 64 → Bool) (Inv : Memory → Prop)
    (P_ghost P_real : Program) : Prop :=
  ∀ (pc : BitVec 64) (f : State → State),
    P_ghost.externAt? pc = some f →
    (P_real.externAt? pc = some f ∧
      (∀ u : State, u.status = .Running → ExecFrozen u.mem → ExecFrozen (f u).mem)) ∨
    (P_real.externAt? pc = none ∧
      ∀ u : State,
        u.pc = pc →
        u.status = .Running →
        (∀ msg, (f u).status ≠ .Exception msg) →
        ExecFrozen u.mem →
        keep (u.readReg64 .lr) = false →
        Inv u.mem →
        Steps P_real u (f u) ∧ ExecFrozen (f u).mem)

/-- Discharge `GhostExternReplays`'s ghost arm for `linkedCallHook`: along any non-`.Exception`
    execution, `(f u).status ≠ .Exception _` forces `ActiveRealPre spec u` to hold automatically,
    so `StubReachesTarget` + `linkedCallHook_active_steps` replay `u ↦ f u` as `Steps P_real u (f u)`! -/
theorem ghostExternReplays_of_linkedCallHook {α : Type}
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_real P_sub : Program} {stubPc entryTarget : BitVec 64}
    {spec : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hInvCode : ∀ m : Memory, ExecFrozen m → Inv m → P_sub.CodeLoaded (stripExecOutside keep m))
    (hOk : subroutine_ok P_sub entryTarget spec)
    (hSpecInv : SpecStripSInvariant keep spec)
    (hFsT : SpecPreservesFsTrace spec)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), spec.pre x (s.setPC pc) = spec.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome spec x R (s0.setPC pc) sf → SubroutineOutcome spec x R s0 sf) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (linkedCallHook keep P_real P_sub entryTarget spec fallback u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps P_real u (linkedCallHook keep P_real P_sub entryTarget spec fallback u) ∧
      ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  have hActPre : ActiveRealPre spec u := by
    classical
    by_contra hnAct
    have hex : (linkedCallHook keep P_real P_sub entryTarget spec fallback u).status =
        .Exception "ghost-hook precondition violated" := by
      unfold linkedCallHook
      simp [hnAct]
    exact hnoex _ hex
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr
  obtain ⟨hBodySteps, hFrOut⟩ :=
    linkedCallHook_active_steps hsvc_real hsvc_sub hreal_no hsub_no hOk hSpecInv hFsT
      hPrePC hOutPC hActPre hfr hlr (hInvCode u.mem hfr hinv)
  exact ⟨hStubSteps.trans hBodySteps, hFrOut⟩

/-- Discharge `GhostExternReplays`'s ghost arm for `hookNoop` (`lsRustNoAllocShimSymCli`) against a
    real `ret` (`Instr.ret .lr`) instruction at `entryTarget` (optionally behind `StubReachesTarget`). -/
theorem ghostExternReplays_of_hookNoop
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_real : Program} {stubPc entryTarget : BitVec 64}
    (hreal_stub_none : P_real.externAt? stubPc = none)
    (hStub : StubReachesTarget P_real stubPc entryTarget)
    (hFetchRet : ∀ m : Memory, ExecFrozen m → Inv m →
      P_real.fetchMem m entryTarget = some (.ret .lr)) :
    P_real.externAt? stubPc = none ∧
    ∀ u : State,
      u.pc = stubPc →
      u.status = .Running →
      (∀ msg, (hookNoop u).status ≠ .Exception msg) →
      ExecFrozen u.mem →
      keep (u.readReg64 .lr) = false →
      Inv u.mem →
      Steps P_real u (hookNoop u) ∧
      ExecFrozen (hookNoop u).mem := by
  refine ⟨hreal_stub_none, fun u hpc hrun _ hfr _ hinv => ?_⟩
  have hStubSteps : Steps P_real u (u.setPC entryTarget) := hStub u hpc hrun hfr
  have hfm : P_real.fetchMem (u.setPC entryTarget).mem (u.setPC entryTarget).pc = some (.ret .lr) :=
    hFetchRet u.mem hfr hinv
  have hrun1 : (u.setPC entryTarget).status = .Running := hrun
  have hstep1 : Step P_real (u.setPC entryTarget) (P_real.evalInst (.ret .lr) (u.setPC entryTarget)) :=
    Step.exec hrun1 hfm
  have heval : P_real.evalInst (.ret .lr) (u.setPC entryTarget) = hookNoop u := by
    rfl
  rw [heval] at hstep1
  exact ⟨hStubSteps.trans (Steps.step hstep1 (Steps.refl _)), hfr⟩

/-- Trace-level ghost-to-real link transfer: every `Steps P_ghost s0 sf` reaching a non-`.Exception`,
    non-`.Halted` terminal state `sf` replays as `Steps P_real s0 sf` preserving `ExecFrozen sf.mem`
    whenever both programs use `Syscall.standard`, `P_real` adds no extra hooks over `P_ghost`,
    `GhostExternReplays keep Inv P_ghost P_real` holds, `Inv` is `KeepsFrozen`-stable and holds at
    `s0.mem`, and `keep (u.readReg64 .lr) = false` at every ghost-only call step. -/
theorem steps_transfer_allocGhost
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_ghost P_real : Program}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    (hReplays : GhostExternReplays keep Inv P_ghost P_real)
    (hInvStable : ∀ m m' : Memory, Inv m → m.KeepsFrozen m' → Inv m')
    {s0 sf : State}
    (hsteps : Steps P_ghost s0 sf)
    (hnoex_sf : ∀ msg, sf.status ≠ .Exception msg)
    (hnhalt_sf : sf.status ≠ .Halted)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : Inv s0.mem)
    (hlr_calls : ∀ u : State,
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keep (u.readReg64 .lr) = false) :
    Steps P_real s0 sf ∧ ExecFrozen sf.mem := by
  induction hsteps with
  | refl s => exact ⟨Steps.refl s, hfr0⟩
  | @step u v w h1 hrest ih =>
    have hstep_uw : Steps P_ghost u w := Steps.step h1 hrest
    cases h1 with
    | halt_unmapped _ _ _ =>
      exact False.elim (hnhalt_sf (steps_preserves_halted hrest rfl))
    | extern_fault _ _ _ =>
      exact False.elim (hnoex_sf _ (steps_preserves_exception hrest rfl))
    | @exec inst hrun hfm =>
      unfold Program.fetchMem at hfm
      cases heg : P_ghost.externAt? u.pc with
      | some f => simp [heg] at hfm
      | none =>
        have her : P_real.externAt? u.pc = none := hno_new_hooks u.pc heg
        have hfm_real : P_real.fetchMem u.mem u.pc = some inst := by
          unfold Program.fetchMem
          simpa [heg, her] using hfm
        by_cases hsvc0 : inst.isSvc0 = true
        · have hinst : inst = .system false 0#16 := by
            cases inst <;> simp [Instr.isSvc0] at hsvc0
            rcases hsvc0 with ⟨rfl, rfl⟩; rfl
          subst hinst
          have hev_g : P_ghost.evalInst (.system false 0#16) u = Syscall.standard u := by
            simp [Program.evalInst, execInstWithSvc, hsvc_ghost]
          have hev_r : P_real.evalInst (.system false 0#16) u = Syscall.standard u := by
            simp [Program.evalInst, execInstWithSvc, hsvc_real]
          have hstep1_g : Step P_ghost u (Syscall.standard u) := hev_g ▸ Step.exec hrun hfm
          have hstep1_r : Step P_real u (Syscall.standard u) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨_, hfr_v⟩ := standard_stripS (keep := keep) hfr0
          have hinv_v : Inv (Syscall.standard u).mem := hInvStable u.mem _ hinv0 hstep1_r.keepsFrozen
          rw [hev_g] at hrest ih
          obtain ⟨hrest_r, hfr_w⟩ :=
            ih hnoex_sf hnhalt_sf hfr_v hinv_v fun z hzu hzw hrz hne =>
              hlr_calls z (Steps.step hstep1_g hzu) hzw hrz hne
          exact ⟨Steps.step hstep1_r hrest_r, hfr_w⟩
        · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
          have hev_g : P_ghost.evalInst inst u = execInst inst u :=
            evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 u
          have hev_r : P_real.evalInst inst u = execInst inst u :=
            evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0 u
          have hstep1_g : Step P_ghost u (execInst inst u) := hev_g ▸ Step.exec hrun hfm
          have hstep1_r : Step P_real u (execInst inst u) := hev_r ▸ Step.exec hrun hfm_real
          obtain ⟨hfr_v, _⟩ := execInst_preserves_execFrozen hnsvc0 hfr0
          have hinv_v : Inv (execInst inst u).mem := hInvStable u.mem _ hinv0 hstep1_r.keepsFrozen
          rw [hev_g] at hrest ih
          obtain ⟨hrest_r, hfr_w⟩ :=
            ih hnoex_sf hnhalt_sf hfr_v hinv_v fun z hzu hzw hrz hne =>
              hlr_calls z (Steps.step hstep1_g hzu) hzw hrz hne
          exact ⟨Steps.step hstep1_r hrest_r, hfr_w⟩
    | @extern f hrun heg hkf hsym =>
      have hstep1_g : Step P_ghost u (f u) := Step.extern hrun heg hkf hsym
      have hnoex_fu : ∀ msg, (f u).status ≠ .Exception msg := fun msg hex =>
        hnoex_sf msg (steps_preserves_exception hrest hex)
      rcases hReplays u.pc f heg with ⟨her, hfr_pres⟩ | ⟨her_none, hghost_run⟩
      · have hstep1_r : Step P_real u (f u) := Step.extern hrun her hkf hsym
        have hfr_v : ExecFrozen (f u).mem := hfr_pres u hrun hfr0
        have hinv_v : Inv (f u).mem := hInvStable u.mem _ hinv0 hkf
        obtain ⟨hrest_r, hfr_w⟩ :=
          ih hnoex_sf hnhalt_sf hfr_v hinv_v fun z hzu hzw hrz hne =>
            hlr_calls z (Steps.step hstep1_g hzu) hzw hrz hne
        exact ⟨Steps.step hstep1_r hrest_r, hfr_w⟩
      · have hne_ext : P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc := by
          rw [heg, her_none]; nofun
        have hlr_u : keep (u.readReg64 .lr) = false :=
          hlr_calls u (Steps.refl u) hstep_uw hrun hne_ext
        obtain ⟨hsteps_fu, hfr_v⟩ := hghost_run u rfl hrun hnoex_fu hfr0 hlr_u hinv0
        have hinv_v : Inv (f u).mem := hInvStable u.mem _ hinv0 hkf
        obtain ⟨hrest_r, hfr_w⟩ :=
          ih hnoex_sf hnhalt_sf hfr_v hinv_v fun z hzu hzw hrz hne =>
            hlr_calls z (Steps.step hstep1_g hzu) hzw hrz hne
        exact ⟨hsteps_fu.trans hrest_r, hfr_w⟩

/-- Transfers `SepWPp P_ghost` to `SepWPp P_real` whenever `s0.mem` satisfies `ExecFrozen`, `Inv`,
    and `P_ghost.CodeLoaded`. -/
theorem sepWPp_transfer_allocGhost
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_ghost P_real : Program}
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    (hReplays : GhostExternReplays keep Inv P_ghost P_real)
    (hInvStable : ∀ m m' : Memory, Inv m → m.KeepsFrozen m' → Inv m')
    {ret : BitVec 64} {s0 : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hCodeGhost : P_ghost.CodeLoaded s0.mem)
    (hfr0 : ExecFrozen s0.mem)
    (hinv0 : Inv s0.mem)
    (hlr : ∀ (u sf : State),
      Steps P_ghost s0 u →
      Steps P_ghost u sf →
      u.status = .Running →
      P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
      keep (u.readReg64 .lr) = false)
    (hwp : SepWPp P_ghost ret s0 P Q Qp oom) :
    SepWPp P_real ret s0 P Q Qp oom := by
  intro R hm _
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hCodeGhost
  have hnoex : ∀ msg, sf.status ≠ .Exception msg := by
    intro msg hex
    rcases hout with ⟨_, hrun, _⟩ | ⟨hpan, _⟩ | ⟨hoom, _⟩
    · rw [hex] at hrun; cases hrun
    · rw [hex] at hpan; cases hpan
    · rw [hex] at hoom; cases hoom
  have hnhalt : sf.status ≠ .Halted := by
    rcases hout with ⟨_, hrun, _⟩ | ⟨hpan, _⟩ | ⟨hoom, _⟩
    · rw [hrun]; decide
    · rw [hpan]; decide
    · rw [hoom]; decide
  obtain ⟨hsteps_real, _⟩ :=
    steps_transfer_allocGhost hsvc_ghost hsvc_real hno_new_hooks hReplays hInvStable
      hsteps hnoex hnhalt hfr0 hinv0 (fun u hsu hus hr hne => hlr u sf hsu hus hr hne)
  exact ⟨sf, hsteps_real, hout⟩

/-- Transfers `subroutine_ok P_ghost entry spec` (over `cliGhostExterns g baseExt`) to
    `subroutine_ok P_real entry spec` (over `baseExt`, executing real allocator bytes) under a
    precondition guard `Guard s0` supplying `P_ghost.CodeLoaded s0.mem`, `ExecFrozen s0.mem`,
    `Inv s0.mem`, and `lr ∉ keep` at reachable ghost call sites. -/
theorem subroutine_ok_transfer_allocGhost {α : Type}
    {keep : BitVec 64 → Bool} {Inv : Memory → Prop}
    {P_ghost P_real : Program} {entry : BitVec 64} {spec : Spec α}
    (Guard : State → Prop)
    (hsvc_ghost : P_ghost.svc = Syscall.standard)
    (hsvc_real : P_real.svc = Syscall.standard)
    (hno_new_hooks : ∀ pc, P_ghost.externAt? pc = none → P_real.externAt? pc = none)
    (hReplays : GhostExternReplays keep Inv P_ghost P_real)
    (hInvStable : ∀ m m' : Memory, Inv m → m.KeepsFrozen m' → Inv m')
    (hGuard : ∀ s0 : State, Guard s0 →
      P_ghost.CodeLoaded s0.mem ∧ ExecFrozen s0.mem ∧ Inv s0.mem ∧
      (∀ (u sf : State),
        Steps P_ghost s0 u →
        Steps P_ghost u sf →
        u.status = .Running →
        P_ghost.externAt? u.pc ≠ P_real.externAt? u.pc →
        keep (u.readReg64 .lr) = false))
    (hGhostOk : subroutine_ok P_ghost entry spec) :
    subroutine_ok P_real entry
      { spec with pre := fun x s => ⌜Guard s⌝ ∗ spec.pre x s } := by
  apply subroutine_ok_of_steps_outcome
  intro x R s0 hpc hrun hm hsp _
  dsimp only at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨hG, hm_pre⟩ := hm
  obtain ⟨hCodeG, hFr0, hInv0, hLr⟩ := hGuard s0 hG
  obtain ⟨sf, hsteps, hout⟩ :=
    subroutine_ok_elim_steps_outcome hGhostOk x R s0 hpc hrun hm_pre hsp hCodeG
  have hnoex : ∀ msg, sf.status ≠ .Exception msg := by
    intro msg hex
    rcases hout with ⟨⟨_, _, hr⟩, _, _⟩ | ⟨hp, _⟩ | ⟨_, he, _⟩ | ⟨ho, _⟩
    · rw [hex] at hr; cases hr
    · rw [hex] at hp; cases hp
    · rw [hex] at he; cases he
    · rw [hex] at ho; cases ho
  have hnhalt : sf.status ≠ .Halted := subroutineOutcome_not_halted hout
  obtain ⟨hsteps_real, _⟩ :=
    steps_transfer_allocGhost hsvc_ghost hsvc_real hno_new_hooks hReplays hInvStable
      hsteps hnoex hnhalt hFr0 hInv0 (fun u hsu hus hr hne => hLr u sf hsu hus hr hne)
  exact ⟨sf, hsteps_real, hout⟩

/-- Discharges `keep (u.readReg64 .lr) = false` at a `BL` call site: when `pc_call` executes
    `Instr.bl off` with `pc_call + 4#64` outside `keep`, `execInst (.bl off) s_call` sets
    `.lr = s_call.pc + 4#64`, hence outside `keep`. -/
theorem lr_not_keep_of_caller_bl {keep : BitVec 64 → Bool}
    {s_call : State} {off : BitVec 64}
    (hNextOut : keep (s_call.pc + 4#64) = false) :
    keep ((execInst (.bl off) s_call).readReg64 .lr) = false := by
  have hlr : (execInst (.bl off) s_call).readReg64 .lr = s_call.pc + 4#64 := by
    cases s_call; rfl
  rwa [hlr]

/-- Discharges `keep (u.readReg64 .lr) = false` for tail calls preserving `.lr` from an entry
    state whose `.lr` lies outside `keep`. -/
theorem lr_not_keep_of_eq_entry {keep : BitVec 64 → Bool} {s0 u : State}
    (hlr_eq : u.readReg64 .lr = s0.readReg64 .lr)
    (hlr0 : keep (s0.readReg64 .lr) = false) :
    keep (u.readReg64 .lr) = false :=
  hlr_eq ▸ hlr0

end LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer

