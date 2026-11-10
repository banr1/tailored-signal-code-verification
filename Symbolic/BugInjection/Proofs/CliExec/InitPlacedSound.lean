/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.Placed
public import ProofLib.Process.FastParse
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlacedSound
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecSound
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildSpecPlaced
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildPlacedSound
public import Symbolic.BugInjection.Proofs.CliExec.ExternAtPlaced

/-!
# Soundness of Placed `FastState` Initialization

Proves that `initFastStateFromBasePlacedProcess` and `initFastStateFromBasePlaced` construct an
initial `FastState` agreeing with `cliTokenPatchPlaced mpl s0` for a valid `elf.loadState` witness
`s0`, together with `FastProgSoundPlaced` and `mallocngLib.CodeLoaded`. Also proves congruence
lemmas transporting `HooksAgreePlaced` and `FastProgSoundPlaced` across pointwise-equal extern
hook tables.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.InitPlacedSound

open Arm64 Arm64.Memory Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.E2E (heapBase)
open CryptoVerification.SignalSession (CliHooks Inputs cliExternsPlacedSig cliProcessInputs
  libsignalSessionLib)
open CryptoVerification.SignalSession.Placed (cliProgPlacedSig cliTokenPatchPlaced)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Cell FastRegs Line64 btGet
  linesEq_setCellsAt memory_writeBytes_cells_noWrap rawCellAt rawCellAt_foldSetRawCell_noWrap
  regionToCells setCellsAt sub_lt_iff_range withForcedBinTree_eq)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux (HeapIntervalsAgree heapAddr_toNat
  inHeapIvs initFastFs initFastFs_agrees)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (MallocngCallAddrs)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlacedSound (MallocngCallAddrsMatches)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (FastProgPlaced PrebuiltElfPlaced
  decodeStepFromLinePlaced initFastStateFromBasePlaced initFastStateFromBasePlacedProcess
  lookupStepEntryPlaced overlayHooksPlaced progPlacedDepth)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecSound (FastProgSoundPlaced
  decodeStepFromLinePlaced_fetchMem decodeStepFromLinePlaced_valid)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfFullSpecPlaced
  headerElfOfFullPlaced initFastStateFromBasePlaced_congr prebuiltOfFullPlaced)
open Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced (prebuildElfPlaced)
open Symbolic.BugInjection.Proofs.CliExec.PrebuildSpecPlaced (HooksAgreePlaced PrebuildSpecPlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (ElfFullValidPlaced
  checkHooksAlignedPlaced mallocngCallAddrsPlaced mallocngCallAddrsPlaced_fnAddr stubsOfMpl
  tokOnceAddrPlaced tokStorageAddrPlaced)
open Symbolic.BugInjection.Proofs.CliExec.PrebuildPlacedSound (codeLoaded_cliTokenPatchPlaced
  prebuildElfPlaced_sound)
open Symbolic.BugInjection.Proofs.CliExec.ExternAtPlaced (hooksAgreePlaced_stubsOfMpl)

theorem mallocngCallAddrsPlaced_matches (mmpl : MultiPlacement) :
    MallocngCallAddrsMatches (mallocngCallAddrsPlaced mmpl) mmpl := by
  rcases mallocngCallAddrsPlaced_fnAddr mmpl with ⟨hc, hm, hf⟩
  exact ⟨hc, rfl, hm, rfl, hf, rfl⟩

theorem cliProgPlacedSig_congr_W
    {mpl mmpl : MultiPlacement} {W₁ W₂ : CliHooks}
    (hW : ∀ name, cliExternsPlacedSig mmpl W₁ name = cliExternsPlacedSig mmpl W₂ name) :
    cliProgPlacedSig mpl mmpl W₁ = cliProgPlacedSig mpl mmpl W₂ := by
  unfold cliProgPlacedSig
  rw [funext hW]

attribute [local irreducible] cliProgPlacedSig overlayHooksPlaced stubsOfMpl
  compHooks0 mallocngCallAddrsPlaced

theorem HooksAgreePlaced.congr_W
    {mpl mmpl : MultiPlacement} {W₁ W₂ : CliHooks} {t : BinTree String}
    (hW : ∀ name, cliExternsPlacedSig mmpl W₁ name = cliExternsPlacedSig mmpl W₂ name)
    (hag : HooksAgreePlaced mpl mmpl W₁ t) :
    HooksAgreePlaced mpl mmpl W₂ t := by
  have hprog := cliProgPlacedSig_congr_W (mpl := mpl) hW
  intro pc hmod4
  have hpc := hag pc hmod4
  cases hbt : btGet progPlacedDepth t (pc.toNat / 4) with
  | none =>
    rw [hbt] at hpc; dsimp only at hpc ⊢
    rwa [← hprog]
  | some name =>
    rw [hbt] at hpc; dsimp only at hpc ⊢
    intro h hext
    rw [← hprog]
    exact hpc h ((hW _).trans hext)

theorem hooksAgreePlaced_congr_W
    {mpl mmpl : MultiPlacement} {W₁ W₂ : CliHooks} {t : BinTree String}
    (hW : ∀ name, cliExternsPlacedSig mmpl W₁ name = cliExternsPlacedSig mmpl W₂ name)
    (hag : HooksAgreePlaced mpl mmpl W₁ t) :
    HooksAgreePlaced mpl mmpl W₂ t :=
  HooksAgreePlaced.congr_W hW hag

theorem FastProgSoundPlaced.congr_W
    {mpl mmpl : MultiPlacement} {W₁ W₂ : CliHooks} {fp : FastProgPlaced} {m0 : Memory}
    (hW : ∀ name, cliExternsPlacedSig mmpl W₁ name = cliExternsPlacedSig mmpl W₂ name)
    (hfp : FastProgSoundPlaced mpl mmpl W₁ fp m0) :
    FastProgSoundPlaced mpl mmpl W₂ fp m0 := by
  have hprog := cliProgPlacedSig_congr_W (mpl := mpl) hW
  refine ⟨hfp.addrs_matches, fun pc m hkf hmod4 => ?_⟩
  have hstep := hfp.step_sound pc m hkf hmod4
  cases hget : lookupStepEntryPlaced fp (pc.toNat / 4) with
  | instr inst =>
    rw [hget] at hstep; dsimp only at hstep ⊢
    rwa [← hprog]
  | hook name =>
    rw [hget] at hstep; dsimp only at hstep ⊢
    intro h hext
    rw [← hprog]
    exact hstep h ((hW _).trans hext)
  | unmapped => trivial

theorem fastProgSoundPlaced_congr_W
    {mpl mmpl : MultiPlacement} {W₁ W₂ : CliHooks} {fp : FastProgPlaced} {m0 : Memory}
    (hW : ∀ name, cliExternsPlacedSig mmpl W₁ name = cliExternsPlacedSig mmpl W₂ name)
    (hfp : FastProgSoundPlaced mpl mmpl W₁ fp m0) :
    FastProgSoundPlaced mpl mmpl W₂ fp m0 :=
  FastProgSoundPlaced.congr_W hW hfp

/-- `Memory`-level counterpart of `cliTokenPatchPlaced` parameterized by `(tokS, tokO)`. -/
def patchTokenMemPlaced (tokS tokO : BitVec 64) (m : Memory) : Memory :=
  (m.writeBytes tokS [0#8]).writeBytes (tokO + 8#64) [0#8, 0#8, 0#8, 0#8]

private theorem cliTokenPatchPlaced_eq_setMem (mpl : MultiPlacement) (s : State) :
    cliTokenPatchPlaced mpl s =
      s.setMem (patchTokenMemPlaced (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl) s.mem) :=
  rfl

attribute [local irreducible] tokStorageAddrPlaced tokOnceAddrPlaced

private theorem pow48_lt_pow64 : 2 ^ 48 < 2 ^ 64 :=
  Nat.pow_lt_pow_right (by decide) (by decide)

private theorem pow60_lt_pow64 : 2 ^ 60 < 2 ^ 64 :=
  Nat.pow_lt_pow_right (by decide) (by decide)

private theorem tokOnce_add8_bound {tokO : BitVec 64} {brk : Nat}
    (htokO : tokO.toNat + 12 ≤ brk) (hbrk : brk ≤ 2 ^ 48) :
    (tokO + 8#64).toNat + 4 ≤ brk := by
  have h48 := pow48_lt_pow64
  have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
  have hlt : tokO.toNat + 8 < 2 ^ 64 := by omega
  have hadd : (tokO + 8#64).toNat = tokO.toNat + 8 := by
    rw [BitVec.toNat_add, h8, Nat.mod_eq_of_lt hlt]
  omega

private theorem regionToCells_length' (perm : Perm) (nonAnonLen : Nat) :
    ∀ (i : Nat) (bs : List (BitVec 8)), (regionToCells perm nonAnonLen i bs).length = bs.length
  | _, [] => rfl
  | i, _ :: bs => by
    simp only [regionToCells, List.length_cons,
      regionToCells_length' perm nonAnonLen (i + 1) bs]

private theorem regionToCells_getElem' (perm : Perm) (nonAnonLen : Nat) :
    ∀ (i : Nat) (bs : List (BitVec 8)) (k : Nat) (hk : k < bs.length),
      (regionToCells perm nonAnonLen i bs)[k]'(by rw [regionToCells_length']; exact hk) =
        (some { perm with lazyFree := false, anon := if i + k < nonAnonLen then false else perm.anon },
          bs[k]'hk)
  | _, [], _, hk => absurd hk (Nat.not_lt_zero _)
  | i, b :: bs, k, hk => by
    simp only [List.length_cons] at hk
    cases k with
    | zero => simp [regionToCells]
    | succ j =>
      simp only [regionToCells, List.getElem_cons_succ]
      have hrec := regionToCells_getElem' perm nonAnonLen (i + 1) bs j (by omega)
      have hadd : i + 1 + j = i + (j + 1) := by omega
      simpa only [hadd] using hrec

private theorem loadCellAt_singleton (r : Snapshot.Region) (a : BitVec 64) :
    Snapshot.loadCellAt [r] a =
      if h : (a - r.start).toNat < r.bytes.length then
        let p := { r.perm with
          lazyFree := false
          anon := if (a - r.start).toNat < r.nonAnonLen then false else r.perm.anon }
        some (some p, r.bytes[(a - r.start).toNat])
      else none := by
  simp [Snapshot.loadCellAt]

private theorem loadCellAt_cons (r : Snapshot.Region) (rs : List Snapshot.Region) (a : BitVec 64) :
    Snapshot.loadCellAt (r :: rs) a = (Snapshot.loadCellAt [r] a).or (Snapshot.loadCellAt rs a) := by
  simp only [Snapshot.loadCellAt, List.findSome?_cons, List.findSome?_nil]
  split <;> rfl

private theorem rawCellAt_setRegion (lines : BinTree Line64) (r : Snapshot.Region)
    (hwrap : r.start.toNat + r.bytes.length ≤ 2 ^ 64) (a : BitVec 64) :
    rawCellAt (setCellsAt lines r.start.toNat (regionToCells r.perm r.nonAnonLen 0 r.bytes)) a.toNat =
      (Snapshot.loadCellAt [r] a).or (rawCellAt lines a.toNat) := by
  set cs := regionToCells r.perm r.nonAnonLen 0 r.bytes
  have hlen : cs.length = r.bytes.length := regionToCells_length' r.perm r.nonAnonLen 0 r.bytes
  rw [linesEq_setCellsAt _ _ cs a.toNat a.isLt,
    rawCellAt_foldSetRawCell_noWrap _ _ cs (by rw [hlen]; exact hwrap) a.toNat a.isLt,
    loadCellAt_singleton r a]
  have hrng_iff := sub_lt_iff_range hwrap (a := a)
  by_cases hlt : (a - r.start).toNat < r.bytes.length
  · have hrng : r.start.toNat ≤ a.toNat ∧ a.toNat < r.start.toNat + cs.length := by
      rw [hlen]; exact hrng_iff.mp hlt
    rw [dite_eq_left_of_eq_true (eq_true hrng), dite_eq_left_of_eq_true (eq_true hlt), Option.some_or]
    have hidx : a.toNat - r.start.toNat = (a - r.start).toNat := by
      simp only [BitVec.toNat_sub]
      have heq : 2 ^ 64 - r.start.toNat + a.toNat = 2 ^ 64 + (a.toNat - r.start.toNat) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hget := regionToCells_getElem' r.perm r.nonAnonLen 0 r.bytes
      (a.toNat - r.start.toNat) (by omega)
    dsimp only [cs]
    rw [hget]
    simp only [Nat.zero_add, hidx]
  · have hrng : ¬ (r.start.toNat ≤ a.toNat ∧ a.toNat < r.start.toNat + cs.length) := by
      rw [hlen]; exact fun h1 => hlt (hrng_iff.mpr h1)
    rw [dite_eq_right_of_eq_false (eq_false hrng), dite_eq_right_of_eq_false (eq_false hlt),
      Option.none_or]

private theorem loadCellAt_eq_none_of_ge {regions : List Snapshot.Region} {bound : Nat}
    (hbnd : ∀ r ∈ regions, r.start.toNat + r.bytes.length ≤ bound)
    {a : BitVec 64} (ha : bound ≤ a.toNat) :
    Snapshot.loadCellAt regions a = none := by
  induction regions with
  | nil => rfl
  | cons r rs ih =>
    have hr := hbnd r (List.mem_cons_self ..)
    have hr_wrap : r.start.toNat + r.bytes.length ≤ 2 ^ 64 := by have := a.isLt; omega
    have hrng_iff := sub_lt_iff_range hr_wrap (a := a)
    have hnot_lt : ¬ ((a - r.start).toNat < r.bytes.length) := by
      intro hlt; have := hrng_iff.mp hlt; omega
    rw [loadCellAt_cons, loadCellAt_singleton, dite_eq_right_of_eq_false (eq_false hnot_lt),
      Option.none_or]
    exact ih (fun q hq => hbnd q (List.mem_cons_of_mem _ hq))

private theorem cellAt_eq_none_of_lt {r : Snapshot.Region} {a : BitVec 64}
    (hwrap : r.start.toNat + r.bytes.length ≤ 2 ^ 64) (ha : a.toNat < r.start.toNat) :
    Snapshot.loadCellAt [r] a = none := by
  have hrng_iff := sub_lt_iff_range hwrap (a := a)
  have hnot_lt : ¬ ((a - r.start).toNat < r.bytes.length) := by
    intro hlt; have := hrng_iff.mp hlt; omega
  rw [loadCellAt_singleton, dite_eq_right_of_eq_false (eq_false hnot_lt)]

private theorem loadCellAt_append_singleton (regions : List Snapshot.Region) (r : Snapshot.Region)
    (a : BitVec 64) :
    Snapshot.loadCellAt (regions ++ [r]) a =
      (Snapshot.loadCellAt regions a).or (Snapshot.loadCellAt [r] a) := by
  induction regions with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.cons_append]
    rw [loadCellAt_cons q (qs ++ [r]), loadCellAt_cons q qs, ih, Option.or_assoc]

private theorem loadCellAt_perm_mapped_of_some' {regions : List Snapshot.Region} {a : BitVec 64}
    {c : Cell} (h : Snapshot.loadCellAt regions a = some c) :
    ∃ p b, c = (some p, b) := by
  induction regions with
  | nil => nomatch h
  | cons r rs ih =>
    rw [loadCellAt_cons, loadCellAt_singleton] at h
    by_cases hlt : (a - r.start).toNat < r.bytes.length
    · rw [dite_eq_left_of_eq_true (eq_true hlt), Option.some_or] at h
      injection h with h
      exact ⟨_, _, h.symm⟩
    · rw [dite_eq_right_of_eq_false (eq_false hlt), Option.none_or] at h
      exact ih h

private theorem writeBytes_cells_below_eq {m1 m2 : Memory} {sb : Nat}
    (hsb : sb ≤ 2 ^ 64)
    (hag : ∀ a : BitVec 64, a.toNat < sb → m1.cells a = m2.cells a)
    (base : BitVec 64) (bs : List (BitVec 8)) (hb : base.toNat + bs.length ≤ sb) :
    ∀ a : BitVec 64, a.toNat < sb →
      (m1.writeBytes base bs).cells a = (m2.writeBytes base bs).cells a := by
  intro a ha
  have hwrap : base.toNat + bs.length ≤ 2 ^ 64 := by omega
  rw [memory_writeBytes_cells_noWrap m1 base bs hwrap a,
    memory_writeBytes_cells_noWrap m2 base bs hwrap a]
  split
  · have hrp : m1.rawPerm a = m2.rawPerm a := by simp only [Memory.rawPerm, hag a ha]
    rw [hrp]
  · exact hag a ha

private theorem writeBytes_cells_above_eq (m : Memory) {sb : Nat} (hsb : sb ≤ 2 ^ 64)
    (base : BitVec 64) (bs : List (BitVec 8)) (hb : base.toNat + bs.length ≤ sb)
    {a : BitVec 64} (ha : sb ≤ a.toNat) :
    (m.writeBytes base bs).cells a = m.cells a := by
  have hwrap : base.toNat + bs.length ≤ 2 ^ 64 := by omega
  rw [memory_writeBytes_cells_noWrap m base bs hwrap a]
  have hnot : ¬ (base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + bs.length) := by omega
  exact dite_eq_right_of_eq_false (eq_false hnot)

private theorem patchTokenMemPlaced_cells_below
    {tokS tokO : BitVec 64} {m1 m2 : Memory} {sb : Nat} (hsb : sb ≤ 2 ^ 64)
    (hag : ∀ a : BitVec 64, a.toNat < sb → m1.cells a = m2.cells a)
    (htok1 : tokS.toNat + 1 ≤ sb)
    (htok2 : (tokO + 8#64).toNat + 4 ≤ sb) :
    ∀ a : BitVec 64, a.toNat < sb →
      (patchTokenMemPlaced tokS tokO m1).cells a = (patchTokenMemPlaced tokS tokO m2).cells a := by
  unfold patchTokenMemPlaced
  have h1 := writeBytes_cells_below_eq hsb hag tokS [0#8] htok1
  exact writeBytes_cells_below_eq hsb h1 (tokO + 8#64) [0#8, 0#8, 0#8, 0#8] htok2

private theorem patchTokenMemPlaced_cells_above
    {tokS tokO : BitVec 64} (m : Memory) {sb : Nat} (hsb : sb ≤ 2 ^ 64)
    (htok1 : tokS.toNat + 1 ≤ sb)
    (htok2 : (tokO + 8#64).toNat + 4 ≤ sb)
    {a : BitVec 64} (ha : sb ≤ a.toNat) :
    (patchTokenMemPlaced tokS tokO m).cells a = m.cells a := by
  unfold patchTokenMemPlaced
  have h2 := writeBytes_cells_above_eq (m.writeBytes tokS [0#8])
    hsb (tokO + 8#64) [0#8, 0#8, 0#8, 0#8] htok2 ha
  exact h2.trans (writeBytes_cells_above_eq m hsb tokS [0#8] htok1 ha)

private theorem prebuildSpecPlaced_cells_eq
    {W : CliHooks} {elf : ElfImage} {tokS tokO : BitVec 64}
    {addrs : MallocngCallAddrs} {stubs : List (String × Nat)} {pb : PrebuiltElfPlaced}
    (hspec : PrebuildSpecPlaced W elf tokS tokO addrs stubs pb) (a : BitVec 64) :
    rawCellAt pb.baseLines a.toNat =
      (patchTokenMemPlaced tokS tokO ⟨Snapshot.loadCellAt elf.segments⟩).cells a :=
  hspec.cells a

attribute [local irreducible] patchTokenMemPlaced
attribute [local irreducible] cliTokenPatchPlaced

private theorem loadState_ok_of_checks
    {elf : ElfImage} {pinputs : ProcessInputs} {sp : BitVec 64} {stackRegion : Snapshot.Region}
    (hwf : elf.WellFormed = true)
    (hdirs : pinputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d) = false)
    (hfiles : pinputs.files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) = false)
    (hstk : buildInitialStack elf pinputs = .ok (sp, stackRegion)) :
    elf.loadState pinputs = .ok {
      regs := RegFile.empty, vregs := VRegFile.empty, sp := sp, pc := elf.entry,
      pstate := PState.zero,
      mem := (⟨Snapshot.loadCellAt (elf.segments ++ [stackRegion])⟩ : Memory).mapZero
               (BitVec.ofNat 64 (pinputs.init.stackTop.toNat - pinputs.init.stackSize))
               pinputs.init.stackSize,
      tpidrEl0 := 0#64, brkStart := elf.brkStart, brk := elf.brkStart,
      physMemAvail := pinputs.init.physMemAvail, fs := initFsState pinputs,
      oracle := pinputs.init.oracle, oracleIdx := 0,
      exclFails := pinputs.init.oracle.exclFails, trace := [], status := .Running,
      symtab := fun _ name => (elf.symbols.find? (·.1 == name)).map (·.2) } := by
  simp only [ElfImage.loadState, hwf, hdirs, hfiles, hstk,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem sb_bv_rng_iff {top sz : Nat} (hsz_top : sz ≤ top) (htop_lt : top < 2 ^ 64)
    (a : BitVec 64) :
    (a - BitVec.ofNat 64 (top - sz)).toNat < sz ↔ (top - sz ≤ a.toNat ∧ a.toNat < top) := by
  have hsb_lt : top - sz < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le top sz) htop_lt
  have hsbBv_nat : (BitVec.ofNat 64 (top - sz)).toNat = top - sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsb_lt]
  have hsum : (top - sz) + sz = top := Nat.sub_add_cancel hsz_top
  have hw : (BitVec.ofNat 64 (top - sz)).toNat + sz ≤ 2 ^ 64 := by
    rw [hsbBv_nat, hsum]; exact Nat.le_of_lt htop_lt
  have hr := sub_lt_iff_range hw (a := a)
  rwa [hsbBv_nat, hsum] at hr

private theorem mapZero_stack_below {segments : List Snapshot.Region} {stackRegion : Snapshot.Region}
    {top sz : Nat} (hsz_top : sz ≤ top) (htop_lt : top < 2 ^ 64)
    (hsb_stk : top - sz ≤ stackRegion.start.toNat)
    (hstk_wrap : stackRegion.start.toNat + stackRegion.bytes.length ≤ 2 ^ 64)
    {a : BitVec 64} (ha : a.toNat < top - sz) :
    ((⟨Snapshot.loadCellAt (segments ++ [stackRegion])⟩ : Memory).mapZero
      (BitVec.ofNat 64 (top - sz)) sz).cells a = Snapshot.loadCellAt segments a := by
  dsimp only [Memory.mapZero]
  have hnot_sb : decide ((a - BitVec.ofNat 64 (top - sz)).toNat < sz) = false :=
    decide_eq_false (fun hlt =>
      Nat.not_le.mpr ha ((sb_bv_rng_iff hsz_top htop_lt a).mp hlt).1)
  simp only [hnot_sb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [loadCellAt_append_singleton,
    cellAt_eq_none_of_lt hstk_wrap (Nat.lt_of_lt_of_le ha hsb_stk), Option.or_none]

private theorem fastMem_cellAt_eq (lines : BinTree Line64) (sb top : Nat) (a : BitVec 64) :
    FastMem.cellAt { lines := lines, stackBase := sb, stackTop := top } a =
      (rawCellAt lines a.toNat).or
        (if decide (sb ≤ a.toNat) && decide (a.toNat < top) then
          some (some Perm.rw, 0#8) else none) := by
  simp only [FastMem.cellAt]
  cases rawCellAt lines a.toNat <;> rfl

private theorem mapZero_stack_above {segments : List Snapshot.Region} {stackRegion : Snapshot.Region}
    {top sz : Nat} (hsz_top : sz ≤ top) (htop_lt : top < 2 ^ 64)
    {a : BitVec 64} (ha_ge : top - sz ≤ a.toNat)
    (hseg_none : Snapshot.loadCellAt segments a = none) :
    (Snapshot.loadCellAt [stackRegion] a).or
      (if decide (top - sz ≤ a.toNat) && decide (a.toNat < top) then
        some (some Perm.rw, 0#8) else none) =
    ((⟨Snapshot.loadCellAt (segments ++ [stackRegion])⟩ : Memory).mapZero
      (BitVec.ofNat 64 (top - sz)) sz).cells a := by
  have hload_above : Snapshot.loadCellAt (segments ++ [stackRegion]) a =
      Snapshot.loadCellAt [stackRegion] a := by
    rw [loadCellAt_append_singleton, hseg_none, Option.none_or]
  dsimp only [Memory.mapZero]
  rw [hload_above]
  cases hcell_stk : Snapshot.loadCellAt [stackRegion] a with
  | some c =>
    obtain ⟨p, b, rfl⟩ := loadCellAt_perm_mapped_of_some' hcell_stk
    have hm : (!(Memory.perm ⟨Snapshot.loadCellAt (segments ++ [stackRegion])⟩ a).mapped) = false := by
      dsimp only [Memory.perm]; rw [hload_above, hcell_stk]; rfl
    rw [hm, Bool.and_false]; rfl
  | none =>
    have hm : (!(Memory.perm ⟨Snapshot.loadCellAt (segments ++ [stackRegion])⟩ a).mapped) = true := by
      dsimp only [Memory.perm]; rw [hload_above, hcell_stk]; rfl
    rw [hm, Bool.and_true, Option.none_or]
    by_cases hlt_top : a.toNat < top
    · have hc1 : (decide (top - sz ≤ a.toNat) && decide (a.toNat < top)) = true := by
        simp [ha_ge, hlt_top]
      have hc2 : decide ((a - BitVec.ofNat 64 (top - sz)).toNat < sz) = true :=
        decide_eq_true ((sb_bv_rng_iff hsz_top htop_lt a).mpr ⟨ha_ge, hlt_top⟩)
      rw [hc1, hc2]
    · have hc1 : (decide (top - sz ≤ a.toNat) && decide (a.toNat < top)) = false := by
        simp [hlt_top]
      have hc2 : decide ((a - BitVec.ofNat 64 (top - sz)).toNat < sz) = false :=
        decide_eq_false (fun hl => hlt_top ((sb_bv_rng_iff hsz_top htop_lt a).mp hl).2)
      rw [hc1, hc2]

private theorem initStackOverlay_mem_agrees
    {segments : List Snapshot.Region} {brk : Nat}
    {baseLines : BinTree Line64} {stackRegion : Snapshot.Region}
    {top sz : Nat} (hsz_top : sz ≤ top) (htop_lt : top < 2 ^ 64)
    (hseg_brk : ∀ r ∈ segments, r.start.toNat + r.bytes.length ≤ brk)
    (hbrk_sb : brk ≤ top - sz) (hsb_stk : top - sz ≤ stackRegion.start.toNat)
    (hstk_top : stackRegion.start.toNat + stackRegion.bytes.length ≤ top)
    {patchM : Memory → Memory}
    (hpatch_below : ∀ {m1 m2 : Memory},
      (∀ a : BitVec 64, a.toNat < top - sz → m1.cells a = m2.cells a) →
      ∀ a : BitVec 64, a.toNat < top - sz → (patchM m1).cells a = (patchM m2).cells a)
    (hpatch_above : ∀ (m : Memory) {a : BitVec 64},
      top - sz ≤ a.toNat → (patchM m).cells a = m.cells a)
    (hbase_raw : ∀ a : BitVec 64, rawCellAt baseLines a.toNat =
      (patchM ⟨Snapshot.loadCellAt segments⟩).cells a)
    {s0Mem : Memory}
    (hs0Mem : ∀ a : BitVec 64, s0Mem.cells a =
      ((⟨Snapshot.loadCellAt (segments ++ [stackRegion])⟩ : Memory).mapZero
        (BitVec.ofNat 64 (top - sz)) sz).cells a) :
    FastMem.Agrees
      { lines := setCellsAt baseLines stackRegion.start.toNat
          (regionToCells stackRegion.perm stackRegion.nonAnonLen 0 stackRegion.bytes)
        stackBase := top - sz, stackTop := top }
      (patchM s0Mem) ∧
    (∀ a : BitVec 64, a.toNat < top - sz →
      (patchM s0Mem).cells a = rawCellAt baseLines a.toNat) ∧
    (∀ a : BitVec 64, top ≤ a.toNat → (patchM s0Mem).cells a = none) := by
  have htop_64 : top ≤ 2 ^ 64 := Nat.le_of_lt htop_lt
  have hstk_wrap : stackRegion.start.toNat + stackRegion.bytes.length ≤ 2 ^ 64 :=
    Nat.le_trans hstk_top htop_64
  have hs0Mem_below : ∀ a : BitVec 64, a.toNat < top - sz →
      s0Mem.cells a = (⟨Snapshot.loadCellAt segments⟩ : Memory).cells a :=
    fun a ha => (hs0Mem a).trans (mapZero_stack_below hsz_top htop_lt hsb_stk hstk_wrap ha)
  have hs0Patched_below : ∀ a : BitVec 64, a.toNat < top - sz →
      (patchM s0Mem).cells a = (patchM ⟨Snapshot.loadCellAt segments⟩).cells a :=
    hpatch_below hs0Mem_below
  have hmSegP_above : ∀ a : BitVec 64, top - sz ≤ a.toNat →
      (patchM ⟨Snapshot.loadCellAt segments⟩).cells a = none := by
    intro a ha
    rw [hpatch_above ⟨Snapshot.loadCellAt segments⟩ ha]
    exact loadCellAt_eq_none_of_ge hseg_brk (Nat.le_trans hbrk_sb ha)
  have hmem_ag : FastMem.Agrees
      { lines := setCellsAt baseLines stackRegion.start.toNat
          (regionToCells stackRegion.perm stackRegion.nonAnonLen 0 stackRegion.bytes)
        stackBase := top - sz, stackTop := top }
      (patchM s0Mem) := by
    intro a
    rw [fastMem_cellAt_eq, rawCellAt_setRegion baseLines stackRegion hstk_wrap a, hbase_raw a]
    by_cases ha_sb : a.toNat < top - sz
    · rw [cellAt_eq_none_of_lt hstk_wrap (Nat.lt_of_lt_of_le ha_sb hsb_stk),
        Option.none_or, ← hs0Patched_below a ha_sb]
      have hnot : (decide (top - sz ≤ a.toNat) && decide (a.toNat < top)) = false := by
        simp [Nat.not_le.mpr ha_sb]
      simp only [hnot, Bool.false_eq_true, ↓reduceIte, Option.or_none]
    · have ha_ge : top - sz ≤ a.toNat := Nat.le_of_not_lt ha_sb
      rw [hmSegP_above a ha_ge, Option.or_none, hpatch_above s0Mem ha_ge, hs0Mem a]
      exact mapZero_stack_above (stackRegion := stackRegion) hsz_top htop_lt ha_ge
        (loadCellAt_eq_none_of_ge hseg_brk (Nat.le_trans hbrk_sb ha_ge))
  refine ⟨hmem_ag, fun a ha => (hs0Patched_below a ha).trans (hbase_raw a).symm, fun a ha => ?_⟩
  have ha_ge_sb : top - sz ≤ a.toNat := Nat.le_trans (Nat.sub_le top sz) ha
  rw [hpatch_above s0Mem ha_ge_sb, hs0Mem a,
    ← mapZero_stack_above (stackRegion := stackRegion) hsz_top htop_lt ha_ge_sb
      (loadCellAt_eq_none_of_ge hseg_brk (Nat.le_trans hbrk_sb ha_ge_sb)),
    loadCellAt_eq_none_of_ge (bound := top)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hstk_top) ha,
    Option.none_or]
  have hnot : (decide (top - sz ≤ a.toNat) && decide (a.toNat < top)) = false := by
    simp [Nat.not_lt.mpr ha]
  simp only [hnot, Bool.false_eq_true, ↓reduceIte]

private theorem initStackOverlay_heap_agrees
    {m : Memory} {top : Nat} (htop_60 : top ≤ 2 ^ 60)
    (hnone : ∀ a : BitVec 64, top ≤ a.toNat → m.cells a = none) :
    HeapIntervalsAgree [] m := by
  refine ⟨trivial, fun k hk => ?_⟩
  have haddr_nat := heapAddr_toNat (Nat.le_of_lt hk)
  have hge_top : top ≤ (heapBase + BitVec.ofNat 64 k).toNat := by omega
  have hcell_none := hnone (heapBase + BitVec.ofNat 64 k) hge_top
  simp [Memory.perm, hcell_none, inHeapIvs]

private theorem rawCellAt_baseLines_eq_none_of_brk_le
    {W : CliHooks} {elf : ElfImage} {tokS tokO : BitVec 64}
    {addrs : MallocngCallAddrs} {stubs : List (String × Nat)} {pb : PrebuiltElfPlaced}
    (hspec : PrebuildSpecPlaced W elf tokS tokO addrs stubs pb)
    {a : BitVec 64} (ha : elf.brkStart.toNat ≤ a.toNat) :
    rawCellAt pb.baseLines a.toNat = none := by
  have h48 := pow48_lt_pow64
  have hbrk_64 : elf.brkStart.toNat ≤ 2 ^ 64 := by have := hspec.brk_le; omega
  have htok2 : (tokO + 8#64).toNat + 4 ≤ elf.brkStart.toNat :=
    tokOnce_add8_bound hspec.tokO_le hspec.brk_le
  have hc : rawCellAt pb.baseLines a.toNat =
      (patchTokenMemPlaced tokS tokO ⟨Snapshot.loadCellAt elf.segments⟩).cells a :=
    prebuildSpecPlaced_cells_eq hspec a
  rw [hc, patchTokenMemPlaced_cells_above _ hbrk_64 hspec.tokS_le htok2 ha]
  exact loadCellAt_eq_none_of_ge hspec.seg_le_brk ha

/-- Derive `FastProgSoundPlaced` across the full 64-bit address space from cell agreement with
`pb.baseLines` below `elf.brkStart.toNat`: since `pb.baseLines` is unmapped at and above
`elf.brkStart.toNat`, every decoded instruction word lies strictly below `elf.brkStart.toNat`. -/
theorem fastProgSoundPlaced_of_baseLines_agree
    {mpl mmpl : MultiPlacement} {W : CliHooks} {elf : ElfImage} {tokS tokO : BitVec 64}
    {addrs : MallocngCallAddrs} {stubs : List (String × Nat)} {pb : PrebuiltElfPlaced}
    {m0 : Memory}
    (hspec : PrebuildSpecPlaced W elf tokS tokO addrs stubs pb)
    (hmatch : MallocngCallAddrsMatches addrs mmpl)
    (hagree : HooksAgreePlaced mpl mmpl W (overlayHooksPlaced W stubs .empty))
    (hm0 : ∀ a : BitVec 64, a.toNat < elf.brkStart.toNat →
      m0.cells a = rawCellAt pb.baseLines a.toNat) :
    FastProgSoundPlaced mpl mmpl W pb.prog m0 := by
  rw [hspec.prog_eq]
  refine ⟨hmatch, fun pc m hkf hmod4 => ?_⟩
  unfold lookupStepEntryPlaced
  dsimp only
  have hdiv_eq : Nat.div (pc.toNat / 4) 16 = (pc.toNat / 4) / 16 := rfl
  have hmod_eq : Nat.mod (pc.toNat / 4) 16 = (pc.toNat / 4) % 16 := rfl
  rw [hdiv_eq, hmod_eq]
  have hag_pc := hagree pc hmod4
  cases hbt : btGet progPlacedDepth (overlayHooksPlaced W stubs .empty) (pc.toNat / 4) with
  | some name =>
    rw [hbt] at hag_pc
    exact hag_pc
  | none =>
    rw [hbt] at hag_pc
    dsimp only
    cases hline : btGet 58 pb.baseLines ((pc.toNat / 4) / 16) with
    | none => trivial
    | some line =>
      dsimp only
      have hv := decodeStepFromLinePlaced_valid pb.baseLines
        ((pc.toNat / 4) / 16) ((pc.toNat / 4) % 16) line hline (by omega)
      cases hdec : decodeStepFromLinePlaced line ((pc.toNat / 4) % 16) with
      | hook _ => rw [hdec] at hv; exact False.elim hv
      | unmapped => trivial
      | instr inst =>
        rw [hdec] at hv
        rcases hv with ⟨p0, b0, p1, b1, p2, b2, p3, b3,
          ⟨hc0, _, _⟩, ⟨hc1, _, _⟩, ⟨hc2, _, _⟩, ⟨hc3, _, _⟩, _⟩
        have hpc_lt : pc.toNat < 2 ^ 64 := pc.isLt
        have hbase_eq : 64 * ((pc.toNat / 4) / 16) + 4 * ((pc.toNat / 4) % 16) = pc.toNat := by
          omega
        rw [hbase_eq] at hc0 hc1 hc2 hc3
        have htoNat_j : ∀ j < 4, (pc + BitVec.ofNat 64 j).toNat = pc.toNat + j := by
          intro j hj
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        have hsome_j : ∀ j < 4, rawCellAt pb.baseLines (pc + BitVec.ofNat 64 j).toNat ≠ none := by
          intro j hj
          rw [htoNat_j j hj]
          rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
          · rw [Nat.add_zero, hc0]; exact fun h => nomatch h
          · rw [hc1]; exact fun h => nomatch h
          · rw [hc2]; exact fun h => nomatch h
          · rw [hc3]; exact fun h => nomatch h
        have hlt_brk : ∀ j < 4, (pc + BitVec.ofNat 64 j).toNat < elf.brkStart.toNat := by
          intro j hj
          by_contra hge
          exact hsome_j j hj
            (rawCellAt_baseLines_eq_none_of_brk_le hspec (Nat.le_of_not_lt hge))
        exact decodeStepFromLinePlaced_fetchMem (mpl := mpl) (mmpl := mmpl) (W := W)
          (fun j hj => hm0 (pc + BitVec.ofNat 64 j) (hlt_brk j hj))
          hkf hmod4 hag_pc hline hdec

/-- If `initFastStateFromBasePlacedProcess` returns `some fs0`, then `elf.loadState pinputs`
succeeds with a state `s0` such that `fs0` agrees with `cliTokenPatchPlaced mpl s0` and `pb.prog`
is sound at `(cliTokenPatchPlaced mpl s0).mem`. -/
theorem initFastStateFromBasePlacedProcess_sound
    {mpl mmpl : MultiPlacement} {W : CliHooks} {elf : ElfImage}
    {addrs : MallocngCallAddrs} {stubs : List (String × Nat)}
    {pb : PrebuiltElfPlaced} {pinputs : ProcessInputs} {fs0 : FastState}
    (hspec : PrebuildSpecPlaced W elf (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl)
      addrs stubs pb)
    (hmatch : MallocngCallAddrsMatches addrs mmpl)
    (hagree : HooksAgreePlaced mpl mmpl W (overlayHooksPlaced W stubs .empty))
    (hinit : initFastStateFromBasePlacedProcess elf pb pinputs = some fs0) :
    ∃ s0 : State,
      elf.loadState pinputs = .ok s0 ∧
      fs0.Agrees (cliTokenPatchPlaced mpl s0) ∧
      FastProgSoundPlaced mpl mmpl W pb.prog (cliTokenPatchPlaced mpl s0).mem := by
  have hbase_raw : ∀ a : BitVec 64, rawCellAt pb.baseLines a.toNat =
      (patchTokenMemPlaced (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl)
        ⟨Snapshot.loadCellAt elf.segments⟩).cells a :=
    prebuildSpecPlaced_cells_eq hspec
  unfold initFastStateFromBasePlacedProcess at hinit
  cases hdirs : pinputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d)
  · simp only [hdirs, Bool.false_eq_true, ↓reduceIte] at hinit
    cases hfiles : pinputs.files.any (fun (p, bs) =>
        hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE))
    · simp only [hfiles, Bool.false_eq_true, ↓reduceIte] at hinit
      cases hstk : buildInitialStack elf pinputs with
      | error _ => rw [hstk] at hinit; nomatch hinit
      | ok pair =>
        rcases pair with ⟨sp, stackRegion⟩
        rw [hstk] at hinit; dsimp only at hinit
        rw [Symbolic.BugInjection.Proofs.CliExec.RadixMemAux.withForcedNat_eq] at hinit
        split at hinit; swap; · nomatch hinit
        rename_i hsz_top
        split at hinit; swap; · nomatch hinit
        rename_i hstack_bnds
        simp only [withForcedBinTree_eq] at hinit
        injection hinit with hinit; subst hinit
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hstack_bnds
        rcases hstack_bnds with ⟨⟨⟨hbrk_sb, hsb_stk⟩, hstk_top⟩, htop_60⟩
        have hload_ok := loadState_ok_of_checks hspec.wellFormed hdirs hfiles hstk
        generalize hs0Mem_eq :
          ((⟨Snapshot.loadCellAt (elf.segments ++ [stackRegion])⟩ : Memory).mapZero
            (BitVec.ofNat 64 (pinputs.init.stackTop.toNat - pinputs.init.stackSize))
            pinputs.init.stackSize) = s0Mem at hload_ok
        have htop_lt : pinputs.init.stackTop.toNat < 2 ^ 64 :=
          Nat.lt_of_le_of_lt htop_60 pow60_lt_pow64
        have hsb_64 : pinputs.init.stackTop.toNat - pinputs.init.stackSize ≤ 2 ^ 64 :=
          Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt htop_lt)
        have htok1_sb : (tokStorageAddrPlaced mpl).toNat + 1 ≤
            pinputs.init.stackTop.toNat - pinputs.init.stackSize :=
          Nat.le_trans hspec.tokS_le hbrk_sb
        have htok2_brk : (tokOnceAddrPlaced mpl + 8#64).toNat + 4 ≤ elf.brkStart.toNat :=
          tokOnce_add8_bound hspec.tokO_le hspec.brk_le
        have htok2_sb : (tokOnceAddrPlaced mpl + 8#64).toNat + 4 ≤
            pinputs.init.stackTop.toNat - pinputs.init.stackSize :=
          Nat.le_trans htok2_brk hbrk_sb
        obtain ⟨hmem_ag, hbelow_ag, habove_none⟩ :=
          initStackOverlay_mem_agrees hsz_top htop_lt hspec.seg_le_brk hbrk_sb hsb_stk hstk_top
            (patchM := patchTokenMemPlaced (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl))
            (fun h => patchTokenMemPlaced_cells_below hsb_64 h htok1_sb htok2_sb)
            (fun m _ ha => patchTokenMemPlaced_cells_above m hsb_64 htok1_sb htok2_sb ha)
            hbase_raw
            (s0Mem := s0Mem)
            (fun a => congrArg (fun m : Memory => m.cells a) hs0Mem_eq.symm)
        have hheap_ag := initStackOverlay_heap_agrees htop_60 habove_none
        have hpatch_state :
            cliTokenPatchPlaced mpl {
              regs := RegFile.empty, vregs := VRegFile.empty, sp := sp, pc := elf.entry,
              pstate := PState.zero, mem := s0Mem, tpidrEl0 := 0#64,
              brkStart := elf.brkStart, brk := elf.brkStart,
              physMemAvail := pinputs.init.physMemAvail, fs := initFsState pinputs,
              oracle := pinputs.init.oracle, oracleIdx := 0,
              exclFails := pinputs.init.oracle.exclFails, trace := [], status := .Running,
              symtab := fun _ name => (elf.symbols.find? (·.1 == name)).map (·.2) } =
            { regs := RegFile.empty, vregs := VRegFile.empty, sp := sp, pc := elf.entry,
              pstate := PState.zero,
              mem := patchTokenMemPlaced (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl) s0Mem,
              tpidrEl0 := 0#64,
              brkStart := elf.brkStart, brk := elf.brkStart,
              physMemAvail := pinputs.init.physMemAvail, fs := initFsState pinputs,
              oracle := pinputs.init.oracle, oracleIdx := 0,
              exclFails := pinputs.init.oracle.exclFails, trace := [], status := .Running,
              symtab := fun _ name => (elf.symbols.find? (·.1 == name)).map (·.2) } :=
          cliTokenPatchPlaced_eq_setMem mpl _
        refine ⟨_, hload_ok, ?_, ?_⟩
        · rw [hpatch_state]
          exact {
            regs := FastRegs.empty_agrees, sp := rfl, pc := rfl, pstate := rfl,
            mem := hmem_ag,
            heapIvs := hheap_ag,
            tpidrEl0 := rfl, fpsr := rfl,
            brkStart := rfl, brk := rfl, physMemAvail := rfl, fs := initFastFs_agrees pinputs,
            oracle := rfl, oracleIdx := rfl, exclFails := rfl, trace := rfl,
            status := rfl, sigAltStack := rfl }
        · rw [hpatch_state]
          exact fastProgSoundPlaced_of_baseLines_agree (mpl := mpl) (mmpl := mmpl) (W := W)
            hspec hmatch hagree
            (fun a ha_brk => hbelow_ag a (Nat.lt_of_lt_of_le ha_brk hbrk_sb))
    · simp only [hfiles, ↓reduceIte] at hinit; nomatch hinit
  · simp only [hdirs, ↓reduceIte] at hinit; nomatch hinit

theorem initFastStateFromBasePlaced_sound
    {mpl mmpl : MultiPlacement} {W : CliHooks} {elf : ElfImage}
    {addrs : MallocngCallAddrs} {stubs : List (String × Nat)}
    {pb : PrebuiltElfPlaced} {inp : Inputs} {fs0 : FastState}
    (hspec : PrebuildSpecPlaced W elf (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl)
      addrs stubs pb)
    (hmatch : MallocngCallAddrsMatches addrs mmpl)
    (hagree : HooksAgreePlaced mpl mmpl W (overlayHooksPlaced W stubs .empty))
    (hinit : initFastStateFromBasePlaced elf pb inp = some fs0) :
    ∃ s0 : State,
      elf.loadState (cliProcessInputs inp) = .ok s0 ∧
      fs0.Agrees (cliTokenPatchPlaced mpl s0) ∧
      FastProgSoundPlaced mpl mmpl W pb.prog (cliTokenPatchPlaced mpl s0).mem :=
  initFastStateFromBasePlacedProcess_sound (mpl := mpl) (mmpl := mmpl) (W := W)
    hspec hmatch hagree hinit

theorem initFastStateFromBasePlaced_eq_header
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {fs : ElfFullSpecPlaced} (inp : Inputs)
    (hv : ElfFullValidPlaced mpl mmpl elf fs) :
    initFastStateFromBasePlaced elf (prebuiltOfFullPlaced fs) inp =
      initFastStateFromBasePlaced (headerElfOfFullPlaced fs) (prebuiltOfFullPlaced fs) inp :=
  initFastStateFromBasePlaced_congr (prebuiltOfFullPlaced fs) inp
    hv.entry_eq hv.phdrVaddr_eq hv.phent_eq hv.phnum_eq hv.brkStart_eq

theorem initFastStateFromBasePlaced_sound_of_valid_with
    {mpl mmpl : MultiPlacement} {W : CliHooks} {elf : ElfImage}
    {fs : ElfFullSpecPlaced} {inp : Inputs} {fs0 : FastState}
    (hhk_agree : checkHooksAlignedPlaced mpl = true →
      HooksAgreePlaced mpl mmpl compHooks0
        (overlayHooksPlaced compHooks0 (stubsOfMpl mpl) .empty))
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hinit : initFastStateFromBasePlaced elf (prebuiltOfFullPlaced fs) inp = some fs0) :
    ∃ s0 : State,
      elf.loadState (cliProcessInputs inp) = .ok s0 ∧
      fs0.Agrees (cliTokenPatchPlaced mpl s0) ∧
      FastProgSoundPlaced mpl mmpl W (prebuiltOfFullPlaced fs).prog
        (cliTokenPatchPlaced mpl s0).mem ∧
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl (cliTokenPatchPlaced mpl s0).mem := by
  obtain ⟨s0, hload, hag0, hfp0⟩ :=
    initFastStateFromBasePlaced_sound (mpl := mpl) (mmpl := mmpl) (W := compHooks0)
      (prebuildElfPlaced_sound hv.prebuild_eq)
      (mallocngCallAddrsPlaced_matches mmpl)
      (hhk_agree hv.hooksAligned)
      hinit
  exact ⟨s0, hload, hag0, FastProgSoundPlaced.congr_W hW hfp0,
    codeLoaded_cliTokenPatchPlaced hv hload⟩

/-- Combine `ElfFullValidPlaced` and `initFastStateFromBasePlaced = some fs0` to obtain the
initial `elf.loadState` witness `s0`, `FastState.Agrees`, `FastProgSoundPlaced`, and
`mallocngLib.CodeLoaded` after `cliTokenPatchPlaced`. -/
theorem initFastStateFromBasePlaced_sound_of_valid
    {mpl mmpl : MultiPlacement} {W : CliHooks} {elf : ElfImage}
    {fs : ElfFullSpecPlaced} {inp : Inputs} {fs0 : FastState}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hinit : initFastStateFromBasePlaced elf (prebuiltOfFullPlaced fs) inp = some fs0) :
    ∃ s0 : State,
      elf.loadState (cliProcessInputs inp) = .ok s0 ∧
      fs0.Agrees (cliTokenPatchPlaced mpl s0) ∧
      FastProgSoundPlaced mpl mmpl W (prebuiltOfFullPlaced fs).prog
        (cliTokenPatchPlaced mpl s0).mem ∧
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl (cliTokenPatchPlaced mpl s0).mem :=
  initFastStateFromBasePlaced_sound_of_valid_with
    (@hooksAgreePlaced_stubsOfMpl mpl mmpl) hv hW hinit

theorem initFastStateFromBasePlaced_sound_of_valid_compHooks0
    {mpl mmpl : MultiPlacement} {elf : ElfImage}
    {fs : ElfFullSpecPlaced} {inp : Inputs} {fs0 : FastState}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    (hinit : initFastStateFromBasePlaced elf (prebuiltOfFullPlaced fs) inp = some fs0) :
    ∃ s0 : State,
      elf.loadState (cliProcessInputs inp) = .ok s0 ∧
      fs0.Agrees (cliTokenPatchPlaced mpl s0) ∧
      FastProgSoundPlaced mpl mmpl compHooks0 (prebuiltOfFullPlaced fs).prog
        (cliTokenPatchPlaced mpl s0).mem ∧
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl (cliTokenPatchPlaced mpl s0).mem :=
  initFastStateFromBasePlaced_sound_of_valid hv (fun _ => rfl) hinit

theorem initFastStateFromBasePlaced_sound_of_valid_header
    {mpl mmpl : MultiPlacement} {W : CliHooks} {elf : ElfImage}
    {fs : ElfFullSpecPlaced} {inp : Inputs} {fs0 : FastState}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    (hW : ∀ name, cliExternsPlacedSig mmpl compHooks0 name = cliExternsPlacedSig mmpl W name)
    (hinit : initFastStateFromBasePlaced (headerElfOfFullPlaced fs)
      (prebuiltOfFullPlaced fs) inp = some fs0) :
    ∃ s0 : State,
      elf.loadState (cliProcessInputs inp) = .ok s0 ∧
      fs0.Agrees (cliTokenPatchPlaced mpl s0) ∧
      FastProgSoundPlaced mpl mmpl W (prebuiltOfFullPlaced fs).prog
        (cliTokenPatchPlaced mpl s0).mem ∧
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl (cliTokenPatchPlaced mpl s0).mem :=
  initFastStateFromBasePlaced_sound_of_valid hv hW
    ((initFastStateFromBasePlaced_eq_header inp hv).trans hinit)

end Symbolic.BugInjection.Proofs.CliExec.InitPlacedSound
