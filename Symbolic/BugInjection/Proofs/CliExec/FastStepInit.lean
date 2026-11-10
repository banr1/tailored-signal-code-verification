/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.Process.FastParse
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProcessFixed
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooks
public import Symbolic.BugInjection.Proofs.CliExec.FastStepInitAux

/-!
# Shared-Base Initial State Loader and Soundness

Builds shared per-ELF segment memory and pre-decoded program tables (`prebuildElf`,
`prebuildMutantElf`) after checking `ElfImage.WellFormed` and token-patch bounds. Per-invocation
initialization (`initFastStateFromBaseProcess`, `initFastStateFromBase`) overlays only the initial
stack region onto `pb.baseLines` and proves `elf.loadState = .ok s0`,
`fs0.Agrees (cliTokenPatch s0)`, and `FastProgSound`.
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.FastStepInit

set_option autoImplicit false

open Arm64 Arm64.Memory Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.E2E (heapBase heapSize)
open CryptoVerification.LibsignalSpqrV1 (tokenOnceOff tokenStorageOff)
open CryptoVerification.SignalSession (CliHooks Inputs cliBase cliExternsAbortOnPanic
  cliProcessInputs cliTokenPatch)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
open Symbolic.BugInjection.Proofs.CliExec.FastHooks
open Symbolic.BugInjection.Proofs.CliExec.FastStepInitAux

export Symbolic.BugInjection.Proofs.CliExec.FastStepInitAux (progDepth progWordBound progByteBound
  StepEntry FastProg PrebuiltElf decodeStepFromLine lookupStepEntry
  overlayHooks buildFastProgWithLens buildFastProg buildFastProg0
  FastProgSound fastProgSound_of_cells_agree)

/-- Check `elf.WellFormed`, 48-bit `brkStart` bound, and `cliTokenPatch` range bounds using
precomputed segment lengths `regsWithLen`. -/
def checkElfPrebuildOk (elf : ElfImage) (regsWithLen : List (Snapshot.Region × Nat)) : Bool :=
  !elf.segments.isEmpty &&
  elf.phent == 56 &&
  fastRegionsDisjointAndAligned regsWithLen &&
  fastEntryInExecRegion elf.entry regsWithLen &&
  elf.brkStart.toNat % Obj.pageSize == 0 &&
  regsWithLen.all (fun (r, len) => r.start.toNat + len ≤ elf.brkStart.toNat) &&
  elf.brkStart.toNat ≤ 2 ^ 48 &&
  (cliBase + tokenStorageOff).toNat + 1 ≤ elf.brkStart.toNat &&
  (cliBase + tokenOnceOff).toNat + 4 ≤ elf.brkStart.toNat

def patchTokenFastMem (fm0 : FastMem) : FastMem :=
  (fm0.writeBytes (cliBase + tokenStorageOff) [0#8]).writeBytes
    (cliBase + tokenOnceOff) [0#8, 0#8, 0#8, 0#8]

def prebuildElfBaseLines (elf : ElfImage) : Option (BinTree Line64) :=
  let regsWithLen := mapRegionsWithLen elf.segments
  if checkElfPrebuildOk elf regsWithLen then
    let fm0 : FastMem := { lines := loadRegionsLines elf.segments, stackBase := 0, stackTop := 0 }
    some (patchTokenFastMem fm0).lines
  else
    none

/-- Load `li.code` and `padLen` zero-padding bytes at `cliBase` directly so
`li.code ++ List.replicate padLen 0#8` is never materialized in kernel WHNF. -/
def loadMutantSegments (code : List (BitVec 8)) (codeLen padLen : Nat)
    (tailSegs : List Snapshot.Region) : BinTree Line64 :=
  withForcedBinTree (loadRegionsLines tailSegs) fun tailLines =>
  withForcedBinTree (loadRegionFast tailLines cliBase.toNat codeLen Perm.rx code) fun codeLines =>
    setCellsAt codeLines (Nat.add cliBase.toNat codeLen)
      (regionToCells Perm.rx codeLen codeLen (List.replicate padLen 0#8))

/-- Build `PrebuiltElf` from decomposed mutant segments (`li.code`, `padLen`, `tailSegs`) and
precomputed `regsWithLen`. -/
def prebuildMutantElf (W : CliHooks) (li : LinkedImage) (elf : ElfImage)
    (codeLen padLen : Nat) (tailSegs : List Snapshot.Region)
    (regsWithLen : List (Snapshot.Region × Nat)) : Option PrebuiltElf :=
  if checkElfPrebuildOk elf regsWithLen then
    let fm0 : FastMem :=
      { lines := loadMutantSegments li.code codeLen padLen tailSegs, stackBase := 0, stackTop := 0 }
    withForcedBinTree (patchTokenFastMem fm0).lines fun baseLines =>
      some { baseLines := baseLines, prog := buildFastProgWithLens W li regsWithLen baseLines }
  else
    none

def prebuildElfWithLens (W : CliHooks) (li : LinkedImage) (elf : ElfImage)
    (regsWithLen : List (Snapshot.Region × Nat)) : Option PrebuiltElf :=
  if checkElfPrebuildOk elf regsWithLen then
    let fm0 : FastMem := { lines := loadRegionsLines elf.segments, stackBase := 0, stackTop := 0 }
    withForcedBinTree (patchTokenFastMem fm0).lines fun baseLines =>
      some { baseLines := baseLines, prog := buildFastProgWithLens W li regsWithLen baseLines }
  else
    none

/-- Validate `elf` and build its shared token-patched `baseLines` and `FastProg`. -/
def prebuildElf (W : CliHooks) (li : LinkedImage) (elf : ElfImage) : Option PrebuiltElf :=
  prebuildElfWithLens W li elf (mapRegionsWithLen elf.segments)

theorem prebuildElfWithLens_eq_prebuildElf (W : CliHooks) (li : LinkedImage) (elf : ElfImage)
    {regsWithLen : List (Snapshot.Region × Nat)}
    (hlens : regsWithLen = elf.segments.map (fun r => (r, r.bytes.length))) :
    prebuildElfWithLens W li elf regsWithLen = prebuildElf W li elf := by
  rw [prebuildElf, mapRegionsWithLen_eq, hlens]

abbrev prebuildElf0 : LinkedImage → ElfImage → Option PrebuiltElf :=
  prebuildElf compHooks0

/-- Initialize `FastState` for `pinputs` by overlaying the initial stack region onto
`pb.baseLines`. -/
def initFastStateFromBaseProcess (elf : ElfImage) (pb : PrebuiltElf)
    (pinputs : ProcessInputs) : Option FastState :=
  if pinputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d) then
    none
  else if pinputs.files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) then
    none
  else
    match buildInitialStack elf pinputs with
    | .error _ => none
    | .ok (sp, stackRegion) =>
      let top := pinputs.init.stackTop.toNat
      let sz := pinputs.init.stackSize
      RadixMemAux.withForcedNat stackRegion.bytes.length fun stackLen =>
        if sz ≤ top then
          let sb := top - sz
          if elf.brkStart.toNat ≤ sb &&
              cliBase.toNat + progByteBound ≤ sb &&
              sb ≤ stackRegion.start.toNat &&
              stackRegion.start.toNat + stackLen ≤ top &&
              top ≤ 2 ^ 60 then
            let stackCells := regionToCells stackRegion.perm stackRegion.nonAnonLen 0 stackRegion.bytes
            withForcedBinTree (setCellsAt pb.baseLines stackRegion.start.toNat stackCells) fun lines =>
              let fm : FastMem := { lines := lines, stackBase := sb, stackTop := top }
              some {
                regs         := FastRegs.empty
                sp           := sp
                pc           := elf.entry
                pstate       := PState.zero
                mem          := fm
                heapIvs      := []
                tpidrEl0     := 0#64
                fpsr         := 0#32
                brkStart     := elf.brkStart
                brk          := elf.brkStart
                physMemAvail := pinputs.init.physMemAvail
                fs           := initFastFs pinputs
                oracle       := pinputs.init.oracle
                oracleIdx    := 0
                exclFails    := pinputs.init.oracle.exclFails
                trace        := []
                status       := .Running
                sigAltStack  := {}
              }
          else none
        else none

def initFastStateFromBase (elf : ElfImage) (pb : PrebuiltElf) (inp : Inputs) : Option FastState :=
  initFastStateFromBaseProcess elf pb (cliProcessInputs inp)

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
        let p := { r.perm with lazyFree := false, anon := if (a - r.start).toNat < r.nonAnonLen then false else r.perm.anon }
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

private theorem rawCellAt_loadRegionsLines' (regions : List Snapshot.Region)
    (hwrap : ∀ r ∈ regions, r.start.toNat + r.bytes.length ≤ 2 ^ 64) (a : BitVec 64) :
    rawCellAt (loadRegionsLines regions) a.toNat = Snapshot.loadCellAt regions a := by
  induction regions with
  | nil => simp [loadRegionsLines, rawCellAt, Snapshot.loadCellAt]
  | cons r rs ih =>
    have hcons : loadRegionsLines (r :: rs) =
        loadRegionFast (loadRegionsLines rs) r.start.toNat r.nonAnonLen r.perm r.bytes := by
      (conv_lhs => unfold loadRegionsLines); cases loadRegionsLines rs <;> rfl
    rw [hcons, linesEq_loadRegionFast _ r.start.toNat r.nonAnonLen r.perm r.bytes a.toNat a.isLt,
      ← linesEq_setCellsAt _ r.start.toNat _ a.toNat a.isLt,
      rawCellAt_setRegion _ r (hwrap r (List.mem_cons_self ..)) a,
      ih (fun q hq => hwrap q (List.mem_cons_of_mem _ hq)), ← loadCellAt_cons]

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

private theorem writeBytes_stackBase_eq (fm : FastMem) (base : BitVec 64) (bs : List (BitVec 8)) :
    (fm.writeBytes base bs).stackBase = fm.stackBase ∧
      (fm.writeBytes base bs).stackTop = fm.stackTop := by
  have hslow : ∀ (f : FastMem) (b : BitVec 64) (xs : List (BitVec 8)),
      (f.writeBytesSlow b xs).stackBase = f.stackBase ∧
        (f.writeBytesSlow b xs).stackTop = f.stackTop := by
    intro f b xs
    induction xs generalizing f b with
    | nil => exact ⟨rfl, rfl⟩
    | cons _ rest ih =>
      rcases f with ⟨_, _, _⟩
      simpa only [FastMem.writeBytesSlow, FastMem.write8, FastMem.mkFastMem_eq]
        using ih _ (b + 1#64)
  cases bs with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ =>
    rcases fm with ⟨_, _, _⟩
    simp only [FastMem.writeBytes, FastMem.withForcedLineOpt_eq, withForcedBinTree_eq]
    split
    · exact ⟨rfl, rfl⟩
    · exact hslow _ base _

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

def patchTokenMem (m : Memory) : Memory :=
  (m.writeBytes (cliBase + tokenStorageOff) [0#8]).writeBytes
    (cliBase + tokenOnceOff) [0#8, 0#8, 0#8, 0#8]

private theorem cliTokenPatch_mem_eq (s : State) :
    (cliTokenPatch s).mem = patchTokenMem s.mem := rfl

private theorem cliTokenPatch_eq_setMem (s : State) :
    cliTokenPatch s = s.setMem (patchTokenMem s.mem) := rfl

private theorem patchTokenFastMem_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m) :
    (patchTokenFastMem fm).Agrees (patchTokenMem m) :=
  FastMem.writeBytes_agrees (FastMem.writeBytes_agrees h _ _) _ _

private theorem patchTokenFastMem_stackBase_eq (fm : FastMem) :
    (patchTokenFastMem fm).stackBase = fm.stackBase ∧
      (patchTokenFastMem fm).stackTop = fm.stackTop := by
  unfold patchTokenFastMem
  have h1 := writeBytes_stackBase_eq fm (cliBase + tokenStorageOff) [0#8]
  have h2 := writeBytes_stackBase_eq (fm.writeBytes (cliBase + tokenStorageOff) [0#8])
    (cliBase + tokenOnceOff) [0#8, 0#8, 0#8, 0#8]
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

attribute [local irreducible] patchTokenFastMem buildFastProgWithLens

private theorem regionToCells_append (perm : Perm) (nonAnonLen : Nat) :
    ∀ (i : Nat) (bs1 bs2 : List (BitVec 8)),
      regionToCells perm nonAnonLen i (bs1 ++ bs2) =
        regionToCells perm nonAnonLen i bs1 ++
          regionToCells perm nonAnonLen (i + bs1.length) bs2
  | _, [], _ => by simp [regionToCells]
  | i, _ :: bs1, bs2 => by
    simp only [List.cons_append, regionToCells, List.length_cons,
      regionToCells_append perm nonAnonLen (i + 1) bs1 bs2]
    have hadd : i + 1 + bs1.length = i + (bs1.length + 1) := by omega
    rw [hadd]

private theorem rawCellAt_loadMutantSegments (code : List (BitVec 8)) (padLen : Nat)
    (tailSegs : List Snapshot.Region)
    (hwrap0 : cliBase.toNat + (code ++ List.replicate padLen 0#8).length ≤ 2 ^ 64)
    (hwrap_tail : ∀ r ∈ tailSegs, r.start.toNat + r.bytes.length ≤ 2 ^ 64)
    (a : BitVec 64) :
    let seg0 : Snapshot.Region :=
      { start := cliBase, perm := Perm.rx,
        bytes := code ++ List.replicate padLen 0#8, nonAnonLen := code.length }
    rawCellAt (loadMutantSegments code code.length padLen tailSegs) a.toNat =
      Snapshot.loadCellAt (seg0 :: tailSegs) a := by
  intro seg0
  have hadd_eq : Nat.add cliBase.toNat code.length = cliBase.toNat + code.length := rfl
  simp only [loadMutantSegments, withForcedBinTree_eq, hadd_eq]
  set tailLines := loadRegionsLines tailSegs
  set cs1 := regionToCells Perm.rx code.length 0 code
  set cs2 := regionToCells Perm.rx code.length code.length (List.replicate padLen 0#8)
  have hlen1 : cs1.length = code.length := regionToCells_length' Perm.rx code.length 0 code
  have hwrap1 : cliBase.toNat + cs1.length ≤ 2 ^ 64 := by
    rw [hlen1]; rw [List.length_append] at hwrap0; omega
  rw [linesEq_setCellsAt _ (cliBase.toNat + code.length) cs2 a.toNat a.isLt,
    linesEq_foldSetRawCell
      (linesEq_loadRegionFast tailLines cliBase.toNat code.length Perm.rx code)
      (cliBase.toNat + code.length) cs2 a.toNat a.isLt]
  have hadd1 : cliBase.toNat + code.length = cliBase.toNat + cs1.length := by rw [hlen1]
  change rawCellAt (foldSetRawCell (foldSetRawCell tailLines cliBase.toNat cs1)
      (cliBase.toNat + code.length) cs2) a.toNat = _
  rw [hadd1, ← foldSetRawCell_append tailLines cliBase.toNat cs1 cs2 hwrap1]
  have hcs : cs1 ++ cs2 = regionToCells seg0.perm seg0.nonAnonLen 0 seg0.bytes := by
    dsimp only [cs1, cs2, seg0]
    have := regionToCells_append Perm.rx code.length 0 code (List.replicate padLen 0#8)
    simpa only [Nat.zero_add] using this.symm
  rw [hcs, ← linesEq_setCellsAt tailLines seg0.start.toNat _ a.toNat a.isLt,
    rawCellAt_setRegion tailLines seg0 hwrap0 a,
    rawCellAt_loadRegionsLines' tailSegs hwrap_tail a, ← loadCellAt_cons]

/-- Abstract postcondition shared by `prebuildElf` and `prebuildMutantElf`. -/
def PrebuildSpec (W : CliHooks) (li : LinkedImage) (elf : ElfImage) (pb : PrebuiltElf) : Prop :=
  elf.WellFormed = true ∧
  (∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ elf.brkStart.toNat) ∧
  elf.brkStart.toNat ≤ 2 ^ 48 ∧
  (cliBase + tokenStorageOff).toNat + 1 ≤ elf.brkStart.toNat ∧
  (cliBase + tokenOnceOff).toNat + 4 ≤ elf.brkStart.toNat ∧
  (∀ a : BitVec 64, rawCellAt pb.baseLines a.toNat =
    (patchTokenMem ⟨Snapshot.loadCellAt elf.segments⟩).cells a) ∧
  ∃ regsWithLen, pb.prog = buildFastProgWithLens W li regsWithLen pb.baseLines

private theorem prebuildElf_sound
    {W : CliHooks} {li : LinkedImage} {elf : ElfImage} {pb : PrebuiltElf}
    (hpb : prebuildElf W li elf = some pb) :
    PrebuildSpec W li elf pb := by
  unfold prebuildElf prebuildElfWithLens at hpb
  simp only [withForcedBinTree_eq] at hpb
  split at hpb; swap; · nomatch hpb
  rename_i hok
  set fm0 : FastMem := { lines := loadRegionsLines elf.segments, stackBase := 0, stackTop := 0 }
  have hwf_fast : fastWellFormed elf = true := by
    unfold checkElfPrebuildOk at hok; unfold fastWellFormed
    simp only [Bool.and_eq_true] at hok ⊢; exact hok.1.1.1
  have hwf : elf.WellFormed = true := (fastWellFormed_eq elf).symm.trans hwf_fast
  have hok_bounds :
      (∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ elf.brkStart.toNat) ∧
      elf.brkStart.toNat ≤ 2 ^ 48 ∧
      (cliBase + tokenStorageOff).toNat + 1 ≤ elf.brkStart.toNat ∧
      (cliBase + tokenOnceOff).toNat + 4 ≤ elf.brkStart.toNat := by
    unfold checkElfPrebuildOk at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, mapRegionsWithLen_eq, List.all_map,
      List.all_eq_true] at hok
    exact ⟨fun r hr => of_decide_eq_true (hok.1.1.1.2 r hr), hok.1.1.2, hok.1.2, hok.2⟩
  rcases hok_bounds with ⟨hseg_brk, hbrk_48, htok1_brk, htok2_brk⟩
  have hseg_wrap : ∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ 2 ^ 64 :=
    fun r hr => by have := hseg_brk r hr; omega
  have hfm0_ag : fm0.Agrees ⟨Snapshot.loadCellAt elf.segments⟩ := by
    intro a; dsimp only [FastMem.cellAt, fm0]
    rw [rawCellAt_loadRegionsLines' elf.segments hseg_wrap a]
    cases Snapshot.loadCellAt elf.segments a with
    | some _ => rfl
    | none => simp
  have hfm1_ag := patchTokenFastMem_agrees hfm0_ag
  have hfm1_sb := patchTokenFastMem_stackBase_eq fm0
  generalize patchTokenFastMem fm0 = fm1 at hpb hfm1_ag hfm1_sb
  injection hpb with hpb; subst hpb
  refine ⟨hwf, hseg_brk, hbrk_48, htok1_brk, htok2_brk, ?_, mapRegionsWithLen elf.segments, rfl⟩
  intro a
  have hc := hfm1_ag a
  dsimp only [FastMem.cellAt] at hc
  rw [hfm1_sb.1, hfm1_sb.2] at hc
  cases hr : rawCellAt fm1.lines a.toNat with
  | some _ => rw [hr] at hc; exact hc
  | none =>
    rw [hr] at hc; dsimp only at hc
    have hnot : (decide (0 ≤ a.toNat) && decide (a.toNat < 0)) = false := by simp
    rw [hnot] at hc
    exact hc

theorem prebuildMutantElf_sound
    {W : CliHooks} {li : LinkedImage} {elf : ElfImage} {pb : PrebuiltElf}
    {codeLen padLen : Nat} {tailSegs : List Snapshot.Region}
    {regsWithLen : List (Snapshot.Region × Nat)}
    (hcl : codeLen = li.code.length)
    (hsegs : elf.segments =
      { start := cliBase, perm := Perm.rx,
        bytes := li.code ++ List.replicate padLen 0#8, nonAnonLen := li.code.length } :: tailSegs)
    (hlens : regsWithLen = elf.segments.map (fun r => (r, r.bytes.length)))
    (hpb : prebuildMutantElf W li elf codeLen padLen tailSegs regsWithLen = some pb) :
    PrebuildSpec W li elf pb := by
  subst hcl
  unfold prebuildMutantElf at hpb
  simp only [withForcedBinTree_eq] at hpb
  split at hpb; swap; · nomatch hpb
  rename_i hok
  have hok' : checkElfPrebuildOk elf (mapRegionsWithLen elf.segments) = true := by
    rwa [mapRegionsWithLen_eq, ← hlens]
  set fm0 : FastMem :=
    { lines := loadMutantSegments li.code li.code.length padLen tailSegs, stackBase := 0, stackTop := 0 }
  have hwf_fast : fastWellFormed elf = true := by
    unfold checkElfPrebuildOk at hok'; unfold fastWellFormed
    simp only [Bool.and_eq_true] at hok' ⊢; exact hok'.1.1.1
  have hwf : elf.WellFormed = true := (fastWellFormed_eq elf).symm.trans hwf_fast
  have hok_bounds :
      (∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ elf.brkStart.toNat) ∧
      elf.brkStart.toNat ≤ 2 ^ 48 ∧
      (cliBase + tokenStorageOff).toNat + 1 ≤ elf.brkStart.toNat ∧
      (cliBase + tokenOnceOff).toNat + 4 ≤ elf.brkStart.toNat := by
    unfold checkElfPrebuildOk at hok'
    simp only [Bool.and_eq_true, decide_eq_true_eq, mapRegionsWithLen_eq, List.all_map,
      List.all_eq_true] at hok'
    exact ⟨fun r hr => of_decide_eq_true (hok'.1.1.1.2 r hr), hok'.1.1.2, hok'.1.2, hok'.2⟩
  rcases hok_bounds with ⟨hseg_brk, hbrk_48, htok1_brk, htok2_brk⟩
  have hseg_wrap : ∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ 2 ^ 64 :=
    fun r hr => by have := hseg_brk r hr; omega
  have hwrap0 : cliBase.toNat + (li.code ++ List.replicate padLen 0#8).length ≤ 2 ^ 64 := by
    let seg0 : Snapshot.Region :=
      { start := cliBase, perm := Perm.rx,
        bytes := li.code ++ List.replicate padLen 0#8, nonAnonLen := li.code.length }
    exact hseg_wrap seg0 (by rw [hsegs]; exact List.mem_cons_self ..)
  have hwrap_tail : ∀ r ∈ tailSegs, r.start.toNat + r.bytes.length ≤ 2 ^ 64 :=
    fun r hr => hseg_wrap r (by rw [hsegs]; exact List.mem_cons_of_mem _ hr)
  have hfm0_ag : fm0.Agrees ⟨Snapshot.loadCellAt elf.segments⟩ := by
    intro a; dsimp only [FastMem.cellAt, fm0]
    rw [hsegs, rawCellAt_loadMutantSegments li.code padLen tailSegs hwrap0 hwrap_tail a]
    cases Snapshot.loadCellAt _ a with
    | some _ => rfl
    | none => simp
  have hfm1_ag := patchTokenFastMem_agrees hfm0_ag
  have hfm1_sb := patchTokenFastMem_stackBase_eq fm0
  generalize patchTokenFastMem fm0 = fm1 at hpb hfm1_ag hfm1_sb
  injection hpb with hpb; subst hpb
  refine ⟨hwf, hseg_brk, hbrk_48, htok1_brk, htok2_brk, ?_, regsWithLen, rfl⟩
  intro a
  have hc := hfm1_ag a
  dsimp only [FastMem.cellAt] at hc
  rw [hfm1_sb.1, hfm1_sb.2] at hc
  cases hr : rawCellAt fm1.lines a.toNat with
  | some _ => rw [hr] at hc; exact hc
  | none =>
    rw [hr] at hc; dsimp only at hc
    have hnot : (decide (0 ≤ a.toNat) && decide (a.toNat < 0)) = false := by simp
    rw [hnot] at hc
    exact hc

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

private theorem pow60_lt_pow64 : 2 ^ 60 < 2 ^ 64 :=
  Nat.pow_lt_pow_right (by decide) (by decide)

private theorem patchTokenMem_cells_below {m1 m2 : Memory} {sb : Nat} (hsb : sb ≤ 2 ^ 64)
    (hag : ∀ a : BitVec 64, a.toNat < sb → m1.cells a = m2.cells a)
    (htok1 : (cliBase + tokenStorageOff).toNat + 1 ≤ sb)
    (htok2 : (cliBase + tokenOnceOff).toNat + 4 ≤ sb) :
    ∀ a : BitVec 64, a.toNat < sb → (patchTokenMem m1).cells a = (patchTokenMem m2).cells a := by
  unfold patchTokenMem
  have h1 := writeBytes_cells_below_eq hsb hag (cliBase + tokenStorageOff) [0#8] htok1
  exact writeBytes_cells_below_eq hsb h1 (cliBase + tokenOnceOff) [0#8, 0#8, 0#8, 0#8] htok2

private theorem patchTokenMem_cells_above (m : Memory) {sb : Nat} (hsb : sb ≤ 2 ^ 64)
    (htok1 : (cliBase + tokenStorageOff).toNat + 1 ≤ sb)
    (htok2 : (cliBase + tokenOnceOff).toNat + 4 ≤ sb)
    {a : BitVec 64} (ha : sb ≤ a.toNat) : (patchTokenMem m).cells a = m.cells a := by
  unfold patchTokenMem
  have h2 := writeBytes_cells_above_eq (m.writeBytes (cliBase + tokenStorageOff) [0#8])
    hsb (cliBase + tokenOnceOff) [0#8, 0#8, 0#8, 0#8] htok2 ha
  exact h2.trans (writeBytes_cells_above_eq m hsb (cliBase + tokenStorageOff) [0#8] htok1 ha)

attribute [local irreducible] patchTokenMem
attribute [local irreducible] cliTokenPatch

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

/-- Under `PrebuildSpec`, `initFastStateFromBaseProcess` produces a `FastState` agreeing with
`cliTokenPatch s0` for `elf.loadState pinputs = .ok s0` and establishes `FastProgSound`. -/
theorem initFastStateFromBaseProcess_sound_of_spec
    {W : CliHooks} {li : LinkedImage} {elf : ElfImage} {pb : PrebuiltElf}
    {pinputs : ProcessInputs} {fs0 : FastState}
    (hspec : PrebuildSpec W li elf pb)
    (hinit : initFastStateFromBaseProcess elf pb pinputs = some fs0) :
    ∃ s0 : State,
      elf.loadState pinputs = .ok s0 ∧
      fs0.Agrees (cliTokenPatch s0) ∧
      FastProgSound W li pb.prog (cliTokenPatch s0).mem := by
  obtain ⟨hwf, hseg_brk, _hbrk_48, htok1_brk, htok2_brk, hbase_raw, regsWL, hprog_eq⟩ := hspec
  unfold initFastStateFromBaseProcess at hinit
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
        rw [RadixMemAux.withForcedNat_eq] at hinit
        split at hinit; swap; · nomatch hinit
        rename_i hsz_top
        split at hinit; swap; · nomatch hinit
        rename_i hstack_bnds
        simp only [withForcedBinTree_eq] at hinit
        injection hinit with hinit; subst hinit
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hstack_bnds
        rcases hstack_bnds with ⟨⟨⟨⟨hbrk_sb, hprog_sb⟩, hsb_stk⟩, hstk_top⟩, htop_60⟩
        have hload_ok := loadState_ok_of_checks hwf hdirs hfiles hstk
        generalize hs0Mem_eq :
          ((⟨Snapshot.loadCellAt (elf.segments ++ [stackRegion])⟩ : Memory).mapZero
            (BitVec.ofNat 64 (pinputs.init.stackTop.toNat - pinputs.init.stackSize))
            pinputs.init.stackSize) = s0Mem at hload_ok
        have htop_lt : pinputs.init.stackTop.toNat < 2 ^ 64 :=
          Nat.lt_of_le_of_lt htop_60 pow60_lt_pow64
        have hsb_64 : pinputs.init.stackTop.toNat - pinputs.init.stackSize ≤ 2 ^ 64 :=
          Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt htop_lt)
        have htok1_sb : (cliBase + tokenStorageOff).toNat + 1 ≤
            pinputs.init.stackTop.toNat - pinputs.init.stackSize :=
          Nat.le_trans htok1_brk hbrk_sb
        have htok2_sb : (cliBase + tokenOnceOff).toNat + 4 ≤
            pinputs.init.stackTop.toNat - pinputs.init.stackSize :=
          Nat.le_trans htok2_brk hbrk_sb
        obtain ⟨hmem_ag, hbelow_ag, habove_none⟩ :=
          initStackOverlay_mem_agrees hsz_top htop_lt hseg_brk hbrk_sb hsb_stk hstk_top
            (patchM := patchTokenMem)
            (fun h => patchTokenMem_cells_below hsb_64 h htok1_sb htok2_sb)
            (fun m _ ha => patchTokenMem_cells_above m hsb_64 htok1_sb htok2_sb ha)
            hbase_raw
            (s0Mem := s0Mem)
            (fun a => congrArg (fun m : Memory => m.cells a) hs0Mem_eq.symm)
        have hheap_ag := initStackOverlay_heap_agrees htop_60 habove_none
        have hpatch_state :
            cliTokenPatch {
              regs := RegFile.empty, vregs := VRegFile.empty, sp := sp, pc := elf.entry,
              pstate := PState.zero, mem := s0Mem, tpidrEl0 := 0#64,
              brkStart := elf.brkStart, brk := elf.brkStart,
              physMemAvail := pinputs.init.physMemAvail, fs := initFsState pinputs,
              oracle := pinputs.init.oracle, oracleIdx := 0,
              exclFails := pinputs.init.oracle.exclFails, trace := [], status := .Running,
              symtab := fun _ name => (elf.symbols.find? (·.1 == name)).map (·.2) } =
            { regs := RegFile.empty, vregs := VRegFile.empty, sp := sp, pc := elf.entry,
              pstate := PState.zero, mem := patchTokenMem s0Mem, tpidrEl0 := 0#64,
              brkStart := elf.brkStart, brk := elf.brkStart,
              physMemAvail := pinputs.init.physMemAvail, fs := initFsState pinputs,
              oracle := pinputs.init.oracle, oracleIdx := 0,
              exclFails := pinputs.init.oracle.exclFails, trace := [], status := .Running,
              symtab := fun _ name => (elf.symbols.find? (·.1 == name)).map (·.2) } :=
          cliTokenPatch_eq_setMem _
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
        · rw [hpatch_state, hprog_eq]
          exact fastProgSound_of_cells_agree W li regsWL
            pb.baseLines (patchTokenMem s0Mem)
            (fun a ha_prog => hbelow_ag a (Nat.lt_of_lt_of_le ha_prog hprog_sb))
    · simp only [hfiles, ↓reduceIte] at hinit; nomatch hinit
  · simp only [hdirs, ↓reduceIte] at hinit; nomatch hinit

theorem initFastStateFromBaseProcess_sound
    {W : CliHooks} {li : LinkedImage} {elf : ElfImage} {pb : PrebuiltElf}
    {pinputs : ProcessInputs} {fs0 : FastState}
    (hpb : prebuildElf W li elf = some pb)
    (hinit : initFastStateFromBaseProcess elf pb pinputs = some fs0) :
    ∃ s0 : State,
      elf.loadState pinputs = .ok s0 ∧
      fs0.Agrees (cliTokenPatch s0) ∧
      FastProgSound W li pb.prog (cliTokenPatch s0).mem :=
  initFastStateFromBaseProcess_sound_of_spec (prebuildElf_sound hpb) hinit

theorem initFastStateFromBase_sound_of_spec
    {W : CliHooks} {li : LinkedImage} {elf : ElfImage} {pb : PrebuiltElf}
    {inp : Inputs} {fs0 : FastState}
    (hspec : PrebuildSpec W li elf pb)
    (hinit : initFastStateFromBase elf pb inp = some fs0) :
    ∃ s0 : State,
      elf.loadState (cliProcessInputs inp) = .ok s0 ∧
      fs0.Agrees (cliTokenPatch s0) ∧
      FastProgSound W li pb.prog (cliTokenPatch s0).mem :=
  initFastStateFromBaseProcess_sound_of_spec hspec hinit

theorem initFastStateFromBase_sound
    {W : CliHooks} {li : LinkedImage} {elf : ElfImage} {pb : PrebuiltElf}
    {inp : Inputs} {fs0 : FastState}
    (hpb : prebuildElf W li elf = some pb)
    (hinit : initFastStateFromBase elf pb inp = some fs0) :
    ∃ s0 : State,
      elf.loadState (cliProcessInputs inp) = .ok s0 ∧
      fs0.Agrees (cliTokenPatch s0) ∧
      FastProgSound W li pb.prog (cliTokenPatch s0).mem :=
  initFastStateFromBaseProcess_sound hpb hinit

end Symbolic.BugInjection.Proofs.CliExec.FastStepInit
