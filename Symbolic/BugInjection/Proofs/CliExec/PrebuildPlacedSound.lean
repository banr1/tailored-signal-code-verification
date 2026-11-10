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
public import ProofLib.Process.Core
public import ProofLib.Process.FastParse
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildSpecPlaced

/-!
# Placed Prebuild Soundness

Proves `prebuildElfPlaced_sound`, establishing `PrebuildSpecPlaced` whenever `prebuildElfPlaced`
succeeds. Also proves `keepsFrozen_cliTokenPatchPlaced` and `codeLoaded_cliTokenPatchPlaced`:
under `ElfFullValidPlaced`, the five token-patched bytes are writable in the loaded initial state,
so `cliTokenPatchPlaced` preserves frozen memory cells and `mallocngLib.CodeLoaded`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.PrebuildPlacedSound

open Arm64 Arm64.Memory Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Placed (cliTokenPatchPlaced)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64 rawCellAt
  withForcedBinTree_eq)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemLine (loadRegionsLines
  rawCellAt_loadRegionsLines)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced (patchTokenFastMemPlaced)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux (perm_writeBytes_eq)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (canWrite_of_perm_eq)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (MallocngCallAddrs)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (PrebuiltElfPlaced
  checkElfPrebuildOkPlaced overlayHooksPlaced)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfFullSpecPlaced)
open Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced (prebuildElfPlaced
  prebuildElfPlacedWithLens)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced (ElfFullValidPlaced
  extractElfRawLinesPlaced tokOnceAddrPlaced tokStorageAddrPlaced)
open Symbolic.BugInjection.Proofs.CliExec.PrebuildSpecPlaced (PrebuildSpecPlaced)

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

private theorem patchTokenFastMemPlaced_agrees (tokS tokO : BitVec 64)
    {fm : FastMem} {m : Memory} (h : fm.Agrees m) :
    (patchTokenFastMemPlaced tokS tokO fm).Agrees
      ((m.writeBytes tokS [0#8]).writeBytes (tokO + 8#64) [0#8, 0#8, 0#8, 0#8]) :=
  FastMem.writeBytes_agrees (FastMem.writeBytes_agrees h _ _) _ _

private theorem patchTokenFastMemPlaced_stackBase_eq (tokS tokO : BitVec 64) (fm : FastMem) :
    (patchTokenFastMemPlaced tokS tokO fm).stackBase = fm.stackBase ∧
      (patchTokenFastMemPlaced tokS tokO fm).stackTop = fm.stackTop := by
  unfold patchTokenFastMemPlaced
  have h1 := writeBytes_stackBase_eq fm tokS [0#8]
  have h2 := writeBytes_stackBase_eq (fm.writeBytes tokS [0#8])
    (tokO + 8#64) [0#8, 0#8, 0#8, 0#8]
  exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

private theorem segments_all_noWrap_of_le_brk {elf : ElfImage}
    (hseg_brk : ∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ elf.brkStart.toNat)
    (hbrk_le : elf.brkStart.toNat ≤ 2 ^ 48) :
    elf.segments.all (fun r => decide (r.start.toNat + r.bytes.length ≤ 2 ^ 64)) = true := by
  rw [List.all_eq_true]
  intro r hr
  rw [decide_eq_true_eq]
  have h1 := hseg_brk r hr
  omega

private theorem rawLines_fastMem_agrees {elf : ElfImage}
    (hwrap : elf.segments.all (fun r => decide (r.start.toNat + r.bytes.length ≤ 2 ^ 64)) = true) :
    ({ lines := loadRegionsLines elf.segments, stackBase := 0, stackTop := 0 } : FastMem).Agrees
      ⟨Snapshot.loadCellAt elf.segments⟩ := by
  intro a
  dsimp only [FastMem.cellAt]
  rw [rawCellAt_loadRegionsLines elf.segments hwrap a]
  cases Snapshot.loadCellAt elf.segments a with
  | some _ => rfl
  | none => simp

/-- Soundness of `prebuildElfPlaced`: the boolean header, segment, and spine checks imply
`PrebuildSpecPlaced`. -/
theorem prebuildElfPlaced_sound
    {W : CliHooks} {elf : ElfImage} {tokS tokO : BitVec 64}
    {addrs : MallocngCallAddrs} {stubs : List (String × Nat)} {pb : PrebuiltElfPlaced}
    (hpb : prebuildElfPlaced W elf tokS tokO addrs stubs = some pb) :
    PrebuildSpecPlaced W elf tokS tokO addrs stubs pb := by
  unfold prebuildElfPlaced prebuildElfPlacedWithLens at hpb
  split at hpb; swap; · nomatch hpb
  rename_i hcond0
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond0
  rcases hcond0 with ⟨_hphent, hok⟩
  dsimp only at hpb
  split at hpb
  · nomatch hpb
  · simp only [withForcedBinTree_eq] at hpb
    split at hpb; swap; · nomatch hpb
    have hwf_fast : fastWellFormed elf = true := by
      unfold checkElfPrebuildOkPlaced at hok
      unfold fastWellFormed
      simp only [Bool.and_eq_true] at hok ⊢
      exact hok.1.1.1
    have hwf : elf.WellFormed = true := (fastWellFormed_eq elf).symm.trans hwf_fast
    have hok_bounds :
        (∀ r ∈ elf.segments, r.start.toNat + r.bytes.length ≤ elf.brkStart.toNat) ∧
        elf.brkStart.toNat ≤ 2 ^ 48 ∧
        tokS.toNat + 1 ≤ elf.brkStart.toNat ∧
        tokO.toNat + 12 ≤ elf.brkStart.toNat := by
      unfold checkElfPrebuildOkPlaced at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq, mapRegionsWithLen_eq, List.all_map,
        List.all_eq_true] at hok
      exact ⟨fun r hr => of_decide_eq_true (hok.1.1.1.2 r hr), hok.1.1.2, hok.1.2, hok.2⟩
    rcases hok_bounds with ⟨hseg_brk, hbrk_48, htokS_brk, htokO_brk⟩
    set fm0 : FastMem := { lines := loadRegionsLines elf.segments, stackBase := 0, stackTop := 0 }
    have hwrap := segments_all_noWrap_of_le_brk hseg_brk hbrk_48
    have hfm0_ag : fm0.Agrees ⟨Snapshot.loadCellAt elf.segments⟩ :=
      rawLines_fastMem_agrees hwrap
    have hfm1_ag := patchTokenFastMemPlaced_agrees tokS tokO hfm0_ag
    have hfm1_sb := patchTokenFastMemPlaced_stackBase_eq tokS tokO fm0
    generalize patchTokenFastMemPlaced tokS tokO fm0 = fm1 at hpb hfm1_ag hfm1_sb
    injection hpb with hpb
    subst hpb
    refine {
      wellFormed := hwf
      seg_le_brk := hseg_brk
      brk_le     := hbrk_48
      tokS_le    := htokS_brk
      tokO_le    := htokO_brk
      cells      := ?_
      prog_eq    := rfl
    }
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

private theorem loadCellAt_append (rs1 rs2 : List Snapshot.Region) (a : BitVec 64) :
    Snapshot.loadCellAt (rs1 ++ rs2) a =
      (Snapshot.loadCellAt rs1 a).or (Snapshot.loadCellAt rs2 a) := by
  induction rs1 with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.cons_append, Snapshot.loadCellAt, List.findSome?_cons]
    by_cases hlt : (a - r.start).toNat < r.bytes.length
    · rw [dite_eq_left_of_eq_true (eq_true hlt)]; rfl
    · rw [dite_eq_right_of_eq_false (eq_false hlt)]; exact ih

private theorem perm_mapZero_append_eq_of_perm_w
    (segs tail : List Snapshot.Region) (sb : BitVec 64) (sz : Nat)
    {a : BitVec 64}
    (hw : ((⟨Snapshot.loadCellAt segs⟩ : Memory).perm a).w = true) :
    (((⟨Snapshot.loadCellAt (segs ++ tail)⟩ : Memory).mapZero sb sz).perm a) =
      (⟨Snapshot.loadCellAt segs⟩ : Memory).perm a := by
  unfold Memory.perm at hw
  dsimp only at hw
  cases hcell : Snapshot.loadCellAt segs a with
  | none => rw [hcell] at hw; nomatch hw
  | some pb =>
    rcases pb with ⟨po, b⟩
    cases po with
    | none => rw [hcell] at hw; nomatch hw
    | some p =>
      have happ : Snapshot.loadCellAt (segs ++ tail) a = some (some p, b) := by
        rw [loadCellAt_append, hcell, Option.some_or]
      have hmap_false :
          (!(Memory.perm ⟨Snapshot.loadCellAt (segs ++ tail)⟩ a).mapped) = false := by
        dsimp only [Memory.perm]
        rw [happ]
        rfl
      have hcells_mz :
          ((⟨Snapshot.loadCellAt (segs ++ tail)⟩ : Memory).mapZero sb sz).cells a =
            some (some p, b) := by
        dsimp only [Memory.mapZero]
        rw [hmap_false, Bool.and_false]
        exact happ
      unfold Memory.perm
      rw [hcells_mz]
      dsimp only
      rw [hcell]

private theorem canWrite_mapZero_append_of_canWrite
    (segs tail : List Snapshot.Region) (sb : BitVec 64) (sz : Nat) :
    ∀ (n : Nat) (addr : BitVec 64),
      (⟨Snapshot.loadCellAt segs⟩ : Memory).canWrite addr n = true →
      ((⟨Snapshot.loadCellAt (segs ++ tail)⟩ : Memory).mapZero sb sz).canWrite addr n = true
  | 0, _, _ => rfl
  | n + 1, addr, hcw => by
    simp only [Memory.canWrite, Memory.allPerm, Bool.and_eq_true] at hcw ⊢
    rcases hcw with ⟨⟨hw, hnx⟩, hrest⟩
    have hp := perm_mapZero_append_eq_of_perm_w segs tail sb sz hw
    rw [hp]
    exact ⟨⟨hw, hnx⟩,
      canWrite_mapZero_append_of_canWrite segs tail sb sz n (addr + 1#64) hrest⟩

/-- Under `ElfFullValidPlaced`, token patching at `tokStorageAddrPlaced` and
`tokOnceAddrPlaced + 8` writes only to non-executable writable segment cells and therefore
preserves all frozen cells of `s0.mem`. -/
theorem keepsFrozen_cliTokenPatchPlaced
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {fs : ElfFullSpecPlaced}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    {pin : ProcessInputs} {s0 : State}
    (hload : elf.loadState pin = .ok s0) :
    s0.mem.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem := by
  have hspec := prebuildElfPlaced_sound hv.prebuild_eq
  have hwrap := segments_all_noWrap_of_le_brk hspec.seg_le_brk hspec.brk_le
  have hfm_ag :
      ({ lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 } : FastMem).Agrees
        ⟨Snapshot.loadCellAt elf.segments⟩ :=
    rawLines_fastMem_agrees hwrap
  have htw := hv.tokCanWrite
  rw [Bool.and_eq_true, FastMem.canWrite_eq hfm_ag, FastMem.canWrite_eq hfm_ag] at htw
  rcases htw with ⟨htwS, htwO⟩
  obtain ⟨_, stackRegion, _, hmem, _, _, _, _, _⟩ := ElfImage.loadState_eq_ok hload
  have hcwS : s0.mem.canWrite (tokStorageAddrPlaced mpl) 1 = true := by
    rw [hmem]
    exact canWrite_mapZero_append_of_canWrite elf.segments [stackRegion] _ _ 1 _ htwS
  have hcwO0 : s0.mem.canWrite (tokOnceAddrPlaced mpl + 8#64) 4 = true := by
    rw [hmem]
    exact canWrite_mapZero_append_of_canWrite elf.segments [stackRegion] _ _ 4 _ htwO
  have hkf1 : s0.mem.KeepsFrozen (s0.mem.writeBytes (tokStorageAddrPlaced mpl) [0#8]) :=
    keepsFrozen_writeBytes [0#8] hcwS
  have hcwO :
      (s0.mem.writeBytes (tokStorageAddrPlaced mpl) [0#8]).canWrite
        (tokOnceAddrPlaced mpl + 8#64) 4 = true := by
    rw [canWrite_of_perm_eq (perm_writeBytes_eq s0.mem (tokStorageAddrPlaced mpl) [0#8])]
    exact hcwO0
  have hkf2 :
      (s0.mem.writeBytes (tokStorageAddrPlaced mpl) [0#8]).KeepsFrozen
        ((s0.mem.writeBytes (tokStorageAddrPlaced mpl) [0#8]).writeBytes
          (tokOnceAddrPlaced mpl + 8#64) [0#8, 0#8, 0#8, 0#8]) :=
    keepsFrozen_writeBytes [0#8, 0#8, 0#8, 0#8] hcwO
  exact KeepsFrozen.trans hkf1 hkf2

theorem codeLoaded_cliTokenPatchPlaced
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {fs : ElfFullSpecPlaced}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    {pin : ProcessInputs} {s0 : State}
    (hload : elf.loadState pin = .ok s0) :
    VerifiedLibraries.mallocngLib.CodeLoaded mmpl (cliTokenPatchPlaced mpl s0).mem :=
  MultiPlacedLib.CodeLoaded.of_keepsFrozen (hv.mallocng_codeLoaded hload)
    (keepsFrozen_cliTokenPatchPlaced hv hload)

end Symbolic.BugInjection.Proofs.CliExec.PrebuildPlacedSound
