/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Loader
public import Arm64.Trusted.Process.Placed
public import ProofLib.SepLogic.WP.StepsProcess
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryTokenPatch
public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryTokenPatchPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.InitStack
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslElf
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslStart
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Parameterized `musl` `_start → main` Startup with `MallocngRuntime`

Proves `musl_startup_fineInit_ofProg` across `musl` `_start` / `_start_c` (parameterized by
`ADRP`/`ADD` immediates), tracking `tpidrEl0 = muslTpOf elf`, `MuslStartupVmPreserved`, and
`MallocngRuntime` + `MallocngAuxvAt` (including the 8-byte `AT_RANDOM` slice) up to `main` entry,
together with explicit-`mpl` CPU-probe token-patch lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.MuslStartFineResources

open Arm64 Arm64.Process ProofLib
open VerifiedLibraries.Mallocng (MallocngAddrs MallocngAuxvAt MallocngRuntime)
open CryptoVerification.SignalSession
  (AddrInElf Inputs addrInElf_patchElfByte cliProcessInputs elfStaticOk_patchElfByte
   loadState_patchElfByte patchElfByte patchRegionByte processInputs segSlice_addrInElf
   segSlice_patchElfByte_of_ne)
open CryptoVerification.SignalSession.Cli (ElfStaticOk)
open CryptoVerification.SignalSession.Placed (cliTokenPatchPlaced)
open CryptoVerification.SignalSession.InitStack
  (argcBytes argvAt argvBase argv_length_le auxWords auxWords_length cStrAt cliStackSize
   cliStackSize_eq cliStrs cliStrs_length cli_bounds execfnAddr flatMap_bytesLE_length frameBytes
   headBytes infoBase infoLen infoPadLen le_alignUp16 loadState_cli_layout packAddrs
   packAddrs_length platformAddr ptrBytes ptrWords restBytes restWords restWords_eq sp0 sp0_le_top
   stackBase stackBase_eq strBytes tableWords toNat_sp0 toNat_stackBase top top_eq upperRawLen)
open CryptoVerification.SignalSession.MuslExit (muslFiniFr)
open CryptoVerification.SignalSession.MuslStart
  (Hop2Regs Hop3aRegs Hop3bRegs Hop4Regs Hop5Regs Hop6Regs Hop7Regs MuslHop2Fetch MuslHop3aFetch
   MuslHop3bFetch MuslHop4Fetch MuslHop5Fetch MuslHop6Fetch MuslHop7Fetch MuslMemsetFetch
   StartArgv0 StartPhdrs StartProc execSyscall_setTid musl_start_hop2 musl_start_hop3a
   musl_start_hop3b musl_start_hop4 musl_start_hop5 spAligned_sub48)
open CryptoVerification.SignalSession.MuslElf
  (CliElfMusl PhdrsMapped SegSlice al_of_mod and_neg16 argvAt_cli argvBase_ne cStr_eq cellsW
   cliArgBudget cliStackBudget codeLoaded_of_text entry_bound envp_eq fini_intro holdsBytes_zero
   loadState_fields memRegion_cellsW muslRwWords packed_cons pointsTo64_eq_8 pre_assemble
   sat_of_entails_frame sat_startPhdrs stackBudget_le stack_rebuild startProc_eq sub_add_eq'
   supportedOn_of_holdsBytes_rw toNat_ofNat_add wf_phent x0_eq zeros_split)

/-! ## `MuslStartupVmPreserved` and explicit-`mpl` token patch -/

/-- Startup virtual/physical memory preservation from `loadState` `s0` to `main` entry `sm`
    (definitionally equal to `LibsignalBinary.Heap.Fine.StartupVmPreserved`). -/
def MuslStartupVmPreserved (s0 sm : State) : Prop :=
  sm.brkStart = s0.brkStart ∧ sm.brk = s0.brk ∧ sm.physMemAvail = s0.physMemAvail ∧
  ∀ a : BitVec 64, sm.mem.perm a = s0.mem.perm a

theorem MuslStartupVmPreserved.refl (s : State) : MuslStartupVmPreserved s s :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem MuslStartupVmPreserved.trans {s0 s1 s2 : State}
    (h01 : MuslStartupVmPreserved s0 s1) (h12 : MuslStartupVmPreserved s1 s2) :
    MuslStartupVmPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    fun a => (h12.2.2.2 a).trans (h01.2.2.2 a)⟩

theorem MuslStartupVmPreserved.of_nonSyscallPreserved {s0 sm : State}
    (h : ProofLib.NonSyscallPreserved s0 sm) : MuslStartupVmPreserved s0 sm :=
  ⟨h.2.2.2.1, h.2.2.1, h.2.2.2.2.1, fun a => congrFun h.2.1 a⟩

private theorem write8_perm_eq (m : Memory) (addr : BitVec 64) (val : BitVec 8) (a : BitVec 64) :
    (m.write8 addr val).perm a = m.perm a := by
  unfold Memory.perm Memory.write8 Memory.rawPerm
  by_cases h : a = addr
  · subst h; simp only [↓reduceIte]; rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl
  · simp [h]

private theorem writeBytes_perm_eq (m : Memory) (base : BitVec 64) (bs : List (BitVec 8))
    (a : BitVec 64) : (m.writeBytes base bs).perm a = m.perm a := by
  induction bs generalizing m base with
  | nil => rfl
  | cons _ rest ih => simp only [Memory.writeBytes]; rw [ih, write8_perm_eq]

theorem muslStartupVmPreserved_cliTokenPatchPlaced (mpl : Obj.MultiPlacement) (s : State) :
    MuslStartupVmPreserved s (cliTokenPatchPlaced mpl s) := by
  refine ⟨rfl, rfl, rfl, fun a => ?_⟩
  unfold cliTokenPatchPlaced State.setMem; dsimp only; rw [writeBytes_perm_eq, writeBytes_perm_eq]

/-- `PT_LOAD` `.data` slice bundle for `spqr`'s initial unprobed CPU-feature cells under `mpl`. -/
structure CliElfTokenCellsPlacedAt (mpl : Obj.MultiPlacement) (elf : ElfImage) : Prop where
  storage : SegSlice elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) [0xff#8] Perm.rw
  once : SegSlice elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64)
    [3#8, 0#8, 0#8, 0#8] Perm.rw

/-- Ghost `ElfImage` with `spqr`'s 5 CPU-probe `.data` bytes pre-set to `0` (`DEV-CLI10`). -/
def patchElfTokensPlacedAt (mpl : Obj.MultiPlacement) (elf : ElfImage) : ElfImage :=
  let sAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName
  let oAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64
  patchElfByte (oAddr + 3#64) 0#8 (patchElfByte (oAddr + 2#64) 0#8
    (patchElfByte (oAddr + 1#64) 0#8 (patchElfByte oAddr 0#8 (patchElfByte sAddr 0#8 elf))))

theorem elfStaticOk_patchElfTokensPlacedAt {mpl : Obj.MultiPlacement} {elf : ElfImage}
    (hE : ElfStaticOk elf) : ElfStaticOk (patchElfTokensPlacedAt mpl elf) :=
  elfStaticOk_patchElfByte (elfStaticOk_patchElfByte (elfStaticOk_patchElfByte
    (elfStaticOk_patchElfByte (elfStaticOk_patchElfByte hE))))

private theorem bv_add_1_1_at (x : BitVec 64) : x + 1#64 + 1#64 = x + 2#64 := by
  rw [BitVec.add_assoc]; rfl
private theorem bv_add_2_1_at (x : BitVec 64) : x + 2#64 + 1#64 = x + 3#64 := by
  rw [BitVec.add_assoc]; rfl

theorem loadState_patchElfTokensPlacedAt {mpl : Obj.MultiPlacement} {elf : ElfImage}
    (hE : ElfStaticOk elf) (htok : CliElfTokenCellsPlacedAt mpl elf) (inputs : ProcessInputs) :
    (patchElfTokensPlacedAt mpl elf).loadState inputs =
      (elf.loadState inputs).map (cliTokenPatchPlaced mpl) := by
  have hs : AddrInElf elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      segSlice_addrInElf htok.storage hE (j := 0) (by decide)
  have ho0 : AddrInElf elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      segSlice_addrInElf htok.once hE (j := 0) (by decide)
  have ho1 := segSlice_addrInElf htok.once hE (j := 1) (by decide)
  have ho2 := segSlice_addrInElf htok.once hE (j := 2) (by decide)
  have ho3 := segSlice_addrInElf htok.once hE (j := 3) (by decide)
  unfold patchElfTokensPlacedAt; dsimp only
  rw [loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho3),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho2),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho1),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho0),
      loadState_patchElfByte _ hs]
  cases elf.loadState inputs with
  | error _ => rfl
  | ok s0 =>
    simp only [Except.map, cliTokenPatchPlaced, State.setMem, Memory.writeBytes,
      bv_add_1_1_at, bv_add_2_1_at]

private theorem keepsFrozen_write8_of_perm_rw_at {m : Memory} {addr : BitVec 64} (val : BitVec 8)
    (hp : m.perm addr = some Perm.rw) : m.KeepsFrozen (m.write8 addr val) := by
  intro a ha; have hne : a ≠ addr := by
    rintro rfl; unfold Memory.Frozen at ha; simp only [hp, Option.frozen, Perm.frozen] at ha
    exact Bool.noConfusion ha
  simp [Memory.write8, Memory.read8, Memory.perm, Memory.isLazyFree, Memory.isAnon, hne]

theorem keepsFrozen_cliTokenPatchPlacedAt {mpl : Obj.MultiPlacement} {elf : ElfImage}
    (hE : ElfStaticOk elf) (htok : CliElfTokenCellsPlacedAt mpl elf)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    s0.mem.KeepsFrozen (cliTokenPatchPlaced mpl s0).mem := by
  let sAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName
  let oAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64
  have ps : s0.mem.perm sAddr = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.storage.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p0 : s0.mem.perm oAddr = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p1 : s0.mem.perm (oAddr + 1#64) = some .rw := by
    simpa only [oAddr, BitVec.ofNat_eq_ofNat, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 1 (by decide)).2.1
  have p2 : s0.mem.perm (oAddr + 2#64) = some .rw := by
    simpa only [oAddr, BitVec.ofNat_eq_ofNat, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 2 (by decide)).2.1
  have p3 : s0.mem.perm (oAddr + 3#64) = some .rw := by
    simpa only [oAddr, BitVec.ofNat_eq_ofNat, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 3 (by decide)).2.1
  have hmem : (cliTokenPatchPlaced mpl s0).mem =
      (((((s0.mem.write8 sAddr 0#8).write8 oAddr 0#8).write8 (oAddr + 1#64) 0#8).write8
        (oAddr + 2#64) 0#8).write8 (oAddr + 3#64) 0#8) := by
    simp only [cliTokenPatchPlaced, State.setMem, Memory.writeBytes, sAddr, oAddr,
      bv_add_1_1_at, bv_add_2_1_at]
  rw [hmem]
  exact ((((keepsFrozen_write8_of_perm_rw_at 0#8 ps).trans
    (keepsFrozen_write8_of_perm_rw_at 0#8 (by simpa only [Memory.perm_write8_apply] using p0))).trans
    (keepsFrozen_write8_of_perm_rw_at 0#8 (by simpa only [Memory.perm_write8_apply] using p1))).trans
    (keepsFrozen_write8_of_perm_rw_at 0#8 (by simpa only [Memory.perm_write8_apply] using p2))).trans
    (keepsFrozen_write8_of_perm_rw_at 0#8 (by simpa only [Memory.perm_write8_apply] using p3))

theorem segSlice_patchElfTokensPlacedAt_of_ne {mpl : Obj.MultiPlacement} {elf : ElfImage}
    {a : BitVec 64} {bs : List (BitVec 8)} {p : Perm}
    (hs : SegSlice elf a bs p) (hE : ElfStaticOk elf)
    (hs_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName)
    (ho0_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64)
    (ho1_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 1#64)
    (ho2_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 2#64)
    (ho3_ne : ∀ j (_ : j < bs.length),
      a + BitVec.ofNat 64 j ≠ mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 3#64) :
    SegSlice (patchElfTokensPlacedAt mpl elf) a bs p := by
  let sAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName
  let oAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64
  have e1 := elfStaticOk_patchElfByte (addr := sAddr) (val := 0#8) hE
  have e2 := elfStaticOk_patchElfByte (addr := oAddr) (val := 0#8) e1
  have e3 := elfStaticOk_patchElfByte (addr := oAddr + 1#64) (val := 0#8) e2
  have e4 := elfStaticOk_patchElfByte (addr := oAddr + 2#64) (val := 0#8) e3
  exact segSlice_patchElfByte_of_ne (segSlice_patchElfByte_of_ne (segSlice_patchElfByte_of_ne
    (segSlice_patchElfByte_of_ne (segSlice_patchElfByte_of_ne hs hE hs_ne) e1 ho0_ne)
    e2 ho1_ne) e3 ho2_ne) e4 ho3_ne

theorem segSlice_patchElfTokensPlacedAt_of_ne_rw {mpl : Obj.MultiPlacement} {elf : ElfImage}
    {a : BitVec 64} {bs : List (BitVec 8)} {p : Perm}
    (hs : SegSlice elf a bs p) (hp_ne : p.rwx ≠ Perm.rw)
    (hE : ElfStaticOk elf) (htok : CliElfTokenCellsPlacedAt mpl elf) :
    SegSlice (patchElfTokensPlacedAt mpl elf) a bs p := by
  have hload := (loadState_cli_layout elf [] [] [] [] hE.1 hE.2
    (by simp) (by simp) (by simp) (by simp)).1
  have hperm_ne : ∀ addr,
      (elf.rawState (processInputs ["libsignal-cli"] [] [] [])).mem.perm addr = some .rw →
      ∀ j (_ : j < bs.length), a + BitVec.ofNat 64 j ≠ addr := by
    intro addr hrw j hj heq; have hpj := ((hs.holdsBytes hE.1 hE.2 hload) j hj).2.1
    rw [heq, hrw] at hpj; exact hp_ne (Option.some.inj hpj).symm
  have ps : (elf.rawState (processInputs ["libsignal-cli"] [] [] [])).mem.perm
      (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.storage.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  have p0 : (elf.rawState (processInputs ["libsignal-cli"] [] [] [])).mem.perm
      (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) = some .rw := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, show Perm.rw.rwx = Perm.rw from rfl] using
      ((htok.once.holdsBytes hE.1 hE.2 hload) 0 (by decide)).2.1
  exact segSlice_patchElfTokensPlacedAt_of_ne hs hE (hperm_ne _ ps) (hperm_ne _ p0)
    (hperm_ne _ ((htok.once.holdsBytes hE.1 hE.2 hload) 1 (by decide)).2.1)
    (hperm_ne _ ((htok.once.holdsBytes hE.1 hE.2 hload) 2 (by decide)).2.1)
    (hperm_ne _ ((htok.once.holdsBytes hE.1 hE.2 hload) 3 (by decide)).2.1)

@[local simp] private theorem patchElfByte_segments_length (a : BitVec 64) (v : BitVec 8)
    (elf : ElfImage) : (patchElfByte a v elf).segments.length = elf.segments.length := by
  simp [patchElfByte]
private theorem patchRegionByte_bytes_len_eq (a : BitVec 64) (v : BitVec 8) (r : Snapshot.Region) :
    (patchRegionByte a v r).bytes.length = r.bytes.length := by
  unfold patchRegionByte; dsimp only; split <;> simp
@[local simp] private theorem patchElfByte_segments_bytes_sum (a : BitVec 64) (v : BitVec 8)
    (elf : ElfImage) :
    ((patchElfByte a v elf).segments.map (fun r => r.bytes.length)).sum =
      (elf.segments.map (fun r => r.bytes.length)).sum := by
  unfold patchElfByte; simp [List.map_map, Function.comp_def, patchRegionByte_bytes_len_eq]

theorem patchElfTokensPlacedAt_entry (mpl : Obj.MultiPlacement) (elf : ElfImage) :
    (patchElfTokensPlacedAt mpl elf).entry = elf.entry := rfl
theorem patchElfTokensPlacedAt_phnum (mpl : Obj.MultiPlacement) (elf : ElfImage) :
    (patchElfTokensPlacedAt mpl elf).phnum = elf.phnum := rfl
theorem patchElfTokensPlacedAt_phdrVaddr (mpl : Obj.MultiPlacement) (elf : ElfImage) :
    (patchElfTokensPlacedAt mpl elf).phdrVaddr = elf.phdrVaddr := rfl
theorem patchElfTokensPlacedAt_brkStart (mpl : Obj.MultiPlacement) (elf : ElfImage) :
    (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
theorem patchElfTokensPlacedAt_segments_length (mpl : Obj.MultiPlacement) (elf : ElfImage) :
    (patchElfTokensPlacedAt mpl elf).segments.length = elf.segments.length := by
  simp [patchElfTokensPlacedAt]
theorem patchElfTokensPlacedAt_segments_bytes_sum (mpl : Obj.MultiPlacement) (elf : ElfImage) :
    (((patchElfTokensPlacedAt mpl elf).segments.map (fun r => r.bytes.length)).sum) =
      (elf.segments.map (fun r => r.bytes.length)).sum := by simp [patchElfTokensPlacedAt]

theorem phdrsMapped_patchElfTokensPlacedAt {mpl : Obj.MultiPlacement} {elf : ElfImage}
    {ph : BitVec 64} (hP : PhdrsMapped elf ph)
    (hE : ElfStaticOk elf) (htok : CliElfTokenCellsPlacedAt mpl elf) :
    PhdrsMapped (patchElfTokensPlacedAt mpl elf) ph :=
  have f {a bs} (h : SegSlice elf a bs Perm.ro) :=
    segSlice_patchElfTokensPlacedAt_of_ne_rw h (by decide) hE htok
  ⟨f hP.p0_type, f hP.p0_vaddr, f hP.p1_type, f hP.p2_type, f hP.p3_type, f hP.p4_type,
    f hP.p5_type, f hP.p6_type, f hP.p7_type, f hP.p8_type, f hP.p9_type, f hP.p9_vaddr,
    f hP.p9_filesz, f hP.p9_memsz, f hP.p9_align, f hP.p10_type, f hP.p10_memsz⟩

/-- Disjointness between `musl`'s 600-byte writable statics `[elf.entry + 0x2000, +600)` and
    `spqr`'s 5 CPU-probe token bytes under placement `mpl`. -/
def TokenDisjointFromMuslRw (mpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  let sAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName
  let oAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64
  ∀ j, j < 600 →
    elf.entry + 0x2000#64 + BitVec.ofNat 64 j ≠ sAddr ∧
    elf.entry + 0x2000#64 + BitVec.ofNat 64 j ≠ oAddr ∧
    elf.entry + 0x2000#64 + BitVec.ofNat 64 j ≠ oAddr + 1#64 ∧
    elf.entry + 0x2000#64 + BitVec.ofNat 64 j ≠ oAddr + 2#64 ∧
    elf.entry + 0x2000#64 + BitVec.ofNat 64 j ≠ oAddr + 3#64

theorem cliElfMusl_patchElfTokensPlacedAt {mpl : Obj.MultiPlacement} {elf : ElfImage}
    {code : List (BitVec 8)} (hC : CliElfMusl elf code)
    (hE : ElfStaticOk elf) (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hDisj : TokenDisjointFromMuslRw mpl elf) :
    CliElfMusl (patchElfTokensPlacedAt mpl elf) code := by
  obtain ⟨h0, g3, g4, ia, F, hh0, hrw⟩ := hC.rw
  have hML : (unpackL (muslRwWords h0 g3 g4 ia F)).length = 600 := by rw [unpackL_length]; rfl
  exact { entry_page := hC.entry_page, phnum := hC.phnum, phdr_ne := hC.phdr_ne
          text := segSlice_patchElfTokensPlacedAt_of_ne_rw hC.text (by decide) hE htok
          phdrs := phdrsMapped_patchElfTokensPlacedAt hC.phdrs hE htok
          rw := ⟨h0, g3, g4, ia, F, hh0, segSlice_patchElfTokensPlacedAt_of_ne hrw hE
            (fun j hj => (hDisj j (hML ▸ hj)).1) (fun j hj => (hDisj j (hML ▸ hj)).2.1)
            (fun j hj => (hDisj j (hML ▸ hj)).2.2.1) (fun j hj => (hDisj j (hML ▸ hj)).2.2.2.1)
            (fun j hj => (hDisj j (hML ▸ hj)).2.2.2.2)⟩ }

/-! ## Parameterized `MuslStartFetchAt` and step lifting -/

/-- Thread pointer initialized by `musl`'s `__init_tp`: `elf.entry + 0x2148#64`. -/
def muslTpOf (elf : ElfImage) : BitVec 64 := elf.entry + 0x2148#64

/-- Target `main` PC computed by `_start_c`'s `adrp x0, pageImm; add x0, x0, addImm` at `B`. -/
def mainPcOf (B pageImm : BitVec 64) (addImm : BitVec 12) : BitVec 64 :=
  B + pageImm + addImm.zeroExtend 64

/-- Hop 1 (26 instructions) parameterized over `dynPageImm` and `(pageImm, addImm)`. -/
def MuslHop1FetchAt (Q : Program) (B dynPageImm pageImm : BitVec 64) (addImm : BitVec 12) : Prop :=
  Q.fetch B = some (.moveWide .W64 .MOVZ (.gpr 0x1d#5) 0x0000#16 0) ∧
  Q.fetch (B + 0x4#64) = some (.moveWide .W64 .MOVZ (.gpr 0x1e#5) 0x0000#16 0) ∧
  Q.fetch (B + 0x8#64) = some (.addSubImm .W64 .ADD (.gpr 0x00#5) .sp 0x000#12 false) ∧
  Q.fetch (B + 0xc#64) = some (.adr true (.gpr 0x01#5) dynPageImm) ∧
  Q.fetch (B + 0x10#64) = some (.addSubImm .W64 .ADD (.gpr 0x01#5) (.gpr 0x01#5) 0x000#12 false) ∧
  Q.fetch (B + 0x14#64) = some (.logicalImm .W64 .AND .sp (.gpr 0x00#5) 0xfffffffffffffff0#64) ∧
  Q.fetch (B + 0x18#64) = some (.b 4#64) ∧
  Q.fetch (B + 0x1c#64) = some (.logicalShift .W64 .ORR (.gpr 0x02#5) .xzr (.gpr 0x00#5) .LSL 0) ∧
  Q.fetch (B + 0x20#64) = some (.adr true (.gpr 0x03#5) 0x2000#64) ∧
  Q.fetch (B + 0x24#64) = some (.adr true (.gpr 0x04#5) 0x2000#64) ∧
  Q.fetch (B + 0x28#64) = some (.ldr .W32 .W32 false (.gpr 0x01#5) (.PostIndex (.gpr 0x02#5) 8#64)) ∧
  Q.fetch (B + 0x2c#64) = some (.ldr .W64 .X64 false (.gpr 0x03#5) (.Offset (.gpr 0x03#5) 0x10#64)) ∧
  Q.fetch (B + 0x30#64) = some (.ldr .W64 .X64 false (.gpr 0x04#5) (.Offset (.gpr 0x04#5) 0x18#64)) ∧
  Q.fetch (B + 0x34#64) = some (.adr true (.gpr 0x00#5) pageImm) ∧
  Q.fetch (B + 0x38#64) = some (.addSubImm .W64 .ADD (.gpr 0x00#5) (.gpr 0x00#5) addImm false) ∧
  Q.fetch (B + 0x3c#64) = some (.logicalShift .W64 .ORR (.gpr 0x05#5) .xzr .xzr .LSL 0) ∧
  Q.fetch (B + 0x40#64) = some (.b 0x7a0#64) ∧
  Q.fetch (B + 0x7e0#64) =
    some (.stp .W64 (.gpr 0x1e#5) (.gpr 0x15#5) (.PreIndex .sp 0xffffffffffffffe0#64)) ∧
  Q.fetch (B + 0x7e4#64) = some (.stp .W64 (.gpr 0x14#5) (.gpr 0x13#5) (.Offset .sp 16#64)) ∧
  Q.fetch (B + 0x7e8#64) = some (.addSubExt .W64 .ADD (.gpr 0x08#5) (.gpr 0x02#5) (.gpr 0x01#5) .SXTW 3) ∧
  Q.fetch (B + 0x7ec#64) = some (.logicalShift .W32 .ORR (.gpr 0x14#5) .xzr (.gpr 0x01#5) .LSL 0) ∧
  Q.fetch (B + 0x7f0#64) = some (.ldr .W64 .X64 false (.gpr 0x01#5) (.Offset (.gpr 0x02#5) 0#64)) ∧
  Q.fetch (B + 0x7f4#64) = some (.logicalShift .W64 .ORR (.gpr 0x15#5) .xzr (.gpr 0x00#5) .LSL 0) ∧
  Q.fetch (B + 0x7f8#64) = some (.logicalShift .W64 .ORR (.gpr 0x13#5) .xzr (.gpr 0x02#5) .LSL 0) ∧
  Q.fetch (B + 0x7fc#64) = some (.addSubImm .W64 .ADD (.gpr 0x00#5) (.gpr 0x08#5) 0x008#12 false) ∧
  Q.fetch (B + 0x800#64) = some (.bl 0xfffffffffffffdf4#64)

/-- Parameterized counterpart of `MuslStartFetch` (hops 1–7). -/
def MuslStartFetchAt (Q : Program) (B dynPageImm pageImm : BitVec 64) (addImm : BitVec 12) : Prop :=
  MuslHop1FetchAt Q B dynPageImm pageImm addImm ∧
  MuslHop2Fetch Q B ∧ MuslHop3aFetch Q B ∧ MuslHop3bFetch Q B ∧
  MuslHop4Fetch Q B ∧ MuslHop5Fetch Q B ∧ MuslHop6Fetch Q B ∧ MuslHop7Fetch Q B

/-- Restricted `set_tid_address`-only supervisor handler for `hooklessMuslProg`. -/
def setTidOnlySvc (s : State) : State :=
  if s.readReg64 Reg.x8 == 96#64 then (s.writeReg64 Reg.x0 1#64).advancePC
  else s.setStatus (.Exception "unexpected syscall in musl startup")

def hooklessMuslProg (B : BitVec 64) (code : List (BitVec 8)) : Program :=
  { base := B, code := code.take 0xb90, svc := setTidOnlySvc }

private theorem readWordOff_take_eq {B : BitVec 64} {code : List (BitVec 8)} {off : Nat}
    (h : off + 4 ≤ 0xb90) :
    ({ base := B, code := code.take 0xb90, svc := setTidOnlySvc } : Program).readWordOff off =
      ({ code } : Program).readWordOff off := by
  unfold Program.readWordOff; dsimp only; split
  · rfl
  · rw [List.drop_take]
    obtain ⟨m, hm⟩ : ∃ m, 0xb90 - off = m + 4 := ⟨0xb90 - off - 4, by omega⟩
    rw [hm]; rcases code.drop off with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩ <;> rfl

private theorem hooklessMuslProg_fetch_add (B : BitVec 64) (code : List (BitVec 8))
    (k : BitVec 64) (hk : k.toNat + 4 ≤ 0xb90) :
    (hooklessMuslProg B code).fetch (B + k) = ({ code } : Program).fetch (0#64 + k) := by
  have hx1 : (hooklessMuslProg B code).externAt? (B + k) = none := rfl
  have hx0 : ({ code } : Program).externAt? (0#64 + k) = none := rfl
  have hsub1 : ((B + k) - B).toNat = k.toNat := by rw [BitVec.add_comm, BitVec.add_sub_cancel]
  have hsub0 : ((0#64 + k) - 0#64).toNat = k.toNat := by rw [BitVec.zero_add, BitVec.sub_zero]
  unfold Program.fetch; rw [hx1, hx0]; dsimp only [hooklessMuslProg]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; rw [hsub1, hsub0]
  exact congrArg (Option.bind · decode) (readWordOff_take_eq hk)

theorem muslStartFetchAt_hookless (B : BitVec 64) (code : List (BitVec 8))
    (dynPageImm pageImm : BitVec 64) (addImm : BitVec 12)
    (hf : MuslStartFetchAt ({ code } : Program) 0#64 dynPageImm pageImm addImm) :
    MuslStartFetchAt (hooklessMuslProg B code) B dynPageImm pageImm addImm := by
  have e := hooklessMuslProg_fetch_add B code
  have e0 : (hooklessMuslProg B code).fetch B = ({ code } : Program).fetch 0#64 := by
    simpa only [BitVec.add_zero, BitVec.zero_add] using e 0#64 (by decide)
  unfold MuslStartFetchAt MuslHop1FetchAt MuslHop2Fetch MuslMemsetFetch MuslHop3aFetch
    MuslHop3bFetch MuslHop4Fetch MuslHop5Fetch MuslHop6Fetch MuslHop7Fetch at hf ⊢
  simp (disch := decide) only [e, e0]; exact hf

private theorem codeLoaded_hooklessMuslProg {B : BitVec 64} {code : List (BitVec 8)} {m : Memory}
    (hL : ({ base := B, code } : Program).CodeLoaded m) :
    (hooklessMuslProg B code).CodeLoaded m := by
  have hlen : (code.take 0xb90).length ≤ code.length := List.length_take_le' 0xb90 code
  have hno := hL.no_wrap
  refine Program.CodeLoaded.intro hL.aligned
    (by dsimp [hooklessMuslProg]; dsimp at hno; omega) fun i hi => ?_
  dsimp only [hooklessMuslProg] at hi ⊢
  have hi' : i < code.length := Nat.lt_of_lt_of_le hi hlen
  rw [List.getElem_take]; exact ⟨hL.byte_eq i hi', hL.perm_eq i hi', hL.isLazyFree_eq i hi'⟩

private theorem strip_codeLoaded_prog {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside (progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hin : progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold progKeep
    rw [decide_eq_true_eq, hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
  rw [strip_read8, strip_perm_of_keep hin, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem evalInst_setTidOnly_eq {B : BitVec 64} {code : List (BitVec 8)} (st : State)
    (h8 : st.readReg64 Reg.x8 = 96#64) :
    (hooklessMuslProg B code).evalInst (.system false 0#16) st =
      (st.writeReg64 Reg.x0 1#64).advancePC := by
  unfold Program.evalInst execInstWithSvc hooklessMuslProg setTidOnlySvc evalSvc
  dsimp only; rw [beq_iff_eq.mpr h8]; simp only [↓reduceIte]
  rcases st with ⟨_, _, _, _, _, ⟨_⟩, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  simp [State.writeReg64, State.advancePC]

private theorem evalInst_standard_setTid_eq {P : Program} (hsvc : P.svc = Syscall.standard)
    (st : State) (h8 : st.readReg64 Reg.x8 = 96#64) :
    P.evalInst (.system false 0#16) st = (st.writeReg64 Reg.x0 1#64).advancePC := by
  unfold Program.evalInst execInstWithSvc; rw [hsvc]; change evalSvc execSyscall st = _
  unfold evalSvc; dsimp only; rw [execSyscall_setTid _ h8]
  rcases st with ⟨_, _, _, _, _, ⟨_⟩, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  simp [State.writeReg64, State.advancePC]

private theorem steps_lift_hookless {P : Program} {B : BitVec 64} {code : List (BitVec 8)}
    (hsvcP : P.svc = Syscall.standard)
    (hnoHook : ∀ k : BitVec 64, k.toNat < 0xb90 → P.externAt? (B + k) = none)
    {sa' sf' : State} (hsteps : Steps (hooklessMuslProg B code) sa' sf')
    (hrun_f : sf'.status = .Running) :
    ∀ s1 : State, sa' = stripS (progKeep (hooklessMuslProg B code)) s1 →
      ∃ sf : State, Steps P s1 sf ∧ sf' = stripS (progKeep (hooklessMuslProg B code)) sf ∧
        MuslStartupVmPreserved s1 sf := by
  let Q₀ := hooklessMuslProg B code
  let kp := progKeep Q₀
  induction hsteps with
  | refl _ => intro s1 hs1; exact ⟨s1, Steps.refl s1, hs1, MuslStartupVmPreserved.refl s1⟩
  | @step s1' s2' _ hstep hrest ih =>
    intro s1 hs1
    have hrun2' : s2'.status = .Running := by
      cases hrest with | refl => exact hrun_f | step hs2 _ => exact hs2.running_of_step
    cases hstep with
    | halt_unmapped _ _ _ => cases hrun2'
    | extern _ hex _ _ => simp [hooklessMuslProg, Program.externAt?, Program.hookAtOff?] at hex
    | extern_fault _ hex _ => simp [hooklessMuslProg, Program.externAt?, Program.hookAtOff?] at hex
    | @exec inst hrun1' hfm' =>
      have hrun1 : s1.status = .Running := by rw [hs1] at hrun1'; cases s1; exact hrun1'
      have hpc_eq : s1'.pc = s1.pc := by rw [hs1]; cases s1; rfl
      have hmem_eq : s1'.mem = stripExecOutside kp s1.mem := by rw [hs1]; cases s1; rfl
      rw [hpc_eq, hmem_eq] at hfm'; unfold Program.fetchMem at hfm'
      have heQ : Q₀.externAt? s1.pc = none := rfl
      rw [heQ] at hfm'; simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm'
      by_cases hal_pc : s1.pc.toNat % 4 = 0
      · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm'
        by_cases hce' : (stripExecOutside kp s1.mem).canExec s1.pc 4 = true
        · simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm'
          have hr32 : (stripExecOutside kp s1.mem).read32 s1.pc = s1.mem.read32 s1.pc := by
            simp [Memory.read32, strip_read8]
          rw [hr32] at hfm'
          have hx4 :
              ((stripExecOutside kp s1.mem).perm s1.pc).x = true ∧
              ((stripExecOutside kp s1.mem).perm (s1.pc + 1#64)).x = true ∧
              ((stripExecOutside kp s1.mem).perm (s1.pc + 2#64)).x = true ∧
              ((stripExecOutside kp s1.mem).perm (s1.pc + 3#64)).x = true := by
            simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
          obtain ⟨hx0, hk0⟩ := strip_perm_x_imp hx4.1
          obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
          obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
          obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
          have hce : s1.mem.canExec s1.pc 4 = true := by
            simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
          have hpc_off : (s1.pc - B).toNat < 0xb90 := by
            have hlt : (s1.pc - Q₀.base).toNat < Q₀.code.length := of_decide_eq_true hk0
            have htk : (code.take 0xb90).length ≤ 0xb90 := List.length_take_le 0xb90 code
            dsimp [Q₀, hooklessMuslProg] at hlt; exact Nat.lt_of_lt_of_le hlt htk
          have hpc_B : B + (s1.pc - B) = s1.pc := by bv_omega
          have heP : P.externAt? s1.pc = none := hpc_B ▸ hnoHook (s1.pc - B) hpc_off
          have hfmP : P.fetchMem s1.mem s1.pc = some inst := by
            unfold Program.fetchMem; simpa [heP, hal_pc, hce] using hfm'
          cases hsvc0 : inst.isSvc0 with
          | false =>
            have hs2Q := evalInst_eq_execInst_of_not_isSvc0 (prog := Q₀) hsvc0 s1'
            have hs2P := Program.evalInst_eq_execInst inst s1 hsvcP
            have hstepP : Step P s1 (execInst inst s1) := hs2P ▸ Step.exec hrun1 hfmP
            have hcomm : Q₀.evalInst inst s1' = stripS kp (execInst inst s1) := by
              rw [hs2Q, hs1, execInst_stripS hsvc0 kp s1]
            have hvm1 : MuslStartupVmPreserved s1 (execInst inst s1) :=
              MuslStartupVmPreserved.of_nonSyscallPreserved
                (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hsvc0 s1)
            obtain ⟨sf, hsteps_rest, hsf_eq, hvm_rest⟩ := ih hrun_f (execInst inst s1) hcomm
            exact ⟨sf, Steps.step hstepP hsteps_rest, hsf_eq, hvm1.trans hvm_rest⟩
          | true =>
            have hinst_eq : inst = .system false 0#16 := by
              cases inst with
              | system isHalt imm =>
                cases isHalt with
                | true => simp [Instr.isSvc0] at hsvc0
                | false =>
                  simp only [Instr.isSvc0, Bool.not_false, Bool.true_and, beq_iff_eq] at hsvc0
                  subst hsvc0; rfl
              | _ => simp [Instr.isSvc0] at hsvc0
            subst hinst_eq
            have hr8_eq : s1'.readReg64 Reg.x8 = s1.readReg64 Reg.x8 := by
              rw [hs1]; cases s1; rfl
            by_cases h8 : s1.readReg64 Reg.x8 = 96#64
            · have hs2Q := evalInst_setTidOnly_eq (B := B) (code := code) s1' (hr8_eq.trans h8)
              have hs2P := evalInst_standard_setTid_eq hsvcP s1 h8
              have hstepP : Step P s1 ((s1.writeReg64 Reg.x0 1#64).advancePC) :=
                hs2P ▸ Step.exec hrun1 hfmP
              have hcomm : Q₀.evalInst (.system false 0#16) s1' =
                  stripS kp ((s1.writeReg64 Reg.x0 1#64).advancePC) := by
                rw [hs2Q, hs1]; cases s1; rfl
              have hvm1 : MuslStartupVmPreserved s1 ((s1.writeReg64 Reg.x0 1#64).advancePC) := by
                cases s1; exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
              obtain ⟨sf, hsteps_rest, hsf_eq, hvm_rest⟩ :=
                ih hrun_f ((s1.writeReg64 Reg.x0 1#64).advancePC) hcomm
              exact ⟨sf, Steps.step hstepP hsteps_rest, hsf_eq, hvm1.trans hvm_rest⟩
            · exfalso
              have hb : (s1'.readReg64 Reg.x8 == 96#64) = false :=
                beq_eq_false_iff_ne.mpr (hr8_eq ▸ h8)
              have hst_fault : (Q₀.evalInst (.system false 0#16) s1').status =
                  .Exception "unexpected syscall in musl startup" := by
                unfold Program.evalInst execInstWithSvc
                dsimp only [Q₀, hooklessMuslProg, evalSvc, setTidOnlySvc]; rw [hb]; rfl
              rw [hst_fault] at hrun2'; cases hrun2'
        · simp [hce'] at hfm'
      · simp [hal_pc] at hfm'

/-- Lift a `SepWP (hooklessMuslProg B code)` triple to `Steps P s sm` with `MuslStartupVmPreserved`. -/
theorem steps_startupVm_of_hooklessSepWP {P : Program} {B : BitVec 64} {code : List (BitVec 8)}
    (hsvcP : P.svc = Syscall.standard)
    (hnoHook : ∀ k : BitVec 64, k.toNat < 0xb90 → P.externAt? (B + k) = none)
    {s : State} (hL : ({ base := B, code } : Program).CodeLoaded s.mem)
    {tgt : BitVec 64} {Pre Post R : SepProp} {Inv : State → Prop}
    (hInv : ∀ sm, Inv (stripS (progKeep (hooklessMuslProg B code)) sm) → Inv sm)
    (hwp : SepWP (hooklessMuslProg B code) tgt
      (stripS (progKeep (hooklessMuslProg B code)) s) Pre (sepPost Inv Post))
    (hm : s.mem ⊨ Pre ∗ R) :
    ∃ sm, Steps P s sm ∧ sm.pc = tgt ∧ sm.status = .Running ∧
      MuslStartupVmPreserved s sm ∧ Inv sm ∧ (sm.mem ⊨ Post ∗ R) := by
  let Q₀ := hooklessMuslProg B code
  let kp := progKeep Q₀
  have hLQ : Q₀.CodeLoaded (stripS kp s).mem := by
    have h1 : (stripS kp s).mem = stripExecOutside kp s.mem := by cases s; rfl
    rw [h1]; exact strip_codeLoaded_prog (codeLoaded_hooklessMuslProg hL)
  obtain ⟨R_view, hm_strip, hunstrip⟩ := strip_frame kp hm
  have hm_strip' : (stripS kp s).mem ⊨ Pre ∗ R_view := by
    have h1 : (stripS kp s).mem = stripExecOutside kp s.mem := by cases s; rfl
    rwa [h1]
  obtain ⟨sm', hsteps', hout⟩ := SepWP.to_reaches_pc hwp hm_strip' hLQ
  rcases hout with ⟨hpc', hrun', P_f, hmf, hInv', hent⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hstepsP, hsm_eq, hvm⟩ :=
      steps_lift_hookless hsvcP hnoHook hsteps' hrun' s rfl
    have hpc : sm.pc = tgt := by rw [hsm_eq] at hpc'; cases sm; exact hpc'
    have hrun : sm.status = .Running := by rw [hsm_eq] at hrun'; cases sm; exact hrun'
    have hInv_sm : Inv sm := hInv sm (hsm_eq ▸ hInv')
    have hpost_strip : stripExecOutside kp sm.mem ⊨ Post ∗ R_view := by
      have h1 : sm'.mem = stripExecOutside kp sm.mem := by rw [hsm_eq]; cases sm; rfl
      exact h1 ▸ Satisfies.mono (sepConj_mono_left hent) hmf
    exact ⟨sm, hstepsP, hpc, hrun, hvm, hInv_sm, hunstrip hvm.2.2.2 hpost_strip⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-! ## Startup hops and `musl_start_fine_block_ofProg` -/

def Hop1RegsAt (B sp0 envp p m : BitVec 64) (a32 : BitVec 32)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 32#64 ∧ s.readReg64 .x0 = envp ∧ s.readReg64 .x1 = p ∧
  s.readReg64 .x19 = sp0 + 8#64 ∧ s.readReg64 .x20 = a32.zeroExtend 64 ∧
  s.readReg64 .x21 = m ∧ s.readReg64 .lr = B + 2052#64 ∧ s.readReg64 .x29 = 0#64 ∧
  s.fs = fs0 ∧ s.trace = tr0

set_option maxHeartbeats 1600000 in
theorem musl_start_hop1_at (Q : Program) (B dynPageImm pageImm : BitVec 64) (addImm : BitVec 12)
    (hf : MuslHop1FetchAt Q B dynPageImm pageImm addImm)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) (hpc : s.pc = B) (hrun : s.status = .Running)
    (hal : (s.sp &&& 15#64 == 0#64) = true) (hsp16 : s.sp &&& -16#64 = s.sp)
    (p g3 g4 v0 v1 v2 v3 r19 r20 r21 envp : BitVec 64) (a32 ah32 : BitVec 32)
    (h19 : s.readReg64 .x19 = r19) (h20 : s.readReg64 .x20 = r20) (h21 : s.readReg64 .x21 = r21)
    (henvp : envp = s.sp + 8#64 + BitVec.signExtend 64 a32 <<< 3 + 8#64) :
    SepWP Q (B + 0x5f4#64) s
      ((s.sp ↦₃₂ a32) ∗ ((s.sp + 4#64) ↦₃₂ ah32) ∗ ((s.sp + 8#64) ↦₆₄ p) ∗
       ((B + 0x2010#64) ↦₆₄ g3) ∗ ((B + 0x2018#64) ↦₆₄ g4) ∗
       ((s.sp - 32#64) ↦₆₄ v0) ∗ ((s.sp - 24#64) ↦₆₄ v1) ∗ ((s.sp - 16#64) ↦₆₄ v2) ∗
       ((s.sp - 8#64) ↦₆₄ v3))
      (sepPost (Hop1RegsAt B s.sp envp p (mainPcOf B pageImm addImm) a32 s.fs s.trace)
        ((s.sp ↦₃₂ a32) ∗ ((s.sp + 4#64) ↦₃₂ ah32) ∗ ((s.sp + 8#64) ↦₆₄ p) ∗
         ((B + 0x2010#64) ↦₆₄ g3) ∗ ((B + 0x2018#64) ↦₆₄ g4) ∗
         ((s.sp - 32#64) ↦₆₄ 0#64) ∗ ((s.sp - 24#64) ↦₆₄ r21) ∗ ((s.sp - 16#64) ↦₆₄ r20) ∗
         ((s.sp - 8#64) ↦₆₄ r19))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, f23, f24, f25⟩ := hf
  change s.sp &&& 18446744073709551600#64 = s.sp at hsp16
  (delta Hop1RegsAt mainPcOf; iterate 26 wp_step); wp_done

private theorem sp_sub_aligned {sp0 : BitVec 64} (k : BitVec 64) (hk : k.toNat % 16 = 0)
    (hal : (sp0 &&& 15#64 == 0#64) = true) : ((sp0 - k) &&& 15#64 == 0#64) = true := by
  have h0 : sp0 &&& 15#64 = 0#64 := eq_of_beq hal
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h0
  rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have := sp0.isLt; have := k.isLt; omega

private theorem hop6_gen_state_tp {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc sp x0 x19 x21 x30 tp : BitVec 64} {fs : FsState} {tr : List TraceEvent}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (h0 : s.readReg64 .x0 = x0) (h19 : s.readReg64 .x19 = x19) (h21 : s.readReg64 .x21 = x21)
    (h30 : s.readReg64 .lr = x30) (htp : s.tpidrEl0 = tp) (hfs : s.fs = fs) (htr : s.trace = tr)
    (h : ∀ s' : State, s'.pc = pc → s'.status = .Running → s'.sp = sp →
      s'.readReg64 .x0 = x0 → s'.readReg64 .x19 = x19 → s'.readReg64 .x21 = x21 →
      s'.readReg64 .lr = x30 → s'.tpidrEl0 = tp → s'.fs = fs → s'.trace = tr →
      SepWP prog tgt s' P post oom) :
    SepWP prog tgt s P post oom :=
  h s hpc hrun hsp h0 h19 h21 h30 htp hfs htr

private theorem hop6_gen_state9_tp {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc sp x0 x9 x19 x21 x30 tp : BitVec 64} {fs : FsState} {tr : List TraceEvent}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (h0 : s.readReg64 .x0 = x0) (h9 : s.readReg64 .x9 = x9) (h19 : s.readReg64 .x19 = x19)
    (h21 : s.readReg64 .x21 = x21) (h30 : s.readReg64 .lr = x30) (htp : s.tpidrEl0 = tp)
    (hfs : s.fs = fs) (htr : s.trace = tr)
    (h : ∀ s' : State, s'.pc = pc → s'.status = .Running → s'.sp = sp →
      s'.readReg64 .x0 = x0 → s'.readReg64 .x9 = x9 → s'.readReg64 .x19 = x19 →
      s'.readReg64 .x21 = x21 → s'.readReg64 .lr = x30 → s'.tpidrEl0 = tp →
      s'.fs = fs → s'.trace = tr → SepWP prog tgt s' P post oom) :
    SepWP prog tgt s P post oom :=
  h s hpc hrun hsp h0 h9 h19 h21 h30 htp hfs htr

def Hop6FineRegs (B sp0 r19 m : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 432#64 ∧ s.readReg64 .x0 = 0#64 ∧ s.readReg64 .x19 = r19 ∧
  s.readReg64 .lr = B + 0xaec#64 ∧ s.readReg64 .x21 = m ∧
  s.fs = fs0 ∧ s.trace = tr0 ∧ s.tpidrEl0 = B + 0x2148#64

set_option maxHeartbeats 3200000 in
theorem musl_start_hop6_fine (Q : Program) (B : BitVec 64) (hf : MuslHop6Fetch Q B)
    (hsetTid : ∀ st : State, st.readReg64 Reg.x8 = 96#64 →
      Q.evalInst (.system false 0#16) st = (st.writeReg64 Reg.x0 1#64).advancePC)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) {fs0 : FsState} {tr0 : List TraceEvent}
    (sp0 r19 m : BitVec 64) (hpc : s.pc = B + 0x858#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (hsp : s.sp = sp0 - 432#64)
    (hx0 : s.readReg64 .x0 = B + 0x2080#64) (hlr : s.readReg64 .lr = B + 0xaec#64)
    (h19 : s.readReg64 .x19 = r19) (h21 : s.readReg64 .x21 = m)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (d0 d1 e0 e3 e5 e6 e7 e8 sy : BitVec 64) (e1 : BitVec 8) (e2 e4 : BitVec 32) :
    SepWP Q (B + 0xaec#64) s
      (((sp0 - 448#64) ↦₆₄ d0) ∗ ((sp0 - 440#64) ↦₆₄ d1) ∗ ((B + 0x2080#64) ↦₆₄ e0) ∗
       ((B + 0x21e8#64) ↦₈ e1) ∗ ((B + 0x20a8#64) ↦₃₂ e2) ∗ ((B + 0x2118#64) ↦₆₄ e3) ∗
       ((B + 0x20a0#64) ↦₃₂ e4) ∗ ((B + 0x20f8#64) ↦₆₄ e5) ∗ ((B + 0x21d0#64) ↦₆₄ sy) ∗
       ((B + 0x2088#64) ↦₆₄ e6) ∗ ((B + 0x2090#64) ↦₆₄ e7) ∗ ((B + 0x2098#64) ↦₆₄ e8))
      (sepPost (Hop6FineRegs B sp0 r19 m fs0 tr0)
        (((sp0 - 448#64) ↦₆₄ (B + 0xaec#64)) ∗ ((sp0 - 440#64) ↦₆₄ r19) ∗
         ((B + 0x2080#64) ↦₆₄ (B + 0x2080#64)) ∗ ((B + 0x21e8#64) ↦₈ 1#8) ∗
         ((B + 0x20a8#64) ↦₃₂ 2#32) ∗ ((B + 0x2118#64) ↦₆₄ (B + 0x2220#64)) ∗
         ((B + 0x20a0#64) ↦₃₂ 1#32) ∗ ((B + 0x20f8#64) ↦₆₄ (B + 0x20f8#64)) ∗
         ((B + 0x21d0#64) ↦₆₄ sy) ∗ ((B + 0x2088#64) ↦₆₄ (B + 0x2080#64)) ∗
         ((B + 0x2090#64) ↦₆₄ (B + 0x2080#64)) ∗ ((B + 0x2098#64) ↦₆₄ sy))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32⟩ := hf
  have hal' : (s.sp &&& 15#64 == 0#64) = true := hsp ▸ sp_sub_aligned 432#64 (by decide) hal
  delta Hop6FineRegs; iterate 4 wp_step
  have hmsr : ∀ st : State, Q.evalInst (.sysReg false 0x5e82#15 (.gpr 0x00#5)) st =
      (setTpidrEl0 st (st.readReg64 (.gpr 0x00#5))).advancePC := fun st => by cases st; rfl
  refine SepWP.step_pure (by simp) (by simp [hrun]) f30 rfl (by rw [hmsr]; simp) ?_; rw [hmsr]
  refine hop6_gen_state_tp (pc := B + 0xb88#64) (sp := sp0 - 448#64) (x0 := B + 0x2148#64)
    (x19 := B + 0x2080#64) (x21 := m) (x30 := B + 0x868#64) (tp := B + 0x2148#64)
    (fs := fs0) (tr := tr0) (by simp [BitVec.add_assoc]) (by simp [hrun]) (by simp) (by simp)
    (by simp) (by simp [h21]) (by simp) (by simp [setTpidrEl0, State.advancePC, BitVec.add_assoc])
    (by simp [setTpidrEl0, hfs]) (by simp [setTpidrEl0, htr]) fun s hpc hrun hsp hx0 h19 h21 hlr htp hfs htr => ?_
  have hal' : (s.sp &&& 15#64 == 0#64) = true := hsp ▸ sp_sub_aligned 448#64 (by decide) hal
  iterate 13 wp_step
  refine SepWP.step_pure (by simp) (by simp [hrun]) f15 rfl (by rw [hsetTid _ (by simp)]; simp) ?_
  rw [hsetTid _ (by simp)]; clear hal'
  refine hop6_gen_state9_tp (pc := B + 0x898#64) (sp := sp0 - 448#64) (x0 := 1#64) (x9 := 0#64)
    (x19 := B + 0x2080#64) (x21 := m) (x30 := B + 0x868#64) (tp := B + 0x2148#64)
    (fs := fs0) (tr := tr0) (by simp [BitVec.add_assoc]) (by simp [hrun]) (by simp [hsp]) (by simp)
    (by simp) (by simp [h19]) (by simp [h21]) (by simp [hlr]) (by simp [htp]) (by simp [hfs])
    (by simp [htr]) ?_
  clear hpc hrun hsp hx0 h19 h21 hlr htp hfs htr
  intro s hpc hrun hsp hx0 hx9 h19 h21 hlr htp hfs htr
  have hal' : (s.sp &&& 15#64 == 0#64) = true := hsp ▸ sp_sub_aligned 448#64 (by decide) hal
  (iterate 14 wp_step); wp_done

def Hop7FineRegs (B sp0 x19v x20v tp : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  Hop7Regs B sp0 x19v x20v fs0 tr0 s ∧ s.tpidrEl0 = tp

set_option maxHeartbeats 3200000 in
theorem musl_start_hop7_at (Q : Program) (B m tp : BitVec 64) (hf : MuslHop7Fetch Q B)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) {fs0 : FsState} {tr0 : List TraceEvent}
    (sp0 r22 : BitVec 64) (hpc : s.pc = B + 0xaec#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (htp : s.tpidrEl0 = tp) (hsp : s.sp = sp0 - 432#64)
    (hx0 : s.readReg64 .x0 = 0#64) (h21 : s.readReg64 .x21 = m) (h22 : s.readReg64 .x22 = r22)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (rnd uid gid ia k0 k1 x29v x20v x19v o21 o20 o19 : BitVec 64) :
    SepWP Q m s
      (((sp0 - 432#64) ↦₆₄ (B + 0x6d0#64)) ∗ ((sp0 - 168#64) ↦₆₄ rnd) ∗
       ((sp0 - 280#64) ↦₆₄ uid) ∗ ((sp0 - 272#64) ↦₆₄ uid) ∗ ((sp0 - 264#64) ↦₆₄ gid) ∗
       ((sp0 - 256#64) ↦₆₄ gid) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((B + 0x2020#64) ↦₆₄ ia) ∗
       ((B + 0x2028#64) ↦₆₄ ia) ∗ ((sp0 - 80#64) ↦₆₄ k0) ∗ ((sp0 - 72#64) ↦₆₄ k1) ∗
       ((sp0 - 64#64) ↦₆₄ x29v) ∗ ((sp0 - 56#64) ↦₆₄ (B + 2052#64)) ∗ ((sp0 - 48#64) ↦₆₄ x20v) ∗
       ((sp0 - 40#64) ↦₆₄ x19v) ∗ ((sp0 - 32#64) ↦₆₄ 0#64) ∗ ((sp0 - 24#64) ↦₆₄ o21) ∗
       ((sp0 - 16#64) ↦₆₄ o20) ∗ ((sp0 - 8#64) ↦₆₄ o19))
      (sepPost (Hop7FineRegs B sp0 x19v x20v tp fs0 tr0)
        (((sp0 - 432#64) ↦₆₄ (B + 0x6d0#64)) ∗ ((sp0 - 168#64) ↦₆₄ rnd) ∗
         ((sp0 - 280#64) ↦₆₄ uid) ∗ ((sp0 - 272#64) ↦₆₄ uid) ∗ ((sp0 - 264#64) ↦₆₄ gid) ∗
         ((sp0 - 256#64) ↦₆₄ gid) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗ ((B + 0x2020#64) ↦₆₄ ia) ∗
         ((B + 0x2028#64) ↦₆₄ ia) ∗ ((sp0 - 80#64) ↦₆₄ (B + 0x844#64)) ∗ ((sp0 - 72#64) ↦₆₄ k1) ∗
         ((sp0 - 64#64) ↦₆₄ (x20v.truncate 32).zeroExtend 64) ∗ ((sp0 - 56#64) ↦₆₄ x19v) ∗
         ((sp0 - 48#64) ↦₆₄ 0#64) ∗ ((sp0 - 40#64) ↦₆₄ x19v) ∗ ((sp0 - 32#64) ↦₆₄ r22) ∗
         ((sp0 - 24#64) ↦₆₄ o21) ∗ ((sp0 - 16#64) ↦₆₄ o20) ∗ ((sp0 - 8#64) ↦₆₄ o19))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36,
    f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50⟩ := hf
  have hal' : (s.sp &&& 15#64 == 0#64) = true := hsp ▸ sp_sub_aligned 432#64 (by decide) hal
  (delta Hop7FineRegs Hop7Regs; iterate 51 wp_step); wp_done

set_option maxHeartbeats 3200000 in
theorem musl_start_fine (Q : Program) (B dynPageImm pageImm : BitVec 64) (addImm : BitVec 12)
    (hf : MuslStartFetchAt Q B dynPageImm pageImm addImm)
    (hsetTid : ∀ st : State, st.readReg64 Reg.x8 = 96#64 →
      Q.evalInst (.system false 0#16) st = (st.writeReg64 Reg.x0 1#64).advancePC)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) (hpc : s.pc = B) (hrun : s.status = .Running)
    (hal : (s.sp &&& 15#64 == 0#64) = true) (hsp16 : s.sp &&& -16#64 = s.sp)
    (envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex : BitVec 64) (a32 ah32 : BitVec 32)
    (henvp : envp = s.sp + 8#64 + BitVec.signExtend 64 a32 <<< 3 + 8#64)
    (hp : p ≠ 0#64) (hph : ph + 504#64 ≠ 0#64)
    (g3 g4 ia e0 e1 t0 t1 t2 t3 t4 t5 t6 t7 t8 f0 f3 f5 f6 f7 f8 sy u0 u1 u2
     d0 d1 d2 d3 : BitVec 64) (f1 : BitVec 8) (f2 f4 : BitVec 32)
    (w480 w472 w464 w456 w448 w440 w432 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16
     m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37
     n64 n56 n48 n40 v0 v1 v2 v3 : BitVec 64) :
    SepWP Q (mainPcOf B pageImm addImm) s
      (StartProc s.sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗ StartArgv0 p ∗
        StartPhdrs ph ∗ ((B + 0x2000#64) ↦₃₂ 0x20000#32) ∗ ((B + 0x2008#64) ↦₆₄ 0#64) ∗
       ((B + 0x2010#64) ↦₆₄ g3) ∗ ((B + 0x2018#64) ↦₆₄ g4) ∗ ((B + 0x2020#64) ↦₆₄ ia) ∗
       ((B + 0x2028#64) ↦₆₄ ia) ∗ ((B + 0x2040#64) ↦₆₄ e0) ∗ ((B + 0x2050#64) ↦₆₄ 0#64) ∗
       ((B + 0x2058#64) ↦₆₄ t0) ∗ ((B + 0x2060#64) ↦₆₄ t1) ∗ ((B + 0x2068#64) ↦₆₄ t2) ∗
       ((B + 0x2070#64) ↦₆₄ t3) ∗ ((B + 0x2078#64) ↦₆₄ t4) ∗ ((B + 0x2080#64) ↦₆₄ f0) ∗
       ((B + 0x2088#64) ↦₆₄ f6) ∗ ((B + 0x2090#64) ↦₆₄ f7) ∗ ((B + 0x2098#64) ↦₆₄ f8) ∗
       ((B + 0x20a0#64) ↦₃₂ f4) ∗ ((B + 0x20a8#64) ↦₃₂ f2) ∗ ((B + 0x20f8#64) ↦₆₄ f5) ∗
       ((B + 0x2118#64) ↦₆₄ f3) ∗ ((B + 0x2140#64) ↦₆₄ u0) ∗ ((B + 0x2150#64) ↦₆₄ u1) ∗
       ((B + 0x2158#64) ↦₆₄ u2) ∗ ((B + 0x21d0#64) ↦₆₄ sy) ∗ ((B + 0x21d8#64) ↦₆₄ d3) ∗
       ((B + 0x21e0#64) ↦₆₄ d2) ∗ ((B + 0x21e8#64) ↦₈ f1) ∗ ((B + 0x21f0#64) ↦₆₄ e1) ∗
       ((B + 0x21f8#64) ↦₆₄ t5) ∗ ((B + 0x2200#64) ↦₆₄ t6) ∗ ((B + 0x2208#64) ↦₆₄ t7) ∗
       ((B + 0x2210#64) ↦₆₄ t8) ∗ ((B + 0x2218#64) ↦₆₄ d1) ∗ ((B + 0x2250#64) ↦₆₄ d0) ∗
       ((s.sp - 480#64) ↦₆₄ w480) ∗ ((s.sp - 472#64) ↦₆₄ w472) ∗ ((s.sp - 464#64) ↦₆₄ w464) ∗ ((s.sp - 456#64) ↦₆₄ w456) ∗
       ((s.sp - 448#64) ↦₆₄ w448) ∗ ((s.sp - 440#64) ↦₆₄ w440) ∗ ((s.sp - 432#64) ↦₆₄ w432) ∗ ((s.sp - 368#64) ↦₆₄ m0) ∗
       ((s.sp - 360#64) ↦₆₄ m1) ∗ ((s.sp - 352#64) ↦₆₄ m2) ∗ ((s.sp - 344#64) ↦₆₄ m3) ∗ ((s.sp - 336#64) ↦₆₄ m4) ∗
       ((s.sp - 328#64) ↦₆₄ m5) ∗ ((s.sp - 320#64) ↦₆₄ m6) ∗ ((s.sp - 312#64) ↦₆₄ m7) ∗ ((s.sp - 304#64) ↦₆₄ m8) ∗
       ((s.sp - 296#64) ↦₆₄ m9) ∗ ((s.sp - 288#64) ↦₆₄ m10) ∗ ((s.sp - 280#64) ↦₆₄ m11) ∗ ((s.sp - 272#64) ↦₆₄ m12) ∗
       ((s.sp - 264#64) ↦₆₄ m13) ∗ ((s.sp - 256#64) ↦₆₄ m14) ∗ ((s.sp - 248#64) ↦₆₄ m15) ∗ ((s.sp - 240#64) ↦₆₄ m16) ∗
       ((s.sp - 232#64) ↦₆₄ m17) ∗ ((s.sp - 224#64) ↦₆₄ m18) ∗ ((s.sp - 216#64) ↦₆₄ m19) ∗ ((s.sp - 208#64) ↦₆₄ m20) ∗
       ((s.sp - 200#64) ↦₆₄ m21) ∗ ((s.sp - 192#64) ↦₆₄ m22) ∗ ((s.sp - 184#64) ↦₆₄ m23) ∗ ((s.sp - 176#64) ↦₆₄ m24) ∗
       ((s.sp - 168#64) ↦₆₄ m25) ∗ ((s.sp - 160#64) ↦₆₄ m26) ∗ ((s.sp - 152#64) ↦₆₄ m27) ∗ ((s.sp - 144#64) ↦₆₄ m28) ∗
       ((s.sp - 136#64) ↦₆₄ m29) ∗ ((s.sp - 128#64) ↦₆₄ m30) ∗ ((s.sp - 120#64) ↦₆₄ m31) ∗ ((s.sp - 112#64) ↦₆₄ m32) ∗
       ((s.sp - 104#64) ↦₆₄ m33) ∗ ((s.sp - 96#64) ↦₆₄ m34) ∗ ((s.sp - 88#64) ↦₆₄ m35) ∗ ((s.sp - 80#64) ↦₆₄ m36) ∗
       ((s.sp - 72#64) ↦₆₄ m37) ∗ ((s.sp - 64#64) ↦₆₄ n64) ∗ ((s.sp - 56#64) ↦₆₄ n56) ∗ ((s.sp - 48#64) ↦₆₄ n48) ∗
       ((s.sp - 40#64) ↦₆₄ n40) ∗ ((s.sp - 32#64) ↦₆₄ v0) ∗ ((s.sp - 24#64) ↦₆₄ v1) ∗ ((s.sp - 16#64) ↦₆₄ v2) ∗
       ((s.sp - 8#64) ↦₆₄ v3))
      (sepPost (Hop7FineRegs B s.sp (s.sp + 8#64) (a32.zeroExtend 64) (B + 0x2148#64) s.fs s.trace)
        (StartProc s.sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗ StartArgv0 p
          ∗ StartPhdrs ph ∗ ((B + 0x2000#64) ↦₃₂ 0x20000#32) ∗ ((B + 0x2008#64) ↦₆₄ 0#64) ∗
         ((B + 0x2010#64) ↦₆₄ g3) ∗ ((B + 0x2018#64) ↦₆₄ g4) ∗ ((B + 0x2020#64) ↦₆₄ ia) ∗
         ((B + 0x2028#64) ↦₆₄ ia) ∗ ((B + 0x2040#64) ↦₆₄ envp) ∗ ((B + 0x2050#64) ↦₆₄ 0#64) ∗
         ((B + 0x2058#64) ↦₆₄ 0#64) ∗ ((B + 0x2060#64) ↦₆₄ 0#64) ∗ ((B + 0x2068#64) ↦₆₄ 0#64) ∗
         ((B + 0x2070#64) ↦₆₄ 8#64) ∗ ((B + 0x2078#64) ↦₆₄ 0#64) ∗
         ((B + 0x2080#64) ↦₆₄ (B + 0x2080#64)) ∗ ((B + 0x2088#64) ↦₆₄ (B + 0x2080#64)) ∗
         ((B + 0x2090#64) ↦₆₄ (B + 0x2080#64)) ∗ ((B + 0x2098#64) ↦₆₄ sy) ∗
         ((B + 0x20a0#64) ↦₃₂ 1#32) ∗ ((B + 0x20a8#64) ↦₃₂ 2#32) ∗
         ((B + 0x20f8#64) ↦₆₄ (B + 0x20f8#64)) ∗ ((B + 0x2118#64) ↦₆₄ (B + 0x2220#64)) ∗
         ((B + 0x2140#64) ↦₆₄ (B + 0x2150#64)) ∗ ((B + 0x2150#64) ↦₆₄ 1#64) ∗
         ((B + 0x2158#64) ↦₆₄ (B + 0x2148#64)) ∗ ((B + 0x21d0#64) ↦₆₄ sy) ∗
         ((B + 0x21d8#64) ↦₆₄ p) ∗ ((B + 0x21e0#64) ↦₆₄ p) ∗ ((B + 0x21e8#64) ↦₈ 1#8) ∗
         ((B + 0x21f0#64) ↦₆₄ (envp + 8#64)) ∗ ((B + 0x21f8#64) ↦₆₄ (B + 0x2050#64)) ∗
         ((B + 0x2200#64) ↦₆₄ 0xe0#64) ∗ ((B + 0x2208#64) ↦₆₄ 8#64) ∗ ((B + 0x2210#64) ↦₆₄ 1#64) ∗
         ((B + 0x2218#64) ↦₆₄ pg) ∗ ((B + 0x2250#64) ↦₆₄ hw) ∗
         ((s.sp - 480#64) ↦₆₄ (B + 0xae8#64)) ∗ (∃∗ v : BitVec 64, (s.sp - 472#64) ↦₆₄ v) ∗
         (∃∗ v : BitVec 64, (s.sp - 464#64) ↦₆₄ v) ∗ ((s.sp - 456#64) ↦₆₄ mainPcOf B pageImm addImm) ∗
         ((s.sp - 448#64) ↦₆₄ (B + 0xaec#64)) ∗ (∃∗ v : BitVec 64, (s.sp - 440#64) ↦₆₄ v) ∗
         ((s.sp - 432#64) ↦₆₄ (B + 0x6d0#64)) ∗ ((s.sp - 368#64) ↦₆₄ 0#64) ∗ ((s.sp - 360#64) ↦₆₄ 0#64) ∗
         ((s.sp - 352#64) ↦₆₄ 0#64) ∗ ((s.sp - 344#64) ↦₆₄ ph) ∗ ((s.sp - 336#64) ↦₆₄ 56#64) ∗ ((s.sp - 328#64) ↦₆₄ 11#64) ∗
         ((s.sp - 320#64) ↦₆₄ pg) ∗ ((s.sp - 312#64) ↦₆₄ ab) ∗ ((s.sp - 304#64) ↦₆₄ af) ∗ ((s.sp - 296#64) ↦₆₄ ae) ∗
         ((s.sp - 288#64) ↦₆₄ 0#64) ∗ ((s.sp - 280#64) ↦₆₄ uid) ∗ ((s.sp - 272#64) ↦₆₄ uid) ∗ ((s.sp - 264#64) ↦₆₄ gid) ∗
         ((s.sp - 256#64) ↦₆₄ gid) ∗ ((s.sp - 248#64) ↦₆₄ plat) ∗ ((s.sp - 240#64) ↦₆₄ hw) ∗ ((s.sp - 232#64) ↦₆₄ clk) ∗
         ((s.sp - 224#64) ↦₆₄ 0#64) ∗ ((s.sp - 216#64) ↦₆₄ 0#64) ∗ ((s.sp - 208#64) ↦₆₄ 0#64) ∗ ((s.sp - 200#64) ↦₆₄ 0#64) ∗
         ((s.sp - 192#64) ↦₆₄ 0#64) ∗ ((s.sp - 184#64) ↦₆₄ 0#64) ∗ ((s.sp - 176#64) ↦₆₄ 0#64) ∗ ((s.sp - 168#64) ↦₆₄ rnd) ∗
         ((s.sp - 160#64) ↦₆₄ hw2) ∗ ((s.sp - 152#64) ↦₆₄ 0#64) ∗ ((s.sp - 144#64) ↦₆₄ 0#64) ∗ ((s.sp - 136#64) ↦₆₄ 0#64) ∗
         ((s.sp - 128#64) ↦₆₄ 0#64) ∗ ((s.sp - 120#64) ↦₆₄ ex) ∗ ((s.sp - 112#64) ↦₆₄ 0#64) ∗ ((s.sp - 104#64) ↦₆₄ 0#64) ∗
         ((s.sp - 96#64) ↦₆₄ 0#64) ∗ ((s.sp - 88#64) ↦₆₄ 0#64) ∗ ((s.sp - 80#64) ↦₆₄ (B + 0x844#64)) ∗
         ((s.sp - 72#64) ↦₆₄ 0#64) ∗ ((s.sp - 64#64) ↦₆₄ ((a32.zeroExtend 64).truncate 32).zeroExtend 64) ∗
         ((s.sp - 56#64) ↦₆₄ (s.sp + 8#64)) ∗ ((s.sp - 48#64) ↦₆₄ 0#64) ∗ ((s.sp - 40#64) ↦₆₄ (s.sp + 8#64)) ∗
         (∃∗ v : BitVec 64, (s.sp - 32#64) ↦₆₄ v) ∗ ((s.sp - 24#64) ↦₆₄ (s.readReg64 .x21)) ∗
         ((s.sp - 16#64) ↦₆₄ (s.readReg64 .x20)) ∗ ((s.sp - 8#64) ↦₆₄ (s.readReg64 .x19)))) := by
  let m := mainPcOf B pageImm addImm
  obtain ⟨hf1, hf2, hf3a, hf3b, hf4, hf5, hf6, hf7⟩ := hf
  refine SepWP.bind_sepPost (musl_start_hop1_at Q B dynPageImm pageImm addImm hf1 hB s hpc hrun
    hal hsp16 p g3 g4 v0 v1 v2 v3 _ _ _ envp a32 ah32 rfl rfl rfl henvp) (by sep_frame) ?_
  rintro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hlr1, hx29_1, hfs1, htr1⟩
  refine SepWP.bind_sepPost (musl_start_hop2 Q B hf2 s1 s.sp envp p m (s.sp + 8#64)
    (a32.zeroExtend 64) 0#64 (B + 2052#64) hpc1 hrun1 hfs1 htr1 hsp1 hal hx0_1 hx1_1 hx19_1 hx20_1
    hx29_1 hlr1 hx21_1 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20
    m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 n64 n56 n48 n40)
    (by sep_frame) fun s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx21_2, hfs2, htr2⟩ => ?_
  refine SepWP.bind_sepPost (musl_start_hop3a Q B hf3a hB s2 s.sp envp p m hpc2 hrun2 hfs2 htr2
    hsp2 hx19_2 hx20_2 hx21_2 e0 e1 ph 56#64 11#64 pg ab af ae uid uid gid gid plat hw clk 0#64 rnd
    hw2 ex 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
    0#64) (by sep_frame) fun s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hfs3, htr3⟩ => ?_
  refine SepWP.bind_sepPost (musl_start_hop3b Q B hf3b hB s3 s.sp p m hpc3 hrun3 hfs3 htr3 hsp3
    hx19_3 hp hx21_3 hal hw ex pg d0 d1 d2 d3) (by sep_frame)
    fun s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx0_4, hlr4, hx21_4, hfs4, htr4⟩ => ?_
  refine SepWP.bind_sepPost (musl_start_hop4 Q B hf4 hB s4 s.sp ph m hpc4 hrun4 hfs4 htr4 hsp4
    hx0_4 hlr4 hx21_4 hal hph w432 t0 t1 t2 t3 t4 t5 t6 t7 t8) (by sep_frame)
    fun s5 hpc5 hrun5 ⟨hsp5, hx0_5, hlr5, hx21_5, hfs5, htr5⟩ => ?_
  refine SepWP.bind_sepPost (musl_start_hop5 Q B hf5 hB s5 s.sp (s5.readReg64 .x19)
    (s5.readReg64 .x20) m (s5.readReg64 .x22) (s5.readReg64 .x23) hpc5 hrun5 hfs5 htr5 hsp5 hx0_5
    hlr5 rfl rfl hx21_5 rfl rfl hal w480 w472 w464 w456 w448 w440 u0 u1 u2) (by sep_frame)
    fun s6 hpc6 hrun6 ⟨hsp6, hx0_6, hlr6, hx21_6, hfs6, htr6⟩ => ?_
  refine SepWP.bind_sepPost (musl_start_hop6_fine Q B hf6 hsetTid hB s6 s.sp (s6.readReg64 .x19) m
    hpc6 hrun6 hfs6 htr6 hsp6 hx0_6 hlr6 rfl hx21_6 hal (s5.readReg64 .x20) (s5.readReg64 .x19) f0
    f3 f5 f6 f7 f8 sy f1 f2 f4) (by sep_frame)
    fun s7 hpc7 hrun7 ⟨hsp7, hx0_7, hx19_7, hlr7, hx21_7, hfs7, htr7, htp7⟩ => ?_
  exact SepWP.done_sepPost (musl_start_hop7_at Q B m (B + 0x2148#64) hf7 hB s7 s.sp
    (s7.readReg64 .x22) hpc7 hrun7 hfs7 htr7 htp7 hsp7 hx0_7 hx21_7 rfl hal rnd uid gid ia 0#64 0#64
    0#64 (a32.zeroExtend 64) (s.sp + 8#64) (s.readReg64 .x21) (s.readReg64 .x20) (s.readReg64 .x19))
    (by sep_frame) (fun _ _ _ h => h) (by sep_frame)

set_option maxHeartbeats 3200000 in
/-- Block-level startup run preserving `MuslStartupVmPreserved`, `sm.tpidrEl0 = B + 0x2148#64`,
    and the four `mallocng` runtime/auxv words in `musl`'s statics. -/
theorem musl_start_fine_block_ofProg {P : Program} {B dynPageImm pageImm : BitVec 64}
    {addImm : BitVec 12} {code : List (BitVec 8)} (hsvcP : P.svc = Syscall.standard)
    (hnoHook : ∀ k : BitVec 64, k.toNat < 0xb90 → P.externAt? (B + k) = none)
    (hf : MuslStartFetchAt ({ code } : Program) 0#64 dynPageImm pageImm addImm)
    (hB : B &&& 0xfff#64 = 0#64) {s : State} (hL : ({ base := B, code } : Program).CodeLoaded s.mem)
    (hpc : s.pc = B) (hrun : s.status = .Running)
    (hal : (s.sp &&& 15#64 == 0#64) = true) (hsp16 : s.sp &&& -16#64 = s.sp)
    (envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex : BitVec 64) (a32 ah32 : BitVec 32)
    (henvp : envp = s.sp + 8#64 + BitVec.signExtend 64 a32 <<< 3 + 8#64)
    (hp : p ≠ 0#64) (hph : ph + 504#64 ≠ 0#64)
    (h0 g3 g4 ia F : BitVec 64) (hh0 : h0.extractLsb' 0 32 = 0x20000#32) {R : SepProp}
    (hm : s.mem ⊨ StartProc s.sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗
      StartArgv0 p ∗ StartPhdrs ph ∗ ((B + 0x2000#64) ↦₆₄* muslRwWords h0 g3 g4 ia F) ∗
      ((s.sp - 480#64) ↦₆₄* List.replicate 60 0#64) ∗ R) :
    ∃ sm, Steps P s sm ∧ sm.pc = mainPcOf B pageImm addImm ∧ sm.status = .Running ∧
      MuslStartupVmPreserved s sm ∧
      Hop7FineRegs B s.sp (s.sp + 8#64) (a32.zeroExtend 64) (B + 0x2148#64) s.fs s.trace sm ∧
      (sm.mem ⊨ StartProc s.sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗
        StartArgv0 p ∗ ((B + 0x2030#64) ↦₆₄ F) ∗ ((B + 0x2038#64) ↦₆₄ F) ∗
        ((B + 0x20a4#64) ↦₃₂ 0#32) ∗ ((B + 0x21eb#64) ↦₈ 0#8) ∗
        ((B + 0x21f0#64) ↦₆₄ (envp + 8#64)) ∗ ((B + 0x2218#64) ↦₆₄ pg) ∗
        memRegion (s.sp - 480#64) 432 ∗ R) := by
  unfold muslRwWords at hm
  simp (disch := decide) only [List.cons_append, List.nil_append, List.replicate_succ,
    List.replicate_zero, pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd, bv_sub_add_lit, Nat.reduceSub] at hm
  rw [pointsTo64_split32 (B + 8192#64) h0, hh0, pointsTo64_split32 (B + 8352#64) 0#64,
    pointsTo64_split32 (B + 8360#64) 0#64, pointsTo64_eq_8 (B + 8680#64) 0#64] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  let Q₀ := hooklessMuslProg B code; let kp := progKeep Q₀
  have hs_sp : (stripS kp s).sp = s.sp := by cases s; rfl
  have hs_pc : (stripS kp s).pc = B := (by cases s; rfl : (stripS kp s).pc = s.pc).trans hpc
  have hs_run : (stripS kp s).status = .Running :=
    (by cases s; rfl : (stripS kp s).status = s.status).trans hrun
  have hs_fs : (stripS kp s).fs = s.fs := by cases s; rfl
  have hs_tr : (stripS kp s).trace = s.trace := by cases s; rfl
  have hwp_strip := musl_start_fine Q₀ B dynPageImm pageImm addImm
    (muslStartFetchAt_hookless B code dynPageImm pageImm addImm hf)
    evalInst_setTidOnly_eq hB (stripS kp s) hs_pc hs_run (hs_sp.symm ▸ hal) (hs_sp.symm ▸ hsp16)
    envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 (hs_sp.symm ▸ henvp) hp hph g3 g4
    ia 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 ((0#64).extractLsb' 0 8) ((0#64).extractLsb' 0 32)
    ((0#64).extractLsb' 0 32) 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  rw [hs_sp, hs_fs, hs_tr] at hwp_strip
  obtain ⟨sm, hsteps, hpc', hrun', hvm, hinv, hpost⟩ := steps_startupVm_of_hooklessSepWP (R := _)
    hsvcP hnoHook hL (fun sm h => by cases sm; exact h) hwp_strip (by sep_frame)
  refine ⟨sm, hsteps, hpc', hrun', hvm, hinv, ?_⟩
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨x1, x2, x3, x4, hpost⟩ := hpost
  rw [show memRegion (s.sp - 480#64) 432 = memRegion (s.sp - 480#64) (8 * 54) from rfl,
    memRegion_cellsW _ 54 (by decide)]
  simp (disch := decide) only [cellsW, sepConj_emp, bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  rw [show (0#64).extractLsb' 24 8 = 0#8 from rfl, show (0#64).extractLsb' 32 32 = 0#32 from rfl] at hpost
  exact sat_of_entails_frame hpost (by sep_frame)

/-! ## Initial stack `AT_RANDOM` slice and `musl_startup_fineInit_ofProg` -/

private def auxPreEntries (ph pg ab af ae uid euid gid egid plat hw clk sec : BitVec 64) :
    List (BitVec 64 × BitVec 64) :=
  [ (3#64, ph), (4#64, 56#64), (5#64, 11#64), (6#64, pg), (7#64, ab), (8#64, af), (9#64, ae)
  , (11#64, uid), (12#64, euid), (13#64, gid), (14#64, egid), (15#64, plat), (16#64, hw)
  , (17#64, clk), (23#64, sec) ]

private def auxSufEntries (hw2 ex : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(26#64, hw2), (31#64, ex)]

private theorem auxPreEntries_ok (ph pg ab af ae uid euid gid egid plat hw clk sec : BitVec 64) :
    ∀ e ∈ auxPreEntries ph pg ab af ae uid euid gid egid plat hw clk sec,
      e.1 ≠ 0#64 ∧ e.1 ≠ 25#64 := by
  intro e he; simp only [auxPreEntries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> (dsimp only; exact ⟨by decide, by decide⟩)

private theorem auxSufEntries_ok (hw2 ex : BitVec 64) :
    ∀ e ∈ auxSufEntries hw2 ex, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64 := by
  intro e he; simp only [auxSufEntries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> (dsimp only; exact ⟨by decide, by decide⟩)

private theorem startProc_entails_argv0_and_auxv
    (sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex nullVal : BitVec 64)
    (a32 ah32 : BitVec 32) (secretBytes : List (BitVec 8))
    (hauxvHi : (envp + 8#64).toNat + 304 ≤ 2 ^ 48) (hrandHi : rnd.toNat + 16 ≤ 2 ^ 48)
    (hsecLen : secretBytes.length = 8) :
    (StartProc sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗
      ((envp + 304#64) ↦₆₄ nullVal) ∗ ((rnd + 8#64) ↦ₛ secretBytes)) ⊢
      ((sp + 8#64) ↦₆₄ p) ∗ MallocngAuxvAt (envp + 8#64) ∗ anyHeap := by
  let pre := auxPreEntries ph pg ab af ae uid uid gid gid plat hw clk 0#64
  let suf := auxSufEntries hw2 ex
  have hPure : (∀ e ∈ pre, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧ (∀ e ∈ suf, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
      pre.length + suf.length ≤ 64 ∧ (envp + 8#64).toNat + 16 * (pre.length + suf.length + 2) ≤ 2 ^ 48 ∧
      rnd.toNat + 16 ≤ 2 ^ 48 ∧ secretBytes.length = 8 :=
    ⟨auxPreEntries_ok ph pg ab af ae uid uid gid gid plat hw clk 0#64, auxSufEntries_ok hw2 ex,
      by simp [pre, suf, auxPreEntries, auxSufEntries],
      by simpa [pre, suf, auxPreEntries, auxSufEntries] using hauxvHi, hrandHi, hsecLen⟩
  have hAuxv : (((envp + 8#64) ↦₆₄*
        ((pre ++ [(25#64, rnd)] ++ suf ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) ∗
      ((rnd + 8#64) ↦ₛ secretBytes)) ⊢ MallocngAuxvAt (envp + 8#64) := by
    unfold MallocngAuxvAt
    refine Entails.trans ?_ (Entails.sepExists_intro pre)
    refine Entails.trans ?_ (Entails.sepExists_intro suf)
    refine Entails.trans ?_ (Entails.sepExists_intro rnd)
    refine Entails.trans ?_ (Entails.sepExists_intro nullVal)
    refine Entails.trans ?_ (Entails.sepExists_intro secretBytes)
    exact Entails.pure_right hPure (Entails.refl _)
  have hExpand : (StartProc sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗
        ((envp + 304#64) ↦₆₄ nullVal) ∗ ((rnd + 8#64) ↦ₛ secretBytes)) =
      (((sp + 8#64) ↦₆₄ p) ∗ (((envp + 8#64) ↦₆₄*
        ((pre ++ [(25#64, rnd)] ++ suf ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v])) ∗
        ((rnd + 8#64) ↦ₛ secretBytes)) ∗ ((sp ↦₃₂ a32) ∗ ((sp + 4#64) ↦₃₂ ah32) ∗ (envp ↦₆₄ 0#64))) := by
    unfold StartProc pre suf auxPreEntries auxSufEntries
    simp only [List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
    sep_ac_rfl
  rw [hExpand]; exact sepConj_mono_right (sepConj_mono hAuxv (entails_anyHeap _))

private theorem rearr_frame_rand {A P W D S1 S2 T X : SepProp} (h : P ∗ S1 ⊢ X) :
    A ∗ (P ∗ ((W ∗ (D ∗ S2)) ∗ (S1 ∗ T))) ⊢ A ∗ (X ∗ (W ∗ (S2 ∗ anyHeap))) := by
  have e : A ∗ (P ∗ ((W ∗ (D ∗ S2)) ∗ (S1 ∗ T))) = A ∗ ((P ∗ S1) ∗ (W ∗ (S2 ∗ (D ∗ T)))) := by
    sep_ac_rfl
  rw [e]; exact sepConj_mono_right
    (sepConj_mono h (sepConj_mono_right (sepConj_mono_right (entails_anyHeap _))))

/-- `frame_split` refined to retain the 8-byte `AT_RANDOM` secret slice explicitly. -/
theorem frame_split_rand (elf : ElfImage) (strs : List (List (BitVec 8))) (s0 : List (BitVec 8))
    (ss : List (List (BitVec 8))) (hs : strs = s0 :: ss)
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    (BitVec.ofNat 64 (sp0 strs) ↦ₛ frameBytes elf strs) ⊢
      (BitVec.ofNat 64 (sp0 strs) ↦₆₄ BitVec.ofNat 64 strs.length) ∗
        ((((BitVec.ofNat 64 (sp0 strs) + 8#64) ↦₆₄ argvBase strs) ∗
          (cStrAt (argvBase strs) s0 ∗ argvAt (BitVec.ofNat 64 (sp0 strs) + 8#64 + 8#64) ss)) ∗
        (((BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2))) ↦₆₄*
            auxWords elf strs) ∗
          (((BitVec.ofNat 64 (infoBase strs) + 8#64) ↦ₛ List.replicate 8 0#8) ∗ anyHeap))) := by
  have e1 : BitVec.ofNat 64 (argcBytes strs).length = 8#64 := rfl
  have hp : (ptrBytes strs).length = 8 * (strs.length + 1) := by
    unfold ptrBytes ptrWords
    simp only [flatMap_bytesLE_length, List.length_append, packAddrs_length, List.length_singleton]
  have hu : (unpackL (auxWords elf strs)).length = 8 * 39 := by rw [unpackL_length, auxWords_length]
  have hr : (restBytes elf strs).length = 8 * (39 + (strs.length + 41) % 2) := by
    unfold restBytes restWords
    simp only [flatMap_bytesLE_length, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  have hh : (headBytes strs).length = 16 + infoPadLen strs + 8 := by
    unfold headBytes; simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  have e2 : BitVec.ofNat 64 (sp0 strs) + 8#64 + BitVec.ofNat 64 (ptrBytes strs).length =
      BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2)) := by
    rw [hp, BitVec.add_assoc]; congr 1; simp only [BitVec.ofNat_add_ofNat]; congr 1; omega
  have e3 : BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2)) +
      BitVec.ofNat 64 (restBytes elf strs ++ headBytes strs).length = argvBase strs := by
    rw [List.length_append, hr, hh]; unfold argvBase platformAddr; simp only [BitVec.ofNat_add_ofNat]
    congr 1; have := top_eq; have := cliStackSize_eq; unfold sp0 infoBase tableWords at *; omega
  let padBytes := (List.replicate ((strs.length + 41) % 2) (0#64)).flatMap (Obj.bytesLE 8)
  have hpadLen : padBytes.length = 8 * ((strs.length + 41) % 2) := by
    dsimp [padBytes]; rw [flatMap_bytesLE_length, List.length_replicate]
  have eInfo : BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2)) +
        BitVec.ofNat 64 (unpackL (auxWords elf strs)).length + BitVec.ofNat 64 padBytes.length =
      BitVec.ofNat 64 (infoBase strs) := by
    rw [hu, hpadLen]; simp only [BitVec.ofNat_add_ofNat]; congr 1
    have := top_eq; have := cliStackSize_eq; have := le_alignUp16 (upperRawLen strs)
    unfold sp0 infoBase infoLen tableWords at *; omega
  have hheadSplit : headBytes strs = List.replicate 8 0#8 ++ (List.replicate 8 0#8 ++
      (List.replicate (infoPadLen strs) 0#8 ++ [0x61#8, 0x61#8, 0x72#8, 0x63#8, 0x68#8, 0x36#8, 0x34#8, 0x00#8])) := by
    unfold headBytes; rw [show (16 : Nat) = 8 + 8 from rfl, List.replicate_add]; simp only [List.append_assoc]
  have hrest : restBytes elf strs ++ headBytes strs = unpackL (auxWords elf strs) ++ (padBytes ++
      (List.replicate 8 0#8 ++ (List.replicate 8 0#8 ++ (List.replicate (infoPadLen strs) 0#8 ++
        [0x61#8, 0x61#8, 0x72#8, 0x63#8, 0x68#8, 0x36#8, 0x34#8, 0x00#8])))) := by
    unfold restBytes unpackL; rw [restWords_eq, List.flatMap_append, hheadSplit]; dsimp only [padBytes]
    simp only [List.append_assoc]; rfl
  have hPadHead : ((BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2)) +
          BitVec.ofNat 64 (unpackL (auxWords elf strs)).length) ↦ₛ
        (padBytes ++ (List.replicate 8 0#8 ++ (List.replicate 8 0#8 ++ (List.replicate (infoPadLen strs) 0#8 ++
          [0x61#8, 0x61#8, 0x72#8, 0x63#8, 0x68#8, 0x36#8, 0x34#8, 0x00#8]))))) ⊢
      anyHeap ∗ ((BitVec.ofNat 64 (infoBase strs) + 8#64) ↦ₛ List.replicate 8 0#8) := by
    rw [pointsToBytes_append, eInfo, pointsToBytes_append, pointsToBytes_append,
      show BitVec.ofNat 64 (List.replicate 8 0#8).length = 8#64 from rfl]
    have he : ∀ {P1 P2 P3 P4 : SepProp}, P1 ∗ (P2 ∗ (P3 ∗ P4)) = (P1 ∗ P2 ∗ P4) ∗ P3 := by
      intros; sep_ac_rfl
    rw [he]; exact sepConj_mono_left (entails_anyHeap _)
  unfold frameBytes
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    pointsToBytes_append _ (strBytes strs), e1, e2, e3, hrest, pointsToBytes_append, hu,
    ← pointsToWords64_eq_pointsToBytes, show argcBytes strs = unpack64 (BitVec.ofNat 64 strs.length) from rfl,
    ← pointsTo64_eq_pointsToBytes]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right hPadHead)))) ?_
  subst hs
  exact rearr_frame_rand (packed_cons (argvBase (s0 :: ss)) (BitVec.ofNat 64 (sp0 (s0 :: ss)) + 8#64) s0 ss)

private theorem runtime_intro (A : MallocngAddrs) (B envp : BitVec 64)
    (hlibc : A.libc = B + 0x21e8#64) :
    (((B + 0x20a4#64) ↦₃₂ 0#32) ∗ ((B + 0x21eb#64) ↦₈ 0#8) ∗ ((B + 0x21f0#64) ↦₆₄ (envp + 8#64)) ∗
     ((B + 0x2218#64) ↦₆₄ BitVec.ofNat 64 Obj.pageSize)) ⊢
    MallocngRuntime A (B + 0x2148#64) ∗ ((A.libc + 8#64) ↦₆₄ (envp + 8#64)) := by
  have htp_sub : (B + 0x2148#64) - 0xa4#64 = B + 0x20a4#64 := by rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have hl3 : A.libc + 3#64 = B + 0x21eb#64 := by rw [hlibc, BitVec.add_assoc]; rfl
  have hl8 : A.libc + 8#64 = B + 0x21f0#64 := by rw [hlibc, BitVec.add_assoc]; rfl
  have hl48 : A.libc + 48#64 = B + 0x2218#64 := by rw [hlibc, BitVec.add_assoc]; rfl
  unfold MallocngRuntime; rw [htp_sub, hl3, hl8, hl48, show BitVec.ofNat 64 Obj.pageSize = 4096#64 from rfl]
  have hassoc : (((B + 0x20a4#64) ↦₃₂ 0#32) ∗ ((B + 0x21eb#64) ↦₈ 0#8) ∗
        ((B + 0x21f0#64) ↦₆₄ (envp + 8#64)) ∗ ((B + 0x2218#64) ↦₆₄ 4096#64)) =
      ((((B + 0x20a4#64) ↦₃₂ 0#32) ∗ ((B + 0x21eb#64) ↦₈ 0#8) ∗
        ((B + 0x2218#64) ↦₆₄ 4096#64)) ∗ ((B + 0x21f0#64) ↦₆₄ (envp + 8#64))) := by sep_ac_rfl
  rw [hassoc]; exact sepConj_mono_left (sepConj_mono_left (Entails.sepExists_intro 0#32))

private theorem post_finish_fine {m : Memory}
    {SP A0 F1 F2 E0 E1 E2 E3 Mr L Ar Zl R S2 X P8 Auxv Rt Libc8 F1r F2r Garg Gstk Fini : SepProp}
    (hm : m ⊨ SP ∗ A0 ∗ F1 ∗ F2 ∗ E0 ∗ E1 ∗ E2 ∗ E3 ∗ Mr ∗ ((L ∗ Ar) ∗ (Zl ∗ (R ∗ (S2 ∗ X)))))
    (hSP : SP ∗ L ∗ S2 ⊢ P8 ∗ Auxv ∗ anyHeap) (hRt : E0 ∗ E1 ∗ E2 ∗ E3 ⊢ Rt ∗ Libc8)
    (hfz : F1 ∗ F2 ⊢ |==> (F1r ∗ F2r)) (hfini : F1r ∗ F2r ⊢ Fini)
    (harg : P8 ∗ A0 ∗ Ar ⊢ Garg) (hstk : Mr ∗ Zl ⊢ Gstk ∗ anyHeap) :
    m ⊨ (Garg ∗ Gstk ∗ (Rt ∗ Libc8 ∗ Auxv) ∗ R) ∗ Fini := by
  have e1 : SP ∗ A0 ∗ F1 ∗ F2 ∗ E0 ∗ E1 ∗ E2 ∗ E3 ∗ Mr ∗ ((L ∗ Ar) ∗ (Zl ∗ (R ∗ (S2 ∗ X)))) =
      (F1 ∗ F2) ∗ ((SP ∗ L ∗ S2) ∗ ((E0 ∗ E1 ∗ E2 ∗ E3) ∗ (A0 ∗ Ar ∗ (Mr ∗ Zl) ∗ R ∗ X))) := by sep_ac_rfl
  rw [e1] at hm
  have h3 := Satisfies.mono (sepConj_mono hfini (sepConj_mono hSP (sepConj_mono_left hRt)))
    (Satisfies.of_bupd_frame_left hfz hm)
  have e2 : Fini ∗ ((P8 ∗ Auxv ∗ anyHeap) ∗ ((Rt ∗ Libc8) ∗ (A0 ∗ Ar ∗ (Mr ∗ Zl) ∗ R ∗ X))) =
      ((((P8 ∗ A0 ∗ Ar) ∗ (Mr ∗ Zl)) ∗ ((Rt ∗ Libc8 ∗ Auxv) ∗ R)) ∗ Fini) ∗ (anyHeap ∗ X) := by sep_ac_rfl
  rw [e2] at h3
  have h4 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left (sepConj_mono harg hstk)))) h3
  have e3 : (((Garg ∗ (Gstk ∗ anyHeap)) ∗ ((Rt ∗ Libc8 ∗ Auxv) ∗ R)) ∗ Fini) ∗ (anyHeap ∗ X) =
      ((Garg ∗ Gstk ∗ (Rt ∗ Libc8 ∗ Auxv) ∗ R) ∗ Fini) ∗ (anyHeap ∗ anyHeap ∗ X) := by sep_ac_rfl
  rw [e3] at h4; exact sat_of_entails_frame h4 (Entails.refl _)

set_option maxHeartbeats 3200000 in
/-- Complete `musl` `_start → main` startup over any program `P` (`P.svc = Syscall.standard`,
hook-free on `[elf.entry, elf.entry + 0xb90)`), establishing `MuslStartupVmPreserved s0 sm`,
`sm.tpidrEl0 = muslTpOf elf`, and `MallocngRuntime` + `MallocngAuxvAt` alongside `argvAt`,
`stackAt`, caller frame `R`, and `muslFiniFr elf.entry`. -/
theorem musl_startup_fineInit_ofProg {P : Program} {elf : ElfImage} {code : List (BitVec 8)}
    {A : MallocngAddrs} {dynPageImm pageImm : BitVec 64} {addImm : BitVec 12}
    (hsvcP : P.svc = Syscall.standard)
    (hnoHook : ∀ k : BitVec 64, k.toNat < 0xb90 → P.externAt? (elf.entry + k) = none)
    (hC : CliElfMusl elf code) (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hlibc : A.libc = elf.entry + 0x21e8#64)
    (hf : MuslStartFetchAt ({ code } : Program) 0#64 dynPageImm pageImm addImm)
    (argv : List String) (stdin : List (BitVec 8)) (files : List (String × List (BitVec 8)))
    (dirs : List String)
    (hargs : ∀ a ∈ argv, ∀ c ∈ a.toList, 0 < c.toNat ∧ c.toNat < 128)
    (hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ cliArgBudget)
    (hdirs : ∀ d ∈ dirs, Arm64.hasLeadingSlash d = false ∧ Arm64.hasDotDot d = false)
    (hfiles : ∀ f ∈ files,
      (Arm64.hasLeadingSlash f.1 = false ∧ Arm64.hasDotDot f.1 = false) ∧
        f.2.length ≤ Arm64.MAX_LFS_FILESIZE)
    (stk : Nat) (hstk : stk ≤ cliStackBudget) {R : SepProp} {S : Nat → Prop}
    (hR : ∀ s0, elf.loadState (processInputs ("libsignal-cli" :: argv) stdin files dirs) = .ok s0 →
      SupportedOn 0#64 S s0.mem R)
    (hS : ∀ k, S k → k < stackBase ∧
      ¬((elf.entry + 0x2000#64).toNat ≤ k ∧ k < (elf.entry + 0x2000#64).toNat + 600)) :
    ∃ s0 sm auxvPtr,
      elf.loadState (processInputs ("libsignal-cli" :: argv) stdin files dirs) = .ok s0 ∧
      Steps P s0 sm ∧ sm.pc = mainPcOf elf.entry pageImm addImm ∧ sm.status = .Running ∧
      sm.spAligned = true ∧ sm.sp = s0.sp - 48#64 ∧
      (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (argv.length + 1) ∧
      sm.readReg64 .x1 = s0.sp + 8#64 ∧ sm.readReg64 .lr = elf.entry + 0x854#64 ∧
      sm.fs = s0.fs ∧ sm.trace = s0.trace ∧ sm.tpidrEl0 = muslTpOf elf ∧
      0xa4 ≤ sm.tpidrEl0.toNat ∧ sm.tpidrEl0.toNat ≤ 2 ^ 48 ∧
      MuslStartupVmPreserved s0 sm ∧
      (sm.mem ⊨
        (argvAt (sm.readReg64 .x1) (cliStrs argv) ∗ stackAt sm.sp stk ∗
          (MallocngRuntime A sm.tpidrEl0 ∗ ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
            MallocngAuxvAt auxvPtr) ∗ R) ∗
        muslFiniFr elf.entry) ∧
      stk ≤ sm.sp.toNat := by
  replace hstk : stk ≤ 8371776 := stackBudget_le hstk
  replace hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ 16384 := hfits
  obtain ⟨hload, hsp0, hal16, hlo, hlen, hfr, hzero, -⟩ :=
    loadState_cli_layout elf argv stdin files dirs hwf hbrk hargs hfits hdirs hfiles
  generalize elf.rawState (processInputs ("libsignal-cli" :: argv) stdin files dirs) = s0
    at hload hsp0 hfr hzero
  obtain ⟨hpc0, hrun0, -, -⟩ := loadState_fields hload
  obtain ⟨hfit, -, -⟩ := cli_bounds argv hfits
  have hphent := wf_phent elf hwf
  have heb := entry_bound elf hwf hbrk
  have hsb := stackBase_eq; have htop := top_eq; have hcsz := cliStackSize_eq
  have hspn := toNat_sp0 (cliStrs argv)
  have hk : (cliStrs argv).length < 2 ^ 31 := by
    have := argv_length_le argv hfits; rw [cliStrs_length]; omega
  obtain ⟨h0, g3, g4, ia, F, hh0, hrw⟩ := hC.rw
  have hML : (unpackL (muslRwWords h0 g3 g4 ia F)).length = 600 := by rw [unpackL_length]; rfl
  have hne : unpackL (muslRwWords h0 g3 g4 ia F) ≠ [] := by
    intro h; have := congrArg List.length h; rw [hML] at this; simp at this
  have hMb := hrw.bound hne hwf hbrk; rw [hML] at hMb
  have hFs := supportedOn_of_holdsBytes_rw (by rw [hspn]; omega) hfr
  have hZb : Obj.HoldsBytes s0.mem (BitVec.ofNat 64 stackBase)
      (List.replicate (sp0 (cliStrs argv) - stackBase - 480 + 480) 0#8) (fun _ => .rw) := by
    apply holdsBytes_zero; intro i hi
    have hi' : i < sp0 (cliStrs argv) - stackBase - 480 + 480 := hi
    have e := toNat_ofNat_add stackBase i (by omega)
    exact hzero _ (by rw [e]; exact Nat.le_add_right _ _) (by rw [e]; clear e; omega)
  have hZs := supportedOn_of_holdsBytes_rw (by rw [toNat_stackBase, List.length_replicate]; omega) hZb
  have hMs := supportedOn_of_holdsBytes_rw (by omega) (hrw.holdsBytes hwf hbrk hload)
  rw [← pointsToWords64_eq_pointsToBytes] at hMs
  have hMR := hMs.sepConj (hR s0 hload) (fun k ⟨h1a, h1b⟩ h2 => (hS k h2).2 ⟨h1a, by omega⟩)
  have hZMR := hZs.sepConj hMR fun k ⟨h1a, h1b⟩ h2 => by
    simp only [toNat_stackBase, List.length_replicate] at h1a h1b
    rcases h2 with ⟨h2a, h2b⟩ | h2
    · omega
    · have := (hS k h2).1; omega
  have hall := hFs.sepConj hZMR fun k ⟨h1a, h1b⟩ h2 => by
    rw [hspn] at h1a h1b
    rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | h2
    · simp only [toNat_stackBase, List.length_replicate] at h2a h2b; omega
    · omega
    · have := (hS k h2).1; omega
  have hzsp : s0.sp = BitVec.ofNat 64 stackBase +
      BitVec.ofNat 64 (sp0 (cliStrs argv) - stackBase - 480 + 480) := by
    rw [hsp0, BitVec.ofNat_add_ofNat]; exact congrArg (BitVec.ofNat 64) (sub_add_eq' _ _ hlo)
  have hsat2 := Satisfies.mono (sepConj_mono
    (frame_split_rand elf (cliStrs argv) (bytesOfString "libsignal-cli")
      (argv.map bytesOfString) rfl hfit)
    (sepConj_mono_left (zeros_split s0.sp _ _ hzsp))) hall.satisfies
  rw [← hsp0] at hsat2
  let envp := s0.sp + BitVec.ofNat 64 (8 * ((cliStrs argv).length + 2))
  have hpre := pre_assemble hsat2
    (startProc_eq elf (cliStrs argv) s0.sp envp
      (BitVec.ofNat 64 (cliStrs argv).length) hphent hC.phnum)
    (cStr_eq _) (fun Q hQ => sat_startPhdrs hC.phdrs hwf hbrk hload hQ)
  obtain ⟨sm, hsteps, hpc', hrun', hvm, hregs, hpost⟩ := musl_start_fine_block_ofProg
    hsvcP hnoHook hf hC.entry_page (codeLoaded_of_text hC hwf hbrk hload) hpc0 hrun0
    (al_of_mod _ (by rw [hsp0, hspn]; exact hal16)) (and_neg16 _ (by rw [hsp0, hspn]; exact hal16))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (envp_eq s0.sp (cliStrs argv).length hk).symm
    (argvBase_ne argv hfits) hC.phdr_ne h0 g3 g4 ia F hh0 hpre
  obtain ⟨⟨hsp', hx0, hx1, -, hlr, hfs, htr⟩, htp⟩ := hregs
  have htp_nat : (elf.entry + 0x2148#64).toNat = elf.entry.toNat + 0x2148 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have htpLo : 0xa4 ≤ sm.tpidrEl0.toNat := by rw [htp, htp_nat]; omega
  have htpHi : sm.tpidrEl0.toNat ≤ 2 ^ 48 := by rw [htp, htp_nat]; omega
  have hle_align := le_alignUp16 (upperRawLen (cliStrs argv))
  have hrandHi : (BitVec.ofNat 64 (infoBase (cliStrs argv))).toNat + 16 ≤ 2 ^ 48 := by
    have hibLt : infoBase (cliStrs argv) < 2 ^ 64 := by unfold infoBase infoLen at *; omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hibLt]; unfold infoBase infoLen at *; omega
  have hauxvHi : (envp + 8#64).toNat + 304 ≤ 2 ^ 48 := by
    have hev : envp + 8#64 = BitVec.ofNat 64 (sp0 (cliStrs argv) + 8 * ((cliStrs argv).length + 2) + 8) := by
      dsimp [envp]; rw [hsp0]; simp only [BitVec.ofNat_add_ofNat]
    rw [hev, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold sp0 infoBase infoLen tableWords at *; omega)]
    unfold sp0 infoBase infoLen tableWords at *; omega
  refine ⟨s0, sm, envp + 8#64, hload, hsteps, hpc', hrun', ?_, hsp', ?_, hx1, hlr, hfs, htr,
    htp, htpLo, htpHi, hvm, ?_, ?_⟩
  · unfold State.spAligned; rw [hsp']
    exact spAligned_sub48 _ (al_of_mod _ (by rw [hsp0, hspn]; exact hal16))
  · rw [hx0, cliStrs_length]; exact x0_eq _
  · rw [hx1, hsp', htp]
    exact post_finish_fine hpost
      (startProc_entails_argv0_and_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (List.replicate 8 0#8) hauxvHi hrandHi (by simp))
      (runtime_intro A elf.entry envp hlibc)
      (bupd_sep (pointsTo64_freeze_ro _ _) (pointsTo64_freeze_ro _ _))
      (fini_intro _ _) (argvAt_cli _ _ _)
      (stack_rebuild s0.sp (BitVec.ofNat 64 stackBase) (sp0 (cliStrs argv) - stackBase - 480) stk
        (by rw [hsp0, hspn, toNat_stackBase]; omega) (by omega))
  · rw [hsp', hsp0]; have := sp0_le_top (cliStrs argv)
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

end LibsignalBinary.Proofs.SignalSession.Cli.M24.MuslStartFineResources
