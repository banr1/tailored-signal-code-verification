/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ProgramReflection
public import ProofLib.Process.FastParse
public import VerifiedLibraries.Musl.Proofs.MemOps
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.RustStd.Proofs.MallocngBridge
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.Fine.AllocZeroedHelpersFine
public import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TlsZero
public import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.CliPlacement
public meta import ProofLib.ProgramReflection
public meta import ProofLib.StdStartup.Layout
public meta import LibsignalBinary.Heap.Fine.F3LayoutData
public meta import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture

/-!
# Stock `ld.lld` CLI `WordTree`, Shim, and `memcpy`/`memset` Kernel-Tie on `f3TrialElf`

**Checked by Lean. Untrusted (`Role::Proof`, WP3).**

Certifies `f3MatchesImage`, `ProgContainsMallocng f3TrialRxProg f3MallocngMpl`, the 103-instruction
`F3Seg5ShimBundle` (`stock/rdl_shim.S` body/marker in `seg[2]`), checked 1-hop `Instr.b` stub thunks at
`f3StubAddrs.{alloc,dealloc,realloc}` and `f3StubAzAddr` (`< e_entry`), `allocMemcpyVmSpec` and
`allocMemsetVmSpec` on `f3TrialRxProg`, and `KeepsFrozen`-stable `b __rdl_*` execution witnesses
(`f3Trial_keepsFrozen_stub_at` bundle, zero `GeneratedLean.LibsignalSessionObj` dependency).
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries.Musl (memsetWords)
open VerifiedLibraries.Mallocng.Proofs (
  ProgContainsMultiLib ProgContainsMallocng memcpySymWords
)
open VerifiedLibraries.RustStd (
  mallocngPlacedCAddrs RustStdThunkCode checkRustStdThunkCode rustStdThunkCode_of_wordTree
)
open LibsignalBinary.Heap (
  allocMemcpyVmSpec allocMemcpyVm_ok_of_wordTree
)
open LibsignalBinary.Heap.Fine (
  f3SegCount f3RxWordCount f3BrkStart f3StdLayout f3MallocngMpl
  f3StubAddrs f3RdlAddrs f3StubAzAddr f3RdlAzAddr f3StubNoShimAddr f3NoShimV2Addr
  allocMemsetVmSpec allocMemsetVm_ok_of_wordTree
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TlsZero (
  f3MatchesImage f3MatchesImage_codeLoaded
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec (
  F3Seg5ShimBundle checkF3Seg5ShimBundle f3Seg5ShimBundle_of_wordTree
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture (
  f3TrialElf
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.CliPlacement (
  mallocngLib_in_f3TrialElf
)

set_option maxRecDepth 4000000

/-! ## `f3TrialRxProg` (`seg[2]`) and `WordTree` Reflection -/

/-- Page-aligned base address of `rxSeg` (`seg[2]`, `0x469000` on stock `StdBin`, where `.text.b_pre`
    precedes `e_entry = 0x46a000`). -/
abbrev f3RxSegBase : BitVec 64 :=
  LibsignalBinary.Heap.Fine.f3RxSegBase

/-- Base address of `:text_a` (`seg[1]`, `0x40a000` on stock `StdBin`). -/
def f3ImgTextBase : BitVec 64 :=
  0x40a000#64

/-- Hook-free `Syscall.standard` `Program` backed by `f3TrialElf`'s `rxSeg` (`seg[2]`). -/
noncomputable def f3TrialRxProg : Program :=
  f3StdLayout.rxProgram f3TrialElf

/-- Balanced `WordTree` reflected from `f3TrialRxProg`. -/
def f3TrialRxWordTree : WordTree :=
  word_tree_of% f3TrialRxProg

theorem f3TrialRxWordTree_eq :
    f3TrialRxProg.code = f3TrialRxWordTree.toBytes := by
  rfl_kernel

theorem f3TrialRxWordTree_size :
    f3TrialRxWordTree.checkSize? = some f3RxWordCount := by
  rfl_kernel

theorem f3TrialRxProg_base :
    f3TrialRxProg.base = f3RxSegBase := by
  rfl_kernel

theorem f3TrialRxProg_svc :
    f3TrialRxProg.svc = Syscall.standard := by
  unfold f3TrialRxProg StdBinaryLayout.rxProgram; split <;> rfl

theorem f3TrialRxProg_no_ext (pc : BitVec 64) :
    f3TrialRxProg.externAt? pc = none := by
  unfold f3TrialRxProg StdBinaryLayout.rxProgram; split <;> rfl

theorem f3TrialRxProg_externs_none (sym : String) :
    (f3TrialRxProg.externs sym).isNone = true := by
  unfold f3TrialRxProg StdBinaryLayout.rxProgram; split <;> rfl

theorem f3TrialRxProg_overrides_none (sym : String) :
    (f3TrialRxProg.overrides sym).isNone = true := by
  unfold f3TrialRxProg StdBinaryLayout.rxProgram; split <;> rfl

theorem f3TrialRxProg_stubs :
    f3TrialRxProg.stubs = [] := by
  unfold f3TrialRxProg StdBinaryLayout.rxProgram; split <;> rfl

theorem f3TrialRxProg_symbols :
    f3TrialRxProg.symbols = [] := by
  unfold f3TrialRxProg StdBinaryLayout.rxProgram; split <;> rfl

/-! ## Layout, `mallocngLib`, Shim Bundle, and `memcpy`/`memset` Certificates -/

theorem f3Trial_matchesImage :
    f3MatchesImage f3StdLayout f3TrialElf = true := by
  rfl_kernel

private def checkMallocngInRx (L : StdBinaryLayout)
    (mpl : Obj.MultiPlacement) (img : ElfImage) : Bool :=
  match img.segments[L.rxSegIdx]? with
  | none => false
  | some rxSeg =>
    withForcedNat (fastLen512 4096 rxSeg.bytes) fun rxLen =>
      (img.segments.take L.rxSegIdx).all
        (fun q => decide (q.start.toNat + fastLen512 4096 q.bytes ≤ rxSeg.start.toNat)) &&
      decide (rxSeg.start.toNat + rxLen ≤ 2 ^ 64) &&
      (List.range VerifiedLibraries.mallocngLib.blocks.length).all
        (fun i =>
          (mpl.base i).toNat % 4 == 0 &&
          decide (rxSeg.start.toNat ≤ (mpl.base i).toNat) &&
          decide ((mpl.base i).toNat +
            (VerifiedLibraries.mallocngLib.blocks[i]?.map (fun b => fastLen512 4096 b.code)).getD 0 ≤
            rxSeg.start.toNat + rxLen))

private theorem progContainsMallocng_of_inElf {L : StdBinaryLayout}
    {mpl : Obj.MultiPlacement} {img : ElfImage}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mpl)
    (hin : VerifiedLibraries.mallocngLib.InElf img mpl)
    (hok : checkMallocngInRx L mpl img = true) :
    ProgContainsMallocng (L.rxProgram img) mpl := by
  unfold checkMallocngInRx at hok
  split at hok <;> try contradiction
  rename_i rxSeg hrxSeg
  simp only [withForcedNat_eq, fastLen512_eq_length, Bool.and_eq_true,
    decide_eq_true_eq] at hok
  obtain ⟨⟨hpre, hwrap⟩, hblks⟩ := hok
  have hrx_lt : L.rxSegIdx < img.segments.length := by
    apply Classical.byContradiction
    intro hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hrxSeg
    contradiction
  have hrx_eq : img.segments[L.rxSegIdx] = rxSeg := by
    rw [List.getElem?_eq_getElem hrx_lt] at hrxSeg
    exact Option.some.inj hrxSeg
  have hsplit : img.segments =
      img.segments.take L.rxSegIdx ++ rxSeg :: img.segments.drop (L.rxSegIdx + 1) := by
    rw [← hrx_eq, List.getElem_cons_drop, List.take_append_drop]
  have hpre' : (img.segments.take L.rxSegIdx).all (Snapshot.Below rxSeg.start) = true := by
    rw [List.all_eq_true] at hpre ⊢
    intro q hq
    simpa [Snapshot.Below, decide_eq_true_eq] using hpre q hq
  refine ProgContainsMultiLib.of_noExterns hpl (StdBinaryLayout.rxProgram_svc L img)
    (fun m hPm i hi => ?_)
    (fun pc => congrFun (StdBinaryLayout.rxProgram_externAt? L img) pc)
  have hP_eq : L.rxProgram img =
      { base := rxSeg.start, code := rxSeg.bytes, svc := Syscall.standard } := by
    simp [StdBinaryLayout.rxProgram, hrxSeg]
  rw [hP_eq] at hPm
  rw [Program.codeLoaded_iff] at hPm ⊢
  obtain ⟨_, _, hP_bytes⟩ := hPm
  have hbi := List.all_eq_true.mp hblks i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some] at hbi
  rcases hbi with ⟨⟨hal_i, hle_i⟩, hfit_i⟩
  have hbase_eq : (VerifiedLibraries.mallocngLib.blockProgram mpl i).base = mpl.base i := rfl
  have hcode_eq : (VerifiedLibraries.mallocngLib.blockProgram mpl i).code =
      VerifiedLibraries.mallocngLib.blocks[i].patched (VerifiedLibraries.mallocngLib.blockPlacement mpl i) := by
    simp [MultiPlacedLib.blockProgram, PlacedLib.program, VerifiedLibraries.mallocngLib.blockLib_text hi]
  have hlen_i : (VerifiedLibraries.mallocngLib.blockProgram mpl i).code.length =
      VerifiedLibraries.mallocngLib.blocks[i].code.length := by
    rw [hcode_eq]
    exact CodeBlock.length_patched_of_aligned _ (hpl.blocks_ok i hi).len_aligned
  refine ⟨by rw [hbase_eq]; exact hal_i, by rw [hbase_eq, hlen_i]; omega, fun k hk => ?_⟩
  let idx := ((mpl.base i).toNat - rxSeg.start.toNat) + k
  have hidx_lt : idx < rxSeg.bytes.length := by rw [hlen_i] at hk; omega
  have hk_pat : k < (VerifiedLibraries.mallocngLib.blocks[i].patched
      (VerifiedLibraries.mallocngLib.blockPlacement mpl i)).length := by rwa [← hcode_eq]
  obtain ⟨p, hcell1, _⟩ := hin.blocks i hi k hk_pat
  have haddr_eq : rxSeg.start + BitVec.ofNat 64 idx = mpl.base i + BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : idx < 2 ^ 64 := by omega
    have : k < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt ‹idx < 2 ^ 64›, Nat.mod_eq_of_lt ‹k < 2 ^ 64›,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hcell2 : Snapshot.cellAt img.segments (rxSeg.start + BitVec.ofNat 64 idx) =
      some (some rxSeg.perm, rxSeg.bytes[idx]) := by
    rw [hsplit]
    exact Snapshot.cellAt_of_split hpre' hidx_lt hwrap
  rw [← haddr_eq, hcell2, Option.some.injEq, Prod.mk.injEq] at hcell1
  obtain ⟨hrd, hperm⟩ := hP_bytes idx hidx_lt
  rw [hbase_eq, ← haddr_eq]
  have hbyte_eq : (VerifiedLibraries.mallocngLib.blockProgram mpl i).code[k] = rxSeg.bytes[idx] := by
    simp only [hcode_eq]
    exact hcell1.2.symm
  exact ⟨hrd.trans hbyte_eq.symm, hperm⟩

private theorem f3Trial_mallocngInRx_chk :
    checkMallocngInRx f3StdLayout f3MallocngMpl f3TrialElf = true := by
  rfl_kernel

theorem f3Trial_progContainsMallocng :
    ProgContainsMallocng f3TrialRxProg f3MallocngMpl :=
  progContainsMallocng_of_inElf mallocngLib_in_f3TrialElf.1 mallocngLib_in_f3TrialElf.2.1
    f3Trial_mallocngInRx_chk

private theorem f3Trial_seg5ShimBundle_chk :
    checkF3Seg5ShimBundle f3RxSegBase f3TrialRxWordTree
      f3RdlAddrs f3RdlAzAddr f3NoShimV2Addr
      (mallocngPlacedCAddrs f3MallocngMpl)
      (VerifiedLibraries.mallocngLib.fnAddr f3MallocngMpl "calloc")
      f3StdLayout.memcpyAddr f3StdLayout.memsetAddr = true := by
  rfl_kernel

/-- `F3Seg5ShimBundle` covering all 103 instructions of `stock/rdl_shim.S` in `seg[2]` (`rxSeg`). -/
theorem f3Trial_seg5ShimBundle :
    F3Seg5ShimBundle f3TrialRxProg
      f3RdlAddrs f3RdlAzAddr f3NoShimV2Addr
      (mallocngPlacedCAddrs f3MallocngMpl)
      (VerifiedLibraries.mallocngLib.fnAddr f3MallocngMpl "calloc")
      f3StdLayout.memcpyAddr f3StdLayout.memsetAddr :=
  f3Seg5ShimBundle_of_wordTree f3RxWordCount
    f3TrialRxWordTree_eq f3TrialRxWordTree_size
    f3TrialRxProg_externs_none f3TrialRxProg_overrides_none
    (by rw [f3TrialRxProg_base]; exact f3Trial_seg5ShimBundle_chk)

private theorem memcpySymWords_len_le : memcpySymWords.length ≤ 1024 :=
  Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memcpySymWords.length 1024 = true)

private theorem f3Trial_memcpy_chk :
    checkWordsAt f3TrialRxWordTree
      (f3StdLayout.memcpyAddr - f3RxSegBase).toNat memcpySymWords = true := by
  rfl_kernel

theorem f3Trial_allocMemcpyVm_ok :
    subroutine_ok f3TrialRxProg f3StdLayout.memcpyAddr allocMemcpyVmSpec := by
  have hoff_lt : (f3StdLayout.memcpyAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen := memcpySymWords_len_le
  exact allocMemcpyVm_ok_of_wordTree f3RxWordCount
    f3TrialRxWordTree_eq f3TrialRxWordTree_size f3TrialRxProg_no_ext
    (by rw [f3TrialRxProg_base]) (by omega)
    f3TrialRxProg_stubs f3TrialRxProg_symbols f3Trial_memcpy_chk

private theorem memsetWords_len_le : memsetWords.length ≤ 1024 :=
  Nat.le_of_ble_eq_true (by rfl_kernel : Nat.ble memsetWords.length 1024 = true)

private theorem f3Trial_memset_chk :
    checkWordsAt f3TrialRxWordTree
      (f3StdLayout.memsetAddr - f3RxSegBase).toNat memsetWords = true := by
  rfl_kernel

theorem f3Trial_allocMemsetVm_ok :
    subroutine_ok f3TrialRxProg f3StdLayout.memsetAddr allocMemsetVmSpec := by
  have hoff_lt : (f3StdLayout.memsetAddr - f3RxSegBase).toNat < 2 ^ 32 := by decide
  have hlen := memsetWords_len_le
  exact allocMemsetVm_ok_of_wordTree f3RxWordCount
    f3TrialRxWordTree_eq f3TrialRxWordTree_size f3TrialRxProg_no_ext
    (by rw [f3TrialRxProg_base]) (by omega)
    f3TrialRxProg_stubs f3TrialRxProg_symbols f3Trial_memset_chk

/-! ## `stock/rdl_shim.S` `Instr.b` Thunks (`< e_entry` in `seg[2]`) and `KeepsFrozen` Witnesses -/

private theorem f3Trial_rustStdThunkCode_chk :
    checkRustStdThunkCode f3RxSegBase f3TrialRxWordTree
      f3StubAddrs.toRustStd f3RdlAddrs.toRustStd = true := by
  rfl_kernel

/-- Kernel-checked `RustStdThunkCode` for `___rust_{alloc,dealloc,realloc}` in `seg[2]`. -/
theorem f3Trial_rustStdThunkCode :
    RustStdThunkCode f3TrialRxProg f3StubAddrs.toRustStd f3RdlAddrs.toRustStd :=
  rustStdThunkCode_of_wordTree f3RxWordCount
    f3TrialRxWordTree_eq f3TrialRxWordTree_size
    f3TrialRxProg_externs_none f3TrialRxProg_overrides_none
    (by rw [f3TrialRxProg_base]; exact f3Trial_rustStdThunkCode_chk)

private theorem f3Trial_stubAz_chk :
    checkInstrsAt f3TrialRxWordTree (f3StubAzAddr - f3RxSegBase).toNat
      [ .b (f3RdlAzAddr - f3StubAzAddr) ] = true := by
  rfl_kernel

/-- Kernel-checked 1-hop `Instr.b` thunk at `f3StubAzAddr` (`___rust_alloc_zeroed`) in `seg[2]`. -/
theorem f3Trial_stubAz_hasInstrs :
    hasInstrs f3TrialRxProg f3StubAzAddr [ .b (f3RdlAzAddr - f3StubAzAddr) ] :=
  hasInstrs_of_wordTree f3RxWordCount
    f3TrialRxWordTree_eq f3TrialRxWordTree_size
    (by rw [f3TrialRxProg_base]; decide)
    (by decide)
    f3TrialRxProg_externs_none f3TrialRxProg_overrides_none
    f3Trial_stubAz_chk

/-- `rxSeg` (`seg[2]`) `(byteOff, target)` table for the 4 `stock/rdl_shim.S` 1-hop `Instr.b` thunks. -/
def f3BranchStubTargets : List (Nat × BitVec 64) :=
  [ ((f3StubAddrs.alloc - f3RxSegBase).toNat, f3RdlAddrs.alloc),
    ((f3StubAddrs.dealloc - f3RxSegBase).toNat, f3RdlAddrs.dealloc),
    ((f3StubAddrs.realloc - f3RxSegBase).toNat, f3RdlAddrs.realloc),
    ((f3StubAzAddr - f3RxSegBase).toNat, f3RdlAzAddr) ]

theorem f3StubAlloc_mem_targets :
    ((f3StubAddrs.alloc - f3RxSegBase).toNat, f3RdlAddrs.alloc) ∈ f3BranchStubTargets := by
  decide

theorem f3StubDealloc_mem_targets :
    ((f3StubAddrs.dealloc - f3RxSegBase).toNat, f3RdlAddrs.dealloc) ∈ f3BranchStubTargets := by
  decide

theorem f3StubRealloc_mem_targets :
    ((f3StubAddrs.realloc - f3RxSegBase).toNat, f3RdlAddrs.realloc) ∈ f3BranchStubTargets := by
  decide

theorem f3StubAz_mem_targets :
    ((f3StubAzAddr - f3RxSegBase).toNat, f3RdlAzAddr) ∈ f3BranchStubTargets := by
  decide

theorem f3StubAlloc_addr_eq :
    f3RxSegBase + BitVec.ofNat 64 (f3StubAddrs.alloc - f3RxSegBase).toNat =
      f3StubAddrs.alloc := by
  decide

theorem f3StubDealloc_addr_eq :
    f3RxSegBase + BitVec.ofNat 64 (f3StubAddrs.dealloc - f3RxSegBase).toNat =
      f3StubAddrs.dealloc := by
  decide

theorem f3StubRealloc_addr_eq :
    f3RxSegBase + BitVec.ofNat 64 (f3StubAddrs.realloc - f3RxSegBase).toNat =
      f3StubAddrs.realloc := by
  decide

theorem f3StubAz_addr_eq :
    f3RxSegBase + BitVec.ofNat 64 (f3StubAzAddr - f3RxSegBase).toNat =
      f3StubAzAddr := by
  decide

private theorem f3BranchStubTargets_chk :
    (f3BranchStubTargets.all fun (off, tgt) =>
      let stubAddr := f3RxSegBase + BitVec.ofNat 64 off
      decide (off + 4 < 2 ^ 64) &&
        checkInstrsAt f3TrialRxWordTree off [ .b (tgt - stubAddr) ]) = true := by
  rfl_kernel

/-- Any memory `m` satisfying `sLoad.mem.KeepsFrozen m` preserves 4-byte alignment, `canExec`, and
`Instr.b` decoding at every `(off, tgt) ∈ f3BranchStubTargets`. -/
theorem f3Trial_keepsFrozen_stub_at {inputs : ProcessInputs} {sLoad : State} {m : Memory}
    (hsLoad : f3TrialElf.loadState inputs = .ok sLoad)
    (hkf : sLoad.mem.KeepsFrozen m)
    {off : Nat} {tgt stubAddr : BitVec 64}
    (hmem : (off, tgt) ∈ f3BranchStubTargets)
    (haddr : f3RxSegBase + BitVec.ofNat 64 off = stubAddr) :
    stubAddr.toNat % 4 = 0 ∧
    m.canExec stubAddr 4 = true ∧
    Arm64.decode (m.read32 stubAddr) = some (.b (tgt - stubAddr)) := by
  subst haddr
  let pc := f3RxSegBase + BitVec.ofNat 64 off
  have hrow := List.all_eq_true.mp f3BranchStubTargets_chk (off, tgt) hmem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  have hhi : hasInstrs f3TrialRxProg pc [ .b (tgt - pc) ] :=
    hasInstrs_of_wordTree f3RxWordCount
      f3TrialRxWordTree_eq f3TrialRxWordTree_size
      (by rw [f3TrialRxProg_base])
      (by simpa only [List.length_singleton, Nat.mul_one] using hrow.1)
      f3TrialRxProg_externs_none f3TrialRxProg_overrides_none
      hrow.2
  have hf : f3TrialRxProg.fetch pc = some (.b (tgt - pc)) := by
    simpa [pc] using hhi 0 Nat.zero_lt_one
  have hcl0 : f3TrialRxProg.CodeLoaded sLoad.mem :=
    f3MatchesImage_codeLoaded f3Trial_matchesImage hsLoad
  have hcl : f3TrialRxProg.CodeLoaded m := hcl0.of_keepsFrozen hkf
  have hfm : f3TrialRxProg.fetchMem m pc = some (.b (tgt - pc)) :=
    Program.fetchMem_of_fetch hcl hf
  unfold Program.fetchMem at hfm
  rw [f3TrialRxProg_no_ext pc] at hfm
  dsimp only [Option.isSome] at hfm
  by_cases hal : pc.toNat % 4 = 0
  · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfm
    cases hex : m.canExec pc 4 with
    | false => rw [hex] at hfm; simp at hfm
    | true =>
      rw [hex] at hfm
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfm
      exact ⟨hal, rfl, hfm⟩
  · simp only [hal, ne_eq, not_false_eq_true, ↓reduceIte] at hfm
    cases hfm

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
