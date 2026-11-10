/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.StdStartup.StackInit
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.MuslTls
public import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Minimal `StdBinaryLayout` Projection and `PT_TLS` `0/0/0/0` Static TLS

Layout-parametric `StdBinaryLayout` validator (`f3MatchesImage`) and `PT_TLS` `0/0/0/0`
(`p_vaddr = 0`, `p_filesz = 0`, `p_memsz = 0`, `p_align = 0`) static TLS contracts (`f3CopyTlsSpec`,
`f3StaticInitTlsSpec`) for the static `musl` CLI binary with `main` in `.img.text` (`segments[1]`)
and `musl` startup/exit, `RUST_LSE_INIT`, `mallocng`, and `rdl_shim` in `rxSeg` (`segments[5]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TlsZero

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup

/-! ## Minimal `StdBinaryLayout` Projection and `ElfImage` Validator -/

/-- The 29 `rxSeg` code entrypoints executed by F3 `musl` startup, `RUST_LSE_INIT`, and `exit`
    (`L.cMainAddr` lives in `.img.text`, not `rxSeg`, so its 4-byte alignment is checked separately). -/
def f3CodeAddrs (L : StdBinaryLayout) : List (BitVec 64) :=
  [ L.startAddr, L.startCAddr, L.libcStartMainAddr, L.initLibcAddr, L.memsetAddr,
    L.staticInitTlsAddr, L.copyTlsAddr, L.memcpyAddr, L.initTpAddr, L.setThreadAreaAddr,
    L.dummy1Addr, L.libcStartMainStage2Addr, L.libcStartInitAddr, L.initFnAddr, L.initLseAddr,
    L.detectAndInitializeAddr, L.getauxvalAddr, L.rustEnableLseAddr, L.doInitAddr, L.exitAddr,
    L.dummyExitAddr, L.libcExitFiniAddr, L.doFiniAddr, L.finiFnAddr, L.stdioExitNeededAddr,
    L.oflLockFnAddr, L.lockFnAddr, L.closeFileAddr, L.sysExitAddr ]

/-- Initial `.data` atoms excluding `stderr` and unused `std::rt` `STDOUT`/`CLEANUP` globals. -/
def f3DataNoStderrAtoms (L : StdBinaryLayout) : List RwAtom :=
  [ .u32 L.defaultStacksizeAddr 0x20000#32, .u64 L.stderrUsedAddr L.stderrFileAddr ]

/-- Initial `.bss` atoms excluding unused `std::rt` `ARGC`/`ARGV`/`PAGE_SIZE`/`THREAD_ID` globals. -/
def f3BssAtoms (L : StdBinaryLayout) : List RwAtom :=
  [ .u32 L.threadListLockAddr 0#32, .u64 L.sysinfoAddr 0#64, .u64 L.hwcapAddr 0#64,
    .u8 L.finalizedAddr 0#8, .u8 L.initializedAddr 0#8,
    .u64 L.stdDetectCacheAddr 0#64, .u64 L.environAddr 0#64,
    .u64 L.prognameAddr 0#64, .u64 L.prognameFullAddr 0#64,
    .u8 L.haveLseAtomicsAddr 0#8, .u64 L.stdinUsedAddr 0#64 ] ++
  (if L.stdoutUsedAddr == L.stdinUsedAddr then [] else [.u64 L.stdoutUsedAddr 0#64]) ++
  [ .u64 L.oflHeadAddr 0#64, .u32 L.oflLockAddr 0#32 ]

def f3NonStderrAtoms (L : StdBinaryLayout) : List RwAtom :=
  L.initFiniAtoms ++ L.gotAtoms ++ f3DataNoStderrAtoms L ++ L.libcAtoms ++ L.tlsAtoms ++
    f3BssAtoms L ++ L.extraRwAtoms

def f3StdRwAtoms (L : StdBinaryLayout) : List RwAtom :=
  L.initFiniAtoms ++ L.gotAtoms ++ f3DataNoStderrAtoms L ++ L.stderrFileAtoms ++ L.libcAtoms ++
    L.tlsAtoms ++ f3BssAtoms L

def f3AllRwAtoms (L : StdBinaryLayout) : List RwAtom :=
  f3StdRwAtoms L ++ L.extraRwAtoms

/-- Minimal read-only PHDR + empty C-string constants for F3 `musl` startup. -/
def F3RoConstants (L : StdBinaryLayout) : SepProp :=
  (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ (L.emptyCStrAddr ↦₈ᵣ 0#8)

def F3DataGlobals (L : StdBinaryLayout) : SepProp :=
  rwAtomListSep (f3DataNoStderrAtoms L) ∗ StdStderrFile L

def F3BssGlobals (L : StdBinaryLayout) : SepProp :=
  rwAtomListSep (f3BssAtoms L)

def F3InitGlobals (L : StdBinaryLayout) : SepProp :=
  StdInitFiniGlobals L ∗ StdGotGlobals L ∗ F3DataGlobals L ∗ StdLibcGlobals L ∗ StdTlsGlobals L ∗
    F3BssGlobals L

theorem f3AllRwAtoms_sep_eq (L : StdBinaryLayout) :
    rwAtomListSep (f3AllRwAtoms L) = F3InitGlobals L ∗ StdExtraRw L := by
  simp only [f3AllRwAtoms, f3StdRwAtoms, F3InitGlobals, StdInitFiniGlobals, StdGotGlobals,
    F3DataGlobals, StdStderrFile, StdLibcGlobals, StdTlsGlobals, F3BssGlobals, StdExtraRw,
    rwAtomListSep_append, sepConj_assoc]

/-- Validate the `phnum × 56` B program header table with an empty `PT_TLS` (`0/0/0/0`) at
    `L.tlsPhdrIdx`. -/
def f3CheckPhdrTable (L : StdBinaryLayout) : Bool :=
  0 < L.phnum && L.phdrAddr.toNat % 8 == 0 && L.phdrBytes.length == L.phnum * 56 &&
  L.tlsPhdrIdx < L.phnum &&
  listReadU32LE L.phdrBytes 0 == 6 && listReadU64LE L.phdrBytes 16 == L.phdrAddr.toNat &&
  (List.range L.phnum).all fun i =>
    let off := i * 56
    let ptype := listReadU32LE L.phdrBytes off
    let pvaddr := listReadU64LE L.phdrBytes (off + 16)
    let pfilesz := listReadU64LE L.phdrBytes (off + 32)
    let pmemsz := listReadU64LE L.phdrBytes (off + 40)
    let palign := listReadU64LE L.phdrBytes (off + 48)
    ptype != 2 && (if ptype == 6 then pvaddr == L.phdrAddr.toNat else true) &&
    (if ptype == 0x6474e551 then pmemsz == 0 else true) &&
    (if i == L.tlsPhdrIdx then
      ptype == 7 && pvaddr == 0 && pfilesz == 0 && pmemsz == 0 && palign == 0
     else ptype != 7)

/-- Validate `roSeg` (`emptyCStrAddr` + `extraRoSlices`, e.g. `mallocngRoTablesBytes`). -/
def f3CheckRoSegment (L : StdBinaryLayout) (roSeg : Snapshot.Region) (roLen : Nat) : Bool :=
  roSeg.perm == Perm.ro &&
  checkSegSlice roSeg roLen L.emptyCStrAddr [0#8] &&
  L.extraRoSlices.all (fun (a, bs) => checkSegSlice roSeg roLen a bs)

/-- Validate `rwSeg` alignments, initial byte slices, and pairwise disjointness for F3 globals. -/
def f3CheckRwSegment (L : StdBinaryLayout) (rwSeg : Snapshot.Region) (rwLen : Nat) : Bool :=
  rwSeg.perm == Perm.rw && L.builtinTlsAddr.toNat % 8 == 0 && L.mainTlsAddr.toNat % 8 == 0 &&
  L.libcAddr.toNat % 8 == 0 && L.stderrFileAddr.toNat % 8 == 0 &&
  L.initArrayAddr.toNat % 8 == 0 && L.finiArrayAddr.toNat % 8 == 0 && L.gotAddr.toNat % 8 == 0 &&
  rwSeg.start.toNat ≤ L.stderrFileAddr.toNat &&
  L.stderrFileAddr.toNat + 0xe8 ≤ rwSeg.start.toNat + rwLen &&
  (f3AllRwAtoms L).all (fun x =>
    x.addr.toNat % x.align == 0 && checkSegSlice rwSeg rwLen x.addr x.rawBytes) &&
  (f3NonStderrAtoms L).all (fun x =>
    intervalDisjoint (L.stderrFileAddr.toNat, 0xe8) (x.addr.toNat, x.rawBytes.length)) &&
  intervalsPairwiseDisjoint ((f3AllRwAtoms L).map fun x => (x.addr.toNat, x.rawBytes.length))

/-- Kernel-decidable validator checking that `img` conforms to the minimal F3 `StdBinaryLayout`. -/
def f3MatchesImage (L : StdBinaryLayout) (img : ElfImage) : Bool :=
  fastWellFormed img && img.entry == L.startAddr && img.phdrVaddr == L.phdrAddr &&
  img.phnum == L.phnum && img.brkStart == L.brkStart &&
  (0x10000 ≤ L.brkStart.toNat && L.brkStart.toNat ≤ 2 ^ 30) &&
  L.cMainAddr.toNat % 4 == 0 &&
  match img.segments[L.phdrSegIdx]?, img.segments[L.rxSegIdx]?,
        img.segments[L.roSegIdx]?, img.segments[L.rwSegIdx]? with
  | some phdrSeg, some rxSeg, some roSeg, some rwSeg =>
    withForcedNat (fastLen512 4096 phdrSeg.bytes) fun phdrLen =>
    withForcedNat (fastLen512 4096 rxSeg.bytes) fun rxLen =>
    withForcedNat (fastLen512 4096 roSeg.bytes) fun roLen =>
    withForcedNat (fastLen512 4096 rwSeg.bytes) fun rwLen =>
      phdrSeg.perm == Perm.ro && rxSeg.perm == Perm.rx &&
      (f3CodeAddrs L).all (fun a => a.toNat % 4 == 0 &&
        rxSeg.start.toNat ≤ a.toNat && a.toNat + 4 ≤ rxSeg.start.toNat + rxLen) &&
      f3CheckPhdrTable L && checkSegSlice phdrSeg phdrLen L.phdrAddr L.phdrBytes &&
      f3CheckRoSegment L roSeg roLen && f3CheckRwSegment L rwSeg rwLen
  | _, _, _, _ => false

theorem f3MatchesImage_segments {L : StdBinaryLayout} {img : ElfImage}
    (h : f3MatchesImage L img = true) :
    img.WellFormed = true ∧ img.entry = L.startAddr ∧ img.phdrVaddr = L.phdrAddr ∧
    img.phnum = L.phnum ∧ img.brkStart = L.brkStart ∧
    (0x10000 ≤ L.brkStart.toNat ∧ L.brkStart.toNat ≤ 2 ^ 30) ∧
    L.cMainAddr.toNat % 4 = 0 ∧
    ∃ phdrSeg rxSeg roSeg rwSeg,
      img.segments[L.phdrSegIdx]? = some phdrSeg ∧ img.segments[L.rxSegIdx]? = some rxSeg ∧
      img.segments[L.roSegIdx]? = some roSeg ∧ img.segments[L.rwSegIdx]? = some rwSeg ∧
      phdrSeg.perm = Perm.ro ∧ rxSeg.perm = Perm.rx ∧
      ((f3CodeAddrs L).all fun a => a.toNat % 4 == 0 &&
        rxSeg.start.toNat ≤ a.toNat && a.toNat + 4 ≤ rxSeg.start.toNat + rxSeg.bytes.length) = true ∧
      f3CheckPhdrTable L = true ∧
      checkSegSlice phdrSeg phdrSeg.bytes.length L.phdrAddr L.phdrBytes = true ∧
      f3CheckRoSegment L roSeg roSeg.bytes.length = true ∧
      f3CheckRwSegment L rwSeg rwSeg.bytes.length = true := by
  unfold f3MatchesImage at h; rw [fastWellFormed_eq] at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwf, hent⟩, hphv⟩, hphn⟩, hbrk⟩, hbrkle⟩, hcmain⟩, hm⟩ := h
  refine ⟨hwf, hent, hphv, hphn, hbrk, hbrkle, hcmain, ?_⟩
  split at hm <;> try contradiction
  rename_i phdrSeg rxSeg roSeg rwSeg h0 h1 h2 h3
  simp only [withForcedNat_eq, fastLen512_eq_length, Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨hp0, hp1⟩, hcode⟩, hphdrT⟩, hphdrS⟩, hro⟩, hrw⟩ := hm
  exact ⟨phdrSeg, rxSeg, roSeg, rwSeg, h0, h1, h2, h3, hp0, hp1, hcode, hphdrT, hphdrS, hro, hrw⟩

private theorem regionAlignedValid_bounds {r : Snapshot.Region} (hv : regionAlignedValid r = true) :
    Obj.pageSize ≤ r.start.toNat ∧ r.start.toNat % Obj.pageSize = 0 ∧
      0 < r.bytes.length ∧ r.start.toNat + r.bytes.length ≤ 2 ^ 48 := by
  unfold regionAlignedValid at hv; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  exact ⟨hv.1.1.1.1.1.1, hv.1.1.1.1.1.2, hv.1.1.1.1.2, hv.1.1.2⟩

private theorem regionAlignedValid_of_disjoint {regions : List Snapshot.Region}
    (hd : regionsDisjointAndAligned regions = true) {r : Snapshot.Region} (hr : r ∈ regions) :
    regionAlignedValid r = true := by
  match regions with
  | [] => nomatch hr
  | [_] => rw [List.mem_singleton.mp hr]; exact hd
  | r1 :: r2 :: rest =>
    simp only [regionsDisjointAndAligned, Bool.and_eq_true] at hd
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact hd.1.1
    · exact regionAlignedValid_of_disjoint hd.2 hr'

private theorem start_lt_tail_of_disjoint {r1 : Snapshot.Region} {tail : List Snapshot.Region}
    (hd : regionsDisjointAndAligned (r1 :: tail) = true) {q : Snapshot.Region} (hq : q ∈ tail) :
    r1.start.toNat + r1.bytes.length ≤ q.start.toNat := by
  match tail with
  | [] => nomatch hq
  | r2 :: rest =>
    simp only [regionsDisjointAndAligned, Bool.and_eq_true, decide_eq_true_eq] at hd
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact hd.1.2
    · have ⟨_, _, hpos, _⟩ :=
        regionAlignedValid_bounds (regionAlignedValid_of_disjoint hd.2 (List.mem_cons.mpr (Or.inl rfl)))
      have ih := start_lt_tail_of_disjoint hd.2 hq'; omega

private theorem take_below_of_disjoint {regions : List Snapshot.Region}
    (hd : regionsDisjointAndAligned regions = true) (k : Nat) (hk : k < regions.length) :
    (regions.take k).all (Snapshot.Below regions[k].start) = true := by
  induction k generalizing regions with
  | zero => rfl
  | succ k ih =>
    match regions with
    | [] => nomatch hk
    | [_] => simp at hk
    | r1 :: r2 :: rest =>
      simp only [regionsDisjointAndAligned, Bool.and_eq_true] at hd
      have hk' : k < (r2 :: rest).length := Nat.lt_of_succ_lt_succ hk
      have hhead : Snapshot.Below (r2 :: rest)[k].start r1 = true := by
        simp only [Snapshot.Below, decide_eq_true_eq]
        exact start_lt_tail_of_disjoint
          (by simp only [regionsDisjointAndAligned, Bool.and_eq_true]; exact hd)
          (List.getElem_mem hk')
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.all_cons, hhead, Bool.true_and]
      exact ih hd.2 hk'

theorem f3MatchesImage_codeLoaded {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State}
    (h : f3MatchesImage L img = true) (hload : img.loadState inputs = .ok s0) :
    (L.rxProgram img).CodeLoaded s0.mem := by
  obtain ⟨hwf, _, _, _, _, _, _, _, rxSeg, _, _, _, hrx, _, _, _, hperm, _⟩ :=
    f3MatchesImage_segments h
  unfold StdBinaryLayout.rxProgram; rw [hrx]; dsimp only []
  obtain ⟨hidx, rfl⟩ := List.getElem?_eq_some_iff.mp hrx
  have hd : regionsDisjointAndAligned img.segments = true := by
    unfold ElfImage.WellFormed at hwf; simp only [Bool.and_eq_true] at hwf; exact hwf.1.1.1.2
  have ⟨_, hal, _, hhi⟩ :=
    regionAlignedValid_bounds (regionAlignedValid_of_disjoint hd (List.getElem_mem hidx))
  have hhb := ElfImage.holdsBytes_of_segment_slice img hload L.rxSegIdx hidx
    (take_below_of_disjoint hd L.rxSegIdx hidx) (by omega) 0 img.segments[L.rxSegIdx].bytes
    (by rw [List.drop_zero, List.take_length])
  rw [BitVec.add_zero, hperm] at hhb
  exact Program.CodeLoaded.intro (by dsimp only []; unfold Obj.pageSize at hal; omega)
    (by dsimp only []; omega) hhb

theorem f3MatchesImage_holdsBytes_ro_slice {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State} {seg : Snapshot.Region} {addr : BitVec 64}
    {bs : List (BitVec 8)}
    (h : f3MatchesImage L img = true) (hload : img.loadState inputs = .ok s0)
    (hseg : img.segments[L.roSegIdx]? = some seg ∨ img.segments[L.phdrSegIdx]? = some seg)
    (hslice : checkSegSlice seg seg.bytes.length addr bs = true) :
    Obj.HoldsBytes s0.mem addr bs (fun _ => Perm.ro) ∧
      Obj.pageSize ≤ addr.toNat ∧ addr.toNat + bs.length ≤ 2 ^ 48 := by
  obtain ⟨hwf, _, _, _, _, _, _, phdrSeg, _, roSeg, _, hph, _, hro, _, hp0, _, _, _, _, hroC, _⟩ :=
    f3MatchesImage_segments h
  rcases hseg with hs | hs
  · cases hro.symm.trans hs
    unfold f3CheckRoSegment at hroC; simp only [Bool.and_eq_true, beq_iff_eq] at hroC
    have hres := holdsBytes_of_checkSegSlice hwf hload hs hslice
    rw [hroC.1.1] at hres; exact hres
  · cases hph.symm.trans hs
    have hres := holdsBytes_of_checkSegSlice hwf hload hs hslice
    rw [hp0] at hres; exact hres

private theorem satisfies_ro_of_holdsBytes {m : Memory} {addr : BitVec 64} {bs : List (BitVec 8)}
    {P : SepProp} (hhb : Obj.HoldsBytes m addr bs (fun _ => Perm.ro))
    (hlen : bs.length ≤ 2 ^ 64) (hP : m ⊨ P) : m ⊨ (addr ↦ᵣ bs) ∗ P :=
  Satisfies.rodata_intro (holdsBytes_ro hhb).1 (holdsBytes_ro hhb).2 hlen hP

private theorem satisfies_roSliceList {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    {idx : Nat} {roSeg : Snapshot.Region} {slices : List (BitVec 64 × List (BitVec 8))} {P : SepProp}
    (hwf : img.WellFormed = true) (hload : img.loadState inputs = .ok s0)
    (hseg : img.segments[idx]? = some roSeg) (hperm : roSeg.perm = Perm.ro)
    (hall : slices.all (fun (a, bs) => checkSegSlice roSeg roSeg.bytes.length a bs) = true)
    (hP : s0.mem ⊨ P) : s0.mem ⊨ roSliceListSep slices ∗ P := by
  induction slices with
  | nil => rw [roSliceListSep, emp_sepConj]; exact hP
  | cons hd tl ih =>
    rcases hd with ⟨a, bs⟩; simp only [List.all_cons, Bool.and_eq_true] at hall
    have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hseg hall.1
    rw [hperm] at hhb; rw [roSliceListSep_cons, sepConj_assoc]
    exact satisfies_ro_of_holdsBytes hhb (by omega) (ih hall.2)

theorem f3MatchesImage_satisfies_roConstants {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State} {P : SepProp}
    (h : f3MatchesImage L img = true) (hload : img.loadState inputs = .ok s0) (hP : s0.mem ⊨ P) :
    s0.mem ⊨ F3RoConstants L ∗ StdExtraRo L ∗ P := by
  obtain ⟨hwf, _, _, _, _, _, _, phdrSeg, _, roSeg, _, hph, _, hro, _, hp0, _, _, _, hphS, hroC, _⟩ :=
    f3MatchesImage_segments h
  unfold f3CheckRoSegment at hroC; simp only [Bool.and_eq_true, beq_iff_eq] at hroC
  obtain ⟨⟨hpro, hempS⟩, hexS⟩ := hroC
  have h1 := satisfies_roSliceList hwf hload hro hpro hexS hP
  have ⟨hb_emp, _, hi_emp⟩ := holdsBytes_of_checkSegSlice hwf hload hro hempS
  rw [hpro] at hb_emp
  have h2 := satisfies_ro_of_holdsBytes hb_emp (by omega) h1
  rw [pointsToBytesRO_singleton] at h2
  have ⟨hb_ph, _, hi_ph⟩ := holdsBytes_of_checkSegSlice hwf hload hph hphS
  rw [hp0] at hb_ph
  simpa only [F3RoConstants, StdExtraRo, sepConj_assoc] using
    satisfies_ro_of_holdsBytes hb_ph (by omega) h2

theorem f3MatchesImage_holdsBytes_rw_slice {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State} {seg : Snapshot.Region} {addr : BitVec 64}
    {bs : List (BitVec 8)}
    (h : f3MatchesImage L img = true) (hload : img.loadState inputs = .ok s0)
    (hseg : img.segments[L.rwSegIdx]? = some seg)
    (hslice : checkSegSlice seg seg.bytes.length addr bs = true) :
    Obj.HoldsBytes s0.mem addr bs (fun _ => Perm.rw) ∧
      Obj.pageSize ≤ addr.toNat ∧ addr.toNat + bs.length ≤ 2 ^ 48 := by
  obtain ⟨hwf, _, _, _, _, _, _, _, _, _, rwSeg, _, _, _, hrw, _, _, _, _, _, _, hrwC⟩ :=
    f3MatchesImage_segments h
  cases hrw.symm.trans hseg
  unfold f3CheckRwSegment at hrwC; simp only [Bool.and_eq_true, beq_iff_eq] at hrwC
  have hres := holdsBytes_of_checkSegSlice hwf hload hseg hslice
  rw [hrwC.1.1.1.1.1.1.1.1.1.1.1.1] at hres; exact hres

theorem f3MatchesImage_supportedOn_initGlobals_below_brk {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State}
    (h : f3MatchesImage L img = true) (hload : img.loadState inputs = .ok s0) :
    SupportedOn 0#64 (fun k => 0 ≤ k ∧ k < L.brkStart.toNat)
      s0.mem (F3InitGlobals L ∗ StdExtraRw L) := by
  obtain ⟨hwf, _, _, _, hbrk_eq, _, _, _, _, _, rwSeg, _, _, _, hrw, _, _, _, _, _, _, hrwC⟩ :=
    f3MatchesImage_segments h
  have hbel_all : img.segments.all (Snapshot.Below L.brkStart) = true := by
    have hwf' := hwf; unfold ElfImage.WellFormed at hwf'
    simp only [Bool.and_eq_true] at hwf'; rw [← hbrk_eq]; exact hwf'.2
  have hbel := List.all_eq_true.mp hbel_all rwSeg (List.mem_of_getElem? hrw)
  simp only [Snapshot.Below, decide_eq_true_eq] at hbel
  unfold f3CheckRwSegment at hrwC; simp only [Bool.and_eq_true, beq_iff_eq] at hrwC
  have hs := supportedOn_rwAtomList (f3AllRwAtoms L) (fun x hx => by
    have hxC := List.all_eq_true.mp hrwC.1.1.2 x hx; simp only [Bool.and_eq_true] at hxC
    have ⟨hhb, _, hhi⟩ := holdsBytes_of_checkSegSlice hwf hload hrw hxC.2
    rw [hrwC.1.1.1.1.1.1.1.1.1.1.1.1] at hhb; exact ⟨by omega, hhb⟩) hrwC.2
  refine (SupportedOn.congr_prop (f3AllRwAtoms_sep_eq L) hs).widen fun k ⟨x, hx, hk1, hk2⟩ => ?_
  have hxC := List.all_eq_true.mp hrwC.1.1.2 x hx; simp only [Bool.and_eq_true] at hxC
  have hb := hxC.2; unfold checkSegSlice at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb; omega

private theorem isAligned_x64_of_mod8 {a : BitVec 64} (h : a.toNat % 8 = 0) :
    MemWidth.isAligned .X64 a = true := by
  simp only [MemWidth.isAligned, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; change a.toNat &&& 7 = 0
  rw [Nat.and_two_pow_sub_one_eq_mod _ 3]; exact h

/-- Alignment, non-null, and table-bounds facts derived from `f3MatchesImage L img = true`. -/
structure F3LayoutImageFacts (L : StdBinaryLayout) : Prop where
  checkPhdr     : f3CheckPhdrTable L = true
  phdr_end      : L.phdrAddr.toNat + L.phnum * 56 < 2 ^ 64
  builtinTls_al : L.builtinTlsAddr.toNat % 8 = 0
  mainTls_nz    : L.mainTlsAddr ≠ 0#64
  initArray_bnd : L.initArrayAddr.toNat + 16 < 2 ^ 64
  finiArray_bnd : L.finiArrayAddr.toNat + 8 < 2 ^ 64
  al_got        : MemWidth.isAligned .X64 L.gotAddr = true
  al_fini       : MemWidth.isAligned .X64 L.finiArrayAddr = true
  al_ofl        : MemWidth.isAligned .X64 L.oflHeadAddr = true
  al_stdin      : MemWidth.isAligned .X64 L.stdinUsedAddr = true
  al_stdout     : MemWidth.isAligned .X64 L.stdoutUsedAddr = true
  al_stderrUsed : MemWidth.isAligned .X64 L.stderrUsedAddr = true
  al_stderrFile : MemWidth.isAligned .X64 L.stderrFileAddr = true
  stderrFile_nz : L.stderrFileAddr ≠ 0#64
  cMain_al4     : L.cMainAddr.toNat % 4 = 0
  tp_bounds     : 0xa4 ≤ (L.builtinTlsAddr + 0xc8#64).toNat ∧
                    (L.builtinTlsAddr + 0xc8#64).toNat ≤ 2 ^ 48

theorem extractF3LayoutImageFacts {L : StdBinaryLayout} {img : ElfImage}
    {inputs : ProcessInputs} {s0 : State}
    (hmatch : f3MatchesImage L img = true) (hload : img.loadState inputs = .ok s0) :
    F3LayoutImageFacts L := by
  obtain ⟨hwf, _, _, _, _, _, hcmain, phdrSeg, _, _, rwSeg, hphdrSeg, _, _, hrwSeg,
    _, _, _, hphdr, hphdrSlice, _, hrwChk⟩ := f3MatchesImage_segments hmatch
  have ⟨_, _, hphdr_hi⟩ :=
    f3MatchesImage_holdsBytes_ro_slice hmatch hload (Or.inr hphdrSeg) hphdrSlice
  have hplen : L.phdrBytes.length = L.phnum * 56 := by
    unfold f3CheckPhdrTable at hphdr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hphdr
    exact hphdr.1.1.1.1.2
  unfold f3CheckRwSegment at hrwChk
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hrwChk
  have hbtls := hrwChk.1.1.1.1.1.1.1.1.1.1.1.2
  have hstderr_al := hrwChk.1.1.1.1.1.1.1.1.2
  have hfini_al := hrwChk.1.1.1.1.1.1.2
  have hgot_al := hrwChk.1.1.1.1.1.2
  have hall_rw := hrwChk.1.1.2
  have atomProps : ∀ {x : RwAtom}, x ∈ f3AllRwAtoms L →
      x.addr.toNat % x.align = 0 ∧ Obj.pageSize ≤ x.addr.toNat ∧
        x.addr.toNat + x.rawBytes.length ≤ 2 ^ 48 := fun hx => by
    have ⟨hal, hsl⟩ := hall_rw _ hx
    have ⟨_, hlo, hhi⟩ := f3MatchesImage_holdsBytes_rw_slice hmatch hload hrwSeg hsl
    exact ⟨hal, hlo, hhi⟩
  have memStd : ∀ {x : RwAtom}, x ∈ f3StdRwAtoms L → x ∈ f3AllRwAtoms L :=
    fun hx => List.mem_append_left _ hx
  have h_init0 := atomProps (memStd (by simp [f3StdRwAtoms, StdBinaryLayout.initFiniAtoms] :
    RwAtom.u64 L.initArrayAddr L.initLseAddr ∈ f3StdRwAtoms L))
  have h_fini0 := atomProps (memStd (by simp [f3StdRwAtoms, StdBinaryLayout.initFiniAtoms] :
    RwAtom.u64 L.finiArrayAddr L.doFiniAddr ∈ f3StdRwAtoms L))
  have h_mtls := atomProps (memStd (by
    simp only [f3StdRwAtoms, StdBinaryLayout.tlsAtoms,
      List.mem_append, List.mem_cons, true_or, or_true] :
    RwAtom.u64 L.mainTlsAddr 0#64 ∈ f3StdRwAtoms L))
  have h_stderrU := atomProps (memStd (by simp [f3StdRwAtoms, f3DataNoStderrAtoms] :
    RwAtom.u64 L.stderrUsedAddr L.stderrFileAddr ∈ f3StdRwAtoms L))
  have h_stderr0 := atomProps (memStd (by simp [f3StdRwAtoms, StdBinaryLayout.stderrFileAtoms] :
    RwAtom.u64 (L.stderrFileAddr + 0x08#64) 0#64 ∈ f3StdRwAtoms L))
  have h_stdin := atomProps (memStd (by simp [f3StdRwAtoms, f3BssAtoms] :
    RwAtom.u64 L.stdinUsedAddr 0#64 ∈ f3StdRwAtoms L))
  have h_ofl := atomProps (memStd (by simp [f3StdRwAtoms, f3BssAtoms] :
    RwAtom.u64 L.oflHeadAddr 0#64 ∈ f3StdRwAtoms L))
  have h_stdout_al : L.stdoutUsedAddr.toNat % 8 = 0 := by
    by_cases heq : L.stdoutUsedAddr == L.stdinUsedAddr
    · rw [beq_iff_eq.mp heq]; exact h_stdin.1
    · exact (atomProps (memStd (by simp [f3StdRwAtoms, f3BssAtoms, heq] :
        RwAtom.u64 L.stdoutUsedAddr 0#64 ∈ f3StdRwAtoms L))).1
  have h_btls := atomProps (memStd (by
    simp only [f3StdRwAtoms, StdBinaryLayout.tlsAtoms,
      List.mem_append, List.mem_cons, true_or, or_true] :
    RwAtom.bytes L.builtinTlsAddr (List.replicate 0x150 0#8) ∈ f3StdRwAtoms L))
  have dPage : Obj.pageSize = 4096 := rfl
  refine ⟨hphdr, by omega, hbtls, ?_, ?_, ?_,
    isAligned_x64_of_mod8 hgot_al, isAligned_x64_of_mod8 hfini_al,
    isAligned_x64_of_mod8 h_ofl.1, isAligned_x64_of_mod8 h_stdin.1,
    isAligned_x64_of_mod8 h_stdout_al, isAligned_x64_of_mod8 h_stderrU.1,
    isAligned_x64_of_mod8 hstderr_al, ?_, hcmain, ?_⟩
  · intro hz; dsimp only [RwAtom.addr] at h_mtls; rw [hz, dPage] at h_mtls; simp at h_mtls
  · dsimp only [RwAtom.addr, RwAtom.rawBytes] at h_init0; rw [unpack64_length] at h_init0; omega
  · dsimp only [RwAtom.addr, RwAtom.rawBytes] at h_fini0; rw [unpack64_length] at h_fini0; omega
  · intro hz; dsimp only [RwAtom.addr] at h_stderr0
    rw [hz, BitVec.zero_add, dPage] at h_stderr0; simp at h_stderr0
  · dsimp only [RwAtom.addr, RwAtom.rawBytes] at h_btls
    rw [List.length_replicate, dPage] at h_btls
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega⟩

/-! ## `PT_TLS` `0/0/0/0` Static TLS Memory Bundles and Store Lemmas -/

/-- Zero-initialized DTV pointer and two-word DTV array inside `builtin_tls` when `PT_TLS` is
    `0/0/0/0` (`tls_size = 0xe0`, `dtv = td + 0xd0`). -/
def F3DtvZero (td : BitVec 64) : SepProp :=
  ((td + 0xc0#64) ↦₆₄ 0#64) ∗ ((td + 0xd0#64) ↦₆₄ 0#64) ∗ ((td + 0xd8#64) ↦₆₄ 0#64)

/-- Post-`__copy_tls` DTV pointer (`td + 0xc0 ↦ td + 0xd0`) and `[1, td + 0xc8]` DTV array. -/
def F3DtvInit (td : BitVec 64) : SepProp :=
  ((td + 0xc0#64) ↦₆₄ (td + 0xd0#64)) ∗ ((td + 0xd0#64) ↦₆₄ 1#64) ∗
    ((td + 0xd8#64) ↦₆₄ (td + 0xc8#64))

/-- Untouched zero-padding slices inside `builtin_tls` (`0x150` B total) for `PT_TLS` `0/0/0/0`. -/
def F3BuiltinTlsPad (td : BitVec 64) : SepProp :=
  ((td + 0x2c#64) ↦ₛ List.replicate 0x4c 0#8) ∗
  ((td + 0x80#64) ↦ₛ List.replicate 0x18 0#8) ∗
  ((td + 0xa0#64) ↦ₛ List.replicate 0x20 0#8) ∗
  ((td + 0xc8#64) ↦₆₄ 0#64) ∗
  ((td + 0xe0#64) ↦ₛ List.replicate 0x70 0#8)

/-- Initialized `main_tls` descriptor written by `static_init_tls` for `PT_TLS` `0/0/0/0`. -/
def F3MainTlsInit (L : StdBinaryLayout) : SepProp :=
  (L.mainTlsAddr ↦₆₄ 0#64) ∗ ((L.mainTlsAddr + 0x08#64) ↦₆₄ 0#64) ∗
  ((L.mainTlsAddr + 0x10#64) ↦₆₄ 0#64) ∗ ((L.mainTlsAddr + 0x18#64) ↦₆₄ 0#64) ∗
  ((L.mainTlsAddr + 0x20#64) ↦₆₄ 8#64) ∗ ((L.mainTlsAddr + 0x28#64) ↦₆₄ 0#64)

/-- Initialized `__libc.{tls_head, tls_size, tls_align, tls_cnt}` for `PT_TLS` `0/0/0/0`
    (`tls_size = 0xe0`, `tls_align = 8`, `tls_cnt = 1`). -/
def F3LibcTlsInit (L : StdBinaryLayout) : SepProp :=
  ((L.libcAddr + 0x10#64) ↦₆₄ L.mainTlsAddr) ∗ ((L.libcAddr + 0x18#64) ↦₆₄ 0xe0#64) ∗
  ((L.libcAddr + 0x20#64) ↦₆₄ 8#64) ∗ ((L.libcAddr + 0x28#64) ↦₆₄ 1#64)

/-- Bundled post-`static_init_tls` TLS state for `PT_TLS` `0/0/0/0` (excluding `errno` at
    `td + 0x24 = tp - 0xa4`). -/
def F3TlsState (L : StdBinaryLayout) (sysinfoVal : BitVec 64) : SepProp :=
  StdTdInit L sysinfoVal ∗ F3DtvInit L.builtinTlsAddr ∗ F3BuiltinTlsPad L.builtinTlsAddr ∗
    F3MainTlsInit L ∗ F3LibcTlsInit L

/-- Exact contiguous partition of `builtin_tls` (`0x150` zero bytes at `td`) for `PT_TLS` `0/0/0/0`. -/
theorem f3BuiltinTls_zero_split (td : BitVec 64) :
    (td ↦ₛ List.replicate 0x150 0#8) =
      StdTdZero td ∗ F3DtvZero td ∗ ((td + 0x24#64) ↦₃₂ 0#32) ∗ F3BuiltinTlsPad td := by
  rw [show (0x150 : Nat) = 8 + 0x148 from rfl,
      pointsToBytes_replicate_split td 8 0x148 0#8,
      pointsToBytes_replicate_split_off td 0x08 8 0x140 0#8,
      pointsToBytes_replicate_split_off td 0x10 8 0x138 0#8,
      pointsToBytes_replicate_split_off td 0x18 8 0x130 0#8,
      pointsToBytes_replicate_split_off td 0x20 4 0x12c 0#8,
      pointsToBytes_replicate_split_off td 0x24 4 0x128 0#8,
      pointsToBytes_replicate_split_off td 0x28 4 0x124 0#8,
      pointsToBytes_replicate_split_off td 0x2c 0x4c 0xd8 0#8,
      pointsToBytes_replicate_split_off td 0x78 8 0xd0 0#8,
      pointsToBytes_replicate_split_off td 0x80 0x18 0xb8 0#8,
      pointsToBytes_replicate_split_off td 0x98 8 0xb0 0#8,
      pointsToBytes_replicate_split_off td 0xa0 0x20 0x90 0#8,
      pointsToBytes_replicate_split_off td 0xc0 8 0x88 0#8,
      pointsToBytes_replicate_split_off td 0xc8 8 0x80 0#8,
      pointsToBytes_replicate_split_off td 0xd0 8 0x78 0#8,
      pointsToBytes_replicate_split_off td 0xd8 8 0x70 0#8]
  simp only [StdTdZero, F3DtvZero, F3BuiltinTlsPad,
    pointsToBytes_replicate4_zero, pointsToBytes_replicate8_zero]
  sep_ac_rfl

private theorem f3TlsGlobals_split (L : StdBinaryLayout) :
    StdTlsGlobals L =
      StdTdZero L.builtinTlsAddr ∗ F3DtvZero L.builtinTlsAddr ∗
        ((L.builtinTlsAddr + 0x24#64) ↦₃₂ 0#32) ∗ F3BuiltinTlsPad L.builtinTlsAddr ∗
        StdMainTlsZero L := by
  simp only [StdTlsGlobals, StdBinaryLayout.tlsAtoms, rwAtomListSep, RwAtom.toSepProp,
    f3BuiltinTls_zero_split, StdMainTlsZero, sepConj_assoc]

@[local simp] private theorem mem_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).mem = s.mem := by cases r <;> rfl
@[local simp] private theorem mem_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).mem = s.mem := by simp [State.writeReg32]
@[local simp] private theorem mem_setPState (s : State) (p : PState) :
    (s.setPState p).mem = s.mem := rfl
@[local simp] private theorem mem_advancePC (s : State) : s.advancePC.mem = s.mem := rfl
@[local simp] private theorem mem_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).mem = s.mem := rfl
@[local simp] private theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

@[local simp] private theorem stdPres_rfl (s : State) : StdStatePreserved s s := .rfl s
@[local simp] private theorem stdPres_writeReg64 (s0 s : State) (r : Reg) (v : BitVec 64) :
    StdStatePreserved s0 (s.writeReg64 r v) ↔ StdStatePreserved s0 s := by
  cases r <;> simp [State.writeReg64, StdStatePreserved]
@[local simp] private theorem stdPres_writeReg32 (s0 s : State) (r : Reg) (v : BitVec 32) :
    StdStatePreserved s0 (s.writeReg32 r v) ↔ StdStatePreserved s0 s := by simp [State.writeReg32]
@[local simp] private theorem stdPres_setPState (s0 s : State) (p : PState) :
    StdStatePreserved s0 (s.setPState p) ↔ StdStatePreserved s0 s := Iff.rfl
@[local simp] private theorem stdPres_advancePC (s0 s : State) :
    StdStatePreserved s0 s.advancePC ↔ StdStatePreserved s0 s := Iff.rfl
@[local simp] private theorem stdPres_setPC (s0 s : State) (pc : BitVec 64) :
    StdStatePreserved s0 (s.setPC pc) ↔ StdStatePreserved s0 s := Iff.rfl
@[local simp] private theorem stdPres_setMem {s0 s : State} {m : Memory} (hp : m.perm = s.mem.perm) :
    StdStatePreserved s0 (s.setMem m) ↔ StdStatePreserved s0 s := by
  simp [State.setMem, StdStatePreserved, hp]

private theorem satisfies_memRegion_words64 {m : Memory} {base : BitVec 64} (n : Nat) {Rest : SepProp}
    (hn : 8 * n ≤ 2 ^ 64) (hm : m ⊨ memRegion base (8 * n) ∗ Rest) :
    ∃ ws : List (BitVec 64), ws.length = n ∧ (m ⊨ (base ↦₆₄* ws) ∗ Rest) := by
  have hm' := Satisfies.mono (sepConj_mono_left (memRegion_entails_pointsToWords64 n base hn)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm'; obtain ⟨ws, hws⟩ := hm'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hws; exact ⟨ws, hws.1, hws.2⟩

private theorem satisfies_words64_memRegion {m : Memory} {base : BitVec 64} (ws : List (BitVec 64))
    {Rest : SepProp} (hn : 8 * ws.length ≤ 2 ^ 64) (hm : m ⊨ (base ↦₆₄* ws) ∗ Rest) :
    m ⊨ memRegion base (8 * ws.length) ∗ Rest :=
  Satisfies.mono (sepConj_mono_left (pointsToWords64_entails_memRegion ws base hn)) hm

private theorem hasInstrs_fetch_at {P : Program} {base : BitVec 64} {instrs : List Instr}
    (h : hasInstrs P base instrs) (i : Nat) (off : BitVec 64) (inst : Instr)
    (hi : i < instrs.length) (hoff : BitVec.ofNat 64 (4 * i) = off)
    (hinst : instrs[i]'hi = inst) : P.fetch (base + off) = some inst := by
  rw [← hoff, ← hinst]; exact h i hi

private theorem hasInstrs_fetch_at0 {P : Program} {base : BitVec 64} {instrs : List Instr}
    (h : hasInstrs P base instrs) (inst : Instr) (hi : 0 < instrs.length)
    (hinst : instrs[0]'hi = inst) : P.fetch base = some inst := by
  rw [← hinst]; simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h 0 hi

local elab "have_fetches " hc:ident lo:num hi:num : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let hcExpr ← Lean.Elab.Tactic.elabTerm hc none
    let hcTy ← Lean.instantiateMVars (← Lean.Meta.inferType hcExpr)
    let instrsExpr := hcTy.getArg! 2
    let mut cur ← Lean.Meta.whnfD instrsExpr
    let mut elems : Array Lean.Expr := #[]
    while cur.isAppOfArity ``List.cons 3 do
      elems := elems.push (cur.getArg! 1)
      cur ← Lean.Meta.whnfD (cur.getArg! 2)
    for i in [lo.getNat : hi.getNat + 1] do
      let some instExpr := elems[i]? | throwError "have_fetches: index {i} out of range ({elems.size})"
      let lenE ← Lean.Meta.mkAppM ``List.length #[instrsExpr]
      let hiTy ← Lean.Meta.mkAppM ``LT.lt #[Lean.mkNatLit i, lenE]
      let hiGoal ← Lean.Meta.mkFreshExprMVar hiTy
      let saved ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [hiGoal.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        (simp only [initTpInstrs_length, copyTlsInstrs_length, staticInitTlsInstrs_length]; omega)))
      Lean.Elab.Tactic.setGoals saved
      let prf ← if i == 0 then
        Lean.Meta.mkAppM ``hasInstrs_fetch_at0 #[hcExpr, instExpr, hiGoal, ← Lean.Meta.mkEqRefl instExpr]
      else
        let offE ← Lean.Meta.mkAppM ``BitVec.ofNat #[Lean.mkNatLit 64, Lean.mkNatLit (4 * i)]
        Lean.Meta.mkAppM ``hasInstrs_fetch_at #[hcExpr, Lean.mkNatLit i, offE, instExpr, hiGoal,
          ← Lean.Meta.mkEqRefl offE, ← Lean.Meta.mkEqRefl instExpr]
      let g ← Lean.Elab.Tactic.getMainGoal
      let (_, g') ← (← g.assert (Lean.Name.mkSimple s!"_hf_{i}") (← Lean.Meta.inferType prf) prf).intro1P
      Lean.Elab.Tactic.replaceMainGoal [g']

local elab "clear_fetches " lo:num hi:num : tactic => do
  for i in [lo.getNat : hi.getNat + 1] do
    let hId := Lean.mkIdent (Lean.Name.mkSimple s!"_hf_{i}")
    Lean.Elab.Tactic.evalTactic (← `(tactic| try clear $hId))

private theorem step_str8_perm {prog : Program} {target_pc : BitVec 64} {s s' : State}
    {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hfetch : prog.fetch pc = some (.str .B8 rt addr)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have htrunc : (s.readReg64 rt).truncate 8 = val := bitvec_truncate8_truncate32 _ ▸ hval
  let m' := s.mem.write8 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 1 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write8 s.mem ea val)) hm'

private theorem step_str32_perm {prog : Program} {target_pc : BitVec 64} {s s' : State}
    {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 32}
    (hfetch : prog.fetch pc = some (.str .W32 rt addr)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg32 rt = val) (hstore : SepStore32 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  let m' := s.mem.write32 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 4 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .W32 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write32 s.mem ea val)) hm'

private theorem step_str64_perm {prog : Program} {target_pc : BitVec 64} {s s' : State}
    {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hfetch : prog.fetch pc = some (.str .X64 rt addr)) (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val) (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 8 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .X64 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hval, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc (hnext m' (Memory.perm_write64 s.mem ea val)) hm'

private theorem step_stp64_perm {prog : Program} {target_pc : BitVec 64} {s s' : State}
    {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea ea2 : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)}
    {v1 v2 : BitVec 64}
    (hfetch : prog.fetch pc = some (.stp .W64 rt1 rt2 addr)) (hpc : s.pc = pc)
    (hrun : s.status = .Running) (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb)) (hea2 : ea + 8#64 = ea2)
    (hv1 : s.readReg64 rt1 = v1) (hv2 : s.readReg64 rt2 = v2)
    (hstore1 : SepStore64 ea v1 P P1) (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.stp .W64 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hea2, hv1, hv2,
      hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m2 ((Memory.perm_write64 m1 ea2 v2).trans (Memory.perm_write64 s.mem ea v1))) hm2

local elab "wp_steps_p " n:num : tactic => do
  for _ in [0 : n.getNat] do
    Lean.Elab.Tactic.withMainContext do
      let g ← Lean.Elab.Tactic.getMainGoal
      let gTy := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let mut handled := false
      if gTy.isAppOfArity ``SepWP 6 then
        let sExpr := gTy.getArg! 2
        for decl in (← Lean.MonadLCtx.getLCtx) do
          if !handled && decl.userName.toString.startsWith "_hf_" then
            let ty := (← Lean.instantiateMVars decl.type).consumeMData
            if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Program.fetch 2 &&
                (ty.getArg! 2).isAppOfArity ``Option.some 2 then
              let pcExpr := (ty.getArg! 1).getArg! 1
              let inst := (ty.getArg! 2).getArg! 1
              let isStr := inst.isAppOfArity ``Instr.str 3 &&
                ((inst.getArg! 0).isConstOf ``MemWidth.B8 ||
                 (inst.getArg! 0).isConstOf ``MemWidth.W32 ||
                 (inst.getArg! 0).isConstOf ``MemWidth.X64)
              let isStp := inst.isAppOfArity ``Instr.stp 4 && (inst.getArg! 0).isConstOf ``RegWidth.W64
              if isStr || isStp then
                let pcEqTy ← Lean.Meta.mkEq (Lean.mkApp (Lean.mkConst ``State.pc) sExpr) pcExpr
                let sv ← Lean.Elab.Tactic.saveState
                let msgCnt := (← Lean.Core.getMessageLog).toList.length
                let pcOk ← try
                  let m ← Lean.Meta.mkFreshExprMVar pcEqTy
                  let savedG ← Lean.Elab.Tactic.getGoals
                  Lean.Elab.Tactic.setGoals [m.mvarId!]
                  Lean.Elab.Tactic.evalTactic (← `(tactic|
                    (simp (config := { decide := true }) only [wp_norm, arm64_norm, bv_lin_norm, *];
                     try bv_lin)))
                  let rem ← Lean.Elab.Tactic.getGoals
                  Lean.Elab.Tactic.setGoals savedG
                  pure (rem.isEmpty && (← Lean.Core.getMessageLog).toList.length == msgCnt)
                catch _ => pure false
                sv.restore
                if pcOk then
                  let hfId := Lean.mkIdent decl.userName
                  handled := true
                  if isStr then
                    let rId :=
                      if (inst.getArg! 0).isConstOf ``MemWidth.B8 then Lean.mkCIdent ``step_str8_perm
                      else if (inst.getArg! 0).isConstOf ``MemWidth.W32 then Lean.mkCIdent ``step_str32_perm
                      else Lean.mkCIdent ``step_str64_perm
                    Lean.Elab.Tactic.evalTactic (← `(tactic|
                      (apply $rId
                       (wp_focus_close (exact $hfId))
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close wp_sep_access)
                       (wp_focus_close wp_norm_lhs)
                       intro _ _hp
                       try simp only [mem_writeReg64, mem_writeReg32, mem_setPState, mem_advancePC,
                         mem_setPC, mem_setMem] at _hp)))
                  else
                    let stpId := Lean.mkCIdent ``step_stp64_perm
                    Lean.Elab.Tactic.evalTactic (← `(tactic|
                      (apply $stpId
                       (wp_focus_close (exact $hfId))
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close wp_norm_lhs)
                       (wp_focus_close wp_sep_access)
                       (wp_focus_close wp_sep_access)
                       (wp_focus_close wp_norm_lhs)
                       intro _ _hp
                       try simp only [mem_writeReg64, mem_writeReg32, mem_setPState, mem_advancePC,
                         mem_setPC, mem_setMem] at _hp)))
      if !handled then Lean.Elab.Tactic.evalTactic (← `(tactic| wp_step))

/-! ## `__copy_tls` and `static_init_tls` Contracts for `PT_TLS` `0/0/0/0` -/

private theorem align8_and_seven {a : BitVec 64} (h : a.toNat % 8 = 0) : a &&& 7#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and]
  change a.toNat &&& (2 ^ 3 - 1) = 0; rw [Nat.and_two_pow_sub_one_eq_mod]; exact h

private theorem copyTls_align_zero {a : BitVec 64} (h : a.toNat % 8 = 0) :
    7#64 &&& (0xffffffffffffff38#64 - a) = 0#64 := by
  have := align8_and_seven h; bv_bits

/-- Total-correctness contract for `__copy_tls(L.builtinTlsAddr)` under `PT_TLS` `0/0/0/0`. -/
def f3CopyTlsSpec (L : StdBinaryLayout) : Spec Unit where
  pre := fun _ s0 =>
    ⌜s0.readReg64 .x0 = L.builtinTlsAddr⌝ ∗
    (memRegion (s0.sp - 0x50#64) 0x50 ∗ F3DtvZero L.builtinTlsAddr ∗
      F3MainTlsInit L ∗ F3LibcTlsInit L)
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = L.builtinTlsAddr ∧ StdStatePreserved s0 sf⌝ ∗
    (memRegion (sf.sp - 0x50#64) 0x50 ∗ F3DtvInit L.builtinTlsAddr ∗
      F3MainTlsInit L ∗ F3LibcTlsInit L)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

section
arm64_proof_prelude

theorem f3CopyTls_ok {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.copyTlsAddr (copyTlsInstrs L))
    (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    (halign : L.builtinTlsAddr.toNat % 8 = 0)
    (hmain_nz : L.mainTlsAddr ≠ 0#64) :
    subroutine_ok P L.copyTlsAddr (f3CopyTlsSpec L) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [f3CopyTlsSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hx0, hpre⟩
  rw [sepConj_assoc] at hpre
  obtain ⟨ws, hws_len, hpre⟩ := satisfies_memRegion_words64 10 (by decide) hpre
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ |
    ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | ⟨w8, _ | ⟨w9, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> try (simp at hws_len)
  simp only [pointsToWords64_cons, pointsToWords64_nil, F3DtvZero, F3MainTlsInit, F3LibcTlsInit,
    sepConj_emp, sepConj_assoc] at hpre
  have ha1 : s0.sp - 0x50#64 + 8#64 = s0.sp - 0x48#64 := by bv_lin
  have ha2 : s0.sp - 0x48#64 + 8#64 = s0.sp - 0x40#64 := by bv_lin
  have ha3 : s0.sp - 0x40#64 + 8#64 = s0.sp - 0x38#64 := by bv_lin
  have ha4 : s0.sp - 0x38#64 + 8#64 = s0.sp - 0x30#64 := by bv_lin
  have ha5 : s0.sp - 0x30#64 + 8#64 = s0.sp - 0x28#64 := by bv_lin
  have ha6 : s0.sp - 0x28#64 + 8#64 = s0.sp - 0x20#64 := by bv_lin
  have ha7 : s0.sp - 0x20#64 + 8#64 = s0.sp - 0x18#64 := by bv_lin
  have ha8 : s0.sp - 0x18#64 + 8#64 = s0.sp - 0x10#64 := by bv_lin
  have ha9 : s0.sp - 0x10#64 + 8#64 = s0.sp - 0x08#64 := by bv_lin
  rw [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9] at hpre
  refine ⟨((s0.sp - 0x50#64) ↦₆₄ w0) ∗ ((s0.sp - 0x48#64) ↦₆₄ w1) ∗
    ((s0.sp - 0x40#64) ↦₆₄ w2) ∗ ((s0.sp - 0x38#64) ↦₆₄ w3) ∗
    ((s0.sp - 0x30#64) ↦₆₄ w4) ∗ ((s0.sp - 0x28#64) ↦₆₄ w5) ∗
    ((s0.sp - 0x20#64) ↦₆₄ w6) ∗ ((s0.sp - 0x18#64) ↦₆₄ w7) ∗
    ((s0.sp - 0x10#64) ↦₆₄ w8) ∗ ((s0.sp - 0x08#64) ↦₆₄ w9) ∗
    ((L.builtinTlsAddr + 0xc0#64) ↦₆₄ 0#64) ∗ ((L.builtinTlsAddr + 0xd0#64) ↦₆₄ 0#64) ∗
    ((L.builtinTlsAddr + 0xd8#64) ↦₆₄ 0#64) ∗ (L.mainTlsAddr ↦₆₄ 0#64) ∗
    ((L.mainTlsAddr + 0x08#64) ↦₆₄ 0#64) ∗ ((L.mainTlsAddr + 0x10#64) ↦₆₄ 0#64) ∗
    ((L.mainTlsAddr + 0x18#64) ↦₆₄ 0#64) ∗ ((L.mainTlsAddr + 0x20#64) ↦₆₄ 8#64) ∗
    ((L.mainTlsAddr + 0x28#64) ↦₆₄ 0#64) ∗ ((L.libcAddr + 0x10#64) ↦₆₄ L.mainTlsAddr) ∗
    ((L.libcAddr + 0x18#64) ↦₆₄ 0xe0#64) ∗ ((L.libcAddr + 0x20#64) ↦₆₄ 8#64) ∗
    ((L.libcAddr + 0x28#64) ↦₆₄ 1#64), by simpa only [sepConj_assoc] using hpre, ?_⟩
  have halign0 : 7#64 &&& (0xffffffffffffff38#64 - L.builtinTlsAddr) = 0#64 :=
    copyTls_align_zero halign
  have_fetches hc 0 21; wp_steps_p 16; (try simp only [halign0, BitVec.add_zero]); wp_steps_p 6
  clear_fetches 0 21; have_fetches hc 22 29; wp_step; wp_if hcbz1
  · exact absurd (by simpa [wp_norm, arm64_norm] using hcbz1) hmain_nz
  · wp_steps_p 7
    refine ops.call_memcpy (ret_pc := L.copyTlsAddr + 0x78#64)
      (dst := L.builtinTlsAddr + 0xc8#64) (src := 0#64) (bs := []) (hlen := by decide)
      (fun _ hm => by simpa only [List.length_nil, memRegion_zero, pointsToBytes_nil, emp_sepConj] using hm)
      fun sf1 hpc1 hrun1 hsp1 hcs1 _ hstd1 => ?_
    simp only [pointsToBytes_nil, emp_sepConj]
    have hstd01 : StdStatePreserved s0 sf1 := StdStatePreserved.trans (by simp [*]) hstd1
    obtain ⟨hc19, _, _, hc22, hc23, hc24, hc25, hc26, hc27, hc28, _, hcv⟩ := hcs1
    simp only [wp_norm, arm64_norm] at hc19 hc22 hc23 hc24 hc25 hc26 hc27 hc28 hcv
    have hsp1_eq : sf1.sp = s0.sp - 0x50#64 := by rw [hsp1]; simp [wp_norm, arm64_norm]
    have hsp1_align : sf1.spAligned = true := by
      simp only [State.spAligned, hsp1_eq, beq_iff_eq] at hsp_align ⊢; bv_bits
    clear_fetches 22 29; have_fetches hc 30 31; have_fetches hc 22 22; have_fetches hc 32 42
    wp_steps_p 14
    apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
    refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm],
      by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, hc27, hc28, hcv]⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm, *]⟩, ?_⟩
    simp only [wp_norm, arm64_norm] at hm ⊢
    simpa only [List.length_cons, List.length_nil, sepConj_assoc] using
      satisfies_words64_memRegion (base := s0.sp - 0x50#64)
        [s0.readReg64 .x29, s0.readReg64 .x30, s0.readReg64 .x19, s0.readReg64 .x20,
         s0.readReg64 .x21, s0.readReg64 .x22, s0.readReg64 .x23, s0.readReg64 .x24,
         s0.readReg64 .x25, s0.readReg64 .x26]
        (Rest := F3DtvInit L.builtinTlsAddr ∗ F3MainTlsInit L ∗ F3LibcTlsInit L ∗ R) (by simp)
        (by
          simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp,
            ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9,
            F3DtvInit, F3MainTlsInit, F3LibcTlsInit, arm64_norm] at hm ⊢
          ac_nf at hm ⊢)

end

private theorem bitvec_ofNat_or (w x y : Nat) :
    BitVec.ofNat w (x ||| y) = BitVec.ofNat w x ||| BitVec.ofNat w y := by ext i hi; simp
private theorem bitvec_ofNat_u8 (w : Nat) (b : BitVec 8) :
    BitVec.ofNat w b.toNat = b.zeroExtend w := by ext i hi; simp
private theorem bitvec_ofNat_u8_shl (w : Nat) (b : BitVec 8) (k : Nat) :
    BitVec.ofNat w (b.toNat <<< k) = (b.zeroExtend w) <<< k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ofNat, Nat.testBit_shiftLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.testBit_toNat, hi, decide_true, Bool.true_and]
  by_cases hk : k ≤ i
  · simp [hk, show ¬(i < k) by omega, show i - k < w by omega]
  · simp [hk, show i < k by omega]

private theorem u32_pack (b0 b1 b2 b3 : BitVec 8) :
    BitVec.ofNat 32 (b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24)) =
      b3 ++ b2 ++ b1 ++ b0 := by
  rw [bitvec_ofNat_or, bitvec_ofNat_or, bitvec_ofNat_or, bitvec_ofNat_u8,
      bitvec_ofNat_u8_shl, bitvec_ofNat_u8_shl, bitvec_ofNat_u8_shl]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append, Nat.sub_sub, hi, decide_true, Bool.true_and]
  repeat' split
  all_goals simp (discharger := omega) only [decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge,
    Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false]

private theorem listReadU32LE_lt {bs : List (BitVec 8)} {off : Nat} (hle : off + 4 ≤ bs.length) :
    listReadU32LE bs off < 2 ^ 32 := by
  have hlen : 4 ≤ (bs.drop off).length := by simp; omega
  rcases hd : bs.drop off with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩ <;>
    try (rw [hd] at hlen; simp at hlen)
  unfold listReadU32LE; rw [hd]
  have h0 : b0.toNat < 2 ^ 32 := by have := b0.isLt; omega
  have h1 : b1.toNat <<< 8 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; have := b1.isLt; omega
  have h2 : b2.toNat <<< 16 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; have := b2.isLt; omega
  have h3 : b3.toNat <<< 24 < 2 ^ 32 := by rw [Nat.shiftLeft_eq]; have := b3.isLt; omega
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow h0 h1) h2) h3

private theorem phdr_dup_u32 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (hle : off + 4 ≤ bs.length) :
    ((base ↦ᵣ bs) ∗ ((base + BitVec.ofNat 64 off) ↦₃₂ᵣ BitVec.ofNat 32 (listReadU32LE bs off))) =
      (base ↦ᵣ bs) := by
  have hlen : 4 ≤ (bs.drop off).length := by simp; omega
  rcases hd : bs.drop off with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, rest⟩⟩⟩⟩ <;>
    try (rw [hd] at hlen; simp at hlen)
  have hdup := pointsToBytesRO_dup_slice base bs off 4 hle; rw [hd] at hdup
  simp only [List.take] at hdup; rw [pointsToBytesRO4_eq_pointsTo32RO] at hdup
  have hv : BitVec.ofNat 32 (listReadU32LE bs off) = b3 ++ b2 ++ b1 ++ b0 := by
    unfold listReadU32LE; rw [hd]; exact u32_pack b0 b1 b2 b3
  rwa [hv]

private theorem phdr_dup_u64 (base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (hle : off + 8 ≤ bs.length) :
    ((base ↦ᵣ bs) ∗ ((base + BitVec.ofNat 64 off) ↦₆₄ᵣ BitVec.ofNat 64 (listReadU64LE bs off))) =
      (base ↦ᵣ bs) := by
  have hlen : 8 ≤ (bs.drop off).length := by simp; omega
  rcases hd : bs.drop off with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ |
    ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (rw [hd] at hlen; simp at hlen)
  have hdup := pointsToBytesRO_dup_slice base bs off 8 hle; rw [hd] at hdup
  simp only [List.take] at hdup; rw [pointsToBytesRO8_eq_pointsTo64RO] at hdup
  have hv : BitVec.ofNat 64 (listReadU64LE bs off) =
      b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
    unfold listReadU64LE
    rw [hd, bitvec_ofNat_or, bitvec_ofNat_or, bitvec_ofNat_or, bitvec_ofNat_or,
        bitvec_ofNat_or, bitvec_ofNat_or, bitvec_ofNat_or, bitvec_ofNat_u8,
        bitvec_ofNat_u8_shl, bitvec_ofNat_u8_shl, bitvec_ofNat_u8_shl, bitvec_ofNat_u8_shl,
        bitvec_ofNat_u8_shl, bitvec_ofNat_u8_shl, bitvec_ofNat_u8_shl]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_append, Nat.sub_sub, hi, decide_true, Bool.true_and]
    repeat' split
    all_goals simp (discharger := omega) only [decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_or, Bool.or_false]
  rwa [hv]

private theorem ofNat32_eq_iff {n c : Nat} (hn : n < 2 ^ 32) (hc : c < 2 ^ 32) :
    BitVec.ofNat 32 n = BitVec.ofNat 32 c ↔ n = c :=
  ⟨fun h => by have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hc] using this,
   fun h => h ▸ rfl⟩

private theorem f3CheckPhdrTable_entry {L : StdBinaryLayout} (h : f3CheckPhdrTable L = true)
    {i : Nat} (hi : i < L.phnum) :
    let off := i * 56
    listReadU32LE L.phdrBytes off ≠ 2 ∧
    (listReadU32LE L.phdrBytes off = 6 → listReadU64LE L.phdrBytes (off + 16) = L.phdrAddr.toNat) ∧
    (listReadU32LE L.phdrBytes off = 0x6474e551 → listReadU64LE L.phdrBytes (off + 40) = 0) ∧
    (i = L.tlsPhdrIdx →
      listReadU32LE L.phdrBytes off = 7 ∧
      listReadU64LE L.phdrBytes (off + 16) = 0 ∧
      listReadU64LE L.phdrBytes (off + 32) = 0 ∧
      listReadU64LE L.phdrBytes (off + 40) = 0 ∧
      listReadU64LE L.phdrBytes (off + 48) = 0) ∧
    (i ≠ L.tlsPhdrIdx → listReadU32LE L.phdrBytes off ≠ 7) := by
  unfold f3CheckPhdrTable at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne, beq_iff_eq] at h
  have hent := h.2 i hi; dsimp only at hent ⊢
  refine ⟨hent.1.1.1, fun h6 => ?_, fun hst => ?_, fun heq => ?_, fun hne => ?_⟩
  · have := hent.1.1.2; simp [h6] at this; exact this
  · have := hent.1.2; simp [hst] at this; exact this
  · subst heq; have := hent.2; simp at this
    rcases this with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · have := hent.2; simp [hne] at this; exact this

private theorem f3CheckPhdrTable_hdr {L : StdBinaryLayout} (h : f3CheckPhdrTable L = true) :
    0 < L.phnum ∧ L.phdrAddr.toNat % 8 = 0 ∧ L.phdrBytes.length = L.phnum * 56 ∧
    0 < L.tlsPhdrIdx ∧ L.tlsPhdrIdx < L.phnum ∧
    listReadU32LE L.phdrBytes 0 = 6 ∧ listReadU64LE L.phdrBytes 16 = L.phdrAddr.toNat := by
  have hraw := h; unfold f3CheckPhdrTable at hraw
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hraw
  have hpos : 0 < L.phnum := hraw.1.1.1.1.1.1
  have hp0 : listReadU32LE L.phdrBytes 0 = 6 := hraw.1.1.2
  have htls_pos : 0 < L.tlsPhdrIdx := Classical.byContradiction fun hz => by
    have h7 := ((f3CheckPhdrTable_entry h hpos).2.2.2.1 (by omega : 0 = L.tlsPhdrIdx)).1
    rw [Nat.zero_mul, hp0] at h7; omega
  exact ⟨hpos, hraw.1.1.1.1.1.2, hraw.1.1.1.1.2, htls_pos, hraw.1.1.1.2, hp0, hraw.1.2⟩

section
arm64_proof_prelude

private theorem f3StaticInitTls_phdr_loop {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.staticInitTlsAddr (staticInitTlsInstrs L))
    (hphdr : f3CheckPhdrTable L = true)
    (hphdr_end : L.phdrAddr.toNat + L.phnum * 56 < 2 ^ 64)
    (auxPtr : BitVec 64) :
    ∀ (rem idx : Nat), 1 ≤ idx → idx + rem = L.phnum →
      ∀ {target_pc : BitVec 64} (s : State) (F : SepProp)
        {post : State → SepProp → Prop} {oom : State → SepProp},
        s.pc = L.staticInitTlsAddr + 0x54#64 → s.status = .Running → s.spAligned = true →
        s.readReg64 .x0 = auxPtr →
        s.readReg64 .x1 = L.phdrAddr + BitVec.ofNat 64 ((idx - 1) * 56) →
        s.readReg64 .x3 = 0#64 →
        s.readReg64 .x4 = BitVec.ofNat 64 (rem + 1) →
        s.readReg64 .x6 =
          (if L.tlsPhdrIdx < idx then L.phdrAddr + BitVec.ofNat 64 (L.tlsPhdrIdx * 56) else 0#64) →
        s.readReg64 .x7 = L.defaultStacksizeAddr →
        s.readReg64 .x9 = L.phdrAddr →
        s.readReg64 .x10 = 0x6474e551#64 →
        (∀ sf : State, sf.pc = L.staticInitTlsAddr + 0xb0#64 → sf.status = .Running →
          sf.sp = s.sp → CalleeSavedPreserved s sf → sf.mem = s.mem → StdStatePreserved s sf →
          sf.readReg64 .x3 = 0#64 →
          sf.readReg64 .x6 = L.phdrAddr + BitVec.ofNat 64 (L.tlsPhdrIdx * 56) →
          SepWP P target_pc sf
            (((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
              (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ F) post oom) →
        SepWP P target_pc s
          (((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
            (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ F) post oom := by
  obtain ⟨_, _, hplen, _, htls_lt, _, _⟩ := f3CheckPhdrTable_hdr hphdr
  intro rem; induction rem with
  | zero =>
    intro idx hidx1 hsum target_pc s F post oom hpc hrun hsp hx0 hx1 hx3 hx4 hx6 hx7 hx9 hx10 hnext
    have hidx_eq : idx = L.phnum := by omega
    have_fetches hc 21 24; wp_steps_p 4
    exact hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [wp_norm, arm64_norm]) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [*]) (by simp [wp_norm, arm64_norm, hx3])
      (by simp [wp_norm, arm64_norm, hx6, hidx_eq, htls_lt])
  | succ rem' ih =>
    intro idx hidx1 hsum target_pc s F post oom hpc hrun hsp hx0 hx1 hx3 hx4 hx6 hx7 hx9 hx10 hnext
    have hidx_lt : idx < L.phnum := by omega
    have hent := f3CheckPhdrTable_entry hphdr hidx_lt
    have hx4_sub : BitVec.ofNat 64 (rem' + 1 + 1) - 1#64 = BitVec.ofNat 64 (rem' + 1) := by
      rw [show BitVec.ofNat 64 (rem' + 1 + 1) = BitVec.ofNat 64 (rem' + 1) + 1#64 by simp [BitVec.ofNat_add]]
      bv_lin
    have hx4_nz : BitVec.ofNat 64 (rem' + 1) ≠ 0#64 := by
      intro hz; have := congrArg BitVec.toNat hz
      simp [Nat.mod_eq_of_lt (by omega : rem' + 1 < 2 ^ 64)] at this
    have hx1_next : L.phdrAddr + BitVec.ofNat 64 ((idx - 1) * 56) + 56#64 =
        L.phdrAddr + BitVec.ofNat 64 (idx * 56) := by
      rw [BitVec.add_assoc, show (56#64 : BitVec 64) = BitVec.ofNat 64 56 from rfl,
          ← BitVec.ofNat_add, show (idx - 1) * 56 + 56 = idx * 56 by omega]
    have hx6_of_ne (hne : idx ≠ L.tlsPhdrIdx) :
        (if L.tlsPhdrIdx < idx then L.phdrAddr + BitVec.ofNat 64 (L.tlsPhdrIdx * 56) else 0#64) =
          (if L.tlsPhdrIdx < idx + 1 then L.phdrAddr + BitVec.ofNat 64 (L.tlsPhdrIdx * 56) else 0#64) := by
      by_cases hlt : L.tlsPhdrIdx < idx <;> simp [hlt, show L.tlsPhdrIdx < idx + 1 ↔ L.tlsPhdrIdx < idx by omega]
    have_fetches hc 15 29; have_fetches hc 34 39; wp_steps_p 3; wp_step; wp_if hcbz
    · exact absurd (by simpa [wp_norm, arm64_norm, hx4_sub] using hcbz) hx4_nz
    · have hdup_pt := phdr_dup_u32 L.phdrAddr L.phdrBytes (idx * 56) (by omega)
      have hpt_lt := listReadU32LE_lt (bs := L.phdrBytes) (off := idx * 56) (by omega)
      (wp_conv_pre => rw [← hdup_pt]); wp_steps_p 2; wp_step; (wp_conv_pre => rw [hdup_pt])
      wp_if heq6
      · have hpt6 : listReadU32LE L.phdrBytes (idx * 56) = 6 := by
          (try simp only [wp_norm, arm64_norm, hx1_next] at heq6)
          exact (ofNat32_eq_iff hpt_lt (by decide)).mp heq6
        have hdup_pv := phdr_dup_u64 L.phdrAddr L.phdrBytes (idx * 56 + 16) (by omega)
        rw [hent.2.1 hpt6, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_add] at hdup_pv
        (wp_conv_pre => rw [← hdup_pv]); wp_steps_p 3; (wp_conv_pre => rw [hdup_pv])
        have hx6_next := hx6_of_ne (fun heq => by have := (hent.2.2.2.1 heq).1; omega)
        refine ih (idx + 1) (by omega) (by omega) _ F
          (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
          (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp)
          (by simp [wp_norm, arm64_norm, hx0])
          (by simp only [Nat.add_sub_cancel, wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
          (by simp [wp_norm, arm64_norm, hx6, hx6_next]) (by simp [wp_norm, arm64_norm, hx7])
          (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10])
          fun sf hpc_f hrun_f hsp_f hcs_f hmem_f hstd_f hx3_f hx6_f =>
            hnext sf hpc_f hrun_f (by simpa only [wp_norm, arm64_norm] using hsp_f)
              (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
              (by simpa only [wp_norm, arm64_norm] using hmem_f)
              (StdStatePreserved.trans (by simp [*]) hstd_f) hx3_f hx6_f
      · wp_steps_p 1; wp_step; wp_if hne2
        · wp_steps_p 1; wp_step; wp_if hne7
          · have hpt_ne7 : listReadU32LE L.phdrBytes (idx * 56) ≠ 7 :=
              fun h7 => hne7 (by simp [wp_norm, arm64_norm, h7])
            have hx6_next := hx6_of_ne (fun heq => hpt_ne7 (hent.2.2.2.1 heq).1)
            wp_steps_p 1; wp_step; wp_if hne_st
            · refine ih (idx + 1) (by omega) (by omega) _ F
                (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
                (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp)
                (by simp [wp_norm, arm64_norm, hx0])
                (by simp only [Nat.add_sub_cancel, wp_norm, arm64_norm])
                (by simp [wp_norm, arm64_norm, hx3]) (by simp only [wp_norm, arm64_norm])
                (by simp [wp_norm, arm64_norm, hx6, hx6_next]) (by simp [wp_norm, arm64_norm, hx7])
                (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10])
                fun sf hpc_f hrun_f hsp_f hcs_f hmem_f hstd_f hx3_f hx6_f =>
                  hnext sf hpc_f hrun_f (by simpa only [wp_norm, arm64_norm] using hsp_f)
                    (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
                    (by simpa only [wp_norm, arm64_norm] using hmem_f)
                    (StdStatePreserved.trans (by simp [*]) hstd_f) hx3_f hx6_f
            · have hpt_st : listReadU32LE L.phdrBytes (idx * 56) = 0x6474e551 := by
                (try simp only [wp_norm, arm64_norm, Classical.not_not] at hne_st)
                exact (ofNat32_eq_iff hpt_lt (by decide)).mp hne_st
              have hdup_msz := phdr_dup_u64 L.phdrAddr L.phdrBytes (idx * 56 + 40) (by omega)
              rw [hent.2.2.1 hpt_st, BitVec.ofNat_add] at hdup_msz
              (wp_conv_pre => rw [← hdup_msz]); wp_steps_p 4; (wp_conv_pre => rw [hdup_msz])
              refine ih (idx + 1) (by omega) (by omega) _ F
                (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
                (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp)
                (by simp [wp_norm, arm64_norm, hx0])
                (by simp only [Nat.add_sub_cancel, wp_norm, arm64_norm])
                (by simp [wp_norm, arm64_norm, hx3]) (by simp only [wp_norm, arm64_norm])
                (by simp [wp_norm, arm64_norm, hx6, hx6_next]) (by simp [wp_norm, arm64_norm, hx7])
                (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10])
                fun sf hpc_f hrun_f hsp_f hcs_f hmem_f hstd_f hx3_f hx6_f =>
                  hnext sf hpc_f hrun_f (by simpa only [wp_norm, arm64_norm] using hsp_f)
                    (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
                    (by simpa only [wp_norm, arm64_norm] using hmem_f)
                    (StdStatePreserved.trans (by simp [*]) hstd_f) hx3_f hx6_f
          · have hpt7 : listReadU32LE L.phdrBytes (idx * 56) = 7 := by
              (try simp only [wp_norm, arm64_norm, Classical.not_not] at hne7)
              exact (ofNat32_eq_iff hpt_lt (by decide)).mp hne7
            wp_steps_p 1
            have hidx_tls : idx = L.tlsPhdrIdx := Classical.byContradiction fun hne =>
              hent.2.2.2.2 hne hpt7
            refine ih (idx + 1) (by omega) (by omega) _ F
              (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
              (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp)
              (by simp [wp_norm, arm64_norm, hx0])
              (by simp only [Nat.add_sub_cancel, wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hx3]) (by simp only [wp_norm, arm64_norm])
              (by simp [wp_norm, arm64_norm, hidx_tls]) (by simp [wp_norm, arm64_norm, hx7])
              (by simp [wp_norm, arm64_norm, hx9]) (by simp [wp_norm, arm64_norm, hx10])
              fun sf hpc_f hrun_f hsp_f hcs_f hmem_f hstd_f hx3_f hx6_f =>
                hnext sf hpc_f hrun_f (by simpa only [wp_norm, arm64_norm] using hsp_f)
                  (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs_f)
                  (by simpa only [wp_norm, arm64_norm] using hmem_f)
                  (StdStatePreserved.trans (by simp [*]) hstd_f) hx3_f hx6_f
        · exfalso; apply hent.1
          (try simp only [wp_norm, arm64_norm, Classical.not_not] at hne2)
          exact (ofNat32_eq_iff hpt_lt (by decide)).mp hne2

private theorem f3StaticInitTls_setup {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.staticInitTlsAddr (staticInitTlsInstrs L))
    (hphdr : f3CheckPhdrTable L = true)
    (hphdr_end : L.phdrAddr.toNat + L.phnum * 56 < 2 ^ 64)
    {target_pc : BitVec 64} (s : State) (F : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = L.staticInitTlsAddr + 0xb0#64) (hrun : s.status = .Running)
    (hx3 : s.readReg64 .x3 = 0#64)
    (hx6 : s.readReg64 .x6 = L.phdrAddr + BitVec.ofNat 64 (L.tlsPhdrIdx * 56))
    (hnext : ∀ sf : State, sf.pc = L.staticInitTlsAddr + 0x190#64 → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → StdStatePreserved s sf →
      sf.readReg64 .x0 = L.builtinTlsAddr →
      SepWP P target_pc sf ((L.phdrAddr ↦ᵣ L.phdrBytes) ∗ F3MainTlsInit L ∗ F3LibcTlsInit L ∗ F) post oom) :
    SepWP P target_pc s ((L.phdrAddr ↦ᵣ L.phdrBytes) ∗ StdMainTlsZero L ∗ StdLibcTlsZero L ∗ F) post oom := by
  obtain ⟨_, _, hplen, htls_pos, htls_lt, _, _⟩ := f3CheckPhdrTable_hdr hphdr
  obtain ⟨_, hpv, hfsz, hmsz, haln⟩ := (f3CheckPhdrTable_entry hphdr htls_lt).2.2.2.1 rfl
  have hx6_nz : L.phdrAddr + BitVec.ofNat 64 (L.tlsPhdrIdx * 56) ≠ 0#64 := by
    intro hz; have htn := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : L.tlsPhdrIdx * 56 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : L.phdrAddr.toNat + L.tlsPhdrIdx * 56 < 2 ^ 64)] at htn
    omega
  have hdup16 := phdr_dup_u64 L.phdrAddr L.phdrBytes (L.tlsPhdrIdx * 56 + 16) (by omega)
  rw [hpv, BitVec.ofNat_add, ← BitVec.add_assoc] at hdup16
  have hdup32 := phdr_dup_u64 L.phdrAddr L.phdrBytes (L.tlsPhdrIdx * 56 + 32) (by omega)
  rw [hfsz, BitVec.ofNat_add, ← BitVec.add_assoc] at hdup32
  have hdup40 := phdr_dup_u64 L.phdrAddr L.phdrBytes (L.tlsPhdrIdx * 56 + 40) (by omega)
  rw [hmsz, BitVec.ofNat_add, ← BitVec.add_assoc] at hdup40
  have hdup48 := phdr_dup_u64 L.phdrAddr L.phdrBytes (L.tlsPhdrIdx * 56 + 48) (by omega)
  rw [haln, BitVec.ofNat_add, ← BitVec.add_assoc] at hdup48
  (wp_conv_pre => simp only [StdMainTlsZero, StdLibcTlsZero, sepConj_assoc])
  have_fetches hc 44 79; have_fetches hc 93 99
  wp_steps_p 1; wp_step; wp_if hcbz
  · exact absurd (by simpa [wp_norm, arm64_norm, hx6] using hcbz) hx6_nz
  · (wp_conv_pre => rw [← hdup16]); wp_steps_p 6
    (wp_conv_pre => rw [hdup16, ← hdup32]); wp_steps_p 2
    (wp_conv_pre => rw [hdup32, ← hdup48]); wp_steps_p 3
    (wp_conv_pre => rw [hdup48, ← hdup40]); wp_steps_p 1
    (wp_conv_pre => rw [hdup40]); wp_steps_p 28
    exact SepWP.weaken_pre
      (P' := (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ F3MainTlsInit L ∗ F3LibcTlsInit L ∗ F)
      (by dsimp only [F3MainTlsInit, F3LibcTlsInit]; sep_entail)
      (hnext _ (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
        (by simp [wp_norm, arm64_norm]) (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
        (by simp [*]) (by simp [wp_norm, arm64_norm]))

private theorem f3StaticInitTls_prologue {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.staticInitTlsAddr (staticInitTlsInstrs L))
    (hphdr : f3CheckPhdrTable L = true)
    (hphdr_end : L.phdrAddr.toNat + L.phnum * 56 < 2 ^ 64)
    {target_pc : BitVec 64} (s0 : State) (auxPtr w0 w1 : BitVec 64) (F : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s0.pc = L.staticInitTlsAddr) (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true) (hx0 : s0.readReg64 .x0 = auxPtr)
    (hnext : ∀ sf1 : State, sf1.pc = L.staticInitTlsAddr + 0xb0#64 → sf1.status = .Running →
      sf1.sp = s0.sp - 0x10#64 → CalleeSavedPreserved (s0.writeReg64 .x29 (s0.sp - 0x10#64)) sf1 →
      StdStatePreserved s0 sf1 → sf1.readReg64 .x3 = 0#64 →
      sf1.readReg64 .x6 = L.phdrAddr + BitVec.ofNat 64 (L.tlsPhdrIdx * 56) →
      SepWP P target_pc sf1
        (((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((auxPtr + 0x18#64) ↦₆₄ L.phdrAddr) ∗ ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗
         ((auxPtr + 0x28#64) ↦₆₄ BitVec.ofNat 64 L.phnum) ∗
         (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
         (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ F) post oom) :
    SepWP P target_pc s0
      (((s0.sp - 0x10#64) ↦₆₄ w0) ∗ ((s0.sp - 0x08#64) ↦₆₄ w1) ∗
       ((auxPtr + 0x18#64) ↦₆₄ L.phdrAddr) ∗ ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗
       ((auxPtr + 0x28#64) ↦₆₄ BitVec.ofNat 64 L.phnum) ∗
       (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
       (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ F) post oom := by
  obtain ⟨hph_pos, _, hplen, htls_pos, _, hp0_t, hp0_v⟩ := f3CheckPhdrTable_hdr hphdr
  have hph_nz : BitVec.ofNat 64 L.phnum ≠ 0#64 := by
    intro hz; have := congrArg BitVec.toNat hz
    simp [Nat.mod_eq_of_lt (by omega : L.phnum < 2 ^ 64)] at this; omega
  have hdup0_pt := phdr_dup_u32 L.phdrAddr L.phdrBytes 0 (by omega)
  simp only [hp0_t, BitVec.add_zero] at hdup0_pt
  have hdup0_pv := phdr_dup_u64 L.phdrAddr L.phdrBytes 16 (by omega)
  simp only [hp0_v, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hdup0_pv
  have_fetches hc 0 17; have_fetches hc 24 27; wp_steps_p 15; wp_step; wp_if hcbz0
  · exact absurd (by simpa [wp_norm, arm64_norm] using hcbz0) hph_nz
  · (wp_conv_pre => rw [← hdup0_pt]); wp_steps_p 3
    (wp_conv_pre => rw [hdup0_pt, ← hdup0_pv]); wp_steps_p 3
    (wp_conv_pre => rw [hdup0_pv])
    have hsp_sub10_al : (s0.sp - 0x10#64) &&& 15#64 = 0#64 := by
      simp only [State.spAligned, beq_iff_eq] at hsp_align; bv_bits
    refine SepWP.weaken_pre
      (P' := ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
        (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ ?F_loop) (by sep_frame) ?_
    refine f3StaticInitTls_phdr_loop hc hphdr hphdr_end auxPtr (L.phnum - 1) 1 (by omega) (by omega) _ _
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (by simp [State.spAligned, wp_norm, arm64_norm, hsp_sub10_al])
      (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, Nat.sub_add_cancel hph_pos])
      (by simp [wp_norm, arm64_norm, show ¬(L.tlsPhdrIdx < 1) by omega])
      (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      (by simp [wp_norm, arm64_norm]) fun sf1 hpc1 hrun1 hsp1 hcs1 _ hstd1 hx3_1 hx6_1 => ?_
    refine SepWP.weaken_pre
      (P' := ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
        ((auxPtr + 0x18#64) ↦₆₄ L.phdrAddr) ∗ ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗
        ((auxPtr + 0x28#64) ↦₆₄ BitVec.ofNat 64 L.phnum) ∗
        (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
        (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ F) (by sep_entail)
      (hnext sf1 hpc1 hrun1 (by simpa [wp_norm, arm64_norm] using hsp1)
        (CalleeSavedPreserved.trans (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm]) hcs1)
        (StdStatePreserved.trans (by simp [*]) hstd1) hx3_1 hx6_1)

end

private theorem aux_words_split (p a0 a1 a2 a3 a4 a5 : BitVec 64) (tl : List (BitVec 64)) :
    (p ↦₆₄* (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: tl)) =
      (p ↦₆₄ a0) ∗ ((p + 0x08#64) ↦₆₄ a1) ∗ ((p + 0x10#64) ↦₆₄ a2) ∗
      ((p + 0x18#64) ↦₆₄ a3) ∗ ((p + 0x20#64) ↦₆₄ a4) ∗ ((p + 0x28#64) ↦₆₄ a5) ∗
      ((p + 0x30#64) ↦₆₄* tl) := by
  simp only [pointsToWords64_cons, BitVec.add_assoc]; rfl

/-- Total-correctness contract for `musl` `static_init_tls(aux)` under `PT_TLS` `0/0/0/0`. -/
def f3StaticInitTlsSpec (L : StdBinaryLayout) :
    Spec (BitVec 64 × List (BitVec 64) × BitVec 8 × BitVec 64) where
  pre := fun (auxPtr, aux, canDo0, sysinfoVal) s0 =>
    ⌜s0.readReg64 .x0 = auxPtr ∧ aux[3]? = some L.phdrAddr ∧
      aux[4]? = some 56#64 ∧ aux[5]? = some (BitVec.ofNat 64 L.phnum)⌝ ∗
    (memRegion (s0.sp - 0x60#64) 0x60 ∗ (auxPtr ↦₆₄* aux) ∗
     (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
     (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗
     StdTlsGlobals L ∗ (L.libcAddr ↦₈ canDo0) ∗ StdLibcTlsZero L)
  post := fun (auxPtr, aux, _, sysinfoVal) s0 sf =>
    ⌜sf.tpidrEl0 = L.builtinTlsAddr + 0xc8#64 ∧ StdTlsFieldsPreserved s0 sf⌝ ∗
    (((sf.tpidrEl0 - 0xa4#64) ↦₃₂ 0#32) ∗ (L.libcAddr ↦₈ 1#8) ∗
     memRegion (sf.sp - 0x60#64) 0x60 ∗ (auxPtr ↦₆₄* aux) ∗
     (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ (L.gotAddr ↦₆₄ 0#64) ∗
     (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗ (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗
     F3TlsState L sysinfoVal)
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

section
arm64_proof_prelude

/-- Verify `static_init_tls` (`108` insns) at `L.staticInitTlsAddr` for `PT_TLS` `0/0/0/0`,
    parameterized over `hinitTp : subroutine_ok P L.initTpAddr (stdInitTpSpec L)`. -/
theorem f3StaticInitTls_of_initTp {P : Program} {L : StdBinaryLayout}
    (hc_static : hasInstrs P L.staticInitTlsAddr (staticInitTlsInstrs L))
    (hc_copy : hasInstrs P L.copyTlsAddr (copyTlsInstrs L))
    (hinitTp : subroutine_ok P L.initTpAddr (stdInitTpSpec L))
    (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    (hphdr : f3CheckPhdrTable L = true)
    (hphdr_end : L.phdrAddr.toNat + L.phnum * 56 < 2 ^ 64)
    (halign : L.builtinTlsAddr.toNat % 8 = 0)
    (hmain_nz : L.mainTlsAddr ≠ 0#64) :
    subroutine_ok P L.staticInitTlsAddr (f3StaticInitTlsSpec L) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨auxPtr, aux, canDo0, sysinfoVal⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [f3StaticInitTlsSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, haux3, haux4, haux5⟩, hpre⟩
  rcases aux with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, auxTl⟩⟩⟩⟩⟩⟩ <;>
    try (simp at haux3 haux4 haux5)
  subst haux3 haux4 haux5
  have hsp50 : s0.sp - 0x60#64 + 0x50#64 = s0.sp - 0x10#64 := by bv_lin
  have hsp30 : s0.sp - 0x60#64 + 0x30#64 = s0.sp - 0x30#64 := by bv_lin
  have hsp10_8 : s0.sp - 0x10#64 + 8#64 = s0.sp - 0x08#64 := by bv_lin
  have hmr60 : memRegion (s0.sp - 0x60#64) 0x60 =
      memRegion (s0.sp - 0x60#64) 0x50 ∗ memRegion (s0.sp - 0x10#64) 0x10 := by
    simpa only [hsp50] using memRegion_split_le (s0.sp - 0x60#64) 0x50 0x60 (by decide) (by decide)
  have hmr50 : memRegion (s0.sp - 0x60#64) 0x50 =
      memRegion (s0.sp - 0x60#64) 0x30 ∗ memRegion (s0.sp - 0x30#64) 0x20 := by
    simpa only [hsp30] using memRegion_split_le (s0.sp - 0x60#64) 0x30 0x50 (by decide) (by decide)
  simp only [hmr60, sepConj_assoc] at hpre
  rw [sepConj_left_comm (memRegion (s0.sp - 0x60#64) 0x50)] at hpre
  obtain ⟨ws, hws_len, hpre⟩ := satisfies_memRegion_words64 2 (by decide) hpre
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | _⟩⟩ <;> try (simp at hws_len)
  rw [aux_words_split, f3TlsGlobals_split] at hpre
  simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, hsp10_8, sepConj_assoc] at hpre
  refine ⟨((s0.sp - 0x10#64) ↦₆₄ w0) ∗ ((s0.sp - 0x08#64) ↦₆₄ w1) ∗
    ((auxPtr + 0x18#64) ↦₆₄ L.phdrAddr) ∗ ((auxPtr + 0x20#64) ↦₆₄ 56#64) ∗
    ((auxPtr + 0x28#64) ↦₆₄ BitVec.ofNat 64 L.phnum) ∗ (L.phdrAddr ↦ᵣ L.phdrBytes) ∗
    (L.gotAddr ↦₆₄ 0#64) ∗ (L.defaultStacksizeAddr ↦₃₂ 0x20000#32) ∗
    memRegion (s0.sp - 0x60#64) 0x50 ∗ (auxPtr ↦₆₄ a0) ∗ ((auxPtr + 0x08#64) ↦₆₄ a1) ∗
    ((auxPtr + 0x10#64) ↦₆₄ a2) ∗ ((auxPtr + 0x30#64) ↦₆₄* auxTl) ∗
    (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ StdTdZero L.builtinTlsAddr ∗ F3DtvZero L.builtinTlsAddr ∗
    ((L.builtinTlsAddr + 0x24#64) ↦₃₂ 0#32) ∗ F3BuiltinTlsPad L.builtinTlsAddr ∗
    StdMainTlsZero L ∗ (L.libcAddr ↦₈ canDo0) ∗ StdLibcTlsZero L,
    by dsimp only [StdMainTlsZero, StdLibcTlsZero] at hpre ⊢; ac_nf at hpre ⊢, ?_⟩
  have hsp_sub10_al : (s0.sp - 0x10#64) &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp_align; bv_bits
  refine f3StaticInitTls_prologue hc_static hphdr hphdr_end s0 auxPtr w0 w1 _ hpc hrun hsp_align hx0
    fun sf1 hpc1 hrun1 hsp1_eq hcs01 hstd01 hx3_1 hx6_1 => ?_
  refine SepWP.weaken_pre
    (P' := (L.phdrAddr ↦ᵣ L.phdrBytes) ∗ StdMainTlsZero L ∗ StdLibcTlsZero L ∗ ?F_setup)
    (by dsimp only [StdMainTlsZero, StdLibcTlsZero]; sep_frame) ?_
  refine f3StaticInitTls_setup hc_static hphdr hphdr_end sf1 _ hpc1 hrun1 hx3_1 hx6_1
    fun sf2 hpc2 hrun2 hsp2 hcs2 hstd2 hx0_2 => ?_
  have hstd02 : StdStatePreserved s0 sf2 := StdStatePreserved.trans hstd01 hstd2
  have hsp2_eq : sf2.sp = s0.sp - 0x10#64 := hsp2.trans hsp1_eq
  have hsp2_50 : sf2.sp - 0x50#64 = s0.sp - 0x60#64 := by rw [hsp2_eq]; bv_lin
  have_fetches hc_static 100 104; wp_steps_p 1
  refine SepWP.call_subroutine_frame (ret_pc := L.staticInitTlsAddr + 0x194#64)
    (f3CopyTls_ok hc_copy ops halign hmain_nz) (x := ()) (F := ?F_copy)
    (by simp [wp_norm, arm64_norm]; bv_lin) (by simp [wp_norm, arm64_norm, hrun2])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp2_eq, hsp_sub10_al])
    (by simp [wp_norm, arm64_norm])
    (by dsimp only [f3CopyTlsSpec, F3DtvZero, F3MainTlsInit, F3LibcTlsInit]
        simp only [wp_norm, arm64_norm, hx0_2, hsp2_50]; sep_frame)
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun sf3 hpc3 hrun3 hsp3 hcs3 => ?_
  dsimp only [f3CopyTlsSpec]; (wp_conv_pre => rw [sepConj_assoc])
  apply SepWP.pure_elim; rintro ⟨hx0_3, hstd3⟩
  have hstd03 : StdStatePreserved s0 sf3 :=
    StdStatePreserved.trans (StdStatePreserved.trans hstd02 (by simp [*])) hstd3
  have hsp3_eq : sf3.sp = s0.sp - 0x10#64 := by simpa [wp_norm, arm64_norm, hsp2_eq] using hsp3
  have hsp3_50 : sf3.sp - 0x50#64 = s0.sp - 0x60#64 := by rw [hsp3_eq]; bv_lin
  have hsp3_20 : sf3.sp - 0x20#64 = s0.sp - 0x30#64 := by rw [hsp3_eq]; bv_lin
  (wp_conv_pre => simp only [hsp3_50, hmr50, sepConj_assoc]); wp_steps_p 1
  refine SepWP.call_subroutine_frame (ret_pc := L.staticInitTlsAddr + 0x198#64)
    hinitTp (x := (canDo0, sysinfoVal)) (F := ?F_init)
    (by simp [wp_norm, arm64_norm]; bv_lin) (by simp [wp_norm, arm64_norm, hrun3])
    (by simp [State.spAligned, wp_norm, arm64_norm, hsp3_eq, hsp_sub10_al])
    (by simp [wp_norm, arm64_norm])
    (by dsimp only [stdInitTpSpec, StdTdZero]
        simp only [wp_norm, arm64_norm, hx0_3, hsp3_20]; sep_frame)
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun sf4 hpc4 hrun4 hsp4 hcs4 => ?_
  dsimp only [stdInitTpSpec]; (wp_conv_pre => rw [sepConj_assoc])
  apply SepWP.pure_elim; rintro ⟨htp4, hx0_4, htls4⟩
  simp only [arm64_norm] at hx0_4
  have htls04 : StdTlsFieldsPreserved s0 sf4 :=
    StdTlsFieldsPreserved.trans
      (StdStatePreserved.toTlsFields (StdStatePreserved.trans hstd03 (by simp [*]))) htls4
  have hsp4_eq : sf4.sp = s0.sp - 0x10#64 := by simpa [wp_norm, arm64_norm, hsp3_eq] using hsp4
  have hsp4_al : sf4.spAligned = true := by simp [State.spAligned, hsp4_eq, hsp_sub10_al]
  have hsp4_20 : sf4.sp - 0x20#64 = s0.sp - 0x30#64 := by rw [hsp4_eq]; bv_lin
  (wp_conv_pre => simp only [hsp4_20]); wp_steps_p 3
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun4])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, htp4],
      htls04.trans (StdStatePreserved.toTlsFields (by simp [*]))⟩, ?_⟩
    have herr_addr : L.builtinTlsAddr + 0xc8#64 - 0xa4#64 = L.builtinTlsAddr + 0x24#64 := by bv_lin
    have hpack10 : (((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 30#5))) ⊢
        memRegion (s0.sp - 0x10#64) 0x10 := by
      simpa only [pointsToWords64_cons, pointsToWords64_nil, List.length_cons, List.length_nil,
        sepConj_emp, hsp10_8] using
        pointsToWords64_entails_memRegion
          [s0.readReg64 (.gpr 29#5), s0.readReg64 (.gpr 30#5)] (s0.sp - 0x10#64) (by simp)
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    simp only [wp_norm, arm64_norm, htp4, herr_addr, hmr60, hmr50, aux_words_split, F3TlsState]
    refine Entails.trans
      (Q := (((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
        ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 30#5))) ∗ ?F_pack)
      (by sep_frame)
      (Entails.trans (sepConj_mono_left hpack10) (by sep_entail))
  · obtain ⟨g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, _, gv⟩ :=
      CalleeSavedPreserved.trans
        (CalleeSavedPreserved.trans
          (CalleeSavedPreserved.trans
            (CalleeSavedPreserved.trans
              (CalleeSavedPreserved.trans hcs01 hcs2)
              (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])) hcs3)
          (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])) hcs4
    simp only [wp_norm, arm64_norm] at g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 gv
    simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, g19, g20, g21, g22, g23, g24, g25, g26,
      g27, g28, gv]

theorem f3StaticInitTls_ok {P : Program} {L : StdBinaryLayout}
    (hc_static : hasInstrs P L.staticInitTlsAddr (staticInitTlsInstrs L))
    (hc_copy : hasInstrs P L.copyTlsAddr (copyTlsInstrs L))
    (hc_init : hasInstrs P L.initTpAddr (initTpInstrs L))
    (hc_set : P.hasCode L.setThreadAreaAddr setThreadAreaWords)
    (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    (hsvc : P.svc = Syscall.standard)
    (hphdr : f3CheckPhdrTable L = true)
    (hphdr_end : L.phdrAddr.toNat + L.phnum * 56 < 2 ^ 64)
    (halign : L.builtinTlsAddr.toNat % 8 = 0)
    (hmain_nz : L.mainTlsAddr ≠ 0#64) :
    subroutine_ok P L.staticInitTlsAddr (f3StaticInitTlsSpec L) :=
  f3StaticInitTls_of_initTp hc_static hc_copy (initTp_ok hc_init (setThreadArea_ok hc_set) hsvc)
    ops hphdr hphdr_end halign hmain_nz

end

/-- Minimal syscall handler accepting only `SYS_set_tid_address` (`x8 = 96`) and faulting on every
other `svc #0`, proving no other syscall occurs during stage-1/stage-2 startup. -/
def f3SetTidOnlySvc (s : State) : State :=
  if s.readReg64 .x8 == 96#64 then execSetTidAddress s
  else s.setStatus (.Exception "unexpected syscall in F3 startup")

private theorem evalInst_f3SetTidOnly_of_x8 {P : Program} {s : State}
    (hsvc : P.svc = f3SetTidOnlySvc) (hx8 : s.readReg64 .x8 = 96#64) :
    P.evalInst (.system false 0#16) s = execSetTidAddress s := by
  simp only [Program.evalInst, execInstWithSvc, evalSvc, hsvc, f3SetTidOnlySvc, hx8,
    beq_self_eq_true, ↓reduceIte]
  cases s with | _ _ _ _ _ _ mem =>
  cases mem
  simp [execSetTidAddress, State.writeReg64, State.advancePC]

section
arm64_proof_prelude

@[local simp] private theorem tlsFields_rfl' (s : State) : StdTlsFieldsPreserved s s := .rfl s
@[local simp] private theorem tlsFields_writeReg64' (s0 s : State) (r : Reg) (v : BitVec 64) :
    StdTlsFieldsPreserved s0 (s.writeReg64 r v) ↔ StdTlsFieldsPreserved s0 s := by
  cases r <;> simp [State.writeReg64, StdTlsFieldsPreserved]
@[local simp] private theorem tlsFields_writeReg32' (s0 s : State) (r : Reg) (v : BitVec 32) :
    StdTlsFieldsPreserved s0 (s.writeReg32 r v) ↔ StdTlsFieldsPreserved s0 s := by
  simp [State.writeReg32]
@[local simp] private theorem tlsFields_setPState' (s0 s : State) (p : PState) :
    StdTlsFieldsPreserved s0 (s.setPState p) ↔ StdTlsFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem tlsFields_advancePC' (s0 s : State) :
    StdTlsFieldsPreserved s0 s.advancePC ↔ StdTlsFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem tlsFields_setPC' (s0 s : State) (pc : BitVec 64) :
    StdTlsFieldsPreserved s0 (s.setPC pc) ↔ StdTlsFieldsPreserved s0 s := Iff.rfl
@[local simp] private theorem tlsFields_setMem' {s0 s : State} {m : Memory} (hp : m.perm = s.mem.perm) :
    StdTlsFieldsPreserved s0 (s.setMem m) ↔ StdTlsFieldsPreserved s0 s := by
  simp [State.setMem, StdTlsFieldsPreserved, hp]

/-- Verify `__init_tp` (`36` insns, `34` executed) at `L.initTpAddr` under `f3SetTidOnlySvc`. -/
theorem initTp_f3SetTidOnly_ok {P : Program} {L : StdBinaryLayout}
    (hc : hasInstrs P L.initTpAddr (initTpInstrs L))
    (hset : subroutine_ok P L.setThreadAreaAddr stdSetThreadAreaSpec)
    (hsvc : P.svc = f3SetTidOnlySvc) :
    subroutine_ok P L.initTpAddr (stdInitTpSpec L) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨canDo0, sysinfoVal⟩ R s0 hpc hrun hpre hsp_align
  dsimp only [stdInitTpSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hpre⟩; rw [sepConj_assoc] at hpre
  obtain ⟨ws, hws_len, hpre⟩ := satisfies_memRegion_words64 4 (by decide) hpre
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | _⟩⟩⟩⟩ <;> try (simp at hws_len)
  simp only [pointsToWords64_cons, pointsToWords64_nil, StdTdZero, sepConj_emp, sepConj_assoc] at hpre
  have ha1 : s0.sp - 0x20#64 + 8#64 = s0.sp - 0x18#64 := by bv_lin
  have ha2 : s0.sp - 0x18#64 + 8#64 = s0.sp - 0x10#64 := by bv_lin
  have ha3 : s0.sp - 0x10#64 + 8#64 = s0.sp - 0x08#64 := by bv_lin
  rw [ha1, ha2, ha3] at hpre
  refine ⟨((s0.sp - 0x20#64) ↦₆₄ w0) ∗ ((s0.sp - 0x18#64) ↦₆₄ w1) ∗
    ((s0.sp - 0x10#64) ↦₆₄ w2) ∗ ((s0.sp - 0x08#64) ↦₆₄ w3) ∗
    (L.builtinTlsAddr ↦₆₄ 0#64) ∗ ((L.builtinTlsAddr + 0x08#64) ↦₆₄ 0#64) ∗
    ((L.builtinTlsAddr + 0x10#64) ↦₆₄ 0#64) ∗ ((L.builtinTlsAddr + 0x18#64) ↦₆₄ 0#64) ∗
    ((L.builtinTlsAddr + 0x20#64) ↦₃₂ 0#32) ∗ ((L.builtinTlsAddr + 0x28#64) ↦₃₂ 0#32) ∗
    ((L.builtinTlsAddr + 0x78#64) ↦₆₄ 0#64) ∗ ((L.builtinTlsAddr + 0x98#64) ↦₆₄ 0#64) ∗
    (L.libcAddr ↦₈ canDo0) ∗ (L.sysinfoAddr ↦₆₄ sysinfoVal),
    by simpa only [sepConj_assoc] using hpre, ?_⟩
  have_fetches hc 0 6; wp_steps_p 7
  refine SepWP.call_subroutine_frame (ret_pc := L.initTpAddr + 0x1c#64) hset
    (x := L.builtinTlsAddr + 0xc8#64) (F := ?_)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by simp [wp_norm, arm64_norm, hrun])
    (by simp only [State.spAligned, wp_norm, arm64_norm, beq_iff_eq] at hsp_align ⊢; bv_bits)
    (by simp [wp_norm, arm64_norm]; try bv_lin)
    (by dsimp only [stdSetThreadAreaSpec]; simp only [wp_norm, arm64_norm]; sep_frame)
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_
  dsimp only [stdSetThreadAreaSpec]; apply SepWP.pure_elim; rintro ⟨htp1, hx0_1, htls1⟩
  have htls01 : StdTlsFieldsPreserved s0 sf1 := StdTlsFieldsPreserved.trans (by simp [*]) htls1
  have hx19_1 : sf1.readReg64 .x19 = L.builtinTlsAddr := by
    rw [hcs1.1]; simp [wp_norm, arm64_norm]
  have hsp1_eq : sf1.sp = s0.sp - 0x20#64 := by rw [hsp1]; simp [wp_norm, arm64_norm]
  have hsp1_align : sf1.spAligned = true := by
    simp only [State.spAligned, hsp1_eq, beq_iff_eq] at hsp_align ⊢; bv_bits
  clear_fetches 0 6; have_fetches hc 7 18; wp_steps_p 11
  refine SepWP.step_svc_set_tid_address (pc := L.initTpAddr + 0x48#64)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) _hf_18
    (by simp [wp_norm, arm64_norm]) rfl ?_
    (hsvc := evalInst_f3SetTidOnly_of_x8 hsvc (by simp [wp_norm, arm64_norm]))
  clear_fetches 7 18; have_fetches hc 19 33; wp_steps_p 15
  apply SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1])
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp [wp_norm, arm64_norm, htp1], by simp [wp_norm, arm64_norm],
      by simp [wp_norm, arm64_norm, *]⟩, ?_⟩
    simp only [wp_norm, arm64_norm, SIM_TID] at hm ⊢
    simpa only [List.length_cons, List.length_nil, sepConj_assoc] using
      satisfies_words64_memRegion (base := s0.sp - 0x20#64)
        [s0.readReg64 .x29, s0.readReg64 .x30, s0.readReg64 .x19, w3]
        (Rest := StdTdInit L sysinfoVal ∗ (L.libcAddr ↦₈ 1#8) ∗ (L.sysinfoAddr ↦₆₄ sysinfoVal) ∗ R)
        (by simp)
        (by simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, ha1, ha2, ha3,
              StdTdInit, arm64_norm] at hm ⊢; ac_nf at hm ⊢)
  · obtain ⟨_, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, _, hcv⟩ := hcs1
    simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, hc20, hc21, hc22, hc23, hc24, hc25,
      hc26, hc27, hc28, hcv]

end

theorem f3StaticInitTls_setTidOnly_ok {P : Program} {L : StdBinaryLayout}
    (hc_static : hasInstrs P L.staticInitTlsAddr (staticInitTlsInstrs L))
    (hc_copy : hasInstrs P L.copyTlsAddr (copyTlsInstrs L))
    (hc_init : hasInstrs P L.initTpAddr (initTpInstrs L))
    (hc_set : P.hasCode L.setThreadAreaAddr setThreadAreaWords)
    (ops : StdMemOps P L.memcpyAddr L.memsetAddr)
    (hsvc : P.svc = f3SetTidOnlySvc)
    (hphdr : f3CheckPhdrTable L = true)
    (hphdr_end : L.phdrAddr.toNat + L.phnum * 56 < 2 ^ 64)
    (halign : L.builtinTlsAddr.toNat % 8 = 0)
    (hmain_nz : L.mainTlsAddr ≠ 0#64) :
    subroutine_ok P L.staticInitTlsAddr (f3StaticInitTlsSpec L) :=
  f3StaticInitTls_of_initTp hc_static hc_copy
    (initTp_f3SetTidOnly_ok hc_init (setThreadArea_ok hc_set) hsvc)
    ops hphdr hphdr_end halign hmain_nz

end LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TlsZero
