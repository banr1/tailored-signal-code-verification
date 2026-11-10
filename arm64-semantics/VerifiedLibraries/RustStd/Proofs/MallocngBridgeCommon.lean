/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.ProgramReflection
public import ProofLib.StdStartup.MemOps
public import ProofLib.SepLogic.WP.StepsProcess
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocHelpers
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Proofs.MallocngInst

/-!
# Shared `MallocngBridge` Contracts, Stack Splits, and Shim Instruction Tables

Defines C-entry `subroutine_ok` bundles (`MallocngCEntryAddrs`, `MallocngProgCContractsWith`) over
`mallocng` placements, `AllocCallPreserved` transport and `Rust.hookFrame` stack-splitting lemmas,
and symbolic `Instr` tables with `WordTree` validators for the `rustc` global-allocator shims.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib.SepLogic ProofLib.ProgramReflection ProofLib.StdStartup
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

/-! ## Placed `mallocng` C Entry Contracts -/

/-- Link addresses of the 5 `musl` v1.2.5 `mallocng` C entry points consumed by Rust global
    allocation (`malloc`, `free`, `realloc`, `aligned_alloc`, `posix_memalign`). -/
structure MallocngCEntryAddrs where
  malloc        : BitVec 64
  free          : BitVec 64
  realloc       : BitVec 64
  alignedAlloc  : BitVec 64
  posixMemalign : BitVec 64
  deriving DecidableEq, Repr

def mallocngPlacedCAddrs (mpl : Obj.MultiPlacement) : MallocngCEntryAddrs where
  malloc        := VerifiedLibraries.mallocngLib.fnAddr mpl "malloc"
  free          := VerifiedLibraries.mallocngLib.fnAddr mpl "free"
  realloc       := VerifiedLibraries.mallocngLib.fnAddr mpl "realloc"
  alignedAlloc  := VerifiedLibraries.mallocngLib.fnAddr mpl "aligned_alloc"
  posixMemalign := VerifiedLibraries.mallocngLib.fnAddr mpl "posix_memalign"

/-- Program-level `subroutine_ok` bundle for the 5 `mallocng` C entry points under
    `Syscall.standard`, framed with a state-independent invariant `extra : SepProp`. -/
structure MallocngProgCContractsWith (J : MallocngIface) (extra : SepProp)
    (P : Program) (mAddrs : MallocngAddrs) (cAddrs : MallocngCEntryAddrs) : Prop where
  malloc_ok : ∀ γ : GhostName,
    subroutine_ok P cAddrs.malloc
      (withExtra extra (ToBaseSpec.toSpec (mallocngMallocSpec J Syscall.standard γ mAddrs) P.base))
  free_ok : ∀ γ : GhostName,
    subroutine_ok P cAddrs.free
      (withExtra extra (ToBaseSpec.toSpec (mallocngFreeSpec J γ mAddrs) P.base))
  realloc_ok : ∀ γ : GhostName,
    subroutine_ok P cAddrs.realloc
      (withExtra extra (ToBaseSpec.toSpec (mallocngReallocSpec J Syscall.standard γ mAddrs) P.base))
  alignedAlloc_ok : ∀ γ : GhostName,
    subroutine_ok P cAddrs.alignedAlloc
      (withExtra extra (ToBaseSpec.toSpec (mallocngAlignedAllocSpec J Syscall.standard γ mAddrs) P.base))
  posixMemalign_ok : ∀ γ : GhostName,
    subroutine_ok P cAddrs.posixMemalign
      (withExtra extra (ToBaseSpec.toSpec (mallocngPosixMemalignSpec J Syscall.standard γ mAddrs) P.base))

theorem MallocngProgCContractsWith.of_placed {J : MallocngIface} {P : Program}
    {mpl : Obj.MultiPlacement} (extra : SepProp)
    (hP : ProgContainsMallocng P mpl)
    (hEntries : MallocngPlacedEntryContracts J mpl Syscall.standard) :
    MallocngProgCContractsWith J extra P (mallocngAddrsOfPlacement mpl)
      (mallocngPlacedCAddrs mpl) where
  malloc_ok γ :=
    subroutine_ok_withExtra extra
      (mallocngMultiSubroutine_to_prog hP (fun _ _ => rfl) (hEntries.malloc_ok γ))
  free_ok γ :=
    subroutine_ok_withExtra extra
      (mallocngMultiSubroutine_to_prog hP (fun _ _ => rfl) (hEntries.free_ok γ))
  realloc_ok γ :=
    subroutine_ok_withExtra extra
      (mallocngMultiSubroutine_to_prog hP (fun _ _ => rfl) (hEntries.realloc_ok γ))
  alignedAlloc_ok γ :=
    subroutine_ok_withExtra extra
      (mallocngMultiSubroutine_to_prog hP (fun _ _ => rfl) (hEntries.alignedAlloc_ok γ))
  posixMemalign_ok γ :=
    subroutine_ok_withExtra extra
      (mallocngMultiSubroutine_to_prog hP (fun _ _ => rfl) (hEntries.posixMemalign_ok γ))

/-! ## Process-Field Preservation and `Rust.hookFrame` Stack Splits -/

theorem allocCallPreserved_of_mallocngProcPreserved {s0 sf : State}
    (h : MallocngProcPreserved s0 sf) :
    AllocCallPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.2.2.2.2, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem allocCallPreserved_of_stdState_oracle_symtab {s0 sf : State}
    (h : StdStatePreserved s0 sf) (horc : sf.oracle = s0.oracle) (hsym : sf.symtab = s0.symtab) :
    AllocCallPreserved s0 sf :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2.1, horc, hsym⟩

theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h01 : AllocCallPreserved s0 s1) (h12 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1,
   h12.2.1.trans h01.2.1,
   h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1,
   h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

theorem allocCallPreserved_of_fields_eq {s0 s1 sf : State}
    (hfs : s1.fs = s0.fs) (htr : s1.trace = s0.trace) (hsig : s1.sigActions = s0.sigActions)
    (htp : s1.tpidrEl0 = s0.tpidrEl0) (hbs : s1.brkStart = s0.brkStart)
    (horc : s1.oracle = s0.oracle) (hsym : s1.symtab = s0.symtab)
    (h1f : AllocCallPreserved s1 sf) :
    AllocCallPreserved s0 sf :=
  allocCallPreserved_trans ⟨hfs, htr, hsig, htp, hbs, horc, hsym⟩ h1f

/-- Total-correctness contract for `memcpy(dst, src, n)` over a read-write source buffer
    `src ↦ₛ bs`, preserving `AllocCallPreserved` and `sf.brk = s0.brk`. -/
def allocMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
    (memRegion dst bs.length ∗ (src ↦ₛ bs))
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ sf.brk = s0.brk⌝ ∗
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem allocMemcpy_len_le_2pow63 {m : Memory} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    refine Satisfies.pointsToBytes_to_ro ?_
    rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
  have hsep : ∀ a, InRegion src bs.length a → ¬InRegion dst bs.length a := fun a hs hd =>
    not_satisfies_ownsRO_ownsRW (ownsRO_pointsToBytesRO_at hlen hs)
      (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length a hd)) hro
  have hself : ∀ b : BitVec 64, bs.length > 2 ^ 63 → InRegion b bs.length b := fun b hgt => by
    simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine Classical.byContradiction fun hgt => ?_
  by_cases hsd : InRegion dst bs.length src
  · exact hsep src (hself src (by omega)) hsd
  · refine hsep dst ?_ (hself dst (by omega))
    simp only [InRegion] at hsd ⊢
    bv_omega

theorem allocMemcpy_ok_of_hasWords (P : Program) (memcpyAddr : BitVec 64)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_words : P.hasWords memcpyAddr memcpySymWords) :
    subroutine_ok P memcpyAddr allocMemcpySpec := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _hL
  simp only [allocMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hm_assoc : s0.mem ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R := by
    rwa [← sepConj_assoc] at hm
  have hn63 : bs.length ≤ 2 ^ 63 := allocMemcpy_len_le_2pow63 (Nat.le_of_lt hlt) hm_assoc
  have hn_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hm_ex : s0.mem ⊨
      (∃∗ dstBs : List (BitVec 8), ⌜dstBs.length = bs.length⌝ ∗ (dst ↦ₛ dstBs)) ∗
        ((src ↦ₛ bs) ∗ R) :=
    Satisfies.mono (sepConj_mono_left (memRegion_entails_exists_pointsToBytes bs.length dst (Nat.le_of_lt hlt))) hm
  rw [sepExists_sepConj_left] at hm_ex
  obtain ⟨dstBs, hm_dst⟩ := (satisfies_sepExists _ _).mp hm_ex
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_dst
  obtain ⟨hdstLen, hm_pts⟩ := hm_dst
  have hLift := subroutine_ok_lift_pureWords_process
    (P := P)
    (memcpy_pureWords_ok memcpyAddr dst src dstBs bs (BitVec.ofNat 64 bs.length)
      (hdstLen.trans hn_nat.symm) hn_nat.symm (by rw [hn_nat]; exact hn63))
    (memcpy_allInstrs_noSvc_noMsr memcpyAddr)
    h_words h_no_ext
    (h_pre_mem := fun _ _ _ => rfl)
    (h_post_mem := fun _ _ _ _ _ => rfl)
  refine hLift.mono_outcome () R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, hm_pts⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [allocMemcpySpec]
      refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym, hx0f⟩ => ?_
      rcases hpf with ⟨hfs, htr, htp, hsig, hbrk, hbrks, _⟩
      exact Entails.pure_right ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩, hbrk⟩
        (Entails.refl _)
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

theorem allocMemcpy_ok_of_wordTree {P : Program} {t : WordTree} {memcpyAddr : BitVec 64}
    {baseOff : Nat} (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (hoff : (memcpyAddr - P.base).toNat = baseOff)
    (hbnd : baseOff + 4 * memcpySymWords.length ≤ 2 ^ 64)
    (hstubs : P.stubs = [] := by rfl) (hsyms : P.symbols = [] := by rfl)
    (hok : checkWordsAt t baseOff memcpySymWords = true) :
    subroutine_ok P memcpyAddr allocMemcpySpec :=
  allocMemcpy_ok_of_hasWords P memcpyAddr h_no_ext
    (hasWords_of_wordTree n hcode hwf hoff hbnd hstubs hsyms hok)

theorem hookFrame_eq_stackFrame4096 (sp : BitVec 64) :
    Rust.hookFrame sp = stackFrameAt sp 4096 :=
  (stackFrameAt_eq_memRegion sp 4096 (by decide)).symm

theorem hookFrame_eq_stack1024 (sp : BitVec 64) :
    Rust.hookFrame sp =
      (stackFrameAt sp mallocngStackBytes ∗ stackFrameAt (sp - 1024#64) 3072) := by
  rw [hookFrame_eq_stackFrame4096 sp]
  exact stackFrameAt_split sp 1024 3072 (by decide)

theorem hookFrame_eq_stack32_1024 (sp : BitVec 64) :
    Rust.hookFrame sp =
      (stackFrameAt sp 32 ∗
        (stackFrameAt (sp - 32#64) mallocngStackBytes ∗
          stackFrameAt (sp - 32#64 - 1024#64) 3040)) := by
  rw [hookFrame_eq_stackFrame4096 sp,
      show (4096 : Nat) = 32 + 4064 from rfl,
      stackFrameAt_split sp 32 4064 (by decide),
      show (4064 : Nat) = 1024 + 3040 from rfl,
      stackFrameAt_split (sp - 32#64) 1024 3040 (by decide)]

theorem hookFrame_eq_stack64_1024 (sp : BitVec 64) :
    Rust.hookFrame sp =
      (stackFrameAt sp 64 ∗
        (stackFrameAt (sp - 64#64) mallocngStackBytes ∗
          stackFrameAt (sp - 64#64 - 1024#64) 3008)) := by
  rw [hookFrame_eq_stackFrame4096 sp,
      show (4096 : Nat) = 64 + 4032 from rfl,
      stackFrameAt_split sp 64 4032 (by decide),
      show (4032 : Nat) = 1024 + 3008 from rfl,
      stackFrameAt_split (sp - 64#64) 1024 3008 (by decide)]

/-! ## Symbolic `Instr` Sequences for `__rdl_{alloc,dealloc,realloc}` -/

/-- Instruction sequence (`22` insns, `88` B) of `rustc 1.98.1` `__rustc::__rdl_alloc` at
    `allocAddr`, branching to `mallocAddr` (`align ≤ 16 ∧ align ≤ size`) or calling
    `posixMemalignAddr` (`align > 16 ∨ align > size`). -/
def rdlAllocInstrs (allocAddr mallocAddr posixMemalignAddr : BitVec 64) : List Instr :=
  [ .addSubImm .W64 .SUBS .xzr .x1 0x10#12 false,
    .logicalShift .W64 .ORR .x2 .xzr .x0 .LSL 0,
    .bCond .HI 0x14#64,
    .addSubShift .W64 .SUBS .xzr .x1 .x2 .LSL 0,
    .bCond .HI 0x0c#64,
    .logicalShift .W64 .ORR .x0 .xzr .x2 .LSL 0,
    .b (mallocAddr - (allocAddr + 0x18#64)),
    .addSubImm .W64 .SUB .sp .sp 0x20#12 false,
    .stp .W64 .x29 .x30 (.Offset .sp 0x10#64),
    .addSubImm .W64 .ADD .x29 .sp 0x10#12 false,
    .addSubImm .W64 .SUBS .xzr .x1 0x8#12 false,
    .moveWide .W32 .MOVZ .x8 0x8#16 0,
    .addSubImm .W64 .ADD .x0 .sp 0x8#12 false,
    .condSelect .W64 .CSEL .x1 .x1 .x8 .HI,
    .str .X64 .xzr (.Offset .sp 0x8#64),
    .bl (posixMemalignAddr - (allocAddr + 0x3c#64)),
    .ldr .W64 .X64 false .x8 (.Offset .sp 0x8#64),
    .addSubImm .W32 .SUBS .xzr .x0 0x0#12 false,
    .condSelect .W64 .CSEL .x0 .x8 .xzr .EQ,
    .ldp .W64 false .x29 .x30 (.Offset .sp 0x10#64),
    .addSubImm .W64 .ADD .sp .sp 0x20#12 false,
    .ret .x30 ]

/-- Instruction sequence (`1` insn, `4` B) of `rustc 1.98.1` `__rustc::__rdl_dealloc` at
    `deallocAddr`, tail-branching to `freeAddr`. -/
def rdlDeallocInstrs (deallocAddr freeAddr : BitVec 64) : List Instr :=
  [ .b (freeAddr - deallocAddr) ]

/-- Instruction sequence (`43` insns, `172` B) of `rustc 1.98.1` `__rustc::__rdl_realloc` at
    `reallocAddr`, branching to `cReallocAddr` (`align ≤ 16 ∧ align ≤ new`) or calling
    `posixMemalignAddr`, `memcpyAddr`, and `freeAddr`. -/
def rdlReallocInstrs (reallocAddr cReallocAddr posixMemalignAddr memcpyAddr freeAddr : BitVec 64) :
    List Instr :=
  [ .addSubImm .W64 .SUB .sp .sp 0x40#12 false,
    .stp .W64 .x29 .x30 (.Offset .sp 0x10#64),
    .stp .W64 .x22 .x21 (.Offset .sp 0x20#64),
    .stp .W64 .x20 .x19 (.Offset .sp 0x30#64),
    .addSubImm .W64 .ADD .x29 .sp 0x10#12 false,
    .logicalShift .W64 .ORR .x19 .xzr .x3 .LSL 0,
    .logicalShift .W64 .ORR .x20 .xzr .x1 .LSL 0,
    .addSubImm .W64 .SUBS .xzr .x2 0x10#12 false,
    .bCond .HI 0x24#64,
    .addSubShift .W64 .SUBS .xzr .x2 .x19 .LSL 0,
    .bCond .HI 0x1c#64,
    .logicalShift .W64 .ORR .x1 .xzr .x19 .LSL 0,
    .ldp .W64 false .x20 .x19 (.Offset .sp 0x30#64),
    .ldp .W64 false .x22 .x21 (.Offset .sp 0x20#64),
    .ldp .W64 false .x29 .x30 (.Offset .sp 0x10#64),
    .addSubImm .W64 .ADD .sp .sp 0x40#12 false,
    .b (cReallocAddr - (reallocAddr + 0x40#64)),
    .addSubImm .W64 .SUBS .xzr .x2 0x8#12 false,
    .moveWide .W32 .MOVZ .x8 0x8#16 0,
    .logicalShift .W64 .ORR .x22 .xzr .x0 .LSL 0,
    .condSelect .W64 .CSEL .x1 .x2 .x8 .HI,
    .addSubImm .W64 .ADD .x0 .sp 0x8#12 false,
    .logicalShift .W64 .ORR .x2 .xzr .x19 .LSL 0,
    .str .X64 .xzr (.Offset .sp 0x8#64),
    .bl (posixMemalignAddr - (reallocAddr + 0x60#64)),
    .logicalShift .W32 .ORR .x8 .xzr .x0 .LSL 0,
    .logicalShift .W64 .ORR .x0 .xzr .xzr .LSL 0,
    .cbz .W32 true .x8 0x2c#64,
    .ldr .W64 .X64 false .x21 (.Offset .sp 0x8#64),
    .cbz .W64 false .x21 0x24#64,
    .addSubShift .W64 .SUBS .xzr .x19 .x20 .LSL 0,
    .logicalShift .W64 .ORR .x0 .xzr .x21 .LSL 0,
    .logicalShift .W64 .ORR .x1 .xzr .x22 .LSL 0,
    .condSelect .W64 .CSEL .x2 .x19 .x20 .CC,
    .bl (memcpyAddr - (reallocAddr + 0x88#64)),
    .logicalShift .W64 .ORR .x0 .xzr .x22 .LSL 0,
    .bl (freeAddr - (reallocAddr + 0x90#64)),
    .logicalShift .W64 .ORR .x0 .xzr .x21 .LSL 0,
    .ldp .W64 false .x20 .x19 (.Offset .sp 0x30#64),
    .ldp .W64 false .x22 .x21 (.Offset .sp 0x20#64),
    .ldp .W64 false .x29 .x30 (.Offset .sp 0x10#64),
    .addSubImm .W64 .ADD .sp .sp 0x40#12 false,
    .ret .x30 ]

@[simp] theorem rdlAllocInstrs_length (a m pm : BitVec 64) :
    (rdlAllocInstrs a m pm).length = 22 := rfl

@[simp] theorem rdlDeallocInstrs_length (d f : BitVec 64) :
    (rdlDeallocInstrs d f).length = 1 := rfl

@[simp] theorem rdlReallocInstrs_length (r cr pm mc f : BitVec 64) :
    (rdlReallocInstrs r cr pm mc f).length = 43 := rfl

/-! ## Shim Code Bundles and `WordTree` Validators -/

theorem fetch_instr_at {P : Program} {fnAddr off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (h : hasInstrs P fnAddr ls)
    (hi : ls[i]? = some inst := by rfl)
    (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (fnAddr + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := h.fetch_off i off hlt hoff
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi
  exact hf

theorem fetch_instr_at0 {P : Program} {fnAddr : BitVec 64} {ls : List Instr} {inst : Instr}
    (h : hasInstrs P fnAddr ls) (hi : ls[0]? = some inst := by rfl) :
    P.fetch fnAddr = some inst := by
  simpa using fetch_instr_at 0 h hi rfl

/-- Instruction-level code witness for the 3 `rustc 1.98.1` `__rustc::__rdl_{alloc,dealloc,realloc}`
    allocator shims placed at `rdlAddrs : RustStdAllocAddrs`. -/
structure RustStdRdlShimCode (P : Program) (rdlAddrs : RustStdAllocAddrs)
    (cAddrs : MallocngCEntryAddrs) (memcpyAddr : BitVec 64) : Prop where
  alloc_instrs :
    hasInstrs P rdlAddrs.alloc
      (rdlAllocInstrs rdlAddrs.alloc cAddrs.malloc cAddrs.posixMemalign)
  dealloc_instrs :
    hasInstrs P rdlAddrs.dealloc
      (rdlDeallocInstrs rdlAddrs.dealloc cAddrs.free)
  realloc_instrs :
    hasInstrs P rdlAddrs.realloc
      (rdlReallocInstrs rdlAddrs.realloc cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free)

/-- 1-instruction unconditional `B`-thunk code witness forwarding `thunkAddrs`
    (`__rustc::__rust_{alloc,dealloc,realloc}`) to `targetAddrs`
    (`__rustc::__rdl_{alloc,dealloc,realloc}`). -/
structure RustStdThunkCode (P : Program) (thunkAddrs targetAddrs : RustStdAllocAddrs) : Prop where
  alloc_thunk   : hasInstrs P thunkAddrs.alloc   [ .b (targetAddrs.alloc   - thunkAddrs.alloc) ]
  dealloc_thunk : hasInstrs P thunkAddrs.dealloc [ .b (targetAddrs.dealloc - thunkAddrs.dealloc) ]
  realloc_thunk : hasInstrs P thunkAddrs.realloc [ .b (targetAddrs.realloc - thunkAddrs.realloc) ]

def checkShimInstrsAt (imgBase : BitVec 64) (t : WordTree) (fnAddr : BitVec 64)
    (is : List Instr) : Bool :=
  (imgBase + BitVec.ofNat 64 (fnAddr - imgBase).toNat == fnAddr) &&
  decide ((fnAddr - imgBase).toNat + 4 * is.length < 2 ^ 64) &&
  checkInstrsAt t (fnAddr - imgBase).toNat is

def checkRustStdRdlShimCode (imgBase : BitVec 64) (t : WordTree)
    (rdlAddrs : RustStdAllocAddrs) (cAddrs : MallocngCEntryAddrs)
    (memcpyAddr : BitVec 64) : Bool :=
  checkShimInstrsAt imgBase t rdlAddrs.alloc
    (rdlAllocInstrs rdlAddrs.alloc cAddrs.malloc cAddrs.posixMemalign) &&
  checkShimInstrsAt imgBase t rdlAddrs.dealloc
    (rdlDeallocInstrs rdlAddrs.dealloc cAddrs.free) &&
  checkShimInstrsAt imgBase t rdlAddrs.realloc
    (rdlReallocInstrs rdlAddrs.realloc cAddrs.realloc cAddrs.posixMemalign memcpyAddr cAddrs.free)

theorem rustStdRdlShimCode_of_wordTree {P : Program} {t : WordTree}
    {rdlAddrs : RustStdAllocAddrs} {cAddrs : MallocngCEntryAddrs} {memcpyAddr : BitVec 64}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkRustStdRdlShimCode P.base t rdlAddrs cAddrs memcpyAddr = true) :
    RustStdRdlShimCode P rdlAddrs cAddrs memcpyAddr := by
  have hi : ∀ a is, checkShimInstrsAt P.base t a is = true → hasInstrs P a is := fun a is h => by
    simp only [checkShimInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkRustStdRdlShimCode at hok
  simp only [Bool.and_eq_true] at hok
  exact ⟨hi _ _ hok.1.1, hi _ _ hok.1.2, hi _ _ hok.2⟩

def checkRustStdThunkCode (imgBase : BitVec 64) (t : WordTree)
    (thunkAddrs targetAddrs : RustStdAllocAddrs) : Bool :=
  checkShimInstrsAt imgBase t thunkAddrs.alloc   [ .b (targetAddrs.alloc   - thunkAddrs.alloc) ] &&
  checkShimInstrsAt imgBase t thunkAddrs.dealloc [ .b (targetAddrs.dealloc - thunkAddrs.dealloc) ] &&
  checkShimInstrsAt imgBase t thunkAddrs.realloc [ .b (targetAddrs.realloc - thunkAddrs.realloc) ]

theorem rustStdThunkCode_of_wordTree {P : Program} {t : WordTree}
    {thunkAddrs targetAddrs : RustStdAllocAddrs}
    (n : Nat) (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hext : ∀ sym, (P.externs sym).isNone = true := by intro _; rfl)
    (hovr : ∀ sym, (P.overrides sym).isNone = true := by intro _; rfl)
    (hok : checkRustStdThunkCode P.base t thunkAddrs targetAddrs = true) :
    RustStdThunkCode P thunkAddrs targetAddrs := by
  have hi : ∀ a is, checkShimInstrsAt P.base t a is = true → hasInstrs P a is := fun a is h => by
    simp only [checkShimInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact hasInstrs_of_wordTree n hcode hwf h.1.1 h.1.2 hext hovr h.2
  unfold checkRustStdThunkCode at hok
  simp only [Bool.and_eq_true] at hok
  exact ⟨hi _ _ hok.1.1, hi _ _ hok.1.2, hi _ _ hok.2⟩

end VerifiedLibraries.RustStd
