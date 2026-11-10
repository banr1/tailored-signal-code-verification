/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.Musl.Proofs.ExecHelpersSym
public import VerifiedLibraries.Musl.Proofs.MemcpySym
public import VerifiedLibraries.Musl.Proofs.MemsetSym
public import ProofLib.StdStartup.Strlen
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.GenPlacedFetches
public meta import ProofLib.ProgramReflection

/-!
# Placement-Generic `musl` Memory, String, and Outline-Atomic Contracts

Bridges `memcpySymWords` and `memsetWordsSym` to `stdMemcpySpec`, `stdMemcpyROSpec`,
`stdMemsetSpec`, and `StdMemOps`, and proves placement-generic `subroutine_ok` contracts on the
5-block relocatable library `muslMemPlacedLib` (`memcpy`, `memset`, `strlen`,
`__aarch64_cas4_acq`, `__aarch64_swp4_rel`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Musl

open Arm64 Arm64.Obj Arm64.Process Arm64.CType ProofLib ProofLib.StdStartup
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches

/-! ## Spec-free `memcpy` contracts and `StdMemOps` word-table bridges -/

@[reducible] def MuslRoSlice8 : SemType (List (BitVec 8)) :=
  { tyName := "const uint8_t[] (read-only)",
    interp := fun p bs => p ↦ᵣ bs,
    pureWf := fun _ _ => True }

c_type_spec memcpySymSpec (dst src : ptr) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg dst : UninitSlot bs.length ⇝ MutSlice8 bs
  c_arg src : ShrRef ShrSlice8 bs
  c_arg n : Val (SliceLen bs)
  returns dst

c_type_spec memcpyROSymSpec (dst src : ptr) (n : u64) (ghost bs : List (BitVec 8)) : ptr where
  c_arg dst : UninitSlot bs.length ⇝ MutSlice8 bs
  c_arg src : ShrRef MuslRoSlice8 bs
  c_arg n : Val (SliceLen bs)
  returns dst

private theorem memcpy_len_le {m : Memory} {ro : Bool} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ memRegion dst bs.length ∗ memcpySrc ro src bs ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    cases ro <;> dsimp only [memcpySrc, Bool.cond_true, Bool.cond_false] at h
    · refine Satisfies.pointsToBytes_to_ro ?_
      rwa [← sepConj_assoc, sepConj_comm (src ↦ₛ bs), sepConj_assoc]
    · rwa [← sepConj_assoc, sepConj_comm (src ↦ᵣ bs), sepConj_assoc]
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

private theorem memcpy_bridge (ro : Bool) (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcpySymWords) (R : SepProp) (s0 : State)
    (dst src n : BitVec 64) (bs : List (BitVec 8)) (Q : State → SepProp)
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = dst) (hx1 : s0.readReg64 .x1 = src)
    (hx2 : s0.readReg64 .x2 = n) (hn : n.toNat = bs.length)
    (hpre : s0.mem ⊨ memRegion dst bs.length ∗ memcpySrc ro src bs ∗ R)
    (hQ : ∀ sf : State, sf.readReg64 .x0 = dst →
      sf.mem ⊨ (dst ↦ₛ bs) ∗ memcpySrc ro src bs ∗ R → sf.mem ⊨ Q sf ∗ R) :
    ∃ P_init : SepProp, (s0.mem ⊨ P_init ∗ R) ∧
      SepWP prog (s0.readReg64 .lr) s0 P_init (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hlen64 : bs.length ≤ 2 ^ 64 := hn ▸ Nat.le_of_lt n.isLt
  have hn63 := memcpy_len_le hlen64 hpre
  refine ⟨memRegion dst bs.length ∗ memcpySrc ro src bs, by rwa [sepConj_assoc], ?_⟩
  rw [memRegion_eq_exists_bytes dst bs.length hlen64, sepExists_sepConj_left]
  refine SepWP.exists_elim fun old => ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hold => ?_
  refine SepWP.mono (memcpy_sepwp ro prog a hc s0 dst src n old bs hpc hrun hx0 hx1 hx2
    (by omega) (by omega) (by omega)) ?_
  rintro sf P_f - - ⟨⟨hx0f, hspf, hcsf⟩, hent⟩
  refine ⟨fun hm => hQ sf hx0f ?_, hspf, hcsf⟩
  rw [← sepConj_assoc]
  exact Satisfies.mono (sepConj_mono_left hent) hm

theorem memcpy_codeAt_ok_sym (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcpySymWords) :
    subroutine_ok prog a memcpySymSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dst, src, n, bs⟩ R s0 hpc hrun hpre -
  simp only [memcpySymSpec, CType.Bytes, CType.ShrSlice8, CType.MutSlice8, CType.SliceLen,
    CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, -, hn⟩, hmem⟩ := hpre
  refine memcpy_bridge false prog a hc R s0 dst src n bs _ hpc hrun hx0 hx1 hx2 hn hmem
    fun sf hx0f hm => ?_
  simp only [memcpySymSpec, CType.Bytes, CType.MutSlice8, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, hx0f⟩, hm⟩

theorem memcpyRO_codeAt_ok_sym (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a memcpySymWords) :
    subroutine_ok prog a memcpyROSymSpec := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨dst, src, n, bs⟩ R s0 hpc hrun hpre -
  simp only [memcpyROSymSpec, CType.Bytes, CType.MutSlice8, CType.SliceLen,
    CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, -, hn⟩, hmem⟩ := hpre
  refine memcpy_bridge true prog a hc R s0 dst src n bs _ hpc hrun hx0 hx1 hx2 hn hmem
    fun sf hx0f hm => ?_
  simp only [memcpyROSymSpec, CType.Bytes, CType.MutSlice8, sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨trivial, hx0f⟩, hm⟩

private theorem pureWordsProg_hasWords_of_base0 {words : List (BitVec 32)} (addr : BitVec 64)
    (hlen : 4 * words.length ≤ 2 ^ 64)
    (h0 : ((List.range words.length).all fun i =>
      (pureWordsProg 0#64 words).readWordOff (4 * i) == words[i]?) = true) :
    (pureWordsProg addr words).hasWords addr words :=
  pureWordsProg_hasWords hlen h0

private theorem pureWordsProg_allInstrs_of_base0 {words : List (BitVec 32)} (addr : BitVec 64)
    {f : Instr → Bool} (h0 : (pureWordsProg 0#64 words).allInstrs f = true) :
    (pureWordsProg addr words).allInstrs f = true :=
  h0

private theorem pureWordsProg_memset_hasWords (addr : BitVec 64) :
    (pureWordsProg addr memsetWordsSym).hasWords addr memsetWordsSym :=
  pureWordsProg_hasWords_of_base0 addr (by decide +kernel) (by decide +kernel)

private theorem pureWordsProg_memcpy_hasWords (addr : BitVec 64) :
    (pureWordsProg addr memcpySymWords).hasWords addr memcpySymWords :=
  pureWordsProg_hasWords_of_base0 addr (by decide +kernel) (by decide +kernel)

private theorem pureWordsProg_memset_allInstrs (addr : BitVec 64) :
    (pureWordsProg addr memsetWordsSym).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  pureWordsProg_allInstrs_of_base0 addr (by decide +kernel)

private theorem pureWordsProg_memcpy_allInstrs (addr : BitVec 64) :
    (pureWordsProg addr memcpySymWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true :=
  pureWordsProg_allInstrs_of_base0 addr (by decide +kernel)

theorem stdMemset_ok_of_hasWords (P : Program) (addr : BitVec 64)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_words : P.hasWords addr memsetWordsSym) :
    subroutine_ok P addr stdMemsetSpec := by
  refine subroutine_ok_refine_entails
    (subroutine_ok_lift_pureWords_process
      (memset_codeAt_ok_sym _ addr (pureWordsProg_memset_hasWords addr))
      (pureWordsProg_memset_allInstrs addr) h_words h_no_ext
      (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)) ?_
  rintro ⟨dst, b, len⟩ R s0 hpre
  simp only [stdMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, rfl, hx2, hlt⟩, hm⟩ := hpre
  have hlen : (BitVec.ofNat 64 len).toNat = len := by
    simp only [BitVec.toNat_ofNat]; omega
  refine ⟨(dst, s0.readReg32 .x1, BitVec.ofNat 64 len), ?_, fun sf => ?_⟩
  · simp only [memsetSymSpec, CType.MutSlice8, CType.Bytes, CType.U32, CType.SizeT,
      CType.scalarTy, CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj, hlen]
    exact ⟨⟨hx0, trivial, hx2, trivial, trivial⟩, hm⟩
  · simp only [memsetSymSpec, stdMemsetSpec, CType.MutSlice8, CType.Bytes, hlen,
      pure_sepConj_pure_assoc]
    exact sepConj_mono_left (Entails.pure_mono fun h => ⟨h.2.2, h.1⟩)

theorem stdMemcpy_ok_of_hasWords (P : Program) (addr : BitVec 64)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_words : P.hasWords addr memcpySymWords) :
    subroutine_ok P addr stdMemcpySpec := by
  refine subroutine_ok_refine_entails
    (subroutine_ok_lift_pureWords_process
      (memcpy_codeAt_ok_sym _ addr (pureWordsProg_memcpy_hasWords addr))
      (pureWordsProg_memcpy_allInstrs addr) h_words h_no_ext
      (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)) ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  simp only [stdMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  refine ⟨(dst, src, BitVec.ofNat 64 bs.length, bs), ?_, fun sf => ?_⟩
  · simp only [memcpySymSpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes, CType.SliceLen,
      CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj, BitVec.toNat_ofNat]
    exact ⟨⟨hx0, hx1, hx2, trivial, Nat.mod_eq_of_lt hlt⟩, hm⟩
  · simp only [memcpySymSpec, stdMemcpySpec, CType.MutSlice8, CType.ShrSlice8, CType.Bytes,
      pure_sepConj_pure_assoc]
    exact sepConj_mono_left (Entails.pure_mono fun h => ⟨h.2.2, h.1⟩)

theorem stdMemcpyRO_ok_of_hasWords (P : Program) (addr : BitVec 64)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_words : P.hasWords addr memcpySymWords) :
    subroutine_ok P addr stdMemcpyROSpec := by
  refine subroutine_ok_refine_entails
    (subroutine_ok_lift_pureWords_process
      (memcpyRO_codeAt_ok_sym _ addr (pureWordsProg_memcpy_hasWords addr))
      (pureWordsProg_memcpy_allInstrs addr) h_words h_no_ext
      (h_pre_mem := fun _ _ _ => rfl) (h_post_mem := fun _ _ _ _ _ => rfl)) ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  simp only [stdMemcpyROSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  refine ⟨(dst, src, BitVec.ofNat 64 bs.length, bs), ?_, fun sf => ?_⟩
  · simp only [memcpyROSymSpec, CType.MutSlice8, CType.Bytes, CType.SliceLen,
      CType.SemType.valWf, sepConj_assoc, satisfies_pure_sepConj, BitVec.toNat_ofNat]
    exact ⟨⟨hx0, hx1, hx2, trivial, Nat.mod_eq_of_lt hlt⟩, hm⟩
  · simp only [memcpyROSymSpec, stdMemcpyROSpec, CType.MutSlice8, CType.Bytes,
      pure_sepConj_pure_assoc]
    exact sepConj_mono_left (Entails.pure_mono fun h => ⟨h.2.2, h.1⟩)

theorem stdMemOps_of_muslWords (P : Program) (memcpyAddr memsetAddr : BitVec 64)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_memcpy : P.hasWords memcpyAddr memcpySymWords)
    (h_memset : P.hasWords memsetAddr memsetWordsSym) :
    StdMemOps P memcpyAddr memsetAddr where
  memset_ok := stdMemset_ok_of_hasWords P memsetAddr h_no_ext h_memset
  memcpy_ok := stdMemcpy_ok_of_hasWords P memcpyAddr h_no_ext h_memcpy
  memcpy_ro_ok := stdMemcpyRO_ok_of_hasWords P memcpyAddr h_no_ext h_memcpy

/-! ## Placement-generic `muslMemPlacedLib` -/

def muslCas4AcqWords : List (BitVec 32) := [
  0x90000010#32, 0x39400210#32, 0x34000070#32, 0x88e07c41#32,
  0xd65f03c0#32, 0x2a0003f0#32, 0x885ffc40#32, 0x6b10001f#32,
  0x54000061#32, 0x88117c41#32, 0x35ffff91#32, 0xd65f03c0#32]

def muslSwp4RelWords : List (BitVec 32) := [
  0x90000010#32, 0x39400210#32, 0x34000070#32, 0xb8608020#32,
  0xd65f03c0#32, 0x2a0003f0#32, 0x885f7c20#32, 0x8811fc30#32,
  0x35ffffd1#32, 0xd65f03c0#32]

def muslBlkMemcpy : CodeBlock where
  code := wordsLE memcpySymWords
  symbols := [("memcpy", 0)]
  relocs := []
  externs := []

def muslBlkMemset : CodeBlock where
  code := wordsLE memsetWordsSym
  symbols := [("memset", 0)]
  relocs := []
  externs := []

def muslBlkStrlen : CodeBlock where
  code := wordsLE muslStrlenWords
  symbols := [("strlen", 0)]
  relocs := []
  externs := []

def muslBlkCas4Acq : CodeBlock where
  code := wordsLE muslCas4AcqWords
  symbols := [("__aarch64_cas4_acq", 0)]
  relocs := [
    { off := 0, kind := .adrpHi21, sym := "__aarch64_have_lse_atomics" },
    { off := 4, kind := .ldst8Lo12, sym := "__aarch64_have_lse_atomics" }]
  externs := ["__aarch64_have_lse_atomics"]

def muslBlkSwp4Rel : CodeBlock where
  code := wordsLE muslSwp4RelWords
  symbols := [("__aarch64_swp4_rel", 0)]
  relocs := [
    { off := 0, kind := .adrpHi21, sym := "__aarch64_have_lse_atomics" },
    { off := 4, kind := .ldst8Lo12, sym := "__aarch64_have_lse_atomics" }]
  externs := ["__aarch64_have_lse_atomics"]

/-- 5-block relocatable library for `musl` `memcpy` (`0`), `memset` (`1`), `strlen` (`2`),
    `__aarch64_cas4_acq` (`3`), and `__aarch64_swp4_rel` (`4`). -/
def muslMemPlacedLib : MultiPlacedLib where
  name := "musl_mem"
  blocks := [muslBlkMemcpy, muslBlkMemset, muslBlkStrlen, muslBlkCas4Acq, muslBlkSwp4Rel]
  data := []

class MuslMemPlacement where
  mpl : MultiPlacement
  placeable : muslMemPlacedLib.Placeable mpl

abbrev muslMemMpl [h : MuslMemPlacement] : MultiPlacement := h.mpl

abbrev muslMemLib3 : PlacedLib := muslMemPlacedLib.blockLib 3
abbrev muslMemLib4 : PlacedLib := muslMemPlacedLib.blockLib 4
abbrev muslMemPl3 [MuslMemPlacement] : Placement := muslMemPlacedLib.blockPlacement muslMemMpl 3
abbrev muslMemPl4 [MuslMemPlacement] : Placement := muslMemPlacedLib.blockPlacement muslMemMpl 4
abbrev muslMemPC3 [MuslMemPlacement] : Program := muslMemLib3.program muslMemPl3
abbrev muslMemPC4 [MuslMemPlacement] : Program := muslMemLib4.program muslMemPl4

theorem muslMemPlaceable3 [MuslMemPlacement] : muslMemLib3.Placeable muslMemPl3 :=
  muslMemPlacedLib.placeable_blockLib (by decide) MuslMemPlacement.placeable
theorem muslMemPlaceable4 [MuslMemPlacement] : muslMemLib4.Placeable muslMemPl4 :=
  muslMemPlacedLib.placeable_blockLib (by decide) MuslMemPlacement.placeable

set_option maxRecDepth 200000
set_option linter.literalFetch false

def muslMemProg3 : Program := { code := muslBlkCas4Acq.code, symbols := muslBlkCas4Acq.symbols }
def muslMemTree3 : WordTree := word_tree_of% muslMemProg3
theorem muslMem3_code_eq : muslMemLib3.text.code = muslMemTree3.toBytes := by rfl_kernel
theorem muslMem3_tree_size : muslMemTree3.checkSize? = some 12 := by rfl_kernel

gen_placed_fetches muslMemPC3 muslMemLib3 muslMemTree3 muslMem3_code_eq muslMem3_tree_size
  via_placement muslMemPl3 muslMemPlaceable3 [0x0 → 0x2c]

@[simp, arm64_norm] theorem muslMemPC3_rebase_fetch_0x4 [MuslMemPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (muslMemPC3.rebase b X).fetch (b + BitVec.ofNat 64 4) =
      some (.ldr .W32 .B8 false (.gpr 16#5) (.Offset (.gpr 16#5)
        (lo12Of (muslMemPl3.ρ "__aarch64_have_lse_atomics")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := muslMemLib3) (pl := muslMemPl3) (off := 4)
    (r := ⟨4, .ldst8Lo12, "__aarch64_have_lse_atomics", 0, false⟩) (scale := 0) (w := 0x39400210#32)
    muslMemPlaceable3 rfl rfl
    (hookAtOff?_rebase_of_placeable muslMem3_code_eq muslMem3_tree_size muslMemPlaceable3 (by omega))
    (wordAt_of_getQuad? muslMem3_code_eq muslMem3_tree_size (j := 1) rfl)
    rfl (by decide) (by decide) rfl rfl

def muslMemProg4 : Program := { code := muslBlkSwp4Rel.code, symbols := muslBlkSwp4Rel.symbols }
def muslMemTree4 : WordTree := word_tree_of% muslMemProg4
theorem muslMem4_code_eq : muslMemLib4.text.code = muslMemTree4.toBytes := by rfl_kernel
theorem muslMem4_tree_size : muslMemTree4.checkSize? = some 10 := by rfl_kernel

gen_placed_fetches muslMemPC4 muslMemLib4 muslMemTree4 muslMem4_code_eq muslMem4_tree_size
  via_placement muslMemPl4 muslMemPlaceable4 [0x0 → 0x24]

@[simp, arm64_norm] theorem muslMemPC4_rebase_fetch_0x4 [MuslMemPlacement] (b : BitVec 64)
    (X : String → Option (State → State)) :
    (muslMemPC4.rebase b X).fetch (b + BitVec.ofNat 64 4) =
      some (.ldr .W32 .B8 false (.gpr 16#5) (.Offset (.gpr 16#5)
        (lo12Of (muslMemPl4.ρ "__aarch64_have_lse_atomics")))) :=
  PlacedLib.fetch_rebase_ldstLo12_of_placeable (lib := muslMemLib4) (pl := muslMemPl4) (off := 4)
    (r := ⟨4, .ldst8Lo12, "__aarch64_have_lse_atomics", 0, false⟩) (scale := 0) (w := 0x39400210#32)
    muslMemPlaceable4 rfl rfl
    (hookAtOff?_rebase_of_placeable muslMem4_code_eq muslMem4_tree_size muslMemPlaceable4 (by omega))
    (wordAt_of_getQuad? muslMem4_code_eq muslMem4_tree_size (j := 1) rfl)
    rfl (by decide) (by decide) rfl rfl

/-! ## Block-level and raw `CodeLoaded` contracts -/

theorem muslMemcpy_raw_ok [MuslMemPlacement] {Q : Program}
    (hext : ∀ pc, Q.externAt? pc = none)
    (hcl0 : ∀ m, Q.CodeLoaded m → (muslMemPlacedLib.blockProgram muslMemMpl 0).CodeLoaded m) :
    subroutine_ok Q (muslMemPlacedLib.fnAddr muslMemMpl "memcpy") stdMemcpySpec := by
  rw [fnAddr_eq_base MuslMemPlacement.placeable 0 "memcpy"]
  have hseg := (muslMemPlacedLib.hasWords_of_checkSegment (mpl := muslMemMpl) (i := 0) (by decide)
    (fo := 0) (ws := memcpySymWords) (R := []) (X := fun _ => none) (svc := Q.svc)
    MuslMemPlacement.placeable (by decide)).1
  simp only [BitVec.add_zero, patchRelocs] at hseg
  exact subroutine_ok_of_codeLoaded_imp
    (stdMemcpy_ok_of_hasWords _ _ (fun pc => by simp) hseg)
    (fun pc => by simp) hext rfl
    (fun m hm => (hcl0 m hm).of_base_code rfl rfl)

theorem muslMemcpyRO_raw_ok [MuslMemPlacement] {Q : Program}
    (hext : ∀ pc, Q.externAt? pc = none)
    (hcl0 : ∀ m, Q.CodeLoaded m → (muslMemPlacedLib.blockProgram muslMemMpl 0).CodeLoaded m) :
    subroutine_ok Q (muslMemPlacedLib.fnAddr muslMemMpl "memcpy") stdMemcpyROSpec := by
  rw [fnAddr_eq_base MuslMemPlacement.placeable 0 "memcpy"]
  have hseg := (muslMemPlacedLib.hasWords_of_checkSegment (mpl := muslMemMpl) (i := 0) (by decide)
    (fo := 0) (ws := memcpySymWords) (R := []) (X := fun _ => none) (svc := Q.svc)
    MuslMemPlacement.placeable (by decide)).1
  simp only [BitVec.add_zero, patchRelocs] at hseg
  exact subroutine_ok_of_codeLoaded_imp
    (stdMemcpyRO_ok_of_hasWords _ _ (fun pc => by simp) hseg)
    (fun pc => by simp) hext rfl
    (fun m hm => (hcl0 m hm).of_base_code rfl rfl)

theorem muslMemset_raw_ok [MuslMemPlacement] {Q : Program}
    (hext : ∀ pc, Q.externAt? pc = none)
    (hcl1 : ∀ m, Q.CodeLoaded m → (muslMemPlacedLib.blockProgram muslMemMpl 1).CodeLoaded m) :
    subroutine_ok Q (muslMemPlacedLib.fnAddr muslMemMpl "memset") stdMemsetSpec := by
  rw [fnAddr_eq_base MuslMemPlacement.placeable 1 "memset"]
  have hseg := (muslMemPlacedLib.hasWords_of_checkSegment (mpl := muslMemMpl) (i := 1) (by decide)
    (fo := 0) (ws := memsetWordsSym) (R := []) (X := fun _ => none) (svc := Q.svc)
    MuslMemPlacement.placeable (by decide)).1
  simp only [BitVec.add_zero, patchRelocs] at hseg
  exact subroutine_ok_of_codeLoaded_imp
    (stdMemset_ok_of_hasWords _ _ (fun pc => by simp) hseg)
    (fun pc => by simp) hext rfl
    (fun m hm => (hcl1 m hm).of_base_code rfl rfl)

theorem muslStdMemOps_of_codeLoaded [MuslMemPlacement] {Q : Program}
    (hext : ∀ pc, Q.externAt? pc = none)
    (hcl0 : ∀ m, Q.CodeLoaded m → (muslMemPlacedLib.blockProgram muslMemMpl 0).CodeLoaded m)
    (hcl1 : ∀ m, Q.CodeLoaded m → (muslMemPlacedLib.blockProgram muslMemMpl 1).CodeLoaded m) :
    StdMemOps Q (muslMemPlacedLib.fnAddr muslMemMpl "memcpy")
      (muslMemPlacedLib.fnAddr muslMemMpl "memset") :=
  ⟨muslMemset_raw_ok hext hcl1, muslMemcpy_raw_ok hext hcl0, muslMemcpyRO_raw_ok hext hcl0⟩

theorem muslMemcpy_block_ok [MuslMemPlacement] :
    subroutine_ok (muslMemPlacedLib.blockProgram muslMemMpl 0)
      (muslMemPlacedLib.fnAddr muslMemMpl "memcpy")
      (muslMemPlacedLib.withCodeLoaded muslMemMpl stdMemcpySpec) :=
  subroutine_ok_withCodeLoaded muslMemPlacedLib muslMemMpl
    (muslMemcpy_raw_ok (muslMemPlacedLib.externAt?_blockProgram_none muslMemMpl 0) (fun _ h => h))

theorem muslMemcpyRO_block_ok [MuslMemPlacement] :
    subroutine_ok (muslMemPlacedLib.blockProgram muslMemMpl 0)
      (muslMemPlacedLib.fnAddr muslMemMpl "memcpy")
      (muslMemPlacedLib.withCodeLoaded muslMemMpl stdMemcpyROSpec) :=
  subroutine_ok_withCodeLoaded muslMemPlacedLib muslMemMpl
    (muslMemcpyRO_raw_ok (muslMemPlacedLib.externAt?_blockProgram_none muslMemMpl 0) (fun _ h => h))

theorem muslMemset_block_ok [MuslMemPlacement] :
    subroutine_ok (muslMemPlacedLib.blockProgram muslMemMpl 1)
      (muslMemPlacedLib.fnAddr muslMemMpl "memset")
      (muslMemPlacedLib.withCodeLoaded muslMemMpl stdMemsetSpec) :=
  subroutine_ok_withCodeLoaded muslMemPlacedLib muslMemMpl
    (muslMemset_raw_ok (muslMemPlacedLib.externAt?_blockProgram_none muslMemMpl 1) (fun _ h => h))

theorem muslStrlenRO_block_ok [MuslMemPlacement] :
    subroutine_ok (muslMemPlacedLib.blockProgram muslMemMpl 2)
      (muslMemPlacedLib.fnAddr muslMemMpl "strlen")
      (muslMemPlacedLib.withCodeLoaded muslMemMpl stdStrlenROSpec) := by
  have hseg := (muslMemPlacedLib.hasWords_of_checkSegment (mpl := muslMemMpl) (i := 2) (by decide)
    (fo := 0) (ws := muslStrlenWords) (R := []) (X := fun _ => none) (svc := Syscall.standard)
    MuslMemPlacement.placeable (by decide)).1
  simp only [BitVec.add_zero, patchRelocs] at hseg
  have hnw : (muslMemMpl.base 2).toNat + 88 ≤ 2 ^ 64 := by
    have h0 := (muslMemPlacedLib.placeable_blockLib (i := 2) (by decide) MuslMemPlacement.placeable).text.no_wrap
    have hlen : (muslMemPlacedLib.blockLib 2).text.code.length = 88 := by decide
    have hb : (muslMemPlacedLib.blockPlacement muslMemMpl 2).base = muslMemMpl.base 2 := rfl
    rw [hb, hlen] at h0; exact h0
  rw [fnAddr_eq_base MuslMemPlacement.placeable 2 "strlen"]
  exact subroutine_ok_withCodeLoaded muslMemPlacedLib muslMemMpl
    (muslStrlen_ro_ok (muslMemPlacedLib.blockProgram muslMemMpl 2) (muslMemMpl.base 2) hseg hnw)

private def muslAtomicLayout [MuslMemPlacement] : StdBinaryLayout :=
  { phdrSegIdx := 0, rxSegIdx := 0, roSegIdx := 0, rwSegIdx := 0
    brkStart := 0#64, startAddr := 0#64, startCAddr := 0#64, libcStartMainAddr := 0#64
    initLibcAddr := 0#64, memsetAddr := 0#64, staticInitTlsAddr := 0#64, copyTlsAddr := 0#64
    memcpyAddr := 0#64, initTpAddr := 0#64, setThreadAreaAddr := 0#64, dummy1Addr := 0#64
    libcStartMainStage2Addr := 0#64, libcStartInitAddr := 0#64, initFnAddr := 0#64
    initLseAddr := 0#64, detectAndInitializeAddr := 0#64, getauxvalAddr := 0#64
    rustEnableLseAddr := 0#64, doInitAddr := 0#64, cMainAddr := 0#64, cas8RelaxAddr := 0#64
    pollAddr := 0#64, syscallCpAddr := 0#64, sccpAddr := 0#64, syscallRetAddr := 0#64
    signalAddr := 0#64, sigactionAddr := 0#64, libcSigactionAddr := 0#64, restoreRtAddr := 0#64
    sysconfAddr := 0#64, beginShortBacktraceAddr := 0#64, userMainAddr := 0#64
    onceCallAddr := 0#64, cas4AcqAddr := muslMemMpl.base 3, cleanupVtableShimAddr := 0#64
    cleanupClosureAddr := 0#64, stdoutOnceLockInitAddr := 0#64, stdoutVtableShimAddr := 0#64
    stdoutCleanupClosureAddr := 0#64, swp4RelAddr := muslMemMpl.base 4, errnoLocationAddr := 0#64
    cas8AcqAddr := 0#64, exitAddr := 0#64, dummyExitAddr := 0#64, libcExitFiniAddr := 0#64
    doFiniAddr := 0#64, finiFnAddr := 0#64, stdioExitNeededAddr := 0#64, oflLockFnAddr := 0#64
    lockFnAddr := 0#64, closeFileAddr := 0#64, sysExitAddr := 0#64, hasArgcGlobal := false
    argcGlobalAddr := 0#64, userMainReturnsExitCode := false, phdrAddr := 0#64, phnum := 0
    tlsPhdrIdx := 0, tlsImageAddr := 0#64, phdrBytes := [], emptyCStrAddr := 0#64
    sysconfValuesAddr := 0#64, cleanupVtableAddr := 0#64, stdoutVtableAddr := 0#64
    devNullStdAddr := 0#64, devNullLibcAddr := 0#64, initArrayAddr := 0#64, finiArrayAddr := 0#64
    gotAddr := 0#64, stdoutGlobalAddr := 0#64, cleanupOnceAddr := 0#64
    defaultStacksizeAddr := 0#64, stderrFileAddr := 0#64, stderrUsedAddr := 0#64
    libcAddr := 0#64, threadListLockAddr := 0#64, sysinfoAddr := 0#64, hwcapAddr := 0#64
    finalizedAddr := 0#64, initializedAddr := 0#64, argvGlobalAddr := 0#64
    pageSizeGlobalAddr := 0#64, threadIdCounterAddr := 0#64, exitingThreadIdAddr := 0#64
    stdDetectCacheAddr := 0#64, environAddr := 0#64, builtinTlsAddr := 0#64, mainTlsAddr := 0#64
    prognameAddr := 0#64, prognameFullAddr := 0#64
    haveLseAtomicsAddr := muslMemPlacedLib.resolve muslMemMpl "__aarch64_have_lse_atomics"
    stdinUsedAddr := 0#64, stdoutUsedAddr := 0#64, oflHeadAddr := 0#64, oflLockAddr := 0#64 }

private theorem lo12Of_eq_pageLo12 (x : BitVec 64) : lo12Of x = pageLo12 x := by
  unfold lo12Of pageLo12; bv_bits

private theorem pageOf_sub_eq_adrpOff (pc target : BitVec 64) :
    pageOf target - pageOf (pc + 0#64) = adrpOff pc target := by
  unfold adrpOff pageOf; bv_bits

private theorem fetch_adrp0_of_placeable {lib : PlacedLib} {pl : Placement}
    {t : ProgramReflection.WordTree} {n : Nat}
    (hcode_eq : lib.text.code = t.toBytes) (hsz : t.checkSize? = some n)
    (hpl : lib.Placeable pl)
    (hr0 : lib.text.relocAt? 0 = some ⟨0, .adrpHi21, "__aarch64_have_lse_atomics", 0, false⟩)
    (hr4 : lib.text.relocAt? 4 = some ⟨4, .ldst8Lo12, "__aarch64_have_lse_atomics", 0, false⟩)
    (hlook : lookup "__aarch64_have_lse_atomics" lib.text.symbols = none)
    (hq0 : t.getQuad? 0 = some (16#8, 0#8, 0#8, 144#8))
    (_hlen_pos : 4 ≤ 4 * n) :
    ((lib.program pl).rebase pl.base (fun _ => none)).fetch (pl.base + BitVec.ofNat 64 0) =
      some (.adr true .x16 (adrpOff pl.base (pl.ρ "__aarch64_have_lse_atomics"))) := by
  let r : RelocEntry := ⟨0, .adrpHi21, "__aarch64_have_lse_atomics", 0, false⟩
  obtain ⟨hal, hlen, hrange⟩ := hpl.text.relocs_ok r (CodeBlock.relocAt?_mem hr0)
  have hb : lib.text.b2bNext? r = none := by simp [CodeBlock.b2bNext?, r]
  rw [CodeBlock.relocTarget_of_b2bNext_none hb] at hrange
  change AdrpInRange (pl.base + BitVec.ofNat 64 0) (lib.text.target pl r) at hrange
  have hnrel : lib.text.relaxableAt 0 = false :=
    CodeBlock.relaxableAt_false_of_next_kind
      (r := ⟨4, .ldst8Lo12, "__aarch64_have_lse_atomics", 0, false⟩) hr4 (by decide)
  have hw0 := CodeBlock.patchedWord_of_notRelaxed (pl := pl) hr0
    (CodeBlock.relaxedAt_of_relaxableAt_false hnrel) (.inl (by omega))
  rw [CodeBlock.relocTarget_of_b2bNext_none hb] at hw0
  have hf0 : ((lib.program pl).rebase pl.base (fun _ => none)).fetch (pl.base + BitVec.ofNat 64 0) =
      decode (lib.text.patchedWord pl 0) :=
    Program.fetch_of_readWordOff (by omega)
      (GenPlacedFetches.hookAtOff?_rebase_of_placeable hcode_eq hsz hpl (by omega))
      (CodeBlock.readWordOff_patched rfl hal hlen)
  have hw_eq := GenPlacedFetches.wordAt_of_getQuad? hcode_eq hsz (j := 0) hq0
  have hmask : lib.text.wordAt 0 &&& 0x9f000000#32 = 0x90000000#32 := by rw [hw_eq]; decide
  have hrd : (lib.text.wordAt 0).extractLsb' 0 5 = 16#5 := by rw [hw_eq]; decide
  have htgt : lib.text.target pl r = pl.ρ "__aarch64_have_lse_atomics" := by
    simp [CodeBlock.target, CodeBlock.resolve, addSignedAddr, r, hlook]
  rw [hf0, hw0]
  simp only [patchRelocWord, r]
  rw [decode_adrpWord hmask hrange, hrd]
  simp only [Reg.fromZRBits, beq_iff_eq, (by decide : ¬(16#5 = 31#5)), ↓reduceIte, htgt,
    pageOf_sub_eq_adrpOff]

private theorem muslMemPC3_hasInstrs [MuslMemPlacement] :
    hasInstrs (muslMemPlacedLib.blockProgram muslMemMpl 3)
      muslAtomicLayout.cas4AcqAddr (cas4AcqInstrs muslAtomicLayout) := by
  intro i hi
  change (muslMemPC3.rebase muslMemPl3.base (fun _ => none)).fetch
    (muslMemPl3.base + BitVec.ofNat 64 (4 * i)) = _
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · simpa [cas4AcqInstrs, muslAtomicLayout, muslMemPC3, muslMemPl3, muslMemMpl,
      MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve] using
      fetch_adrp0_of_placeable muslMem3_code_eq muslMem3_tree_size muslMemPlaceable3
        (by decide) (by decide) (by decide) rfl (by omega)
  · simp [cas4AcqInstrs, muslAtomicLayout, lo12Of_eq_pageLo12]; rfl
  all_goals first | (simp [cas4AcqInstrs, muslAtomicLayout]; done) | (simp [cas4AcqInstrs] at hi; omega)

private theorem muslMemPC4_hasInstrs [MuslMemPlacement] :
    hasInstrs (muslMemPlacedLib.blockProgram muslMemMpl 4)
      muslAtomicLayout.swp4RelAddr (swp4RelInstrs muslAtomicLayout) := by
  intro i hi
  change (muslMemPC4.rebase muslMemPl4.base (fun _ => none)).fetch
    (muslMemPl4.base + BitVec.ofNat 64 (4 * i)) = _
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · simpa [swp4RelInstrs, muslAtomicLayout, muslMemPC4, muslMemPl4, muslMemMpl,
      MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve] using
      fetch_adrp0_of_placeable muslMem4_code_eq muslMem4_tree_size muslMemPlaceable4
        (by decide) (by decide) (by decide) rfl (by omega)
  · simp [swp4RelInstrs, muslAtomicLayout, lo12Of_eq_pageLo12]; rfl
  all_goals first | (simp [swp4RelInstrs, muslAtomicLayout]; done) | (simp [swp4RelInstrs] at hi; omega)

theorem muslCas4Acq_block_ok [MuslMemPlacement] :
    subroutine_ok (muslMemPlacedLib.blockProgram muslMemMpl 3)
      (muslMemPlacedLib.fnAddr muslMemMpl "__aarch64_cas4_acq")
      (muslMemPlacedLib.withCodeLoaded muslMemMpl
        (stdCas4Spec (muslMemPlacedLib.resolve muslMemMpl "__aarch64_have_lse_atomics"))) := by
  rw [fnAddr_eq_base MuslMemPlacement.placeable 3 "__aarch64_cas4_acq"]
  exact subroutine_ok_withCodeLoaded muslMemPlacedLib muslMemMpl
    (cas4Acq_ok (muslMemPlacedLib.blockProgram muslMemMpl 3) muslAtomicLayout muslMemPC3_hasInstrs)

theorem muslSwp4Rel_block_ok [MuslMemPlacement] :
    subroutine_ok (muslMemPlacedLib.blockProgram muslMemMpl 4)
      (muslMemPlacedLib.fnAddr muslMemMpl "__aarch64_swp4_rel")
      (muslMemPlacedLib.withCodeLoaded muslMemMpl
        (stdSwp4Spec (muslMemPlacedLib.resolve muslMemMpl "__aarch64_have_lse_atomics"))) := by
  rw [fnAddr_eq_base MuslMemPlacement.placeable 4 "__aarch64_swp4_rel"]
  exact subroutine_ok_withCodeLoaded muslMemPlacedLib muslMemMpl
    (swp4Rel_ok (muslMemPlacedLib.blockProgram muslMemMpl 4) muslAtomicLayout muslMemPC4_hasInstrs)

end VerifiedLibraries.Musl
