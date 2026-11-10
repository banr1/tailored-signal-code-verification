/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.ProgramReflection.IdxTree
public meta import ProofLib.ProgramReflection.IdxTree
public import ProofLib.Placed.Transfer
public import ProofLib.Placed.Pair
public import ProofLib.Placed.AdrpLdst
public import ProofLib.SepLogic.WPFrozen
public import ProofLib.SepLogic.WP.ProjGuardAttr
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# Multi-Block Placed Libraries

Proof infrastructure for `Obj.MultiPlacedLib`: per-block symbol-resolution coherence
(`MultiPlacedLib.resolve_block`), ELF loading and `Program.pureMem` transfer (`codeLoaded_of_inElf`,
`subroutineOk_toPureMem`), cross-block stepping and call tactics (`sepWP_call_block`,
`subroutine_ok_of_block`, `wp_cut_codeLoaded`, `wp_call_block`), kernel-checked `Placeable`,
`InElf`, and `DataDisjoint` checkers (`checkInElf_spec`, `Interned.checkMulti_spec`,
`Interned.checkMultiDisjoint_spec`), sub-library embedding (`embedsAt`, `embed_subroutine_ok`), and
logarithmic tree-indexed symbol and data lookup (`SymIndex`, `gen_multi_sym_index`).
-/

@[expose] public section

namespace Arm64.Obj

open Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection

/-! ## Block symbol lookup and resolution coherence -/

theorem mem_of_lookup_some {α : Type} {name : String} {v : α} :
    ∀ {syms : List (String × α)}, lookup name syms = some v → (name, v) ∈ syms
  | [], h => nomatch h
  | (k, val) :: rest, h => by
    unfold lookup at h
    simp only [List.find?_cons] at h
    split at h
    · rename_i heq
      simp only [Option.map_some, Option.some.injEq] at h
      rw [beq_iff_eq] at heq
      subst heq h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup_some h)

theorem lookup_none_of_not_mem_fst {α : Type} {name : String} :
    ∀ {syms : List (String × α)}, name ∉ syms.map (·.1) → lookup name syms = none
  | [], _ => rfl
  | (k, val) :: rest, hnm => by
    simp only [List.map_cons, List.mem_cons, not_or] at hnm
    have hne : (k == name) = false := beq_eq_false_iff_ne.2 ( Ne.symm hnm.1 )
    unfold lookup
    simp only [List.find?_cons, hne]
    exact lookup_none_of_not_mem_fst hnm.2

theorem lookupBlockSymAux_some {name : String} :
    ∀ {k : Nat} {blocks : List CodeBlock} {i off : Nat},
      lookupBlockSymAux name k blocks = some (i, off) →
      k ≤ i ∧ ∃ (hlt : i - k < blocks.length), lookup name blocks[i - k].symbols = some off
  | _, [], _, _, h => nomatch h
  | k, blk :: rest, i, off, h => by
    simp only [lookupBlockSymAux] at h
    cases hl : lookup name blk.symbols with
    | some off' =>
      rw [hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ Nat.le_refl k, ⟨by simp, by simpa [Nat.sub_self] using hl⟩ ⟩
    | none =>
      rw [hl] at h
      obtain ⟨hle, hlt, hfind⟩ := lookupBlockSymAux_some h
      refine ⟨by omega, ⟨by simp; omega, ?_⟩⟩
      have hidx : i - k = (i - (k + 1)) + 1 := by omega
      simpa [hidx] using hfind

theorem lookupBlockSym_some {name : String} {blocks : List CodeBlock} {i off : Nat}
    (h : lookupBlockSym name blocks = some (i, off)) :
    ∃ (hi : i < blocks.length), lookup name blocks[i].symbols = some off := by
  obtain ⟨_, hlt, hfind⟩ := lookupBlockSymAux_some h
  simpa using ⟨hlt, hfind⟩

theorem lookupBlockSymAux_of_lookup {name : String} {off : Nat} :
    ∀ {blocks : List CodeBlock} (k : Nat) {i : Nat} (hi : i < blocks.length),
      ((blocks.flatMap (·.symbols)).map (·.1)).Nodup →
      lookup name blocks[i].symbols = some off →
      lookupBlockSymAux name k blocks = some (k + i, off)
  | [], _, _, hi, _, _ => nomatch hi
  | blk :: rest, k, 0, _, _, hl => by
    simp only [List.getElem_cons_zero] at hl
    simp [lookupBlockSymAux, hl]
  | blk :: rest, k, i + 1, hi, hnd, hl => by
    simp only [List.getElem_cons_succ] at hl
    simp only [List.flatMap_cons, List.map_append, List.nodup_append] at hnd
    obtain ⟨_, hnd_rest, hdisj⟩ := hnd
    have hi' : i < rest.length := by simp at hi; omega
    have hmem_sym : (name, off) ∈ rest[i].symbols := mem_of_lookup_some hl
    have hmem_flat : (name, off) ∈ rest.flatMap (·.symbols) :=
      List.mem_flatMap.2 ⟨rest[i], List.getElem_mem hi', hmem_sym⟩
    have hmem_map : name ∈ (rest.flatMap (·.symbols)).map (·.1) :=
      List.mem_map.2 ⟨(name, off), hmem_flat, rfl⟩
    have hnot_blk : name ∉ blk.symbols.map (·.1) := fun hb => hdisj name hb name hmem_map rfl
    have hnone : lookup name blk.symbols = none := lookup_none_of_not_mem_fst hnot_blk
    simp only [lookupBlockSymAux, hnone]
    have ih := lookupBlockSymAux_of_lookup (k + 1) hi' hnd_rest hl
    simpa [Nat.add_right_comm k 1 i, Nat.add_assoc] using ih

theorem lookupBlockSym_of_lookup {name : String} {off : Nat} {blocks : List CodeBlock}
    {i : Nat} (hi : i < blocks.length)
    (hnd : ((blocks.flatMap (·.symbols)).map (·.1)).Nodup)
    (hl : lookup name blocks[i].symbols = some off) :
    lookupBlockSym name blocks = some (i, off) := by
  simpa [lookupBlockSym] using lookupBlockSymAux_of_lookup 0 hi hnd hl

/-- When symbol names across all blocks of `lib` are distinct (`symbols_nodup`), block `i`'s
    local symbol resolution under `lib.blockPlacement mpl i` agrees with `lib.resolve mpl` on
    every symbol. -/
theorem MultiPlacedLib.resolve_block {lib : MultiPlacedLib} {mpl : MultiPlacement} {i : Nat}
    (hi : i < lib.blocks.length) (hnd : ((lib.blocks.flatMap (·.symbols)).map (·.1)).Nodup)
    (sym : String) :
    lib.blocks[i].resolve (lib.blockPlacement mpl i) sym = lib.resolve mpl sym := by
  unfold CodeBlock.resolve
  cases hl : lookup sym lib.blocks[i].symbols with
  | none => rfl
  | some off =>
    have hblk := lookupBlockSym_of_lookup hi hnd hl
    simp [MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hblk]

theorem MultiPlacedLib.resolve_block_fun {lib : MultiPlacedLib} {mpl : MultiPlacement} {i : Nat}
    (hi : i < lib.blocks.length) (hnd : ((lib.blocks.flatMap (·.symbols)).map (·.1)).Nodup) :
    lib.blocks[i].resolve (lib.blockPlacement mpl i) = lib.resolve mpl :=
  funext (lib.resolve_block hi hnd)

@[simp] theorem MultiPlacedLib.blockLib_text {lib : MultiPlacedLib} {i : Nat}
    (hi : i < lib.blocks.length) : (lib.blockLib i).text = lib.blocks[i] := by
  simp only [MultiPlacedLib.blockLib]
  exact Interned.getD_of_lt hi

@[simp] theorem MultiPlacedLib.blockLib_data (lib : MultiPlacedLib) (i : Nat) :
    (lib.blockLib i).data = lib.data := rfl

/-- Segment bridge for block `i` of a `MultiPlacedLib`: from `lib.blocks[i].checkSegment fo ws R = true`,
    `lib.blockProgram mpl i X (fun _ => none) svc` holds the patched words at `mpl.base i + fo`
    resolved through `lib.resolve mpl`. -/
theorem MultiPlacedLib.hasWords_of_checkSegment {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {i : Nat} (hi : i < lib.blocks.length) {fo : Nat} {ws : List (BitVec 32)}
    {R : List RelocEntry} {X : String → Option (State → State)} {svc : State → State}
    (hpl : lib.Placeable mpl)
    (hchk : lib.blocks[i].checkSegment fo ws R = true) :
    (lib.blockProgram mpl i X (fun _ => none) svc).hasWords
        (mpl.base i + BitVec.ofNat 64 fo)
        (patchRelocs R ws (mpl.base i + BitVec.ofNat 64 fo) (lib.resolve mpl)) ∧
      ∀ r ∈ R, CodeRelocInRange r.kind
        (mpl.base i + BitVec.ofNat 64 fo + BitVec.ofNat 64 r.off)
        (addSignedAddr (lib.resolve mpl r.sym) r.addend) := by
  have hP := hpl.blocks_ok i hi
  have hlen : fo + 4 * ws.length ≤ lib.blocks[i].code.length := by
    have hchk' := hchk
    simp only [CodeBlock.checkSegment, Bool.and_eq_true, decide_eq_true_eq] at hchk'
    have hpos : 0 < ws.length := hchk'.1.1.1.2
    have ⟨hlen', _⟩ := CodeBlock.segWordsOk_spec hchk'.2
    rw [List.length_drop] at hlen'; omega
  have hhook : (lib.blockProgram mpl i X (fun _ => none) svc).hookFree fo (4 * ws.length) := by
    unfold MultiPlacedLib.blockProgram
    exact PlacedLib.hookFree_program_noOverrides (by rw [lib.blockLib_text hi]; exact hP)
      (by rw [lib.blockLib_text hi]; exact hlen)
  have hseg := CodeBlock.hasWords_of_checkSegment (prog := lib.blockProgram mpl i X (fun _ => none) svc)
    hP rfl (by simp [MultiPlacedLib.blockProgram, lib.blockLib_text hi]) hchk hhook
  rwa [lib.resolve_block_fun hi hpl.symbols_nodup] at hseg

/-- Step a relaxable `ADRP`+`ADD` pair at byte offset `off` of block `i` of a `MultiPlacedLib`
    under both linker encodings (`ADRP`+`ADD` and `NOP`+`ADR`). -/
theorem MultiPlacedLib.sepWP_relaxablePair {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {i : Nat} (hi : i < lib.blocks.length) {off : Nat} {r : RelocEntry} {rd : BitVec 5}
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp} {X : String → Option (State → State)} {svc : State → State}
    (hpl : lib.Placeable mpl)
    (hrel : lib.blocks[i].relaxableAt off = true)
    (hr : lib.blocks[i].relocAt? off = some r)
    (hrd : (lib.blocks[i].wordAt off).extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (hpc : s.pc = mpl.base i + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP (lib.blockProgram mpl i X (fun _ => none) svc) tgt
      ((s.writeReg64 (.gpr rd) (addSignedAddr (lib.resolve mpl r.sym) r.addend)).setPC
        (mpl.base i + BitVec.ofNat 64 (off + 8)))
      P post oom) :
    SepWP (lib.blockProgram mpl i X (fun _ => none) svc) tgt s P post oom := by
  have hP := hpl.blocks_ok i hi
  have ⟨r2, hr2⟩ : ∃ r2, lib.blocks[i].relocAt? (off + 4) = some r2 := by
    unfold CodeBlock.relaxableAt at hrel
    rw [hr] at hrel
    cases h2 : lib.blocks[i].relocAt? (off + 4) with
    | none => rw [h2] at hrel; cases hrel
    | some r2 => exact ⟨r2, rfl⟩
  have hlen2 := (hP.relocs_ok r2 (CodeBlock.relocAt?_mem hr2)).2.1
  rw [CodeBlock.relocAt?_off hr2] at hlen2
  have hhook : (lib.blockProgram mpl i X (fun _ => none) svc).hookFree off 8 := by
    unfold MultiPlacedLib.blockProgram
    exact PlacedLib.hookFree_program_noOverrides (by rw [lib.blockLib_text hi]; exact hP)
      (by rw [lib.blockLib_text hi]; omega)
  have htarget : lib.blocks[i].target (lib.blockPlacement mpl i) r =
      addSignedAddr (lib.resolve mpl r.sym) r.addend := by
    simp [CodeBlock.target, lib.resolve_block hi hpl.symbols_nodup]
  exact CodeBlock.sepWP_relaxablePair_of_hookFree hP rfl
    (by simp [MultiPlacedLib.blockProgram, lib.blockLib_text hi]) hrel hr hrd hrd31 hhook
    hpc hrun (by rw [htarget]; exact hnext)

/-! ## Projection to `lib.blockLib i` -/

theorem lookup_none_of_lookupBlockSymAux_none {name : String} :
    ∀ {k : Nat} {blocks : List CodeBlock},
      lookupBlockSymAux name k blocks = none →
      ∀ (i : Nat) (hi : i < blocks.length), lookup name blocks[i].symbols = none
  | _, [], _, _, hi => nomatch hi
  | k, blk :: rest, h, 0, _ => by
    simp only [lookupBlockSymAux] at h
    cases hl : lookup name blk.symbols with
    | none => exact hl
    | some _ => rw [hl] at h; cases h
  | k, blk :: rest, h, i + 1, hi => by
    simp only [lookupBlockSymAux] at h
    cases hl : lookup name blk.symbols with
    | none =>
      rw [hl] at h
      exact lookup_none_of_lookupBlockSymAux_none h i (by simp at hi; omega)
    | some _ => rw [hl] at h; cases h

theorem lookup_none_of_lookupBlockSym_none {name : String} {blocks : List CodeBlock}
    (h : lookupBlockSym name blocks = none) {i : Nat} (hi : i < blocks.length) :
    lookup name blocks[i].symbols = none :=
  lookup_none_of_lookupBlockSymAux_none h i hi

theorem MultiPlacedLib.patchDataReloc_blockLib {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {i : Nat} (hi : i < lib.blocks.length)
    (hnd : ((lib.blocks.flatMap (·.symbols)).map (·.1)).Nodup) :
    (lib.blockLib i).patchDataReloc (lib.blockPlacement mpl i) = lib.patchDataReloc mpl := by
  funext addr bytes r
  simp [PlacedLib.patchDataReloc, MultiPlacedLib.patchDataReloc, lib.blockLib_text hi,
    lib.resolve_block hi hnd]

theorem MultiPlacedLib.patchedData_blockLib {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {i : Nat} (hi : i < lib.blocks.length) (hpl : lib.Placeable mpl)
    {d : SymDataInfo} (hd : d ∈ lib.data) :
    (lib.blockLib i).patchedData (lib.blockPlacement mpl i) d = lib.patchedData mpl d := by
  have hd_none := (hpl.data_ok d hd).1
  have hρ : (lib.blockPlacement mpl i).ρ d.sym = mpl.ρ d.sym := by
    simp [MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hd_none]
  simp [PlacedLib.patchedData, MultiPlacedLib.patchedData, hρ,
    lib.patchDataReloc_blockLib hi hpl.symbols_nodup]

theorem MultiPlacedLib.placeable_blockLib {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {i : Nat} (hi : i < lib.blocks.length) (hpl : lib.Placeable mpl) :
    (lib.blockLib i).Placeable (lib.blockPlacement mpl i) := by
  refine ⟨by rw [lib.blockLib_text hi]; exact hpl.blocks_ok i hi, hpl.data_nodup, ?_, ?_⟩
  · intro d hd
    have hdo := hpl.data_ok d hd
    have hρ : (lib.blockPlacement mpl i).ρ d.sym = mpl.ρ d.sym := by
      simp [MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hdo.1]
    rw [lib.blockLib_text hi, hρ]
    exact ⟨lookup_none_of_lookupBlockSym_none hdo.1 hi, hdo.2⟩
  · intro d hd r hr
    have hdo := hpl.data_ok d hd
    have hρ : (lib.blockPlacement mpl i).ρ d.sym = mpl.ρ d.sym := by
      simp [MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hdo.1]
    rw [lib.blockLib_text hi, lib.resolve_block hi hpl.symbols_nodup, hρ]
    exact hpl.data_relocs_ok d hd r hr

theorem MultiPlacedLib.inElf_blockLib_noExports {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {img : ElfImage} {i : Nat} (hi : i < lib.blocks.length)
    (hpl : lib.Placeable mpl) (hin : lib.InElf img mpl) :
    { (lib.blockLib i) with exports := [] }.InElf img (lib.blockPlacement mpl i) := by
  refine ⟨by simpa [lib.blockLib_text hi, MultiPlacedLib.blockPlacement] using hin.blocks i hi,
    ?_, fun _ h => nomatch h⟩
  intro d hd
  have hdo := hpl.data_ok d hd
  have hρ : (lib.blockPlacement mpl i).ρ d.sym = mpl.ρ d.sym := by
    simp [MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hdo.1]
  have hpd : ({ (lib.blockLib i) with exports := [] } : PlacedLib).patchedData
      (lib.blockPlacement mpl i) d = lib.patchedData mpl d :=
    lib.patchedData_blockLib hi hpl hd
  rw [hρ, hpd]
  exact hin.data d hd

/-! ## Transfer to a loaded ELF -/

theorem MultiPlacedLib.CodeLoaded.of_keepsFrozen {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {m m' : Memory} (h : lib.CodeLoaded mpl m) (hkf : m.KeepsFrozen m') :
    lib.CodeLoaded mpl m' :=
  fun i hi => (h i hi).of_keepsFrozen hkf

/-- Block `i`'s placed program has its code loaded in the initial memory of an executable
    containing `lib`, for any externs, overrides, and `svc`. -/
theorem MultiPlacedLib.blockProgram_codeLoaded_of_inElf {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {img : ElfImage} {inputs : ProcessInputs} {s : State}
    (hpl : lib.Placeable mpl) (hin : lib.InElf img mpl) (hload : img.loadState inputs = .ok s)
    {i : Nat} (hi : i < lib.blocks.length)
    {X O : String → Option (State → State)} {svc : State → State} :
    (lib.blockProgram mpl i X O svc).CodeLoaded s.mem := by
  have hpl_blk : ({ (lib.blockLib i) with exports := [] } : PlacedLib).Placeable
      (lib.blockPlacement mpl i) := by
    have := lib.placeable_blockLib hi hpl
    exact ⟨this.text, this.data_nodup, this.data_ok, this.data_relocs_ok⟩
  exact PlacedLib.codeLoaded_of_inElf hpl_blk (lib.inElf_blockLib_noExports hi hpl hin) hload

/-- Every block of `lib` is `CodeLoaded` in the initial memory of an executable containing `lib`. -/
theorem MultiPlacedLib.codeLoaded_of_inElf {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {img : ElfImage} {inputs : ProcessInputs} {s : State}
    (hpl : lib.Placeable mpl) (hin : lib.InElf img mpl) (hload : img.loadState inputs = .ok s) :
    lib.CodeLoaded mpl s.mem :=
  fun _ hi => lib.blockProgram_codeLoaded_of_inElf hpl hin hload hi

/-- Writable data objects of `lib` under `mpl` share no byte with any other data object. -/
def MultiPlacedLib.DataDisjoint (lib : MultiPlacedLib) (mpl : MultiPlacement) : Prop :=
  lib.data.Pairwise fun d₁ d₂ =>
    (d₁.readOnly = true ∧ d₂.readOnly = true) ∨
      ∀ a, InRegion (mpl.ρ d₁.sym) (lib.patchedData mpl d₁).length a →
        ¬ InRegion (mpl.ρ d₂.sym) (lib.patchedData mpl d₂).length a

theorem MultiPlacedLib.dataDisjoint_of_sorted {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (h : rangesSorted (lib.data.map fun d => (mpl.ρ d.sym, (lib.patchedData mpl d).length)) = true) :
    lib.DataDisjoint mpl := by
  have ⟨hpw, hb⟩ := rangesSorted_pairwise h
  rw [List.pairwise_map] at hpw
  refine hpw.imp_of_mem fun {d₁ d₂} _ hd₂ hle => Or.inr fun a h1 => ?_
  exact not_inRegion_of_le hle (hb _ (List.mem_map_of_mem hd₂)) h1

theorem MultiPlacedLib.satisfies_dataRO_of_inElf {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {img : ElfImage} {inputs : ProcessInputs} {s : State}
    (hpl : lib.Placeable mpl) (hin : lib.InElf img mpl) (hload : img.loadState inputs = .ok s)
    (hne : 0 < lib.blocks.length) {d : SymDataInfo} (hd : d ∈ lib.data) (hro : d.readOnly = true) :
    s.mem ⊨ pointsToBytesRO (mpl.ρ d.sym) (lib.patchedData mpl d) := by
  have hpl0 : ({ (lib.blockLib 0) with exports := [] } : PlacedLib).Placeable
      (lib.blockPlacement mpl 0) := by
    have := lib.placeable_blockLib hne hpl
    exact ⟨this.text, this.data_nodup, this.data_ok, this.data_relocs_ok⟩
  have hin0 := lib.inElf_blockLib_noExports hne hpl hin
  have hsat := PlacedLib.satisfies_dataRO_of_inElf hpl0 hin0 hload hd hro
  have hdo := hpl.data_ok d hd
  have hρ : (lib.blockPlacement mpl 0).ρ d.sym = mpl.ρ d.sym := by
    simp [MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hdo.1]
  have hpd : ({ (lib.blockLib 0) with exports := [] } : PlacedLib).patchedData
      (lib.blockPlacement mpl 0) d = lib.patchedData mpl d :=
    lib.patchedData_blockLib hne hpl hd
  rwa [hρ, hpd] at hsat

theorem MultiPlacedLib.satisfies_dataInit_of_inElf {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {img : ElfImage} {inputs : ProcessInputs} {s : State}
    (hpl : lib.Placeable mpl) (hin : lib.InElf img mpl) (hload : img.loadState inputs = .ok s)
    (hne : 0 < lib.blocks.length) (hdisj : lib.DataDisjoint mpl) :
    s.mem ⊨ lib.dataInit mpl := by
  let lib0 : PlacedLib := { (lib.blockLib 0) with exports := [] }
  let pl0 := lib.blockPlacement mpl 0
  have hpl0 : lib0.Placeable pl0 := by
    have := lib.placeable_blockLib hne hpl
    exact ⟨this.text, this.data_nodup, this.data_ok, this.data_relocs_ok⟩
  have hin0 := lib.inElf_blockLib_noExports hne hpl hin
  have hρ_eq : ∀ d ∈ lib.data, pl0.ρ d.sym = mpl.ρ d.sym := fun d hd => by
    simp [pl0, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, (hpl.data_ok d hd).1]
  have hpd_eq : ∀ d ∈ lib.data, lib0.patchedData pl0 d = lib.patchedData mpl d :=
    fun d hd => lib.patchedData_blockLib hne hpl hd
  have hdisj0 : lib0.DataDisjoint pl0 := by
    refine hdisj.imp_of_mem fun {d₁ d₂} hd₁ hd₂ h => ?_
    rcases h with hro | hreg
    · exact Or.inl hro
    · right
      rw [hρ_eq d₁ hd₁, hpd_eq d₁ hd₁, hρ_eq d₂ hd₂, hpd_eq d₂ hd₂]
      exact hreg
  have hsat := PlacedLib.satisfies_dataInit_of_inElf hpl0 hin0 hload hdisj0
  have hinit_eq : lib0.dataInit pl0 = lib.dataInit mpl := by
    unfold PlacedLib.dataInit MultiPlacedLib.dataInit
    refine congrArg sepAll (List.map_congr_left fun d hd => ?_)
    rw [hρ_eq d hd, hpd_eq d hd]
  rwa [hinit_eq] at hsat

/-- Lower `lib.subroutineOk fnName spec X O` at a concrete multi-block placement `mpl` contained
    in `img` to a `Steps Program.pureMem` execution, automatically supplying `lib.CodeLoaded mpl`
    from `InElf` and `KeepsFrozen`. -/
theorem MultiPlacedLib.subroutineOk_toPureMem {S α : Type} [ToBaseSpec S α]
    {lib : MultiPlacedLib} {fnName : String} {spec : MultiPlacement → S}
    {X O : String → Option (State → State)}
    (hok : lib.subroutineOk fnName spec X O) {mpl : MultiPlacement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable mpl) (hin : lib.InElf img mpl)
    (hload : img.loadState inputs = .ok s)
    (h_noPanic : ∀ i x s0 sf, (ToBaseSpec.toSpec (spec mpl) (mpl.base i)).onPanic x s0 sf = ⌜False⌝)
    (h_noExit : ∀ i x c s0 sf, (ToBaseSpec.toSpec (spec mpl) (mpl.base i)).onExit x c s0 sf = ⌜False⌝)
    (h_noOom : ∀ i x s0 sf, (ToBaseSpec.toSpec (spec mpl) (mpl.base i)).onOom x s0 sf = ⌜False⌝)
    {x : α} {R : SepProp} {s0 : State} (hfrozen : s.mem.KeepsFrozen s0.mem)
    (hpc : s0.pc = lib.fnAddr mpl fnName) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    {i off : Nat} (hfn : lookupBlockSym fnName lib.blocks = some (i, off))
    (hpre : s0.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base i)).pre x s0 ∗ R)
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      (lib.blockProgram mpl i X O).externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem → Steps Program.pureMem st (f st)) :
    ∃ sf : State,
      Steps Program.pureMem s0 sf ∧ Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
      (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base i)).post x s0 sf ∗ R) := by
  obtain ⟨_, i', off', hfn', hsub⟩ := hok
  rw [hfn] at hfn'
  injection hfn' with hfn_eq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hfn_eq
  have ⟨hi, _⟩ := lookupBlockSym_some hfn
  have hcl_all : lib.CodeLoaded mpl s0.mem :=
    (lib.codeLoaded_of_inElf hpl hin hload).of_keepsFrozen hfrozen
  have hcl_i : (lib.blockProgram mpl i X O).CodeLoaded s0.mem :=
    (lib.blockProgram_codeLoaded_of_inElf hpl hin hload hi).of_keepsFrozen hfrozen
  have hpre_cl : s0.mem ⊨
      (lib.withCodeLoaded mpl (ToBaseSpec.toSpec (spec mpl) (mpl.base i))).pre x s0 ∗ R := by
    show s0.mem ⊨ ((ToBaseSpec.toSpec (spec mpl) (mpl.base i)).pre x s0 ∗ ⌜lib.CodeLoaded mpl s0.mem⌝) ∗ R
    rw [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true hcl_all]
    exact hpre
  exact subroutine_ok_toPureMem (hsub mpl hpl) (h_noPanic i) (h_noExit i) (h_noOom i)
    hpc hrun hpre_cl hsp hcl_i h_hooks

/-- Outcome-preserving `MultiPlacedLib.subroutineOk_toPureMem`: lowers `lib.subroutineOk fnName spec X O`
    at multi-block placement `mpl` in `img` to `Steps Program.pureMem` preserving `onPanic`,
    `onExit`, and `onOom`. -/
theorem MultiPlacedLib.subroutineOk_toPureMem_outcome {S α : Type} [ToBaseSpec S α]
    {lib : MultiPlacedLib} {fnName : String} {spec : MultiPlacement → S}
    {X O : String → Option (State → State)}
    (hok : lib.subroutineOk fnName spec X O) {mpl : MultiPlacement} {img : ElfImage}
    {inputs : ProcessInputs} {s : State} (hpl : lib.Placeable mpl) (hin : lib.InElf img mpl)
    (hload : img.loadState inputs = .ok s)
    {x : α} {R : SepProp} {s0 : State} (hfrozen : s.mem.KeepsFrozen s0.mem)
    (hpc : s0.pc = lib.fnAddr mpl fnName) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    {i off : Nat} (hfn : lookupBlockSym fnName lib.blocks = some (i, off))
    (hpre : s0.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base i)).pre x s0 ∗ R)
    (h_hooks : ∀ (pc : BitVec 64) (f : State → State) (st : State),
      (lib.blockProgram mpl i X O).externAt? pc = some f → st.pc = pc → st.status = .Running →
      s0.mem.KeepsFrozen st.mem → Steps Program.pureMem st (f st)) :
    ∃ sf : State,
      Steps Program.pureMem s0 sf ∧
      SubroutineOutcome (ToBaseSpec.toSpec (spec mpl) (mpl.base i)) x R s0 sf := by
  obtain ⟨_, i', off', hfn', hsub⟩ := hok
  rw [hfn] at hfn'
  injection hfn' with hfn_eq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hfn_eq
  have ⟨hi, _⟩ := lookupBlockSym_some hfn
  have hcl_all : lib.CodeLoaded mpl s0.mem :=
    (lib.codeLoaded_of_inElf hpl hin hload).of_keepsFrozen hfrozen
  have hcl_i : (lib.blockProgram mpl i X O).CodeLoaded s0.mem :=
    (lib.blockProgram_codeLoaded_of_inElf hpl hin hload hi).of_keepsFrozen hfrozen
  have hpre_cl : s0.mem ⊨
      (lib.withCodeLoaded mpl (ToBaseSpec.toSpec (spec mpl) (mpl.base i))).pre x s0 ∗ R := by
    show s0.mem ⊨ ((ToBaseSpec.toSpec (spec mpl) (mpl.base i)).pre x s0 ∗ ⌜lib.CodeLoaded mpl s0.mem⌝) ∗ R
    rw [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true hcl_all]
    exact hpre
  exact subroutine_ok_toPureMem_outcome (hsub mpl hpl) hpc hrun hpre_cl hsp hcl_i h_hooks

/-! ## Cross-block stepping and calls -/

/-- Switch the active `Program` in `SepWP` from `P` to `Q` when both have the same hooks and `svc`
    handler and `Q.CodeLoaded s.mem` holds at the current state `s`. -/
theorem _root_.ProofLib.SepWP.of_sameHooks {P Q : Program} {target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hext : ∀ pc, Q.externAt? pc = P.externAt? pc) (hsvc : Q.svc = P.svc)
    (hQL : Q.CodeLoaded s.mem) (h : SepWP Q target_pc s Pre post oom) :
    SepWP P target_pc s Pre post oom := by
  unfold SepWP reaches_pc at *
  intro R hm _
  obtain ⟨sf, hsteps, hout⟩ := h R hm hQL
  exact ⟨sf, Steps.of_sameHooks hext hsvc hsteps, hout⟩

@[simp] theorem MultiPlacedLib.externAt?_blockProgram_none (lib : MultiPlacedLib)
    (mpl : MultiPlacement) (i : Nat) {svc : State → State} (pc : BitVec 64) :
    (lib.blockProgram mpl i (fun _ => none) (fun _ => none) svc).externAt? pc = none := by
  dsimp only [Program.externAt?, Program.hookAtOff?, MultiPlacedLib.blockProgram, PlacedLib.program]
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  simp only [ite_self, h0, Option.or_self]

@[simp] theorem PlacedLib.externAt?_program_none (lib : PlacedLib)
    (pl : Placement) {svc : State → State} (pc : BitVec 64) :
    (lib.program pl (fun _ => none) (fun _ => none) svc).externAt? pc = none := by
  dsimp only [Program.externAt?, Program.hookAtOff?, PlacedLib.program]
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  simp only [ite_self, h0, Option.or_self]

@[simp] theorem PlacedLib.externAt?_program_rebase_none (lib : PlacedLib)
    (pl : Placement) (b : BitVec 64) {svc : State → State} (pc : BitVec 64) :
    ((lib.program pl (fun _ => none) (fun _ => none) svc).rebase b (fun _ => none)).externAt? pc = none := by
  dsimp only [Program.externAt?, Program.hookAtOff?, Program.rebase, PlacedLib.program]
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  simp only [ite_self, h0, Option.or_self]

@[simp] theorem MultiPlacedLib.externAt?_blockProgram_rebase_none (lib : MultiPlacedLib)
    (mpl : MultiPlacement) (i : Nat) (b : BitVec 64) {svc : State → State} (pc : BitVec 64) :
    ((lib.blockProgram mpl i (fun _ => none) (fun _ => none) svc).rebase b (fun _ => none)).externAt? pc = none :=
  PlacedLib.externAt?_program_rebase_none _ _ _ _

@[simp] theorem PlacedLib.externAt?_mk_program_none (lib : PlacedLib)
    (pl : Placement) (b : BitVec 64) (c : List (BitVec 8)) (syms : List (String × Nat))
    {svc svc' : State → State} (pc : BitVec 64) :
    ({ base := b, code := c, symbols := syms,
       stubs := (lib.program pl (fun _ => none) (fun _ => none) svc).stubs,
       svc := svc' } : Program).externAt? pc = none := by
  dsimp only [Program.externAt?, Program.hookAtOff?, PlacedLib.program]
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  simp only [ite_self, h0, Option.or_self]

@[simp] theorem MultiPlacedLib.externAt?_mk_blockProgram_none (lib : MultiPlacedLib)
    (mpl : MultiPlacement) (i : Nat) (b : BitVec 64) (c : List (BitVec 8))
    (syms : List (String × Nat)) {svc svc' : State → State} (pc : BitVec 64) :
    ({ base := b, code := c, symbols := syms,
       stubs := (lib.blockProgram mpl i (fun _ => none) (fun _ => none) svc).stubs,
       svc := svc' } : Program).externAt? pc = none :=
  PlacedLib.externAt?_mk_program_none _ _ _ _ _ _

/-- When blocks `i` and `j` share the same external hook symbol list `externs`, their placed
    programs `lib.blockProgram mpl i X` and `lib.blockProgram mpl j X` expose identical hook
    tables `externAt?` at every PC for any external hook map `X`. -/
theorem MultiPlacedLib.externAt?_blockProgram_eq_of_externs_eq {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {i j : Nat} {X : String → Option (State → State)}
    {svc : State → State}
    (hext : (lib.blockLib i).text.externs = (lib.blockLib j).text.externs) (pc : BitVec 64) :
    (lib.blockProgram mpl i X (fun _ => none) svc).externAt? pc =
      (lib.blockProgram mpl j X (fun _ => none) svc).externAt? pc := by
  have key : ∀ (b : BitVec 64) (e : String),
      ((lib.resolve mpl e - b).toNat == (pc - b).toNat) = (lib.resolve mpl e == pc) := by
    intro b e
    cases h : lib.resolve mpl e == pc with
    | true =>
      have heq := beq_iff_eq.1 h
      subst heq
      simp
    | false =>
      rw [beq_eq_false_iff_ne] at h ⊢
      intro hnat
      apply h
      have hbv := BitVec.eq_of_toNat_eq hnat
      have : (lib.resolve mpl e - b) + b = (pc - b) + b := congrArg (· + b) hbv
      simpa [BitVec.sub_add_cancel] using this
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program, MultiPlacedLib.blockPlacement,
    Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none, List.findSome?_map, Function.comp_def, key, hext]

/-- Switch a `SepWP` goal with external hooks `X` from block `i` to block `j` of `lib` using
    `lib.CodeLoaded` when both blocks share the same `externs` list. -/
theorem MultiPlacedLib.sepWP_of_other_block_hooks {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {i j : Nat} {X : String → Option (State → State)} {svc : State → State}
    {target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hj : j < lib.blocks.length)
    (hext : (lib.blockLib i).text.externs = (lib.blockLib j).text.externs)
    (hcl : lib.CodeLoaded mpl s.mem)
    (h : SepWP (lib.blockProgram mpl j X (fun _ => none) svc) target_pc s Pre post oom) :
    SepWP (lib.blockProgram mpl i X (fun _ => none) svc) target_pc s Pre post oom :=
  SepWP.of_sameHooks
    (P := lib.blockProgram mpl i X (fun _ => none) svc)
    (Q := lib.blockProgram mpl j X (fun _ => none) svc)
    (lib.externAt?_blockProgram_eq_of_externs_eq hext.symm) rfl
    ((hcl j hj).of_base_code rfl rfl) h

/-- Switch a hook-free `SepWP` goal from block `i` to block `j` of `lib` using `lib.CodeLoaded`. -/
theorem MultiPlacedLib.sepWP_of_other_block {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {i j : Nat} {target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hj : j < lib.blocks.length) (hcl : lib.CodeLoaded mpl s.mem)
    (h : SepWP (lib.blockProgram mpl j) target_pc s Pre post oom) :
    SepWP (lib.blockProgram mpl i) target_pc s Pre post oom :=
  SepWP.of_sameHooks (P := lib.blockProgram mpl i) (Q := lib.blockProgram mpl j)
    (by simp) rfl (hcl j hj) h

/-- Framed cross-block subroutine call from block `i` into block `j` of a hook-free
    `MultiPlacedLib`, using `lib.CodeLoaded mpl s.mem` at the call site. -/
theorem MultiPlacedLib.sepWP_call_block {α : Type} {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {i j : Nat} {entry target_pc ret_pc : BitVec 64} {spec : Spec α}
    (hj : j < lib.blocks.length)
    (hcall : subroutine_ok (lib.blockProgram mpl j) entry spec)
    {x : α} {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hcl : lib.CodeLoaded mpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP (lib.blockProgram mpl i) target_pc sf (spec.post x s sf ∗ F) post oom)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP (lib.blockProgram mpl i) target_pc s Pre post oom :=
  SepWP.call_subroutine_frame_other (P := lib.blockProgram mpl i) (Q := lib.blockProgram mpl j)
    hcall (by simp) rfl (hcl j hj) hpc hrun hsp_align hlr hpre
    h_no_panic h_no_exit (fun sf hpc' hrun' hsp' hcs' _ => hnext sf hpc' hrun' hsp' hcs') h_oom

/-- Transfer a `subroutine_ok` proved on block `j` of a `MultiPlacedLib` (wrapped with
    `lib.withCodeLoaded mpl`) to any hook-free program `P` (such as block `i`'s program
    `lib.blockProgram mpl i` or `(blkPC.rebase blkPl.base (fun _ => none))`). Because
    `(lib.withCodeLoaded mpl spec).pre` carries `⌜lib.CodeLoaded mpl s0.mem⌝`, the resulting
    `subroutine_ok P entry (lib.withCodeLoaded mpl spec)` works directly with `wp_call` / `wpp_call`. -/
theorem MultiPlacedLib.subroutine_ok_of_block {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {j : Nat} {entry : BitVec 64} {spec : Spec α}
    (hj : j < lib.blocks.length)
    (hcall : subroutine_ok (lib.blockProgram mpl j) entry (lib.withCodeLoaded mpl spec))
    (hext : ∀ pc, P.externAt? pc = none := by intro; simp)
    (hsvc : P.svc = execSyscall := by rfl) :
    subroutine_ok P entry (lib.withCodeLoaded mpl spec) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff] at hcall ⊢
  intro x R s0 hpc hrun hpre hsp _
  have hpre' : s0.mem ⊨ ⌜lib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
    simpa [MultiPlacedLib.withCodeLoaded, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨sf, hsteps, hout⟩ := hcall x R s0 hpc hrun hpre hsp (hpre'.1 j hj)
  exact ⟨sf, Steps.of_sameHooks
    (by intro pc; simp [hext pc])
    (by simp [hsvc, MultiPlacedLib.blockProgram, PlacedLib.program]) hsteps, hout⟩

/-- Transfer a `subroutine_ok` proved on block `j` of a `MultiPlacedLib` with extern hooks `X`
    (wrapped with `lib.withCodeLoaded mpl`) to any program `P` agreeing on `externAt?` and `svc`
    (such as block `i`'s program `lib.blockProgram mpl i X` when blocks `i` and `j` share externs). -/
theorem MultiPlacedLib.subroutine_ok_of_block_hooks {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {j : Nat} {entry : BitVec 64} {spec : Spec α}
    {X : String → Option (State → State)} {svc : State → State}
    (hj : j < lib.blocks.length)
    (hcall : subroutine_ok (lib.blockProgram mpl j X (fun _ => none) svc) entry
      (lib.withCodeLoaded mpl spec))
    (hext : ∀ pc, (lib.blockProgram mpl j X (fun _ => none) svc).externAt? pc = P.externAt? pc)
    (hsvc : (lib.blockProgram mpl j X (fun _ => none) svc).svc = P.svc := by rfl) :
    subroutine_ok P entry (lib.withCodeLoaded mpl spec) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff] at hcall ⊢
  intro x R s0 hpc hrun hpre hsp _
  have hpre' : s0.mem ⊨ ⌜lib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
    simpa [MultiPlacedLib.withCodeLoaded, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at hpre'
  have hcl_j : (lib.blockProgram mpl j X (fun _ => none) svc).CodeLoaded s0.mem :=
    (hpre'.1 j hj).of_base_code rfl rfl
  obtain ⟨sf, hsteps, hout⟩ := hcall x R s0 hpc hrun hpre hsp hcl_j
  exact ⟨sf, Steps.of_sameHooks hext hsvc hsteps, hout⟩

/-- Transfer a `subroutine_ok` proved on hook-free block `j` of a `MultiPlacedLib` (wrapped with
    `lib.withCodeLoaded mpl`) across all four `SubroutineOutcome`s to any program `P` with
    `P.svc = execSyscall` whose extern hooks are unfetched (`P.HooksUnfetched s0.mem`), without
    requiring `P` itself to have no extern hooks. -/
theorem MultiPlacedLib.subroutine_ok_of_block_unfetched {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {j : Nat} {entry : BitVec 64} {spec : Spec α}
    (hj : j < lib.blocks.length)
    (hcall : subroutine_ok (lib.blockProgram mpl j) entry (lib.withCodeLoaded mpl spec))
    (hhooks : ∀ m, P.CodeLoaded m → P.HooksUnfetched m)
    (hsvc : P.svc = execSyscall := by rfl) :
    subroutine_ok P entry (lib.withCodeLoaded mpl spec) := by
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp hcode
  have hpre' : s0.mem ⊨ ⌜lib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
    simpa [MultiPlacedLib.withCodeLoaded, sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨sf, hsteps, hout⟩ :=
    subroutine_ok_toPureMem_outcome hcall hpc hrun hpre hsp (hpre'.1 j hj)
      (fun pc _ _ he _ _ _ => by simp at he) rfl
  have hend : sf.status = .Running ∨ sf.status = .Panicked ∨
      (∃ c, sf.status = .Exited c) ∨ sf.status = .OutOfMemory := by
    rcases hout with ⟨hret, _, _⟩ | ⟨hp, _⟩ | ⟨c, hc, _⟩ | ⟨ho, _⟩
    · exact Or.inl hret.2.2
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc⟩))
    · exact Or.inr (Or.inr (Or.inr ho))
  exact ⟨sf, Steps.of_pureMem_outcome hsvc (hhooks s0.mem hcode) (Memory.KeepsFrozen.refl _)
    hsteps hend, hout⟩

/-- Lift a `subroutine_ok` proved on hook-free block `j` of a `MultiPlacedLib` (wrapped with
    `lib.withCodeLoaded mpl`) directly to `subroutine_ok P entry spec` across all four
    `SubroutineOutcome`s whenever `P.CodeLoaded` implies `lib.CodeLoaded mpl` and `P.HooksUnfetched`. -/
theorem MultiPlacedLib.subroutine_ok_of_pureMem {α : Type} {lib : MultiPlacedLib}
    {mpl : MultiPlacement} {P : Program} {j : Nat} {entry : BitVec 64} {spec : Spec α}
    (hj : j < lib.blocks.length)
    (hcall : subroutine_ok (lib.blockProgram mpl j) entry (lib.withCodeLoaded mpl spec))
    (hcl : ∀ m, P.CodeLoaded m → lib.CodeLoaded mpl m)
    (hhooks : ∀ m, P.CodeLoaded m → P.HooksUnfetched m)
    (hsvc : P.svc = execSyscall := by rfl) :
    subroutine_ok P entry spec := by
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp hcode
  have hpre_cl : s0.mem ⊨ (lib.withCodeLoaded mpl spec).pre x s0 ∗ R := by
    show s0.mem ⊨ (spec.pre x s0 ∗ ⌜lib.CodeLoaded mpl s0.mem⌝) ∗ R
    rw [sepConj_comm _ ⌜_⌝, pure_sepConj_of_true (hcl s0.mem hcode)]
    exact hpre
  obtain ⟨sf, hsteps, hout⟩ := reaches_outcome_iff.1 (subroutine_ok_iff.1
    (MultiPlacedLib.subroutine_ok_of_block_unfetched hj hcall hhooks hsvc)
    x R s0 hpc hrun hpre_cl hsp) hcode
  exact ⟨sf, hsteps, hout⟩

/-- Split a `SepWP` proof at an intermediate PC `mid` and re-establish `lib.CodeLoaded mpl sm.mem`
    at `mid` across any preceding instructions (including `STR`/`STP` memory stores). -/
theorem MultiPlacedLib.seq_codeLoaded {prog : Program} {mid target_pc : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hcl : lib.CodeLoaded mpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      lib.CodeLoaded mpl sm.mem → SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

end Arm64.Obj

namespace ProofLib

open Lean Meta Elab Tactic Arm64 Arm64.Obj

/-- Re-establish `lib.CodeLoaded mpl sm.mem` at an intermediate cut point `mid` across preceding
    instructions (including `STR`/`STP` memory stores). Pair with `wp_steps; wp_call_block ...`. -/
syntax "wp_cut_codeLoaded" (ppSpace colGt term:max)? : tactic
macro_rules
  | `(tactic| wp_cut_codeLoaded) =>
    `(tactic| apply Arm64.Obj.MultiPlacedLib.seq_codeLoaded ‹_›)
  | `(tactic| wp_cut_codeLoaded $hcl:term) =>
    `(tactic| apply Arm64.Obj.MultiPlacedLib.seq_codeLoaded $hcl)

/-- Collect identifiers of `Obj.Placement`, `Obj.MultiPlacedLib`, and `Obj.CodeBlock` constants
    appearing in `e` so cross-block `s.pc = entry` equalities can unfold block placement wrappers
    inside their local proof. -/
public meta def collectPlacementIdents (e : Expr) : MetaM (Array Ident) := do
  let ref ← IO.mkRef #[]
  let addConst (nm : Name) : MetaM Unit := do
    let arr ← ref.get
    if !arr.any (fun i => i.getId == nm) then
      ref.set (arr.push (mkIdent nm))
  e.forEach fun sub => do
    if sub.isConst then
      let nm := sub.constName!
      let ty ← inferType sub
      let body := ty.getForallBody
      if body.isConstOf ``Arm64.Obj.Placement ||
         body.isConstOf ``Arm64.Obj.MultiPlacedLib ||
         body.isConstOf ``Arm64.Obj.CodeBlock then
        addConst nm
        if body.isConstOf ``Arm64.Obj.MultiPlacedLib then
          if let some cinfo := (← getEnv).find? nm then
            if let some val := cinfo.value? then
              val.forEach fun vsub => do
                if vsub.isConst then
                  let vty ← inferType vsub
                  if vty.getForallBody.isConstOf ``Arm64.Obj.CodeBlock then
                    addConst vsub.constName!
  ref.get

/-- Collect `(Placement.ρ pl sym, MultiPlacement.ρ mpl sym)` pairs appearing in `e` that are
    definitionally equal (i.e. non-block data/extern symbols). -/
public meta def collectRhoEqs (e mplE : Expr) : MetaM (Array (Expr × Expr)) := do
  let ref ← IO.mkRef #[]
  let seen ← IO.mkRef (#[] : Array Expr)
  e.forEach fun sub => do
    if sub.isAppOfArity ``Arm64.Obj.Placement.ρ 2 then
      let symE := sub.getArg! 1
      let prev ← seen.get
      unless prev.any (· == sub) do
        seen.set (prev.push sub)
        let rhs := mkApp2 (mkConst ``Arm64.Obj.MultiPlacement.ρ) mplE symE
        if ← withTransparency .all (isDefEq sub rhs) then
          ref.set ((← ref.get).push (sub, rhs))
  ref.get

/-- Step a cross-block subroutine call in a `MultiPlacedLib`: closes any active
    `wp_cut_codeLoaded` (`MultiPlacedLib.seq_codeLoaded`) segment via `SepWP.done` to refresh
    `lib.CodeLoaded mpl s.mem`, infers the target block index `j` from `hcall`, proves `s.pc = entry`,
    and invokes `wp_call (MultiPlacedLib.subroutine_ok_of_block (j := j) (by decide) hcall)`.
    Supports `wp_call_block hcall`, `wp_call_block hcall arg`, `wp_call_block hcall (x := arg)`,
    and `wp_call_block hcall ... (on_panic := term)`. -/
syntax "wp_call_block" ppSpace colGt term:max (ppSpace colGt wppCallOpt)* : tactic
public meta section
elab_rules : tactic
  | `(tactic| wp_call_block $hcall:term $[$opts:wppCallOpt]*) => do
    let _ ← tryTactic do
      let g ← getMainGoal
      let isSeqCodeLoaded ← g.withContext do
        let ty := (← instantiateMVars (← g.getType)).consumeMData
        unless ty.isAppOfArity ``SepWP 6 do return false
        let postExpr := (ty.getArg! 4).consumeMData
        unless postExpr.isLambda && postExpr.bindingBody!.consumeMData.isLambda do return false
        let body2 := postExpr.bindingBody!.consumeMData.bindingBody!.consumeMData
        match body2 with
        | .forallE _ dom _ _ => return dom.consumeMData.isAppOfArity ``MultiPlacedLib.CodeLoaded 3
        | _ => return false
      if isSeqCodeLoaded then
        let hclId ← freshIdent `hcl_m
        evalTactic (← `(tactic| (
          apply SepWP.done
          · first | wp_norm_lhs | wp_norm_goal | rfl
          · wp_norm_lhs
          intro $hclId:ident
        )))
      else
        throwError "not seq_codeLoaded"
    let g ← getMainGoal
    let (jIdx, entryStx?, plIdents, rhoEqs) ← g.withContext do
      let hcallExpr ← elabTerm hcall none
      let hcallTy ← inferType hcallExpr
      let (_, _, concl) ← forallMetaTelescopeReducing hcallTy
      let concl ← whnfR (← instantiateMVars concl)
      unless concl.isAppOfArity ``Arm64.subroutine_ok 4 do
        throwError "wp_call_block: expected `subroutine_ok` contract, got `{concl}`"
      let qProg := concl.getArg! 1
      let entryE := concl.getArg! 2
      let specE := concl.getArg! 3
      unless specE.isAppOfArity ``MultiPlacedLib.withCodeLoaded 4 do
        throwError "wp_call_block: expected callee spec wrapped with `MultiPlacedLib.withCodeLoaded`, got `{specE}`"
      let libE := specE.getArg! 1
      let mplE := specE.getArg! 2
      let mut foundJ : Option Nat := none
      for j in [:64] do
        let jStx := Syntax.mkNumLit (toString j)
        let libStx ← Term.exprToSyntax libE
        let mplStx ← Term.exprToSyntax mplE
        let cand ← elabTerm (← `(Arm64.Obj.MultiPlacedLib.blockProgram $libStx $mplStx $jStx)) none
        if ← withTransparency .all (isDefEq qProg cand) then
          foundJ := some j
          break
      let some j := foundJ
        | throwError "wp_call_block: could not match callee program `{qProg}` to `lib.blockProgram mpl j` for any `j < 64`"
      let goalTy ← instantiateMVars (← g.getType)
      let scanExpr := mkApp3 (mkConst ``And) goalTy entryE libE
      let plIds ← collectPlacementIdents scanExpr
      let rhoPairs ← collectRhoEqs goalTy mplE
      let mut rhoEqs : Array (TSyntax `term × TSyntax `term) := #[]
      for (lhsE, rhsE) in rhoPairs do
        rhoEqs := rhoEqs.push (← Term.exprToSyntax lhsE, ← Term.exprToSyntax rhsE)
      let eStx ← Term.exprToSyntax entryE
      return (j, some eStx, plIds, rhoEqs)
    for (lhsStx, rhsStx) in rhoEqs do
      let _ ← tryTactic do
        let hRhoId ← freshIdent `h_rho
        evalTactic (← `(tactic| have $hRhoId:ident : $lhsStx = $rhsStx := rfl))
    let jLit := Syntax.mkNumLit (toString jIdx)
    let gCur ← getMainGoal
    let (progStx, sStx, progIdents) ← gCur.withContext do
      let ty := (← instantiateMVars (← gCur.getType)).consumeMData
      let pE := ty.getArg! 0
      let pIdsRef ← IO.mkRef (#[] : Array Ident)
      pE.forEach fun sub => do
        if sub.isConst then
          let nm := sub.constName!
          let sTy ← inferType sub
          if sTy.getForallBody.isConstOf ``Arm64.Program then
            let pIds ← pIdsRef.get
            if !pIds.any (fun i => i.getId == nm) then
              pIdsRef.set (pIds.push (mkIdent nm))
      return (← Term.exprToSyntax pE, ← Term.exprToSyntax (ty.getArg! 2), ← pIdsRef.get)
    let dsimpIds : Array Ident := plIdents ++ #[
      mkIdent ``MultiPlacedLib.blockPlacement,
      mkIdent ``MultiPlacedLib.fnAddr,
      mkIdent ``MultiPlacedLib.resolve,
      mkIdent ``lookupBlockSym,
      mkIdent ``lookupBlockSymAux,
      mkIdent ``lookup]
    if let some eStx := entryStx? then
      let _ ← tryTactic do
        let hpcCallId ← freshIdent `hpc_call
        evalTactic (← `(tactic|
          have $hpcCallId:ident : ($sStx : Arm64.State).pc = $eStx := by
            simp only [wp_norm, arm64_norm]
            try simp [$[$dsimpIds:ident],*]
            try bv_omega))
    let hcallBlkId ← freshIdent `hcall_blk
    evalTactic (← `(tactic|
      have $hcallBlkId:ident :=
        Arm64.Obj.MultiPlacedLib.subroutine_ok_of_block (P := $progStx) (j := $jLit) (by decide) $hcall
          (by intro pc; simp only [$[$progIdents:ident],*,
            Arm64.Obj.PlacedLib.externAt?_mk_program_none,
            Arm64.Obj.MultiPlacedLib.externAt?_mk_blockProgram_none,
            Arm64.Obj.PlacedLib.externAt?_program_rebase_none,
            Arm64.Obj.MultiPlacedLib.externAt?_blockProgram_rebase_none,
            Arm64.Obj.PlacedLib.externAt?_program_none,
            Arm64.Obj.MultiPlacedLib.externAt?_blockProgram_none])
          (by simp [$[$progIdents:ident],*, Arm64.Obj.MultiPlacedLib.blockProgram, Arm64.Obj.PlacedLib.program, Arm64.Program.rebase])))
    evalTactic (← `(tactic| wp_call $hcallBlkId:ident $[$opts]*))
    let _ ← tryTactic do evalTactic (← `(tactic| clear $hcallBlkId:ident))
end

end ProofLib

namespace Arm64.Obj

open Arm64.Process ProofLib.ProgramReflection

/-! ## Kernel-checked `Placeable` and `InElf` for `MultiPlacedLib` -/

def allIdx {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | k, x :: xs => f k x && allIdx f (k + 1) xs

theorem allIdx_spec {α : Type} {f : Nat → α → Bool} :
    ∀ {k : Nat} {xs : List α}, allIdx f k xs = true →
      ∀ (i : Nat) (hi : i < xs.length), f (k + i) xs[i] = true
  | _, [], _, _, hi => nomatch hi
  | _, _ :: _, h, 0, _ => by simp only [allIdx, Bool.and_eq_true] at h; simpa using h.1
  | k, _ :: xs, h, i + 1, hi => by
    simp only [allIdx, Bool.and_eq_true] at h
    rw [show k + (i + 1) = (k + 1) + i by omega]
    exact allIdx_spec h.2 i (by simp at hi; omega)

/-- `CodeBlock.relocInRange` as a `Bool` (short-circuiting on `pl.relax` before inspecting
    relocation pairs or code words). -/
def CodeBlock.relocInRangeB (blk : CodeBlock) (pl : Placement) (kind : RelocKind) (off : Nat)
    (place target : BitVec 64) : Bool :=
  match kind with
  | .adrGotPage =>
    if pl.relax off && blk.gotPairAt off then true
    else Interned.sInRange (-4294967296) 4294967296 (pageOf target - pageOf place)
  | .ld64GotLo12Nc =>
    if 4 ≤ off && pl.relax (off - 4) && blk.gotPairAt (off - 4) then
      Interned.sInRange (-1048576) 1048576 (target - place)
    else if 4 ≤ off && pl.relax off && blk.gotPairAt (off - 4) then true
    else (target &&& 7#64) == 0#64
  | .tlsieAdrGottprelPage21 =>
    if pl.relax off && blk.tlsieRelaxableAt off then
      Nat.blt target.toNat 4294967296
    else Interned.sInRange (-4294967296) 4294967296 (pageOf target - pageOf place)
  | .tlsieLd64GottprelLo12Nc =>
    if pl.relax off && blk.tlsieRelaxableAt off then
      Nat.blt target.toNat 4294967296
    else (target &&& 7#64) == 0#64
  | _ => Interned.codeRelocInRangeB kind place target

theorem CodeBlock.relocInRange_of {blk : CodeBlock} {pl : Placement} {kind : RelocKind}
    {off : Nat} {place target : BitVec 64}
    (h : blk.relocInRangeB pl kind off place target = true) :
    blk.relocInRange pl kind off place target := by
  cases kind <;>
    (dsimp only [CodeBlock.relocInRangeB, CodeBlock.relocInRange] at h ⊢
     try exact Interned.codeRelocInRange_of h)
  · rw [Bool.and_comm (pl.relax off)] at h
    split <;> rename_i hcond <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
    · trivial
    · rw [Interned.sInRange_iff] at h
      exact ⟨by omega, by omega⟩
  · revert h
    by_cases h4 : 4 ≤ off <;> cases pl.relax (off - 4) <;> cases pl.relax off <;>
      cases blk.gotPairAt (off - 4) <;>
      simp [h4, Lo12Aligned, lo12AlignMask]
    all_goals exact Interned.adrInRange_of
  · rw [Bool.and_comm (pl.relax off)] at h
    split <;> rename_i hcond <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
    · rw [Nat.blt_eq] at h
      exact h
    · rw [Interned.sInRange_iff] at h
      exact ⟨by omega, by omega⟩
  · rw [Bool.and_comm (pl.relax off)] at h
    split <;> rename_i hcond <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
    · rw [Nat.blt_eq] at h
      exact h
    · simpa [Lo12Aligned, lo12AlignMask] using h

/-- Decidable check for `CodeBlock.Placeable blk pl`. Short-circuits the relaxed-pair range guard
    on `pl.relax (r.off - 4)`, `r.kind == .addLo12`, and `4 ≤ r.off` before scanning `blk.relocs`
    and `blk.code` in `blk.relaxedAt`. -/
def CodeBlock.checkPlaceable (blk : CodeBlock) (pl : Placement) : Bool :=
  let len := blk.code.length
  Nat.blt 0 blk.align && Nat.beq (blk.align % 4) 0 &&
  Nat.beq (pl.base.toNat % blk.align) 0 &&
  Nat.ble (pl.base.toNat + len) 18446744073709551616 &&
  Nat.beq (len % 4) 0 &&
  Interned.natNodupFast (blk.relocs.map (·.off)) &&
  blk.relocs.all (fun r =>
    Nat.beq (r.off % 4) 0 && Nat.ble (r.off + 4) len &&
    blk.relocInRangeB pl r.kind r.off (pl.base + BitVec.ofNat 64 r.off)
      (blk.relocTarget pl r.off r) &&
    (!(pl.relax (r.off - 4) && r.kind == .addLo12 && Nat.ble 4 r.off &&
        blk.relaxedAt pl (r.off - 4)) ||
      Interned.sInRange (-1048576) 1048576
        (blk.target pl r - (pl.base + BitVec.ofNat 64 r.off)))) &&
  blk.symbols.all (fun s => Nat.beq (s.2 % 4) 0 && Nat.ble s.2 len) &&
  blk.externs.all (fun e =>
    (lookup e blk.symbols).isNone && Nat.ble len (pl.ρ e - pl.base).toNat)

theorem CodeBlock.placeable_of_checkPlaceable {blk : CodeBlock} {pl : Placement}
    (h : blk.checkPlaceable pl = true) : blk.Placeable pl := by
  simp only [CodeBlock.checkPlaceable, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq,
    List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hnd⟩, hrel⟩, hsym⟩, hext⟩ := h
  refine ⟨⟨h1, h2⟩, h3, by simpa using h4, h5, Interned.natNodupFast_spec hnd, ?_, ?_, hsym, hext⟩
  · intro r hr
    have := hrel r hr
    exact ⟨this.1.1.1, this.1.1.2, CodeBlock.relocInRange_of this.1.2⟩
  · intro off r hrx hr
    have hmem := CodeBlock.relocAt?_mem hr
    have hoff := CodeBlock.relocAt?_off hr
    have hrx' := hrx
    simp only [CodeBlock.relaxedAt, CodeBlock.relaxableAt, hr, Bool.and_eq_true] at hrx'
    have hrk : (r.kind == .addLo12) = true := by
      rcases h0 : blk.relocAt? off with _ | r0 <;> simp [h0] at hrx'
      simp [hrx'.1.1.1.1.1.1.1.1.2]
    have hble : Nat.ble 4 (off + 4) = true := by rw [Nat.ble_eq]; omega
    have := (hrel r hmem).2
    rw [hoff, Nat.add_sub_cancel] at this
    rcases this with hfalse | hin
    · simp only [hrx'.2, hrk, hble, hrx, Bool.and_self] at hfalse
      cases hfalse
    · exact Interned.adrInRange_of hin

def checkRangesDisjoint (b1 n1 b2 n2 : Nat) : Bool :=
  Nat.ble (b1 + n1) b2 || Nat.ble (b2 + n2) b1

theorem rangesDisjoint_of_check {b1 n1 b2 n2 : Nat}
    (h : checkRangesDisjoint b1 n1 b2 n2 = true) : RangesDisjoint b1 n1 b2 n2 := by
  simp only [checkRangesDisjoint, Bool.or_eq_true, Nat.ble_eq] at h
  exact h

/-- Linear check that the ranges `[bases[i], bases[i] + len xs[i])` are address-sorted and
    non-overlapping: walks `bases` and `xs` in lockstep, verifying that each range starts at or
    after the end `lo` of the previous one (ignoring extra trailing `bases`). -/
def sortedRangesB {α : Type} (len : α → Nat) : Nat → List (BitVec 64) → List α → Bool
  | _, _, [] => true
  | _, [], _ :: _ => false
  | lo, b :: bs, x :: xs => Nat.ble lo b.toNat && sortedRangesB len (b.toNat + len x) bs xs

theorem sortedRangesB_lo {α : Type} {len : α → Nat} :
    ∀ {lo : Nat} {bases : List (BitVec 64)} {xs : List α},
      sortedRangesB len lo bases xs = true →
      ∀ (j : Nat), j < xs.length → lo ≤ (bases.getD j 0#64).toNat
  | _, _, [], _, _, hj => nomatch hj
  | _, [], _ :: _, h, _, _ => nomatch h
  | lo, b :: bs, x :: xs, h, j, hj => by
    simp only [sortedRangesB, Bool.and_eq_true, Nat.ble_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := sortedRangesB_lo h.2 j (by simp at hj; omega)
      simp only [List.getD_cons_succ]
      omega

theorem sortedRangesB_spec {α : Type} {len : α → Nat} :
    ∀ {lo : Nat} {bases : List (BitVec 64)} {xs : List α},
      sortedRangesB len lo bases xs = true →
      ∀ (i j : Nat) (hi : i < xs.length), j < xs.length → i < j →
        (bases.getD i 0#64).toNat + len xs[i] ≤ (bases.getD j 0#64).toNat
  | _, _, [], _, _, _, hi, _, _ => nomatch hi
  | _, [], _ :: _, h, _, _, _, _, _ => nomatch h
  | _, b :: bs, x :: xs, h, i, j, hi, hj, hij => by
    simp only [sortedRangesB, Bool.and_eq_true] at h
    cases j with
    | zero => omega
    | succ j =>
      cases i with
      | zero =>
        have := sortedRangesB_lo h.2 j (by simp at hj; omega)
        simpa using this
      | succ i =>
        have := sortedRangesB_spec h.2 i j (by simp at hi; omega) (by simp at hj; omega)
          (by omega)
        simpa using this

theorem checkRangesDisjoint_of_sortedRangesB {α : Type} {len : α → Nat} {lo : Nat}
    {bases : List (BitVec 64)} {xs : List α} (h : sortedRangesB len lo bases xs = true)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (hij : i < j) :
    checkRangesDisjoint (bases.getD i 0#64).toNat (len xs[i])
      (bases.getD j 0#64).toNat (len xs[j]) = true := by
  have := sortedRangesB_spec h i j hi hj hij
  simp only [checkRangesDisjoint, Bool.or_eq_true, Nat.ble_eq]
  exact Or.inl this

/-- Boolean check for a data relocation's range under `MultiPlacedLib.resolve`. -/
def MultiPlacedLib.checkDataReloc (lib : MultiPlacedLib) (mpl : MultiPlacement)
    (addr : BitVec 64) (n : Nat) (r : RelocEntry) : Bool :=
  let t := addSignedAddr (lib.resolve mpl r.sym) r.addend
  Nat.blt 0 (dataRelocWidth r.kind) && Nat.ble (r.off + dataRelocWidth r.kind) n &&
    match r.kind with
    | .abs32 => Interned.sInRange (-2147483648) 4294967296 t
    | .prel32 => Interned.sInRange (-2147483648) 2147483648 (t - (addr + BitVec.ofNat 64 r.off))
    | _ => true

abbrev MultiPlacedLib.checkBlocksPlaceable (lib : MultiPlacedLib) (mpl : MultiPlacement) : Bool :=
  allIdx (fun i blk => blk.checkPlaceable (lib.blockPlacement mpl i)) 0 lib.blocks

abbrev MultiPlacedLib.checkBlocksDisjoint (lib : MultiPlacedLib) (mpl : MultiPlacement) : Bool :=
  allIdx (fun i b1 =>
    allIdx (fun j b2 =>
      !Nat.blt i j ||
        checkRangesDisjoint (mpl.base i).toNat b1.code.length (mpl.base j).toNat b2.code.length)
      0 lib.blocks) 0 lib.blocks

abbrev MultiPlacedLib.checkBlockSymbolsNodup (lib : MultiPlacedLib) : Bool :=
  decide (((lib.blocks.flatMap (·.symbols)).map (·.1)).Nodup)

abbrev MultiPlacedLib.checkDataNodup (lib : MultiPlacedLib) : Bool :=
  decide ((lib.data.map (·.sym)).Nodup)

/-- Sub-check of `MultiPlacedLib.checkPlaceable`: data objects are aligned, in bounds, and their
    relocations are in range. -/
abbrev MultiPlacedLib.checkDataPlaceable (lib : MultiPlacedLib) (mpl : MultiPlacement) : Bool :=
  lib.data.all (fun d =>
    let a := mpl.ρ d.sym
    (lookupBlockSym d.sym lib.blocks).isNone &&
    Nat.blt 0 d.align && Nat.beq (a.toNat % d.align) 0 &&
    Nat.ble (a.toNat + d.bytes.length + d.zeroTail) 18446744073709551616 &&
    d.relocs.all (lib.checkDataReloc mpl a d.bytes.length))

/-- Decidable check for `MultiPlacedLib.Placeable lib mpl`. -/
def MultiPlacedLib.checkPlaceable (lib : MultiPlacedLib) (mpl : MultiPlacement) : Bool :=
  lib.checkBlocksPlaceable mpl &&
  lib.checkBlocksDisjoint mpl &&
  lib.checkBlockSymbolsNodup &&
  lib.checkDataNodup &&
  lib.checkDataPlaceable mpl

/-- Split-checks counterpart of `MultiPlacedLib.placeable_of_checkPlaceable`: combines separate
    `decide +kernel` sub-check lemmas into `lib.Placeable mpl` in `O(1)`. -/
theorem MultiPlacedLib.placeable_of_split_checks {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hblks : lib.checkBlocksPlaceable mpl = true)
    (hdisj : lib.checkBlocksDisjoint mpl = true)
    (hsym : lib.checkBlockSymbolsNodup = true)
    (hdnd : lib.checkDataNodup = true)
    (hdata : lib.checkDataPlaceable mpl = true) :
    lib.Placeable mpl := by
  simp only [MultiPlacedLib.checkBlockSymbolsNodup, MultiPlacedLib.checkDataNodup,
    decide_eq_true_eq] at hsym hdnd
  simp only [MultiPlacedLib.checkDataPlaceable, List.all_eq_true, Bool.and_eq_true,
    Option.isNone_iff_eq_none, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq] at hdata
  refine ⟨?_, ?_, hsym, hdnd, ?_, ?_⟩
  · intro i hi
    have := allIdx_spec hblks i hi
    rw [Nat.zero_add] at this
    exact CodeBlock.placeable_of_checkPlaceable this
  · intro i j hi hj hij
    have h1 := allIdx_spec hdisj i hi
    rw [Nat.zero_add] at h1
    have h2 := allIdx_spec h1 j hj
    rw [Nat.zero_add] at h2
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Nat.blt_eq] at h2
    rcases h2 with hnot | hok
    · exact absurd hij hnot
    · exact rangesDisjoint_of_check hok
  · intro d hd
    have := (hdata d hd).1
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, by simpa using this.2⟩
  · intro d hd r hr
    have := (hdata d hd).2 r hr
    simp only [MultiPlacedLib.checkDataReloc, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at this
    obtain ⟨⟨hw, hlen⟩, hk⟩ := this
    refine ⟨hw, hlen, fun h32 => ?_, fun hp32 => ?_⟩
    · rw [h32] at hk
      have := Interned.sInRange_iff.1 hk
      exact ⟨this.1, this.2⟩
    · rw [hp32] at hk
      have := Interned.sInRange_iff.1 hk
      exact ⟨this.1, this.2⟩

theorem MultiPlacedLib.exists_placeable_of_split_checks {lib : MultiPlacedLib}
    {mpl : MultiPlacement}
    (hblks : lib.checkBlocksPlaceable mpl = true)
    (hdisj : lib.checkBlocksDisjoint mpl = true)
    (hsym : lib.checkBlockSymbolsNodup = true)
    (hdnd : lib.checkDataNodup = true)
    (hdata : lib.checkDataPlaceable mpl = true) :
    ∃ mpl, lib.Placeable mpl :=
  ⟨mpl, lib.placeable_of_split_checks hblks hdisj hsym hdnd hdata⟩

theorem MultiPlacedLib.placeable_of_checkPlaceable {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (h : lib.checkPlaceable mpl = true) : lib.Placeable mpl := by
  simp only [MultiPlacedLib.checkPlaceable, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hblks, hdisj⟩, hsym⟩, hdnd⟩, hdata⟩ := h
  exact lib.placeable_of_split_checks hblks hdisj hsym hdnd hdata

/-- Check that `bs` is mapped at `addr` in `regions` with a permission satisfying `ok`. -/
def checkElfMaps (regions : List Snapshot.Region) (addr : BitVec 64) (bs : List (BitVec 8))
    (ok : Perm → Bool) : Bool :=
  match Interned.regionView addr regions with
  | some (p, segBs, _) => ok p && bs.isPrefixOf segBs
  | none => false

theorem elfMaps_of_checkElfMaps {img : ElfImage} {addr : BitVec 64} {bs : List (BitVec 8)}
    {ok : Perm → Bool} (h : checkElfMaps img.segments addr bs ok = true) :
    ElfMaps img addr bs ok := by
  unfold checkElfMaps at h
  split at h
  · rename_i p segBs m hv
    simp only [Bool.and_eq_true, List.isPrefixOf_iff_prefix] at h
    have hv' := (Interned.view_of_regionView hv).2
    exact Interned.elfMaps_of_view (hv'.of_prefix h.2) h.1
  · cases h

/-- Walk `blks` (starting at block index `k`), checking that each block's patched bytes are mapped
    `r-x` at `mpl.base (k + i)` in `regions`, reusing the segment view `cur` when addresses
    increase and falling back to `regionView` otherwise. -/
def blocksWalk (lib : MultiPlacedLib) (mpl : MultiPlacement) (regions : List Snapshot.Region) :
    Nat → Option (BitVec 64 × Perm × List (BitVec 8)) → List CodeBlock → Bool
  | _, _, [] => true
  | k, cur, blk :: rest =>
    let a := mpl.base k
    match Interned.nextView regions a cur with
    | some (p, bs) =>
      (p == Perm.rx) && (blk.patched (lib.blockPlacement mpl k)).isPrefixOf bs &&
        blocksWalk lib mpl regions (k + 1) (some (a, p, bs)) rest
    | none => false

theorem blocksWalk_sound {lib : MultiPlacedLib} {mpl : MultiPlacement} {img : ElfImage} :
    ∀ (k : Nat) (cur : Option (BitVec 64 × Perm × List (BitVec 8))) (blks : List CodeBlock),
      (∀ c p bs, cur = some (c, p, bs) → Interned.View img.segments c p bs) →
      blocksWalk lib mpl img.segments k cur blks = true →
      ∀ (i : Nat) (hi : i < blks.length),
        ElfMaps img (mpl.base (k + i)) (blks[i].patched (lib.blockPlacement mpl (k + i)))
          (· == Perm.rx)
  | _, _, [], _, _, _, hi => nomatch hi
  | k, cur, _ :: rest, hcur, h, i, hi => by
    simp only [blocksWalk] at h
    split at h
    · rename_i p bs hnv
      simp only [Bool.and_eq_true, List.isPrefixOf_iff_prefix] at h
      obtain ⟨⟨hp, hpre⟩, hrest⟩ := h
      have hv := Interned.nextView_sound hcur hnv
      cases i with
      | zero =>
        simpa [Nat.add_zero] using Interned.elfMaps_of_view (hv.of_prefix hpre) hp
      | succ i' =>
        rw [show k + (i' + 1) = (k + 1) + i' by omega]
        exact blocksWalk_sound (k + 1) _ rest
          (fun _ _ _ he => by cases he; exact hv) hrest i' (by simp at hi; omega)
    · cases h

/-- Kernel-fast check that `lib` is `Placeable` under `mpl` and contained in `img` (`InElf`). -/
def MultiPlacedLib.checkInElf (lib : MultiPlacedLib) (mpl : MultiPlacement)
    (img : ElfImage) : Bool :=
  lib.checkPlaceable mpl &&
  blocksWalk lib mpl img.segments 0 none lib.blocks &&
  lib.data.all (fun d =>
    checkElfMaps img.segments (mpl.ρ d.sym) (lib.patchedData mpl d)
      (fun p => if d.readOnly then p.r else p == Perm.rw)) &&
  lib.exports.all (fun e =>
    match lookupBlockSym e lib.blocks with
    | some (i, off) =>
      lookupUnique (lib.elfSym e) img.symbols == some (mpl.base i + BitVec.ofNat 64 off)
    | none => false)

/-- Soundness of `MultiPlacedLib.checkInElf`: a `true` result proves `lib.Placeable mpl` and
    `lib.InElf img mpl`. -/
theorem MultiPlacedLib.checkInElf_spec {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {img : ElfImage} (h : lib.checkInElf mpl img = true) :
    lib.Placeable mpl ∧ lib.InElf img mpl := by
  simp only [MultiPlacedLib.checkInElf, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hpl, hblks⟩, hdata⟩, hexp⟩ := h
  refine ⟨lib.placeable_of_checkPlaceable hpl, ⟨?_, ?_, ?_⟩⟩
  · intro i hi
    simpa [Nat.zero_add] using
      blocksWalk_sound 0 none lib.blocks (fun _ _ _ hc => nomatch hc) hblks i hi
  · intro d hd
    exact elfMaps_of_checkElfMaps (hdata d hd)
  · intro e he
    have := hexp e he
    split at this
    · rename_i i off hblk
      rw [beq_iff_eq] at this
      exact ⟨i, off, hblk, this⟩
    · cases this

/-! ## Interned multi-block checker (`Obj.Interned.checkMulti`) -/

namespace Interned

/-- One code block of an interned `MultiLib`, with symbol and extern names represented as indices
    into `MultiLib.names`. -/
structure Block where
  code : List (BitVec 8)
  align : Nat := 4
  symbols : List (Nat × Nat) := []
  relocs : List Reloc := []
  externs : List Nat := []
  weakRefs : List Nat := []
  deriving Inhabited

/-- Convert an interned `Block` to a `CodeBlock` under `names`. -/
def Block.toCodeBlock (names : List String) (b : Block) : CodeBlock :=
  { code := b.code
    align := b.align
    symbols := b.symbols.map fun s => (names.getD s.1 "", s.2)
    relocs := b.relocs.map (Reloc.toEntry names)
    externs := b.externs.map fun e => names.getD e ""
    weakRefs := b.weakRefs.map fun e => names.getD e "" }

/-- A multi-block placed library with interned symbol names (`exportSyms` pairs an export's
    name index with its raw `.symtab` name index). -/
structure MultiLib where
  name : String
  names : List String
  blocks : List Block
  data : List Data := []
  exports : List Nat := []
  exportSyms : List (Nat × Nat) := []
  deriving Inhabited

/-- Project `ML` to a `MultiPlacedLib`. -/
def MultiLib.toMultiPlacedLib (ML : MultiLib) : MultiPlacedLib :=
  { name := ML.name
    blocks := ML.blocks.map (Block.toCodeBlock ML.names)
    data := ML.data.map (Data.toInfo ML.names)
    exports := ML.exports.map fun e => ML.names.getD e ""
    exportSyms := ML.exportSyms.map fun p => (ML.names.getD p.1 "", ML.names.getD p.2 "") }

/-- View block `b` of `ML` as a single-block `Interned.Lib`. -/
def MultiLib.blockLib (ML : MultiLib) (b : Block) : Lib :=
  { name := ML.name
    names := ML.names
    code := b.code
    align := b.align
    symbols := b.symbols
    relocs := b.relocs
    externs := b.externs
    weakRefs := b.weakRefs
    data := ML.data
    exports := [] }

@[simp] theorem MultiLib.blockLib_block (ML : MultiLib) (b : Block) :
    (ML.blockLib b).block = b.toCodeBlock ML.names := rfl

@[simp] theorem MultiLib.blockLib_names (ML : MultiLib) (b : Block) :
    (ML.blockLib b).names = ML.names := rfl

@[simp] theorem MultiLib.toMultiPlacedLib_blocks (ML : MultiLib) :
    ML.toMultiPlacedLib.blocks = ML.blocks.map (Block.toCodeBlock ML.names) := rfl

@[simp] theorem MultiLib.toMultiPlacedLib_data (ML : MultiLib) :
    ML.toMultiPlacedLib.data = ML.data.map (Data.toInfo ML.names) := rfl

/-- Multi-block layout for an `Interned.MultiLib`: per-block `bases`, a single `addrs` table
    giving the runtime address of every name in `ML.names` (both block symbols and external/data
    symbols), per-block `relax` / `b2b` offset lists, and the indices of weak references left
    undefined (`undefWeak`). -/
structure MultiLayout where
  bases : List (BitVec 64)
  addrs : List (BitVec 64)
  relax : List (List Nat) := []
  b2b : List (List Nat) := []
  undefWeak : List Nat := []
  deriving Inhabited

/-- Project `mly` to a single-block `Interned.Layout` for block `i`. -/
def MultiLayout.blockLayout (mly : MultiLayout) (i : Nat) : Layout :=
  { base := mly.bases.getD i 0#64
    addrs := mly.addrs
    relax := mly.relax.getD i []
    b2b := mly.b2b.getD i []
    undefWeak := mly.undefWeak }

/-- Layout for data-only checks on `ML.blockLib { code := [] }`. -/
def MultiLayout.dataLayout (mly : MultiLayout) : Layout :=
  { base := 0#64, addrs := mly.addrs }

/-- Project `mly` to a `MultiPlacement` under `names`. -/
def MultiLayout.toMultiPlacement (mly : MultiLayout) (names : List String) : MultiPlacement :=
  { base := fun i => mly.bases.getD i 0#64
    ρ := fun s => mly.addrs.getD (names.idxOf s) 0#64
    relax := fun i o => memNat o (mly.relax.getD i [])
    b2b := fun i o => memNat o (mly.b2b.getD i [])
    undefWeak := fun s => memNat (names.idxOf s) mly.undefWeak }

/-- Every symbol index in `b` is in range of `n = ML.names.length`. -/
def Block.idsOk (n : Nat) (b : Block) : Bool :=
  b.symbols.all (fun s => Nat.blt s.1 n) &&
  b.relocs.all (fun r => Nat.blt r.sym n) &&
  b.externs.all (fun e => Nat.blt e n)

/-- Every symbol index in `ML` is in range of `ML.names.length`. -/
def MultiLib.idsOk (ML : MultiLib) : Bool :=
  let n := ML.names.length
  ML.blocks.all (Block.idsOk n) &&
  ML.exports.all (fun e => Nat.blt e n) &&
  ML.data.all fun d => Nat.blt d.sym n && d.relocs.all fun r => Nat.blt r.sym n

theorem MultiLib.blockLib_idsOk {ML : MultiLib} (h : ML.idsOk = true) {b : Block}
    (hb : b ∈ ML.blocks) : (ML.blockLib b).IdsOk := by
  simp only [MultiLib.idsOk, Bool.and_eq_true, List.all_eq_true, blt_iff] at h
  obtain ⟨⟨hblks, _⟩, hdata⟩ := h
  have hb' := hblks b hb
  simp only [Block.idsOk, Bool.and_eq_true, List.all_eq_true, blt_iff] at hb'
  exact {
    symbols := hb'.1.1
    relocs := hb'.1.2
    externs := hb'.2
    exports := fun _ h => nomatch h
    data := fun d hd => ⟨(hdata d hd).1, (hdata d hd).2⟩
  }

theorem MultiLib.emptyBlock_idsOk {ML : MultiLib} (h : ML.idsOk = true) :
    (ML.blockLib { code := [] }).IdsOk := by
  simp only [MultiLib.idsOk, Bool.and_eq_true, List.all_eq_true, blt_iff] at h
  obtain ⟨⟨_, _⟩, hdata⟩ := h
  exact {
    symbols := fun _ h => nomatch h
    relocs := fun _ h => nomatch h
    externs := fun _ h => nomatch h
    exports := fun _ h => nomatch h
    data := fun d hd => ⟨(hdata d hd).1, (hdata d hd).2⟩
  }

/-- Check that for every symbol `(s, off)` of block `i`, `mly.addrs[s] = mly.bases[i] + off`. -/
def blockSymsMatchB (ML : MultiLib) (mly : MultiLayout) : Bool :=
  allIdx (fun i b =>
    b.symbols.all fun s =>
      mly.addrs.getD s.1 0#64 == mly.bases.getD i 0#64 + BitVec.ofNat 64 s.2)
    0 ML.blocks

theorem toMultiPlacement_resolve_eq {ML : MultiLib} {mly : MultiLayout}
    (hnd : ML.names.Nodup) (hids : ML.idsOk = true)
    (hmatch : blockSymsMatchB ML mly = true) (s : String) :
    ML.toMultiPlacedLib.resolve (mly.toMultiPlacement ML.names) s =
      mly.addrs.getD (ML.names.idxOf s) 0#64 := by
  unfold MultiPlacedLib.resolve
  cases hl : lookupBlockSym s ML.toMultiPlacedLib.blocks with
  | none => rfl
  | some p =>
    obtain ⟨j, off⟩ := p
    obtain ⟨hj, hfind⟩ := lookupBlockSym_some hl
    simp only [MultiLib.toMultiPlacedLib, List.length_map, List.getElem_map] at hj hfind
    have hmem := mem_of_lookup_some hfind
    simp only [Block.toCodeBlock, List.mem_map] at hmem
    obtain ⟨⟨symId, off'⟩, hsym_mem, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hs_eq, h_off⟩ := heq
    subst h_off
    have hb_ids := (ML.blockLib_idsOk hids (List.getElem_mem hj)).symbols (symId, off') hsym_mem
    have hm := allIdx_spec hmatch j hj
    rw [Nat.zero_add] at hm
    have hm_sym := List.all_eq_true.1 hm (symId, off') hsym_mem
    rw [beq_iff_eq] at hm_sym
    rw [← hs_eq, idxOf_getD hnd hb_ids, hm_sym]
    rfl

theorem toMultiPlacement_blockPlacement_eq {ML : MultiLib} {mly : MultiLayout}
    (hnd : ML.names.Nodup) (hids : ML.idsOk = true)
    (hmatch : blockSymsMatchB ML mly = true) (i : Nat) :
    ML.toMultiPlacedLib.blockPlacement (mly.toMultiPlacement ML.names) i =
      (mly.blockLayout i).toPlacement ML.names := by
  have hρ : ML.toMultiPlacedLib.resolve (mly.toMultiPlacement ML.names) =
      fun s => mly.addrs.getD (ML.names.idxOf s) 0#64 :=
    funext (toMultiPlacement_resolve_eq hnd hids hmatch)
  unfold MultiPlacedLib.blockPlacement
  rw [hρ]
  rfl

def lookupBlockSymIdAux (symId : Nat) : Nat → List Block → Option (Nat × Nat)
  | _, [] => none
  | idx, b :: rest =>
    match lookupId symId b.symbols with
    | some off => some (idx, off)
    | none => lookupBlockSymIdAux symId (idx + 1) rest

def lookupBlockSymId (symId : Nat) (blocks : List Block) : Option (Nat × Nat) :=
  lookupBlockSymIdAux symId 0 blocks

theorem lookupBlockSymAux_map_toCodeBlock {names : List String} (hnd : names.Nodup)
    {symId : Nat} (hs : symId < names.length) :
    ∀ (k : Nat) (blks : List Block),
      (∀ b ∈ blks, ∀ p ∈ b.symbols, p.1 < names.length) →
      lookupBlockSymAux (names.getD symId "") k (blks.map (Block.toCodeBlock names)) =
        lookupBlockSymIdAux symId k blks
  | _, [], _ => rfl
  | k, b :: rest, hok => by
    simp only [List.map_cons, lookupBlockSymAux, lookupBlockSymIdAux, Block.toCodeBlock]
    rw [lookup_map_getD hnd hs b.symbols (hok b List.mem_cons_self)]
    cases lookupId symId b.symbols with
    | some off => rfl
    | none =>
      exact lookupBlockSymAux_map_toCodeBlock hnd hs (k + 1) rest
        (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb'))

theorem lookupBlockSym_toMultiPlacedLib {ML : MultiLib} (hnd : ML.names.Nodup)
    (hids : ML.idsOk = true) {symId : Nat} (hs : symId < ML.names.length) :
    lookupBlockSym (ML.names.getD symId "") ML.toMultiPlacedLib.blocks =
      lookupBlockSymId symId ML.blocks :=
  lookupBlockSymAux_map_toCodeBlock hnd hs 0 ML.blocks
    (fun _ hb => (ML.blockLib_idsOk hids hb).symbols)

/-- Streaming walk of all blocks of `ML` in `regions`, reusing `cur` via `nextView` when block
    addresses increase and falling back to `regionView` otherwise. -/
def multiTextWalk (ML : MultiLib) (mly : MultiLayout) (regions : List Snapshot.Region) :
    Nat → Option (BitVec 64 × Perm × List (BitVec 8)) → List Block → Bool
  | _, _, [] => true
  | i, cur, b :: rest =>
    let ly := mly.blockLayout i
    match nextView regions ly.base cur with
    | some (p, bs) =>
      (p == Perm.rx) && walk (ML.blockLib b) ly 0 false b.relocs b.code bs &&
        multiTextWalk ML mly regions (i + 1) (some (ly.base, p, bs)) rest
    | none => false

theorem multiTextWalk_sound {ML : MultiLib} {mly : MultiLayout}
    (hnd : ML.names.Nodup) (hids : ML.idsOk = true) {regions : List Snapshot.Region} :
    ∀ (k : Nat) (cur : Option (BitVec 64 × Perm × List (BitVec 8))) (blks : List Block),
      (∀ b ∈ blks, b ∈ ML.blocks) →
      (∀ b ∈ blks, relocsWf b.code.length 0 b.relocs = true) →
      (∀ c p bs, cur = some (c, p, bs) → View regions c p bs) →
      multiTextWalk ML mly regions k cur blks = true →
      ∀ (i : Nat) (hi : i < blks.length),
        (∃ p bs, View regions (mly.blockLayout (k + i)).base p bs ∧ p = Perm.rx ∧
          ((ML.blockLib blks[i]).block.patched
            ((mly.blockLayout (k + i)).toPlacement ML.names)).IsPrefix bs) ∧
        WalkOk (ML.blockLib blks[i]) (mly.blockLayout (k + i)) 0 blks[i].relocs
          ((ML.blockLib blks[i]).block.patched
            ((mly.blockLayout (k + i)).toPlacement ML.names) ++ [])
  | _, _, [], _, _, _, _, _, hi => nomatch hi
  | k, cur, b :: rest, hmem, hwf, hcur, h, i, hi => by
    simp only [multiTextWalk] at h
    split at h
    · rename_i p bs hnv
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hp, hwalk⟩, hrest⟩ := h
      have hv := nextView_sound hcur hnv
      cases i with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero]
        have hok := ML.blockLib_idsOk hids (hmem b List.mem_cons_self)
        have hw := walk_sound_zero (L := ML.blockLib b) (ly := mly.blockLayout k)
          hnd hok (hwf b List.mem_cons_self) hwalk
        exact ⟨⟨p, bs, hv, hp, by simpa using hw.1⟩, ⟨by simp, hw.2.1, hw.2.2⟩⟩
      | succ i' =>
        rw [show k + (i' + 1) = (k + 1) + i' by omega]
        exact multiTextWalk_sound hnd hids (k + 1) _ rest
          (fun b' hb' => hmem b' (List.mem_cons_of_mem _ hb'))
          (fun b' hb' => hwf b' (List.mem_cons_of_mem _ hb'))
          (fun _ _ _ he => by cases he; exact hv) hrest i' (by simp at hi; omega)
    · cases h

/-- Check that every export of `ML` is defined in some block `i` at offset `off` and its raw name
    (`exportSyms`, else the export's own name) has a unique `.symtab` entry in `enc` at
    `mly.bases[i] + off`. -/
def multiExportsOk (ML : MultiLib) (mly : MultiLayout) (nameChars : List (List Char))
    (enc : EncSymTable (BitVec 64)) : Bool :=
  ML.exportSyms.all (fun p => Nat.blt p.1 ML.names.length) &&
  ML.exports.all fun e =>
    match lookupBlockSymId e ML.blocks with
    | some (i, off) =>
      match lookupUniqueEnc (encodeCharKey (nameChars.getD ((lookupId e ML.exportSyms).getD e) []))
          enc with
      | some a => a == mly.bases.getD i 0#64 + BitVec.ofNat 64 off
      | none => false
    | none => false

/-- Check `MultiPlacedLib.Placeable` fields (except relocation ranges covered by `multiTextWalk`).
    Block disjointness is checked by the linear `sortedRangesB` walk when blocks are listed in
    increasing address order, falling back to the quadratic pairwise check otherwise. -/
def multiPlaceableB (ML : MultiLib) (mly : MultiLayout) : Bool :=
  allIdx (fun i b => textPlaceableB (ML.blockLib b) (mly.blockLayout i)) 0 ML.blocks &&
  (sortedRangesB (·.code.length) 0 mly.bases ML.blocks ||
    allIdx (fun i b1 =>
      allIdx (fun j b2 =>
        !Nat.blt i j ||
          checkRangesDisjoint (mly.bases.getD i 0#64).toNat b1.code.length
            (mly.bases.getD j 0#64).toNat b2.code.length)
        0 ML.blocks) 0 ML.blocks) &&
  natNodupFast ((ML.blocks.flatMap (·.symbols)).map (·.1)) &&
  dataPlaceableB (ML.blockLib { code := [] }) mly.dataLayout &&
  ML.data.all fun d => (lookupBlockSymId d.sym ML.blocks).isNone

/-- Kernel-fast `Bool` checker for `MultiPlacedLib.Placeable` and `MultiPlacedLib.InElf`. -/
def checkMulti (ML : MultiLib) (mly : MultiLayout) (nameChars : List (List Char))
    (img : ElfImage) (enc : EncSymTable (BitVec 64)) : Bool :=
  namesNodup nameChars && ML.idsOk && blockSymsMatchB ML mly &&
  multiPlaceableB ML mly &&
  multiTextWalk ML mly img.segments 0 none ML.blocks &&
  dataWalk (ML.blockLib { code := [] }) mly.dataLayout img.segments none ML.data &&
  multiExportsOk ML mly nameChars enc

theorem flatMap_toCodeBlock_symbols_fst (names : List String) :
    ∀ (blks : List Block),
      ((blks.map (Block.toCodeBlock names)).flatMap (·.symbols)).map (·.1) =
        ((blks.flatMap (·.symbols)).map (·.1)).map (fun i => names.getD i "")
  | [] => rfl
  | b :: rest => by
    simp only [List.map_cons, List.flatMap_cons, List.map_append]
    rw [flatMap_toCodeBlock_symbols_fst names rest]
    simp only [Block.toCodeBlock, List.map_map]
    rfl

theorem mem_flatMap_symbols_lt {ML : MultiLib} (hids : ML.idsOk = true) {x : Nat}
    (hx : x ∈ (ML.blocks.flatMap (·.symbols)).map (·.1)) : x < ML.names.length := by
  obtain ⟨⟨symId, off⟩, hmem, rfl⟩ := List.mem_map.1 hx
  obtain ⟨b, hb, hbs⟩ := List.mem_flatMap.1 hmem
  exact (ML.blockLib_idsOk hids hb).symbols (symId, off) hbs

abbrev BlockTextOk (ML : MultiLib) (mly : MultiLayout) (regions : List Snapshot.Region) (i : Nat)
    (b : Block) : Prop :=
  (∃ p bs, View regions (mly.blockLayout i).base p bs ∧ p = Perm.rx ∧
    ((ML.blockLib b).block.patched ((mly.blockLayout i).toPlacement ML.names)).IsPrefix bs) ∧
  WalkOk (ML.blockLib b) (mly.blockLayout i) 0 b.relocs
    ((ML.blockLib b).block.patched ((mly.blockLayout i).toPlacement ML.names) ++ [])

abbrev MultiTextOk (ML : MultiLib) (mly : MultiLayout) (regions : List Snapshot.Region) : Prop :=
  ∀ (i : Nat) (hi : i < ML.blocks.length), BlockTextOk ML mly regions i ML.blocks[i]

abbrev DataObjOk (ML : MultiLib) (mly : MultiLayout) (regions : List Snapshot.Region) (d : Data) :
    Prop :=
  ∃ p, View regions (mly.dataLayout.addrs.getD d.sym 0#64) p
      (patchedDataId (ML.blockLib { code := [] }) mly.dataLayout d) ∧
    dataPermOk d.readOnly p = true

abbrev MultiDataOk (ML : MultiLib) (mly : MultiLayout) (regions : List Snapshot.Region) : Prop :=
  ∀ d ∈ ML.data, DataObjOk ML mly regions d

theorem relocsWf_of_multiPlaceableB {ML : MultiLib} {mly : MultiLayout}
    (hmp : multiPlaceableB ML mly = true) :
    ∀ b ∈ ML.blocks, relocsWf b.code.length 0 b.relocs = true := by
  simp only [multiPlaceableB, Bool.and_eq_true] at hmp
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hti := allIdx_spec hmp.1.1.1.1 i hi
  rw [Nat.zero_add] at hti
  simp only [textPlaceableB, Bool.and_eq_true] at hti
  exact hti.1.1.2

theorem blockTextOk_of_walk {ML : MultiLib} {mly : MultiLayout} (hnd : ML.names.Nodup)
    (hids : ML.idsOk = true) {regions : List Snapshot.Region} {k : Nat}
    {cur : Option (BitVec 64 × Perm × List (BitVec 8))} {blks : List Block}
    (hmem : ∀ b ∈ blks, b ∈ ML.blocks)
    (hwf : ∀ b ∈ blks, relocsWf b.code.length 0 b.relocs = true)
    (hcur : ∀ c p bs, cur = some (c, p, bs) → View regions c p bs)
    (h : multiTextWalk ML mly regions k cur blks = true) (j : Nat) (hj : j < blks.length) :
    BlockTextOk ML mly regions (k + j) blks[j] :=
  multiTextWalk_sound hnd hids k cur blks hmem hwf hcur h j hj

theorem multiTextOk_of_walk {ML : MultiLib} {mly : MultiLayout} (hnd : ML.names.Nodup)
    (hids : ML.idsOk = true) (hmp : multiPlaceableB ML mly = true) {regions : List Snapshot.Region}
    (h : multiTextWalk ML mly regions 0 none ML.blocks = true) : MultiTextOk ML mly regions := by
  intro i hi
  have := blockTextOk_of_walk (mly := mly) (k := 0) (cur := none) hnd hids (fun _ hb => hb)
    (relocsWf_of_multiPlaceableB hmp) (fun _ _ _ hc => nomatch hc) h i hi
  rwa [Nat.zero_add] at this

theorem multiDataOk_of_walk {ML : MultiLib} {mly : MultiLayout} {regions : List Snapshot.Region}
    (h : dataWalk (ML.blockLib { code := [] }) mly.dataLayout regions none ML.data = true) :
    MultiDataOk ML mly regions :=
  dataWalk_sound none ML.data (fun _ _ _ hc => nomatch hc) h

/-- `Placeable` and `InElf` from the segment-free checks of `checkMulti` and the text and data
    facts `MultiTextOk` / `MultiDataOk` (however they were proved). -/
theorem checkMulti_spec_of_ok {ML : MultiLib} {mly : MultiLayout} {nameChars : List (List Char)}
    {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hnn : namesNodup nameChars = true) (hids : ML.idsOk = true)
    (hmatch : blockSymsMatchB ML mly = true) (hmp : multiPlaceableB ML mly = true)
    (hwalk : MultiTextOk ML mly img.segments) (hdataOk : MultiDataOk ML mly img.segments)
    (hexp : multiExportsOk ML mly nameChars (prepareCharAssocVal symChars) = true) :
    let lib := ML.toMultiPlacedLib
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl := by
  have hnd := nodup_of_namesNodup hnames hnn
  have hok0 := ML.emptyBlock_idsOk hids
  simp only [multiPlaceableB, Bool.and_eq_true, List.all_eq_true] at hmp
  obtain ⟨⟨⟨⟨htp, hdisj⟩, hsym_nd⟩, hdp⟩, hd_none⟩ := hmp
  have htp0 : textPlaceableB (ML.blockLib { code := [] }) mly.dataLayout = true := by
    dsimp only [textPlaceableB, MultiLib.blockLib, MultiLayout.dataLayout, relocsWf, List.all]
    decide
  have hwalk0 : WalkOk (ML.blockLib { code := [] }) mly.dataLayout 0 [] [] := by
    refine ⟨?_, ?_, ?_⟩
    · simp [MultiLib.blockLib, CodeBlock.patched]
    · intro _ hr; nomatch hr
    · intro _ _ _ _ hr; nomatch hr
  have hpl0 := placeable_of hnd hok0 htp0 hdp hwalk0
  have hbp_eq : ∀ i, ML.toMultiPlacedLib.blockPlacement (mly.toMultiPlacement ML.names) i =
      (mly.blockLayout i).toPlacement ML.names :=
    toMultiPlacement_blockPlacement_eq hnd hids hmatch
  have hres_eq : ∀ s, ML.toMultiPlacedLib.resolve (mly.toMultiPlacement ML.names) s =
      (mly.dataLayout.toPlacement ML.names).ρ s :=
    toMultiPlacement_resolve_eq hnd hids hmatch
  refine ⟨⟨?_, ?_, ?_, hpl0.data_nodup, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · intro i hi
    simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map, List.getElem_map] at hi ⊢
    rw [hbp_eq i, ← MultiLib.blockLib_block]
    have hti := allIdx_spec htp i hi
    rw [Nat.zero_add] at hti
    have ⟨_, hw⟩ := hwalk i hi
    exact textPlaceable_of hnd (ML.blockLib_idsOk hids (List.getElem_mem hi)) hti hw
  · intro i j hi hj hij
    simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map, List.getElem_map] at hi hj ⊢
    rw [Bool.or_eq_true] at hdisj
    rcases hdisj with hsorted | hdisj
    · exact rangesDisjoint_of_check (checkRangesDisjoint_of_sortedRangesB hsorted hi hj hij)
    have h1 := allIdx_spec hdisj i hi
    rw [Nat.zero_add] at h1
    have h2 := allIdx_spec h1 j hj
    rw [Nat.zero_add] at h2
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Nat.blt_eq] at h2
    rcases h2 with hnot | hok
    · exact absurd hij hnot
    · exact rangesDisjoint_of_check hok
  · rw [MultiLib.toMultiPlacedLib_blocks, flatMap_toCodeBlock_symbols_fst]
    have hn := natNodupFast_spec hsym_nd
    rw [List.nodup_iff_pairwise_ne] at hn ⊢
    rw [List.pairwise_map]
    refine hn.imp_of_mem fun {x y} hx hy hxy heq => hxy ?_
    exact getD_inj hnd (mem_flatMap_symbols_lt hids hx) (mem_flatMap_symbols_lt hids hy) heq
  · intro d hd
    have hdo := hpl0.data_ok d hd
    simp only [MultiLib.toMultiPlacedLib, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    have hdi := (hok0.data d' hd').1
    have hln : lookupBlockSym (Data.toInfo ML.names d').sym ML.toMultiPlacedLib.blocks = none := by
      show lookupBlockSym (ML.names.getD d'.sym "") ML.toMultiPlacedLib.blocks = none
      rw [lookupBlockSym_toMultiPlacedLib hnd hids hdi]
      exact Option.isNone_iff_eq_none.1 (hd_none d' hd')
    exact ⟨hln, hdo.2⟩
  · intro d hd r hr
    have hdro := hpl0.data_relocs_ok d hd r hr
    have hres0 : (Block.toCodeBlock ML.names { code := [] }).resolve
        (mly.dataLayout.toPlacement ML.names) r.sym =
        ML.toMultiPlacedLib.resolve (mly.toMultiPlacement ML.names) r.sym := by
      rw [hres_eq r.sym]
      rfl
    have hρ0 : (mly.dataLayout.toPlacement ML.names).ρ d.sym =
        (mly.toMultiPlacement ML.names).ρ d.sym := rfl
    simpa only [Lib.toLib_text, MultiLib.blockLib_block, MultiLib.blockLib_names, hres0, hρ0]
      using hdro
  · intro i hi
    simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map, List.getElem_map] at hi ⊢
    rw [hbp_eq i, ← MultiLib.blockLib_block]
    have ⟨⟨p, bs, hv, hp, hpre⟩, _⟩ := hwalk i hi
    exact elfMaps_of_view (hv.of_prefix hpre) (by simp [hp])
  · intro d hd
    simp only [MultiLib.toMultiPlacedLib, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    obtain ⟨p, hv, hp⟩ := hdataOk d' hd'
    have hi := (hok0.data d' hd').1
    have hρ : (mly.toMultiPlacement ML.names).ρ (Data.toInfo ML.names d').sym =
        mly.dataLayout.addrs.getD d'.sym 0#64 :=
      toPlacement_ρ (ly := mly.dataLayout) hnd hi
    have hpd : ML.toMultiPlacedLib.patchedData (mly.toMultiPlacement ML.names)
        (Data.toInfo ML.names d') =
        patchedDataId (ML.blockLib { code := [] }) mly.dataLayout d' := by
      rw [← patchedData_toLib (L := ML.blockLib { code := [] }) (ly := mly.dataLayout)
        hnd hok0 hd']
      have hpr : ML.toMultiPlacedLib.patchDataReloc (mly.toMultiPlacement ML.names) =
          (ML.blockLib { code := [] }).toLib.patchDataReloc
            (mly.dataLayout.toPlacement ML.names) := by
        funext addr bytes r
        simp only [MultiPlacedLib.patchDataReloc, PlacedLib.patchDataReloc, hres_eq]
        rfl
      simp only [MultiPlacedLib.patchedData, PlacedLib.patchedData, hpr]
      rfl
    rw [show (Data.toInfo ML.names d').readOnly = d'.readOnly from rfl, hρ, hpd]
    exact elfMaps_of_view hv hp
  · intro e he
    simp only [MultiLib.toMultiPlacedLib, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    have he_lt : e' < ML.names.length := by
      simp only [MultiLib.idsOk, Bool.and_eq_true, List.all_eq_true, blt_iff] at hids
      exact hids.1.2 e' he'
    simp only [multiExportsOk, Bool.and_eq_true] at hexp
    obtain ⟨hesb, hexp⟩ := hexp
    have hes : ∀ p ∈ ML.exportSyms, p.1 < ML.names.length := fun p hp =>
      blt_iff.1 (List.all_eq_true.1 hesb p hp)
    have helf : ML.toMultiPlacedLib.elfSym (ML.names.getD e' "") =
        ML.names.getD ((lookupId e' ML.exportSyms).getD e') "" := by
      have hmap : ∀ xs : List (Nat × Nat),
          lookupId e' (xs.map fun p => (p.1, ML.names.getD p.2 "")) =
            (lookupId e' xs).map fun j => ML.names.getD j "" := by
        intro xs
        induction xs with
        | nil => rfl
        | cons p rest ih =>
          simp only [List.map_cons, lookupId]
          cases Nat.beq p.1 e'
          · simpa using ih
          · rfl
      have hl := lookup_map_getD hnd he_lt
        (ML.exportSyms.map fun p => (p.1, ML.names.getD p.2 ""))
        (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
          exact hes q hq)
      rw [List.map_map] at hl
      show (lookup (ML.names.getD e' "")
          (ML.exportSyms.map fun p => (ML.names.getD p.1 "", ML.names.getD p.2 ""))).getD
            (ML.names.getD e' "") = _
      rw [show (fun p : Nat × Nat => (ML.names.getD p.1 "", ML.names.getD p.2 "")) =
          ((fun s : Nat × String => (ML.names.getD s.1 "", s.2)) ∘
            fun p => (p.1, ML.names.getD p.2 "")) from rfl, hl, hmap]
      cases lookupId e' ML.exportSyms <;> rfl
    have hex := List.all_eq_true.1 hexp e' he'
    split at hex
    · rename_i i off hblk
      split at hex
      · rename_i a ha
        rw [beq_iff_eq] at hex
        subst hex
        refine ⟨i, off, ?_, ?_⟩
        · rw [lookupBlockSym_toMultiPlacedLib hnd hids he_lt, hblk]
        · have hng : ML.names.getD ((lookupId e' ML.exportSyms).getD e') "" =
              String.ofList (nameChars.getD ((lookupId e' ML.exportSyms).getD e') []) :=
            names_getD (L := ML.blockLib { code := [] }) hnames _
          rw [helf, lookupUnique_eq_lookupUniqueEnc hsyms rfl hng, ha]
          rfl
      · cases hex
    · cases hex

/-- Soundness of `Interned.checkMulti`: a `true` result proves `Placeable` and `InElf`. -/
theorem checkMulti_spec {ML : MultiLib} {mly : MultiLayout} {nameChars : List (List Char)}
    {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (h : checkMulti ML mly nameChars img (prepareCharAssocVal symChars) = true) :
    let lib := ML.toMultiPlacedLib
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl := by
  simp only [checkMulti, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hnn, hids⟩, hmatch⟩, hmp⟩, htext⟩, hdata⟩, hexp⟩ := h
  exact checkMulti_spec_of_ok hnames hsyms hnn hids hmatch hmp
    (multiTextOk_of_walk (nodup_of_namesNodup hnames hnn) hids hmp htext)
    (multiDataOk_of_walk hdata) hexp

/-- Interned form of `MultiPlacedLib.dataDisjoint_of_sorted`: checks `rangesSorted` on `ML.data`
    using `mly.addrs` and template lengths `d.bytes.length + d.zeroTail`, without patching data. -/
def multiDataSorted (ML : MultiLib) (mly : MultiLayout) : Bool :=
  rangesSorted (ML.data.map fun d => (mly.addrs.getD d.sym 0#64, d.bytes.length + d.zeroTail))

/-- Pairwise check that any pair of data entries `(ro, addr, len)` is either both read-only or
    has disjoint non-wrapping address ranges, independent of list order. -/
def dataEntriesDisjointB : List (Bool × BitVec 64 × Nat) → Bool
  | [] => true
  | (ro1, a1, n1) :: rest =>
    Nat.ble (a1.toNat + n1) 18446744073709551616 &&
    rest.all (fun (ro2, a2, n2) =>
      (ro1 && ro2) || checkRangesDisjoint a1.toNat n1 a2.toNat n2) &&
    dataEntriesDisjointB rest

theorem dataEntriesDisjointB_pairwise : ∀ {ds : List (Bool × BitVec 64 × Nat)},
    dataEntriesDisjointB ds = true →
    (∀ x ∈ ds, x.2.1.toNat + x.2.2 ≤ 2 ^ 64) ∧
    (ds.Pairwise fun x y =>
      (x.1 = true ∧ y.1 = true) ∨
        ∀ a, InRegion x.2.1 x.2.2 a → ¬ InRegion y.2.1 y.2.2 a)
  | [], _ => ⟨(fun _ h => nomatch h), List.Pairwise.nil⟩
  | (ro1, a1, n1) :: rest, h => by
    simp only [dataEntriesDisjointB, Bool.and_eq_true, List.all_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨hb1, hall⟩, hrest⟩ := h
    obtain ⟨hbounds, hpw⟩ := dataEntriesDisjointB_pairwise hrest
    refine ⟨fun x hx => ?_, List.Pairwise.cons (fun y hy => ?_) hpw⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact hb1
      · exact hbounds x hx
    · have hyb := hbounds y hy
      have hc := hall y hy
      rcases y with ⟨ro2, a2, n2⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
      rcases hc with hro | hdisj
      · exact Or.inl hro
      · refine Or.inr fun a ha1 ha2 => ?_
        rcases rangesDisjoint_of_check hdisj with hle | hle
        · exact not_inRegion_of_le hle hyb ha1 ha2
        · exact not_inRegion_of_le hle hb1 ha2 ha1

/-- Order-independent interned `DataDisjoint` check: read-only pairs may share tail-merged string
    bytes, whereas any pair involving a writable object must occupy disjoint address ranges. -/
def multiDataDisjointB (ML : MultiLib) (mly : MultiLayout) : Bool :=
  dataEntriesDisjointB
    (ML.data.map fun d => (d.readOnly, mly.addrs.getD d.sym 0#64, d.bytes.length + d.zeroTail))

/-- `Interned.checkMulti` plus `Interned.multiDataDisjointB`: one `decide +kernel` gives
    `Placeable`, `InElf`, and `DataDisjoint`. -/
def checkMultiDisjoint (ML : MultiLib) (mly : MultiLayout) (nameChars : List (List Char))
    (img : ElfImage) (enc : EncSymTable (BitVec 64)) : Bool :=
  checkMulti ML mly nameChars img enc && multiDataDisjointB ML mly

/-- `DataDisjoint` from `multiDataDisjointB`, given the facts its relocation-length argument needs
    (`Placeable`, and the segment-free checks relating `ML` to `mly`). -/
theorem dataDisjoint_of_multiDataDisjointB {ML : MultiLib} {mly : MultiLayout}
    (hnd : ML.names.Nodup) (hids : ML.idsOk = true) (hmatch : blockSymsMatchB ML mly = true)
    (hpl : ML.toMultiPlacedLib.Placeable (mly.toMultiPlacement ML.names))
    (hs : multiDataDisjointB ML mly = true) :
    ML.toMultiPlacedLib.DataDisjoint (mly.toMultiPlacement ML.names) := by
  have hok0 := ML.emptyBlock_idsOk hids
  have hres_eq : ∀ s, ML.toMultiPlacedLib.resolve (mly.toMultiPlacement ML.names) s =
      (mly.dataLayout.toPlacement ML.names).ρ s :=
    toMultiPlacement_resolve_eq hnd hids hmatch
  have ⟨_, hpw⟩ := dataEntriesDisjointB_pairwise hs
  have heq : (ML.toMultiPlacedLib.data.map fun d =>
      (d.readOnly, (mly.toMultiPlacement ML.names).ρ d.sym,
        (ML.toMultiPlacedLib.patchedData (mly.toMultiPlacement ML.names) d).length)) =
      ML.data.map fun d =>
        (d.readOnly, mly.addrs.getD d.sym 0#64, d.bytes.length + d.zeroTail) := by
    simp only [MultiLib.toMultiPlacedLib_data, List.map_map]
    refine List.map_congr_left fun d hd => ?_
    have hdi : d.toInfo ML.names ∈ ML.toMultiPlacedLib.data := by
      simp only [MultiLib.toMultiPlacedLib_data]; exact List.mem_map_of_mem hd
    simp only [Function.comp_apply, Prod.mk.injEq]
    refine ⟨rfl, toPlacement_ρ (ly := mly.dataLayout) hnd (hok0.data d hd).1, ?_⟩
    have hpr : ML.toMultiPlacedLib.patchDataReloc (mly.toMultiPlacement ML.names) =
        (ML.blockLib { code := [] }).toLib.patchDataReloc
          (mly.dataLayout.toPlacement ML.names) := by
      funext addr bytes r
      simp only [MultiPlacedLib.patchDataReloc, PlacedLib.patchDataReloc, hres_eq]
      rfl
    have hpd : ML.toMultiPlacedLib.patchedData (mly.toMultiPlacement ML.names)
        (d.toInfo ML.names) =
        (ML.blockLib { code := [] }).toLib.patchedData
          (mly.dataLayout.toPlacement ML.names) (d.toInfo ML.names) := by
      simp only [MultiPlacedLib.patchedData, PlacedLib.patchedData, hpr]
      rfl
    rw [hpd, PlacedLib.length_patchedData fun r hr => (hpl.data_relocs_ok _ hdi r hr).2.1]
    rfl
  rw [← heq, List.pairwise_map] at hpw
  exact hpw

theorem checkMultiDisjoint_spec {ML : MultiLib} {mly : MultiLayout} {nameChars : List (List Char)}
    {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (h : checkMultiDisjoint ML mly nameChars img (prepareCharAssocVal symChars) = true) :
    let lib := ML.toMultiPlacedLib
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  simp only [checkMultiDisjoint, Bool.and_eq_true] at h
  obtain ⟨hc, hs⟩ := h
  have ⟨hpl, hin⟩ := checkMulti_spec hnames hsyms hc
  simp only [checkMulti, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hnn, hids⟩, hmatch⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨hpl, hin,
    dataDisjoint_of_multiDataDisjointB (nodup_of_namesNodup hnames hnn) hids hmatch hpl hs⟩

end Interned

/-! ## Sub-library embedding (`MultiPlacedLib.embedsAt` and `embed_subroutine_ok`) -/

deriving instance DecidableEq for CodeBlock

def listNodupB {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && listNodupB xs

theorem listNodupB_spec {α : Type} [DecidableEq α] :
    ∀ {xs : List α}, listNodupB xs = true → xs.Nodup
  | [], _ => .nil
  | x :: xs, h => by
    simp only [listNodupB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact List.Pairwise.cons (fun y hy heq => h.1 (heq ▸ hy)) (listNodupB_spec h.2)

/-- Computable check that `sub` embeds into `caller` via block-index map `idx`:
    `idx` maps each block `k < sub.blocks.length` of `sub` to a distinct block `idx[k]` of
    `caller` with identical `CodeBlock`, `sub`'s block symbols and data symbols are distinct, and
    every `SymDataInfo` of `sub` appears in `caller.data`. -/
def MultiPlacedLib.embedsAt (sub caller : MultiPlacedLib) (idx : List Nat) : Bool :=
  idx.length == sub.blocks.length &&
  listNodupB idx &&
  idx.all (· < caller.blocks.length) &&
  (List.range sub.blocks.length).all (fun k =>
    decide (caller.blocks.getD (idx.getD k 0) { code := [] } = sub.blocks.getD k { code := [] })) &&
  listNodupB ((sub.blocks.flatMap (·.symbols)).map (·.1)) &&
  listNodupB (sub.data.map (·.sym)) &&
  sub.data.all (fun d => caller.data.contains d)

/-- Induced placement for an embedded sub-library `sub` inside `(caller, callerMpl)` along `idx`. -/
def MultiPlacement.subPlacement (callerMpl : MultiPlacement) (caller : MultiPlacedLib)
    (idx : List Nat) : MultiPlacement where
  base k := callerMpl.base (idx.getD k 0)
  ρ := caller.resolve callerMpl
  relax k := callerMpl.relax (idx.getD k 0)
  b2b k := callerMpl.b2b (idx.getD k 0)
  undefWeak := callerMpl.undefWeak

theorem MultiPlacedLib.embedsAt_block_eq {sub caller : MultiPlacedLib} {idx : List Nat}
    (hemb : sub.embedsAt caller idx = true) {k : Nat} (hk : k < sub.blocks.length) :
    ∃ hj : idx.getD k 0 < caller.blocks.length, caller.blocks[idx.getD k 0] = sub.blocks[k] := by
  simp only [MultiPlacedLib.embedsAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at hemb
  rcases hemb with ⟨⟨⟨⟨⟨⟨hlen, _⟩, hall_lt⟩, hall_eq⟩, _⟩, _⟩, _⟩
  have hk_idx : k < idx.length := hlen.symm ▸ hk
  have hmem : idx.getD k 0 ∈ idx := by rw [Interned.getD_of_lt hk_idx]; exact List.getElem_mem hk_idx
  have hj : idx.getD k 0 < caller.blocks.length := hall_lt _ hmem
  have heq := hall_eq k hk
  rw [Interned.getD_of_lt hj, Interned.getD_of_lt hk] at heq
  exact ⟨hj, heq⟩

theorem MultiPlacedLib.lookupBlockSym_of_embedsAt {sub caller : MultiPlacedLib} {idx : List Nat}
    {sym : String} {k off : Nat}
    (hemb : sub.embedsAt caller idx = true)
    (hnd : ((caller.blocks.flatMap (·.symbols)).map (·.1)).Nodup)
    (hl : lookupBlockSym sym sub.blocks = some (k, off)) :
    lookupBlockSym sym caller.blocks = some (idx.getD k 0, off) := by
  obtain ⟨hk, hlk⟩ := lookupBlockSym_some hl
  obtain ⟨hj, hblk_eq⟩ := sub.embedsAt_block_eq hemb hk
  rw [← hblk_eq] at hlk
  exact lookupBlockSym_of_lookup hj hnd hlk

theorem MultiPlacedLib.resolve_subPlacement {sub caller : MultiPlacedLib}
    {callerMpl : MultiPlacement} {idx : List Nat}
    (hemb : sub.embedsAt caller idx = true) (hpl : caller.Placeable callerMpl) (sym : String) :
    sub.resolve (callerMpl.subPlacement caller idx) sym = caller.resolve callerMpl sym := by
  unfold MultiPlacedLib.resolve
  cases hl : lookupBlockSym sym sub.blocks with
  | none => rfl
  | some p =>
    rcases p with ⟨k, off⟩
    rw [sub.lookupBlockSym_of_embedsAt hemb hpl.symbols_nodup hl]
    rfl

theorem MultiPlacedLib.resolve_subPlacement_fun {sub caller : MultiPlacedLib}
    {callerMpl : MultiPlacement} {idx : List Nat}
    (hemb : sub.embedsAt caller idx = true) (hpl : caller.Placeable callerMpl) :
    sub.resolve (callerMpl.subPlacement caller idx) = caller.resolve callerMpl :=
  funext (sub.resolve_subPlacement hemb hpl)

theorem MultiPlacedLib.blockPlacement_subPlacement {sub caller : MultiPlacedLib}
    {callerMpl : MultiPlacement} {idx : List Nat}
    (hemb : sub.embedsAt caller idx = true) (hpl : caller.Placeable callerMpl) (k : Nat) :
    sub.blockPlacement (callerMpl.subPlacement caller idx) k =
      caller.blockPlacement callerMpl (idx.getD k 0) := by
  dsimp only [MultiPlacedLib.blockPlacement]
  rw [sub.resolve_subPlacement_fun hemb hpl]
  rfl

theorem MultiPlacedLib.blockProgram_subPlacement {sub caller : MultiPlacedLib}
    {callerMpl : MultiPlacement} {idx : List Nat} {k : Nat}
    (hemb : sub.embedsAt caller idx = true) (hpl : caller.Placeable callerMpl)
    (hk : k < sub.blocks.length)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) :
    sub.blockProgram (callerMpl.subPlacement caller idx) k externs overrides svc =
      caller.blockProgram callerMpl (idx.getD k 0) externs overrides svc := by
  obtain ⟨hj, hblk_eq⟩ := sub.embedsAt_block_eq hemb hk
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program]
  rw [sub.blockLib_text hk, caller.blockLib_text hj, hblk_eq,
    sub.blockPlacement_subPlacement hemb hpl k]

theorem MultiPlacedLib.placeable_subPlacement {sub caller : MultiPlacedLib}
    {callerMpl : MultiPlacement} {idx : List Nat}
    (hemb : sub.embedsAt caller idx = true) (hpl : caller.Placeable callerMpl) :
    sub.Placeable (callerMpl.subPlacement caller idx) := by
  have hemb' := hemb
  simp only [MultiPlacedLib.embedsAt, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_eq_mem, decide_eq_true_eq] at hemb'
  rcases hemb' with ⟨⟨⟨⟨⟨⟨hlen, hnd_idx⟩, _⟩, _⟩, hnd_sym⟩, hnd_data⟩, hdata_mem⟩
  have hidx_nd : idx.Nodup := listNodupB_spec hnd_idx
  refine
    { blocks_ok := fun i hi => by
        obtain ⟨hj, hblk_eq⟩ := sub.embedsAt_block_eq hemb hi
        rw [sub.blockPlacement_subPlacement hemb hpl i, ← hblk_eq]
        exact hpl.blocks_ok _ hj
      blocks_disjoint := fun i j hi hj hij => by
        obtain ⟨hii, hbi⟩ := sub.embedsAt_block_eq hemb hi
        obtain ⟨hjj, hbj⟩ := sub.embedsAt_block_eq hemb hj
        have hi_idx : i < idx.length := hlen.symm ▸ hi
        have hj_idx : j < idx.length := hlen.symm ▸ hj
        have hne : idx.getD i 0 ≠ idx.getD j 0 := by
          rw [Interned.getD_of_lt hi_idx, Interned.getD_of_lt hj_idx]
          intro heq
          exact Nat.ne_of_lt hij ((hidx_nd.getElem_inj (hi := hi_idx) (hj := hj_idx)).mp heq)
        simp only [MultiPlacement.subPlacement, ← hbi, ← hbj]
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · exact hpl.blocks_disjoint _ _ hii hjj hlt
        · exact (hpl.blocks_disjoint _ _ hjj hii hgt).symm
      symbols_nodup := listNodupB_spec hnd_sym
      data_nodup := listNodupB_spec hnd_data
      data_ok := fun d hd => by
        have hdc := hdata_mem d hd
        obtain ⟨hnone_c, hal_pos, hal, hnw⟩ := hpl.data_ok d hdc
        have hrho : (callerMpl.subPlacement caller idx).ρ d.sym = callerMpl.ρ d.sym := by
          simp [MultiPlacement.subPlacement, MultiPlacedLib.resolve, hnone_c]
        refine ⟨?_, hal_pos, hrho ▸ hal, hrho ▸ hnw⟩
        cases hl : lookupBlockSym d.sym sub.blocks with
        | none => rfl
        | some p =>
          rcases p with ⟨k, off⟩
          have hc := sub.lookupBlockSym_of_embedsAt hemb hpl.symbols_nodup hl
          rw [hnone_c] at hc; cases hc
      data_relocs_ok := fun d hd r hr => by
        have hdc := hdata_mem d hd
        obtain ⟨hnone_c, _, _, _⟩ := hpl.data_ok d hdc
        have hrho : (callerMpl.subPlacement caller idx).ρ d.sym = callerMpl.ρ d.sym := by
          simp [MultiPlacement.subPlacement, MultiPlacedLib.resolve, hnone_c]
        simpa only [sub.resolve_subPlacement hemb hpl, hrho] using hpl.data_relocs_ok d hdc r hr }

theorem MultiPlacedLib.codeLoaded_subPlacement {sub caller : MultiPlacedLib}
    {callerMpl : MultiPlacement} {idx : List Nat} {m : Memory}
    (hemb : sub.embedsAt caller idx = true) (hpl : caller.Placeable callerMpl)
    (hcl : caller.CodeLoaded callerMpl m) :
    sub.CodeLoaded (callerMpl.subPlacement caller idx) m := fun k hk => by
  obtain ⟨hj, _⟩ := sub.embedsAt_block_eq hemb hk
  rw [sub.blockProgram_subPlacement hemb hpl hk]
  exact hcl (idx.getD k 0) hj

theorem MultiPlacedLib.fnAddr_subPlacement {sub caller : MultiPlacedLib}
    {callerMpl : MultiPlacement} {idx : List Nat} {sym : String}
    (hemb : sub.embedsAt caller idx = true) (hpl : caller.Placeable callerMpl)
    (hsym : (lookupBlockSym sym sub.blocks).isSome = true) :
    sub.fnAddr (callerMpl.subPlacement caller idx) sym = caller.fnAddr callerMpl sym := by
  unfold MultiPlacedLib.fnAddr
  cases hl : lookupBlockSym sym sub.blocks with
  | none => simp [hl] at hsym
  | some p =>
    rcases p with ⟨k, off⟩
    rw [sub.lookupBlockSym_of_embedsAt hemb hpl.symbols_nodup hl]
    rfl

/-- Lift a block-program `subroutine_ok` contract from an embedded sub-library `sub` directly to
    `caller.blockProgram callerMpl j` (with `caller.withCodeLoaded callerMpl`), ready for
    `wp_call_block` or `MultiPlacedLib.subroutine_ok_of_block`. -/
theorem MultiPlacedLib.embed_subroutine_ok {α : Type} {sub caller : MultiPlacedLib}
    {callerMpl : MultiPlacement} {idx : List Nat} {k j : Nat} {sym : String}
    {specSub specCaller : Spec α}
    (hemb : sub.embedsAt caller idx = true)
    (hpl : caller.Placeable callerMpl)
    (hk : k < sub.blocks.length := by decide)
    (hj : idx.getD k 0 = j := by decide)
    (hsym : (lookupBlockSym sym sub.blocks).isSome = true := by decide)
    (hspec : specSub = specCaller := by rfl)
    (hok : subroutine_ok
      (sub.blockProgram (callerMpl.subPlacement caller idx) k)
      (sub.fnAddr (callerMpl.subPlacement caller idx) sym)
      (sub.withCodeLoaded (callerMpl.subPlacement caller idx) specSub)) :
    subroutine_ok
      (caller.blockProgram callerMpl j)
      (caller.fnAddr callerMpl sym)
      (caller.withCodeLoaded callerMpl specCaller) := by
  subst hj hspec
  rw [← sub.blockProgram_subPlacement hemb hpl hk, ← sub.fnAddr_subPlacement hemb hpl hsym]
  refine subroutine_ok_mono hok (fun x R s0 hpre => ?_) (fun _ _ _ _ hp => hp)
  dsimp only [MultiPlacedLib.withCodeLoaded] at hpre ⊢
  rw [sepConj_comm (specSub.pre x s0), sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨sub.codeLoaded_subPlacement hemb hpl hpre.1, hpre.2⟩

private theorem steps_transfer_same_svc {P1 P2 : Program}
    (hext1 : ∀ pc, P1.externAt? pc = none) (hext2 : ∀ pc, P2.externAt? pc = none)
    (hsvc : P1.svc = P2.svc) {sa sf : State} (h : Steps P1 sa sf) : Steps P2 sa sf := by
  induction h with
  | refl _ => exact Steps.refl _
  | @step sa' sb _ h1 _ ih =>
    cases h1 with
    | halt_unmapped hrun hfm _ =>
      exact Steps.step (Step.halt_unmapped hrun
        (by simpa [Program.fetchMem, hext1, hext2] using hfm) (hext2 _)) ih
    | extern _ hex => rw [hext1] at hex; cases hex
    | extern_fault _ hex => rw [hext1] at hex; cases hex
    | @exec inst hrun hfm =>
      have hfm2 : P2.fetchMem sa'.mem sa'.pc = some inst := by
        simpa [Program.fetchMem, hext1, hext2] using hfm
      have hev : P1.evalInst inst sa' = P2.evalInst inst sa' := by
        simp [Program.evalInst, hsvc]
      rw [hev] at ih
      exact Steps.step (Step.exec hrun hfm2) ih

/-- Transfer `subroutine_ok` from `P1` to `P2` when both are hook-free, share `svc`, and
    `P2.CodeLoaded m` implies `P1.CodeLoaded m`. -/
theorem subroutine_ok_of_codeLoaded_imp {α : Type} {P1 P2 : Program} {entry : BitVec 64}
    {spec : Spec α} (hsub : subroutine_ok P1 entry spec)
    (hext1 : ∀ pc, P1.externAt? pc = none) (hext2 : ∀ pc, P2.externAt? pc = none)
    (hsvc : P1.svc = P2.svc) (hcl : ∀ m, P2.CodeLoaded m → P1.CodeLoaded m) :
    subroutine_ok P2 entry spec := by
  simp only [subroutine_ok_iff, reaches_outcome_iff] at hsub ⊢
  intro x R s0 hpc hrun hpre hsp hcl2
  obtain ⟨sf, hsteps1, hout⟩ := hsub x R s0 hpc hrun hpre hsp (hcl s0.mem hcl2)
  exact ⟨sf, steps_transfer_same_svc hext1 hext2 hsvc hsteps1, hout⟩

/-! ## Indexed `O(log S)` and `O(log B)` block, symbol, and data lookup -/

/-- Search a pre-extracted list of per-block symbol tables starting at block index `k`. -/
def lookupSymInLists (name : String) : Nat → List (List (String × Nat)) → Option (Nat × Nat)
  | _, [] => none
  | k, syms :: rest =>
    match lookup name syms with
    | some off => some (k, off)
    | none => lookupSymInLists name (k + 1) rest

theorem lookupBlockSymAux_eq_lookupSymInLists (name : String) :
    ∀ (k : Nat) (blocks : List CodeBlock),
      lookupBlockSymAux name k blocks = lookupSymInLists name k (blocks.map (·.symbols))
  | _, [] => rfl
  | k, blk :: rest => by
    simp only [lookupBlockSymAux, List.map_cons, lookupSymInLists]
    cases lookup name blk.symbols with
    | some _ => rfl
    | none => exact lookupBlockSymAux_eq_lookupSymInLists name (k + 1) rest

theorem lookupBlockSym_eq_lookupSymInLists (name : String) (blocks : List CodeBlock) :
    lookupBlockSym name blocks = lookupSymInLists name 0 (blocks.map (·.symbols)) :=
  lookupBlockSymAux_eq_lookupSymInLists name 0 blocks

/-- Two multi-block placed libraries share identical per-block symbol tables. -/
def MultiPlacedLib.SameSymbolLayout (a b : MultiPlacedLib) : Prop :=
  a.blocks.map (·.symbols) = b.blocks.map (·.symbols)

theorem lookupBlockSym_eq_of_sameSymbolLayout {a b : MultiPlacedLib}
    (h : a.SameSymbolLayout b) (name : String) :
    lookupBlockSym name a.blocks = lookupBlockSym name b.blocks := by
  rw [lookupBlockSym_eq_lookupSymInLists, lookupBlockSym_eq_lookupSymInLists, h]

theorem MultiPlacedLib.resolve_eq_of_sameSymbolLayout {a b : MultiPlacedLib}
    (h : a.SameSymbolLayout b) (mpl : MultiPlacement) (name : String) :
    a.resolve mpl name = b.resolve mpl name := by
  simp only [MultiPlacedLib.resolve, lookupBlockSym_eq_of_sameSymbolLayout h]

theorem MultiPlacedLib.fnAddr_eq_of_sameSymbolLayout {a b : MultiPlacedLib}
    (h : a.SameSymbolLayout b) (mpl : MultiPlacement) (name : String) :
    a.fnAddr mpl name = b.fnAddr mpl name := by
  simp only [MultiPlacedLib.fnAddr, lookupBlockSym_eq_of_sameSymbolLayout h]

theorem MultiPlacedLib.blockPlacement_eq_of_sameSymbolLayout {a b : MultiPlacedLib}
    (h : a.SameSymbolLayout b) (mpl : MultiPlacement) (i : Nat) :
    a.blockPlacement mpl i = b.blockPlacement mpl i := by
  simp only [MultiPlacedLib.blockPlacement]
  congr 1
  funext s
  exact a.resolve_eq_of_sameSymbolLayout h mpl s

theorem CodeBlock.target_blockPlacement_eq_of_sameSymbolLayout {a b : MultiPlacedLib}
    (h : a.SameSymbolLayout b) (blk : CodeBlock) (mpl : MultiPlacement) (i : Nat)
    (r : RelocEntry) :
    blk.target (a.blockPlacement mpl i) r = blk.target (b.blockPlacement mpl i) r := by
  rw [a.blockPlacement_eq_of_sameSymbolLayout h]

/-- Convert one block's `(List Char, byteOff)` symbol entries into `(String, byteOff)` via
    forward `String.ofList` (evaluated natively in the kernel without `String.toList`). -/
def charSymsToStrings : List (List Char × Nat) → List (String × Nat)
  | [] => []
  | (cs, off) :: rest => (String.ofList cs, off) :: charSymsToStrings rest

/-- Linear lookup over one block's pre-converted `(cs, off)` list using primitive
    `charListBeq`. -/
def lookupCharSymInList (cs : List Char) : List (List Char × Nat) → Option Nat
  | [] => none
  | p :: rest => if charListBeq p.1 cs then some p.2 else lookupCharSymInList cs rest

theorem lookupCharSymInList_eq_lookup_charSymsToStrings (cs : List Char) :
    ∀ (syms : List (List Char × Nat)),
      lookupCharSymInList cs syms = lookup (String.ofList cs) (charSymsToStrings syms)
  | [] => rfl
  | (k, v) :: rest => by
    unfold lookup lookupCharSymInList charSymsToStrings
    simp only [List.find?_cons]
    cases hc : charListBeq k cs with
    | true =>
      have hk : k = cs := charListBeq_iff_eq.mp hc
      simp [hk]
    | false =>
      have hne : (String.ofList k == String.ofList cs) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro heq
        exact Bool.false_ne_true
          (hc.symm.trans (charListBeq_iff_eq.mpr (String.ofList_inj.mp heq)))
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      exact lookupCharSymInList_eq_lookup_charSymsToStrings cs rest

theorem nodup_blockSymbols_of_symBST_ranks {blocks : List CodeBlock}
    {t : SymBST (Nat × Nat × Nat)} {blkRanks : List (List Nat)}
    (hsort : isStrictSorted t.toList = true)
    (hranks : mapBlockSymRanks t 0 blkRanks = some (blocks.map CodeBlock.symbols)) :
    ((blocks.flatMap (·.symbols)).map (·.1)).Nodup := by
  simpa only [List.flatMap_map, Function.comp_def, id_eq] using
    nodup_flatMap_of_symBST_blockRanks hsort hranks

/-- Precomputed `O(log B)` / `O(log S)` tree index over a `MultiPlacedLib`'s blocks, symbol tables,
    and `.rodata` sections. Build and certify once per library with `gen_multi_sym_index`. -/
structure MultiPlacedLib.SymIndex (lib : MultiPlacedLib) where
  blocksTree : IdxTree CodeBlock
  blockCharSymsTree : IdxTree (List (List Char × Nat))
  symBST : SymBST (Nat × Nat × Nat)
  blkSymRanks : List (List Nat)
  dataTree : IdxTree SymDataInfo
  dataSymBucketTree : IdxTree (List (List Char × Nat))
  blocks_eq : blocksTree.toList = lib.blocks
  blocks_size : blocksTree.size? = some lib.blocks.length
  charSyms_eq :
    blockCharSymsTree.toList.map charSymsToStrings = lib.blocks.map CodeBlock.symbols
  charSyms_size : blockCharSymsTree.size? = some lib.blocks.length
  symbols_nodup : ((lib.blocks.flatMap (·.symbols)).map (·.1)).Nodup
  sym_sorted : isStrictSorted symBST.toList = true
  sym_ranks : mapBlockSymRanks symBST 0 blkSymRanks = some (lib.blocks.map CodeBlock.symbols)
  data_eq : dataTree.toList = lib.data

namespace MultiPlacedLib.SymIndex

/-- Resolve character list `cs` to `(blockIdx, byteOff)` in `O(log S + log B)` kernel steps. -/
def lookupBlockCharSym {lib : MultiPlacedLib} (idx : lib.SymIndex) (cs : List Char) :
    Option (Nat × Nat) :=
  match idx.symBST.find? cs with
  | some (blkIdx, _, _) =>
    match idx.blockCharSymsTree.get? blkIdx with
    | some syms =>
      match lookupCharSymInList cs syms with
      | some off => some (blkIdx, off)
      | none => none
    | none => none
  | none => none

/-- Resolve symbol `name` to `(blockIdx, byteOff)` in `lib.blocks` in `O(log S + log B)` steps. -/
def lookupBlockSym {lib : MultiPlacedLib} (idx : lib.SymIndex) (name : String) :
    Option (Nat × Nat) :=
  idx.lookupBlockCharSym name.toList

/-- Decidable `O(log S)` check that `cs` is absent from all blocks of `lib`. -/
def notBlockCharSym {lib : MultiPlacedLib} (idx : lib.SymIndex) (cs : List Char) : Bool :=
  (idx.symBST.find? cs).isNone

/-- Decidable `O(log S)` check that symbol `name` is absent from all blocks of `lib`. -/
def notBlockSym {lib : MultiPlacedLib} (idx : lib.SymIndex) (name : String) : Bool :=
  idx.notBlockCharSym name.toList

/-- Resolve character list `cs` to `(dataIdx, d)` in `lib.data` in `O(log D)` kernel steps. -/
def findDataSymChars {lib : MultiPlacedLib} (idx : lib.SymIndex) (cs : List Char) :
    Option (Nat × SymDataInfo) :=
  match idx.dataSymBucketTree.get? (hashChars1024 cs) with
  | some bucket =>
    match bucket.find? (fun e => charListBeq e.1 cs) with
    | some (_, dataIdx) =>
      match idx.dataTree.get? dataIdx with
      | some d => if d.sym == String.ofList cs then some (dataIdx, d) else none
      | none => none
    | none => none
  | none => none

/-- Resolve symbol `name` to `(dataIdx, d)` in `lib.data` in `O(log D)` kernel steps. -/
def findDataSym {lib : MultiPlacedLib} (idx : lib.SymIndex) (name : String) :
    Option (Nat × SymDataInfo) :=
  idx.findDataSymChars name.toList

/-- Indexed equivalent of `lib.resolve mpl name`. -/
def resolve {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement) (name : String) :
    BitVec 64 :=
  match idx.lookupBlockSym name with
  | some (i, off) => mpl.base i + BitVec.ofNat 64 off
  | none => mpl.ρ name

/-- Indexed equivalent of `lib.fnAddr mpl name`. -/
def fnAddr {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement) (name : String) :
    BitVec 64 :=
  match idx.lookupBlockSym name with
  | some (i, off) => mpl.base i + BitVec.ofNat 64 off
  | none => mpl.base 0

theorem blocks_get?_eq {lib : MultiPlacedLib} (idx : lib.SymIndex) (i : Nat) :
    idx.blocksTree.get? i = lib.blocks[i]? := by
  rw [IdxTree.get?_eq_getElem? idx.blocks_size, idx.blocks_eq]

theorem block_of_get? {lib : MultiPlacedLib} (idx : lib.SymIndex) {i : Nat} {blk : CodeBlock}
    (h : idx.blocksTree.get? i = some blk) :
    ∃ (hi : i < lib.blocks.length), lib.blocks[i] = blk := by
  rw [idx.blocks_get?_eq] at h
  exact List.getElem?_eq_some_iff.mp h

theorem blockLib_eq_of_get? {lib : MultiPlacedLib} (idx : lib.SymIndex) {i : Nat}
    {blk : CodeBlock} (h : idx.blocksTree.get? i = some blk) :
    lib.blockLib i = { name := lib.name, text := blk, data := lib.data, exports := lib.exports } := by
  obtain ⟨hi, rfl⟩ := idx.block_of_get? h
  simp [MultiPlacedLib.blockLib, hi]

theorem blockProgram_eq_of_get? {lib : MultiPlacedLib} (idx : lib.SymIndex) {i : Nat}
    {blk : CodeBlock} (h : idx.blocksTree.get? i = some blk) (mpl : MultiPlacement)
    (X O : String → Option (State → State)) (svc : State → State) :
    lib.blockProgram mpl i X O svc =
      ({ name := lib.name, text := blk, data := lib.data, exports := lib.exports } : PlacedLib).program
        (lib.blockPlacement mpl i) X O svc := by
  simp only [MultiPlacedLib.blockProgram, idx.blockLib_eq_of_get? h]

theorem charSyms_get?_map_eq {lib : MultiPlacedLib} (idx : lib.SymIndex) (i : Nat) :
    (idx.blockCharSymsTree.get? i).map charSymsToStrings =
      (lib.blocks[i]?).map CodeBlock.symbols := by
  rw [IdxTree.get?_eq_getElem? idx.charSyms_size, ← List.getElem?_map,
    idx.charSyms_eq, List.getElem?_map]

theorem lookupBlockSym_eq_some_of_chars {lib : MultiPlacedLib} (idx : lib.SymIndex)
    {cs : List Char} {i off : Nat}
    (h : idx.lookupBlockCharSym cs = some (i, off)) :
    Obj.lookupBlockSym (String.ofList cs) lib.blocks = some (i, off) := by
  unfold lookupBlockCharSym at h
  cases hf : idx.symBST.find? cs with
  | none => simp [hf] at h
  | some tri =>
    rcases tri with ⟨blkIdx, _, _⟩
    simp only [hf] at h
    cases hg : idx.blockCharSymsTree.get? blkIdx with
    | none => simp [hg] at h
    | some syms =>
      simp only [hg] at h
      cases hl : lookupCharSymInList cs syms with
      | none => simp [hl] at h
      | some off' =>
        simp only [hl, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hmap := idx.charSyms_get?_map_eq blkIdx
        rw [hg, Option.map_some] at hmap
        cases hblk : lib.blocks[blkIdx]? with
        | none => simp [hblk] at hmap
        | some blk =>
          simp only [hblk, Option.map_some, Option.some.injEq] at hmap
          obtain ⟨hi, hblk_eq⟩ := List.getElem?_eq_some_iff.mp hblk
          subst hblk_eq
          rw [lookupCharSymInList_eq_lookup_charSymsToStrings, hmap] at hl
          exact lookupBlockSym_of_lookup hi idx.symbols_nodup hl

theorem lookupBlockSym_eq_some {lib : MultiPlacedLib} (idx : lib.SymIndex)
    {name : String} {i off : Nat}
    (h : idx.lookupBlockSym name = some (i, off)) :
    Obj.lookupBlockSym name lib.blocks = some (i, off) := by
  simpa using idx.lookupBlockSym_eq_some_of_chars h

theorem lookupBlockSym_of_exists {lib : MultiPlacedLib} (idx : lib.SymIndex)
    {name : String} {i off : Nat}
    (h : Obj.lookupBlockSym name lib.blocks = some (i, off)) :
    idx.lookupBlockSym name = some (i, off) := by
  obtain ⟨hi, hl⟩ := lookupBlockSym_some h
  have hmem : (name, off) ∈ lib.blocks[i].symbols := mem_of_lookup_some hl
  obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hmem
  have hi? : (lib.blocks.map CodeBlock.symbols)[i]? = some lib.blocks[i].symbols := by
    simp [hi]
  have hk? : lib.blocks[i].symbols[k]? = some (name, off) := by
    rw [List.getElem?_eq_getElem hk, hkv]
  obtain ⟨cs, hs, hm⟩ := mem_symBST_of_mapBlockSymRanks idx.sym_ranks hi? hk?
  have hcs : cs = name.toList :=
    String.ofList_inj.mp (hs.trans (by simp : name = String.ofList name.toList))
  subst hcs
  rw [Nat.zero_add] at hm
  have hfind := SymBST.find?_eq_some_of_mem idx.sym_sorted hm
  have hmap := idx.charSyms_get?_map_eq i
  rw [List.getElem?_eq_getElem hi, Option.map_some] at hmap
  unfold lookupBlockSym lookupBlockCharSym
  simp only [hfind]
  cases hg : idx.blockCharSymsTree.get? i with
  | none => simp [hg] at hmap
  | some syms =>
    simp only [hg, Option.map_some, Option.some.injEq] at hmap
    simp [lookupCharSymInList_eq_lookup_charSymsToStrings, hmap, hl]

theorem lookupBlockSym_eq {lib : MultiPlacedLib} (idx : lib.SymIndex) (name : String) :
    idx.lookupBlockSym name = Obj.lookupBlockSym name lib.blocks := by
  cases h : Obj.lookupBlockSym name lib.blocks with
  | some p => exact idx.lookupBlockSym_of_exists h
  | none =>
    cases hi : idx.lookupBlockSym name with
    | none => rfl
    | some p =>
      have := idx.lookupBlockSym_eq_some hi
      rw [h] at this; cases this

theorem lookupBlockCharSym_eq {lib : MultiPlacedLib} (idx : lib.SymIndex) (cs : List Char) :
    idx.lookupBlockCharSym cs = Obj.lookupBlockSym (String.ofList cs) lib.blocks := by
  have h := idx.lookupBlockSym_eq (String.ofList cs)
  unfold lookupBlockSym at h
  have hcs : (String.ofList cs).toList = cs :=
    String.ofList_inj.mp (by simp : String.ofList (String.ofList cs).toList = String.ofList cs)
  rwa [hcs] at h

theorem lookupBlockSym_eq_none_of_chars {lib : MultiPlacedLib} (idx : lib.SymIndex)
    {cs : List Char} (h : idx.notBlockCharSym cs = true) :
    Obj.lookupBlockSym (String.ofList cs) lib.blocks = none := by
  rw [← idx.lookupBlockCharSym_eq]
  unfold lookupBlockCharSym
  unfold notBlockCharSym at h
  cases hf : idx.symBST.find? cs <;> simp [hf] at h ⊢

theorem lookupBlockSym_eq_none {lib : MultiPlacedLib} (idx : lib.SymIndex) {name : String}
    (h : idx.notBlockSym name = true) :
    Obj.lookupBlockSym name lib.blocks = none := by
  simpa using idx.lookupBlockSym_eq_none_of_chars h

theorem resolve_eq {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement)
    (name : String) :
    idx.resolve mpl name = lib.resolve mpl name := by
  unfold resolve MultiPlacedLib.resolve
  rw [idx.lookupBlockSym_eq]
  cases Obj.lookupBlockSym name lib.blocks with
  | none => rfl
  | some p => rfl

theorem fnAddr_eq {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement)
    (name : String) :
    idx.fnAddr mpl name = lib.fnAddr mpl name := by
  unfold fnAddr MultiPlacedLib.fnAddr
  rw [idx.lookupBlockSym_eq]
  cases Obj.lookupBlockSym name lib.blocks with
  | none => rfl
  | some p => rfl

theorem resolve_eq_base_of_chars {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement)
    {cs : List Char} {i off : Nat}
    (h : idx.lookupBlockCharSym cs = some (i, off)) :
    lib.resolve mpl (String.ofList cs) = mpl.base i + BitVec.ofNat 64 off := by
  simp only [MultiPlacedLib.resolve, idx.lookupBlockSym_eq_some_of_chars h]

theorem resolve_eq_base {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement)
    {name : String} {i off : Nat}
    (h : idx.lookupBlockSym name = some (i, off)) :
    lib.resolve mpl name = mpl.base i + BitVec.ofNat 64 off := by
  simp only [MultiPlacedLib.resolve, idx.lookupBlockSym_eq_some h]

theorem resolve_eq_rho_of_chars {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement)
    {cs : List Char} (h : idx.notBlockCharSym cs = true) :
    lib.resolve mpl (String.ofList cs) = mpl.ρ (String.ofList cs) := by
  simp only [MultiPlacedLib.resolve, idx.lookupBlockSym_eq_none_of_chars h]

theorem resolve_eq_rho {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement)
    {name : String} (h : idx.notBlockSym name = true) :
    lib.resolve mpl name = mpl.ρ name := by
  simp only [MultiPlacedLib.resolve, idx.lookupBlockSym_eq_none h]

theorem fnAddr_eq_base_of_chars {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement)
    {cs : List Char} {i off : Nat}
    (h : idx.lookupBlockCharSym cs = some (i, off)) :
    lib.fnAddr mpl (String.ofList cs) = mpl.base i + BitVec.ofNat 64 off := by
  simp only [MultiPlacedLib.fnAddr, idx.lookupBlockSym_eq_some_of_chars h]

theorem fnAddr_eq_base {lib : MultiPlacedLib} (idx : lib.SymIndex) (mpl : MultiPlacement)
    {name : String} {i off : Nat}
    (h : idx.lookupBlockSym name = some (i, off)) :
    lib.fnAddr mpl name = mpl.base i + BitVec.ofNat 64 off := by
  simp only [MultiPlacedLib.fnAddr, idx.lookupBlockSym_eq_some h]

theorem blockProgram_fnAddr_eq {lib : MultiPlacedLib} (idx : lib.SymIndex)
    (mpl : MultiPlacement) {X O : String → Option (State → State)} {svc : State → State}
    {name : String} {i off : Nat}
    (h : idx.lookupBlockSym name = some (i, off)) :
    (lib.blockProgram mpl i X O svc).fnAddr name = mpl.base i + BitVec.ofNat 64 off := by
  have hs := idx.lookupBlockSym_eq_some h
  obtain ⟨hi, hl⟩ := lookupBlockSym_some hs
  have hl' : lookup name (lib.blockLib i).text.symbols = some off := by
    rwa [lib.blockLib_text hi]
  have hfn := PlacedLib.fnAddr_program (pl := lib.blockPlacement mpl i)
    (X := X) (O := O) (svc := svc) hl'
  exact hfn.1.trans hfn.2

theorem findDataSymChars_spec {lib : MultiPlacedLib} (idx : lib.SymIndex) {cs : List Char}
    {k : Nat} {d : SymDataInfo}
    (h : idx.findDataSymChars cs = some (k, d)) :
    d ∈ lib.data ∧ d.sym = String.ofList cs ∧ idx.dataTree.get? k = some d := by
  unfold findDataSymChars at h
  cases hb : idx.dataSymBucketTree.get? (hashChars1024 cs) with
  | none => simp [hb] at h
  | some bucket =>
    simp only [hb] at h
    cases hf : bucket.find? (fun e => charListBeq e.1 cs) with
    | none => simp [hf] at h
    | some p =>
      rcases p with ⟨_, dataIdx⟩
      simp only [hf] at h
      cases hg : idx.dataTree.get? dataIdx with
      | none => simp [hg] at h
      | some d0 =>
        simp only [hg] at h
        cases hc : (d0.sym == String.ofList cs) with
        | false => simp [hc] at h
        | true =>
          simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact ⟨idx.data_eq ▸ IdxTree.mem_toList_of_get? hg, eq_of_beq hc, hg⟩

theorem findDataSym_spec {lib : MultiPlacedLib} (idx : lib.SymIndex) {name : String}
    {k : Nat} {d : SymDataInfo}
    (h : idx.findDataSym name = some (k, d)) :
    d ∈ lib.data ∧ d.sym = name ∧ idx.dataTree.get? k = some d := by
  simpa using idx.findDataSymChars_spec h

theorem satisfies_dataRO_of_findDataSym {lib : MultiPlacedLib} (idx : lib.SymIndex)
    {mpl : MultiPlacement} {img : ElfImage} {inputs : ProcessInputs} {s : State}
    (hpl : lib.Placeable mpl) (hin : lib.InElf img mpl) (hload : img.loadState inputs = .ok s)
    (hne : 0 < lib.blocks.length) {name : String} {k : Nat} {d : SymDataInfo}
    (hd : idx.findDataSym name = some (k, d)) (hro : d.readOnly = true) :
    s.mem ⊨ pointsToBytesRO (mpl.ρ name) (lib.patchedData mpl d) := by
  obtain ⟨hmem, hsym, _⟩ := idx.findDataSym_spec hd
  simpa only [hsym] using lib.satisfies_dataRO_of_inElf hpl hin hload hne hmem hro

end MultiPlacedLib.SymIndex

end Arm64.Obj

end

public meta section

namespace Arm64.Obj

declare_wp_proj_guard guardInternedBlockCode Interned.Block code ``Interned.Block.code ``Interned.Block.mk
declare_wp_proj_guard guardInternedBlockSymbols Interned.Block symbols ``Interned.Block.symbols ``Interned.Block.mk
declare_wp_proj_guard guardInternedBlockRelocs Interned.Block relocs ``Interned.Block.relocs ``Interned.Block.mk
declare_wp_proj_guard guardInternedBlockExterns Interned.Block externs ``Interned.Block.externs ``Interned.Block.mk

declare_wp_proj_guard guardInternedMultiLibNames Interned.MultiLib names ``Interned.MultiLib.names ``Interned.MultiLib.mk
declare_wp_proj_guard guardInternedMultiLibBlocks Interned.MultiLib blocks ``Interned.MultiLib.blocks ``Interned.MultiLib.mk
declare_wp_proj_guard guardInternedMultiLibData Interned.MultiLib data ``Interned.MultiLib.data ``Interned.MultiLib.mk
declare_wp_proj_guard guardInternedMultiLibExports Interned.MultiLib exports ``Interned.MultiLib.exports ``Interned.MultiLib.mk

declare_wp_proj_guard guardInternedMultiLayoutBases Interned.MultiLayout bases ``Interned.MultiLayout.bases ``Interned.MultiLayout.mk
declare_wp_proj_guard guardInternedMultiLayoutAddrs Interned.MultiLayout addrs ``Interned.MultiLayout.addrs ``Interned.MultiLayout.mk
declare_wp_proj_guard guardInternedMultiLayoutRelax Interned.MultiLayout relax ``Interned.MultiLayout.relax ``Interned.MultiLayout.mk
declare_wp_proj_guard guardInternedMultiLayoutB2b Interned.MultiLayout b2b ``Interned.MultiLayout.b2b ``Interned.MultiLayout.mk

section GenMultiSymIndex

open Lean Elab Command Term Meta ProofLib.ProgramReflection

/-- Persistent registry mapping a `MultiPlacedLib` constant name to a precomputed `SymIndex`. -/
initialize multiSymIndexExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (libNm, idxNm) => m.insert libNm idxNm
    addImportedFn := fun arrs =>
      arrs.foldl (init := {}) fun m arr =>
        arr.foldl (init := m) fun m (libNm, idxNm) => m.insert libNm idxNm
  }

private partial def multiListElems (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    let e ← whnf e
    if e.isAppOfArity ``List.cons 3 then go (e.getArg! 2) (acc.push (e.getArg! 1))
    else if e.isAppOfArity ``List.nil 1 then return acc
    else throwError "gen_multi_sym_index: expected a concrete list, got{indentExpr e}"
  go e #[]

private def multiNatVal (e : Expr) : MetaM Nat := do
  if let some n := e.rawNatLit? then return n
  if let some n ← (evalNat e).run then return n
  let e ← whnf e
  match e.rawNatLit? with
  | some n => return n
  | none => throwError "gen_multi_sym_index: expected a Nat literal, got{indentExpr e}"

private def multiStrVal (e : Expr) : MetaM String := do
  match (← whnf e) with
  | .lit (.strVal s) => return s
  | e => throwError "gen_multi_sym_index: expected a String literal, got{indentExpr e}"

private def addPrebuiltTreeDef (declName : Name) (ty val : Expr) : TermElabM Unit := do
  let env ← getEnv
  addDecl (.defnDecl {
    name := declName
    levelParams := []
    type := ty
    value := val
    hints := .regular (getMaxHeight env val + 1)
    safety := .safe
  })
  modifyEnv (addNoncomputable · declName)

/-- `gen_multi_sym_index <idxName> <lib>`: precompute and kernel-certify an `O(log B)` /
    `O(log S)` `MultiPlacedLib.SymIndex` over `<lib>.blocks` and `<lib>.data`. -/
syntax (name := genMultiSymIndex) "gen_multi_sym_index " ident ppSpace ident : command

@[command_elab genMultiSymIndex]
def elabGenMultiSymIndex : CommandElab := fun stx => do
  match stx with
  | `(gen_multi_sym_index $idxId:ident $lib:ident) =>
    let currNs ← getCurrNamespace
    let base := idxId.getId
    let mkHelper (sfx : String) : Name × Name × Ident :=
      let s := base.appendAfter sfx
      (s, currNs ++ s, mkIdentFrom idxId s)
    let (_, blocksTreeFull, blocksTreeId) := mkHelper "_blocksTree"
    let (_, charSymsTreeFull, charSymsTreeId) := mkHelper "_blockCharSymsTree"
    let (_, symBSTFull, symBSTId) := mkHelper "_symBST"
    let (_, blkSymRanksFull, blkSymRanksId) := mkHelper "_blkSymRanks"
    let (_, dataTreeFull, dataTreeId) := mkHelper "_dataTree"
    let (_, dataBucketFull, dataBucketId) := mkHelper "_dataSymBucketTree"
    let (_, _, blocksEqId) := mkHelper "_blocks_eq"
    let (_, _, blocksSizeId) := mkHelper "_blocks_size"
    let (_, _, charSymsEqId) := mkHelper "_charSyms_eq"
    let (_, _, charSymsSizeId) := mkHelper "_charSyms_size"
    let (_, _, symSortedId) := mkHelper "_sym_sorted"
    let (_, _, symRanksId) := mkHelper "_sym_ranks"
    let (_, _, symsNodupId) := mkHelper "_symbols_nodup"
    let (_, _, dataEqId) := mkHelper "_data_eq"
    let libConstName? ← liftTermElabM do
      let libE ← instantiateMVars (← elabTerm lib (some (Lean.mkConst ``MultiPlacedLib)))
      let blocks ← multiListElems (← mkAppM ``MultiPlacedLib.blocks #[libE])
      let datas ← multiListElems (← mkAppM ``MultiPlacedLib.data #[libE])
      let cbTy := Lean.mkConst ``CodeBlock
      let sdTy := Lean.mkConst ``SymDataInfo
      let charTy := Lean.mkConst ``Char
      let listCharTy := mkApp (Lean.mkConst ``List [0]) charTy
      let natTy := Lean.mkConst ``Nat
      let pairTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) listCharTy natTy
      let listPairTy := mkApp (Lean.mkConst ``List [0]) pairTy
      let natNatTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy natTy
      let natTripleTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy natNatTy
      let listNatTy := mkApp (Lean.mkConst ``List [0]) natTy
      let listListNatTy := mkApp (Lean.mkConst ``List [0]) listNatTy
      let mkTreeTy (t : Expr) := mkApp (Lean.mkConst ``IdxTree [0]) t
      addPrebuiltTreeDef blocksTreeFull (mkTreeTy cbTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero cbTy blocks)
      addPrebuiltTreeDef dataTreeFull (mkTreeTy sdTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero sdTy datas)
      let mut seenSyms : Std.HashMap String Nat := {}
      let mut blockSymLists : Array Expr := Array.mkEmpty blocks.size
      let mut bstItems : Array (List Char × Nat × Nat × Expr × Expr) := #[]
      let mut blkRankArrs : Array (Array Nat) := Array.mkEmpty blocks.size
      for h : i in [:blocks.size] do
        let symPairs ← multiListElems (← mkAppM ``CodeBlock.symbols #[blocks[i]])
        let mut blkPairs : Array Expr := Array.mkEmpty symPairs.size
        for hj : j in [:symPairs.size] do
          let sp := symPairs[j]
          let s ← multiStrVal (← whnf (← mkAppM ``Prod.fst #[sp]))
          let off ← multiNatVal (← whnf (← mkAppM ``Prod.snd #[sp]))
          if let some prev := seenSyms[s]? then
            throwError "gen_multi_sym_index: duplicate symbol {repr s} across `{lib}.blocks` \
              (blocks {prev} and {i})"
          seenSyms := seenSyms.insert s i
          let cs := s.toList
          let csExpr := ProofLib.ProgramReflection.mkCharListExpr s
          blkPairs := blkPairs.push
            (mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) listCharTy natTy csExpr (mkRawNatLit off))
          let jo := mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) natTy natTy (mkRawNatLit j) (mkRawNatLit off)
          let triVal := mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) natTy natNatTy (mkRawNatLit i) jo
          bstItems := bstItems.push (cs, i, j, csExpr, triVal)
        blockSymLists := blockSymLists.push (← mkListLit pairTy blkPairs.toList)
        blkRankArrs := blkRankArrs.push (Array.replicate symPairs.size 0)
      addPrebuiltTreeDef charSymsTreeFull (mkTreeTy listPairTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero listPairTy blockSymLists)
      let sorted := bstItems.qsort fun a b => charListLt a.1 b.1
      for r in [:sorted.size] do
        let (_, bi, sj, _, _) := sorted[r]!
        blkRankArrs := blkRankArrs.set! bi (blkRankArrs[bi]!.set! sj r)
      let bstTy := mkApp (Lean.mkConst ``SymBST) natTripleTy
      addPrebuiltTreeDef symBSTFull bstTy
        (ProofLib.ProgramReflection.mkSymBSTExpr natTripleTy
          (sorted.map fun (_, _, _, ke, ve) => (ke, ve)))
      let innerRankLists ← blkRankArrs.mapM fun arr => mkListLit natTy (arr.toList.map mkRawNatLit)
      addPrebuiltTreeDef blkSymRanksFull listListNatTy (← mkListLit listNatTy innerRankLists.toList)
      let mut seenData : Std.HashMap String Nat := {}
      let mut dataBuckets : Array (Array Expr) := Array.replicate 1024 #[]
      for h : k in [:datas.size] do
        let s ← multiStrVal (← whnf (← mkAppM ``SymDataInfo.sym #[datas[k]]))
        if let some prev := seenData[s]? then
          throwError "gen_multi_sym_index: duplicate data symbol {repr s} in `{lib}.data` \
            (indices {prev} and {k})"
        seenData := seenData.insert s k
        let cs := s.toList
        let csExpr := ProofLib.ProgramReflection.mkCharListExpr s
        let bIdx := hashChars1024 cs
        let pr := mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) listCharTy natTy csExpr (mkRawNatLit k)
        dataBuckets := dataBuckets.set! bIdx (dataBuckets[bIdx]!.push pr)
      let dataBucketExprs ← dataBuckets.mapM fun b => mkListLit pairTy b.toList
      addPrebuiltTreeDef dataBucketFull (mkTreeTy listPairTy)
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero listPairTy dataBucketExprs)
      return libE.constName?
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      theorem $blocksEqId :
          ($blocksTreeId).toList = ($lib : Arm64.Obj.MultiPlacedLib).blocks := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      theorem $blocksSizeId :
          ($blocksTreeId).size? = some ($lib : Arm64.Obj.MultiPlacedLib).blocks.length := by
        rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      theorem $charSymsEqId :
          ($charSymsTreeId).toList.map Arm64.Obj.charSymsToStrings =
            (($lib : Arm64.Obj.MultiPlacedLib).blocks).map Arm64.Obj.CodeBlock.symbols := by
        rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      theorem $charSymsSizeId :
          ($charSymsTreeId).size? = some ($lib : Arm64.Obj.MultiPlacedLib).blocks.length := by
        rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      theorem $symSortedId : isStrictSorted ($symBSTId).toList = true := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      theorem $symRanksId :
          mapBlockSymRanks $symBSTId 0 $blkSymRanksId =
            some ((($lib : Arm64.Obj.MultiPlacedLib).blocks).map Arm64.Obj.CodeBlock.symbols) := by
        rfl_kernel))
    elabCommand (← `(command|
      theorem $symsNodupId :
          (((($lib : Arm64.Obj.MultiPlacedLib).blocks).flatMap (·.symbols)).map (·.1)).Nodup :=
        Arm64.Obj.nodup_blockSymbols_of_symBST_ranks $symSortedId $symRanksId))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      theorem $dataEqId : ($dataTreeId).toList = ($lib : Arm64.Obj.MultiPlacedLib).data := by
        rfl_kernel))
    elabCommand (← `(command|
      noncomputable def $idxId : ($lib : Arm64.Obj.MultiPlacedLib).SymIndex := {
        blocksTree := $blocksTreeId
        blockCharSymsTree := $charSymsTreeId
        symBST := $symBSTId
        blkSymRanks := $blkSymRanksId
        dataTree := $dataTreeId
        dataSymBucketTree := $dataBucketId
        blocks_eq := $blocksEqId
        blocks_size := $blocksSizeId
        charSyms_eq := $charSymsEqId
        charSyms_size := $charSymsSizeId
        symbols_nodup := $symsNodupId
        sym_sorted := $symSortedId
        sym_ranks := $symRanksId
        data_eq := $dataEqId
      }))
    if let some libNm := libConstName? then
      modifyEnv (multiSymIndexExt.addEntry · (libNm, currNs ++ base))
  | _ => throwUnsupportedSyntax

end GenMultiSymIndex

end Arm64.Obj

end
