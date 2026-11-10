/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Fetch
public import ProofLib.CoreLemmas

/-!
# Shared-Code Transfer for Placed Libraries

Transfers function proofs over template instruction words (`RelocCodeAtWith` and `RelocCodeAt`) to
arbitrary placed libraries (`PlacedLib.program`), supporting text and data relocations,
branch-to-branch linker retargeting (`CodeBlock.checkSegmentB2b`), and kernel-checked instantiation
macros (`placed_code_at%`, `placed_reloc_code_at_with%`, `placed_reloc_code_at%`).
-/

set_option autoImplicit false

@[expose] public section

namespace Arm64
namespace Obj

open ProofLib

/-! ## Shared-code predicates -/

/-- `prog` holds the template `words` at `sym` with the local relocations `R` patched against the
    resolver `res`, and each relocation target is in range of its site. A `BL`/`B` to `r.sym`
    decodes to a branch to `res r.sym`, an `ADRP`/`ADD`/`LDR :lo12:` to `res r.sym + addend`. -/
def RelocCodeAtWith (prog : Program) (sym : String) (words : List (BitVec 32))
    (R : List RelocEntry) (res : String → BitVec 64) : Prop :=
  prog.hasWords (prog.fnAddr sym) (patchRelocs R words (prog.fnAddr sym) res) ∧
    ∀ r ∈ R, CodeRelocInRange r.kind (prog.fnAddr sym + BitVec.ofNat 64 r.off)
      (addSignedAddr (res r.sym) r.addend)

/-- `RelocCodeAtWith` against `prog`'s own symbol addresses (`prog.fnAddr`): every relocation
    targets a function of `prog`. -/
def RelocCodeAt (prog : Program) (sym : String) (words : List (BitVec 32))
    (R : List RelocEntry) : Prop :=
  prog.hasWords (prog.fnAddr sym) (patchRelocs R words (prog.fnAddr sym) prog.fnAddr) ∧
    ∀ r ∈ R, CodeRelocInRange r.kind (prog.fnAddr sym + BitVec.ofNat 64 r.off)
      (addSignedAddr (prog.fnAddr r.sym) r.addend)

theorem relocCodeAt_iff_with {prog : Program} {sym : String} {words : List (BitVec 32)}
    {R : List RelocEntry} : RelocCodeAt prog sym words R ↔ RelocCodeAtWith prog sym words R prog.fnAddr :=
  Iff.rfl

/-- `patchRelocs` only reads the resolver at the relocations' symbols. -/
theorem patchRelocs_congr (R : List RelocEntry) (ws : List (BitVec 32)) (a : BitVec 64)
    {f g : String → BitVec 64} (h : ∀ r ∈ R, f r.sym = g r.sym) :
    patchRelocs R ws a f = patchRelocs R ws a g := by
  unfold patchRelocs
  apply List.map_congr_left
  rintro ⟨w, j⟩ _
  cases hf : R.find? (·.off == 4 * j) with
  | none => simp only [hf]
  | some r => simp only [hf, h r (List.mem_of_find?_eq_some hf)]

/-- `RelocCodeAtWith` only reads the resolver at the relocations' symbols. -/
theorem relocCodeAtWith_congr {prog : Program} {sym : String} {words : List (BitVec 32)}
    {R : List RelocEntry} {f g : String → BitVec 64} (h : ∀ r ∈ R, f r.sym = g r.sym)
    (hf : RelocCodeAtWith prog sym words R f) : RelocCodeAtWith prog sym words R g := by
  obtain ⟨hw, hr⟩ := hf
  refine ⟨?_, fun r hmem => ?_⟩
  · rw [← patchRelocs_congr R words _ h]; exact hw
  · rw [← h r hmem]; exact hr r hmem

/-- A resolver that agrees with `prog.fnAddr` on every relocation symbol gives `RelocCodeAt`. -/
theorem RelocCodeAt.of_with {prog : Program} {sym : String} {words : List (BitVec 32)}
    {R : List RelocEntry} {res : String → BitVec 64} (hres : ∀ r ∈ R, res r.sym = prog.fnAddr r.sym)
    (h : RelocCodeAtWith prog sym words R res) : RelocCodeAt prog sym words R :=
  relocCodeAtWith_congr hres h

/-! ## Placed resolver -/

/-- A text symbol resolves to its block address. -/
theorem CodeBlock.resolve_of_lookup {blk : CodeBlock} {pl : Placement} {s : String} {off : Nat}
    (h : lookup s blk.symbols = some off) : blk.resolve pl s = pl.base + BitVec.ofNat 64 off := by
  simp only [CodeBlock.resolve, h]

/-- A symbol outside the block (data object or extern) resolves through `pl.ρ`. -/
theorem CodeBlock.resolve_of_lookup_none {blk : CodeBlock} {pl : Placement} {s : String}
    (h : lookup s blk.symbols = none) : blk.resolve pl s = pl.ρ s := by
  simp only [CodeBlock.resolve, h]

/-- On a text symbol the placed resolver is the placed program's `fnAddr` (any hooks). -/
theorem PlacedLib.resolve_eq_fnAddr {lib : PlacedLib} {pl : Placement}
    {X O : String → Option (State → State)} {svc : State → State} {s : String}
    (h : (lookup s lib.text.symbols).isSome = true) :
    lib.text.resolve pl s = (lib.program pl X O svc).fnAddr s := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨h1, h2⟩ := PlacedLib.fnAddr_program (X := X) (O := O) (svc := svc) ho
  rw [h1, h2, CodeBlock.resolve_of_lookup ho]

/-- A data object of a placeable library resolves to its placed address `pl.ρ d.sym`. -/
theorem PlacedLib.resolve_data {lib : PlacedLib} {pl : Placement} (hP : lib.Placeable pl)
    {d : SymDataInfo} (hd : d ∈ lib.data) : lib.text.resolve pl d.sym = pl.ρ d.sym :=
  CodeBlock.resolve_of_lookup_none (hP.data_ok d hd).1

/-! ## Placed instances -/

private theorem patchRelocs_nil_eq (ws : List (BitVec 32)) (a : BitVec 64)
    (r : String → BitVec 64) : patchRelocs [] ws a r = ws := by
  simp [patchRelocs]

private theorem fnAddr_program_of_lookup {lib : PlacedLib} {pl : Placement}
    {X : String → Option (State → State)} {svc : State → State} {sym : String} {off : Nat}
    (hoff : lookup sym lib.text.symbols = some off) :
    (lib.program pl X (fun _ => none) svc).fnAddr sym = pl.base + BitVec.ofNat 64 off := by
  obtain ⟨h1, h2⟩ := PlacedLib.fnAddr_program (X := X) (O := fun _ => none) (svc := svc) hoff
  rw [h1, h2]

/-- A relocation-free function of a placed library `lib` holds its unrelocated words `words` in
    the placed program (no overrides) for every placeable `pl`. -/
theorem PlacedLib.codeAt_of_checkSegment {lib : PlacedLib} {pl : Placement}
    {X : String → Option (State → State)} {svc : State → State}
    {sym : String} {words : List (BitVec 32)} (hP : lib.Placeable pl)
    (hsym : (lookup sym lib.text.symbols).isSome = true)
    (hchk : lib.text.checkSegment ((lookup sym lib.text.symbols).getD 0) words [] = true)
    (hlen : (lookup sym lib.text.symbols).getD 0 + 4 * words.length ≤
      lib.text.code.length) (_hne : 0 < words.length := by decide +kernel) :
    (lib.program pl X (fun _ => none) svc).codeAt sym words := by
  obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsym
  rw [hoff, Option.getD_some] at hchk hlen
  have h := (CodeBlock.hasWords_of_checkSegment
    (prog := lib.program pl X (fun _ => none) svc)
    (fo := off) (R := []) hP.text (PlacedLib.program_base _ _)
    (PlacedLib.program_code _ _) hchk
    (PlacedLib.hookFree_program_noOverrides hP.text hlen)).1
  rw [patchRelocs_nil_eq] at h
  unfold Program.hasWords at h
  have hnw := hP.text.no_wrap
  rw [PlacedLib.program_base, Program.add_ofNat_sub_self, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)] at h
  have hfo : (lib.program pl X (fun _ => none) svc).fnOff sym = off := by
    have h' : (lib.text.symbols.find? (·.1 == sym)).map (·.2) = some off := hoff
    simp only [Program.fnOff, Program.findSymbol?, PlacedLib.program]
    cases hf : lib.text.symbols.find? (·.1 == sym) with
    | none => rw [hf] at h'; simp at h'
    | some p => rw [hf] at h'; simpa [Option.orElse] using h'
  unfold Program.codeAt
  rw [hfo]
  exact h

/-- A function of a placed library whose local relocations are plain sites (`checkSegment`)
    satisfies `RelocCodeAtWith` against `lib.text.resolve pl` in the placed program (no overrides)
    for every placeable `pl`. Text-symbol targets resolve via `resolve_eq_fnAddr` and data-object
    targets via `resolve_data`. -/
theorem PlacedLib.relocCodeAtWith_of_checkSegment {lib : PlacedLib} {pl : Placement}
    {X : String → Option (State → State)} {svc : State → State}
    {sym : String} {words : List (BitVec 32)} {R : List RelocEntry} (hP : lib.Placeable pl)
    (hsym : (lookup sym lib.text.symbols).isSome = true)
    (hchk : lib.text.checkSegment ((lookup sym lib.text.symbols).getD 0) words R = true)
    (hlen : (lookup sym lib.text.symbols).getD 0 + 4 * words.length ≤
      lib.text.code.length) :
    RelocCodeAtWith (lib.program pl X (fun _ => none) svc) sym words R (lib.text.resolve pl) := by
  obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsym
  rw [hoff, Option.getD_some] at hchk hlen
  have h := CodeBlock.hasWords_of_checkSegment
    (prog := lib.program pl X (fun _ => none) svc)
    (fo := off) hP.text (PlacedLib.program_base _ _)
    (PlacedLib.program_code _ _) hchk
    (PlacedLib.hookFree_program_noOverrides hP.text hlen)
  rw [RelocCodeAtWith, fnAddr_program_of_lookup hoff]
  exact h

/-- `relocCodeAtWith_of_checkSegment` specialized to relocations targeting text symbols. -/
theorem PlacedLib.relocCodeAt_of_checkSegment {lib : PlacedLib} {pl : Placement}
    {X : String → Option (State → State)} {svc : State → State}
    {sym : String} {words : List (BitVec 32)} {R : List RelocEntry} (hP : lib.Placeable pl)
    (hsym : (lookup sym lib.text.symbols).isSome = true)
    (hchk : lib.text.checkSegment ((lookup sym lib.text.symbols).getD 0) words R = true)
    (hlen : (lookup sym lib.text.symbols).getD 0 + 4 * words.length ≤
      lib.text.code.length)
    (hR : R.all (fun r => (lookup r.sym lib.text.symbols).isSome) = true) :
    RelocCodeAt (lib.program pl X (fun _ => none) svc) sym words R :=
  RelocCodeAt.of_with (fun r hr => PlacedLib.resolve_eq_fnAddr (List.all_eq_true.mp hR r hr))
    (PlacedLib.relocCodeAtWith_of_checkSegment hP hsym hchk hlen)

/-! ## Branch-to-branch sites

`CodeBlock.checkSegment` rejects a `BL f` whose target `f` is itself a tail `B g` (a
branch-to-branch candidate), which a linker may retarget to `BL g` (`Placement.b2b`). The variant
below establishes words patched against the per-placement relocations `R.map (b2bResolve blk pl fo)`,
where each candidate site targets `f` or `g` according to `pl.b2b`. -/

namespace CodeBlock

/-- The relocation `r` (local offset `r.off` in the segment at `fo`) as patched under `pl`: if
    `pl.b2b` retargets the branch at `fo + r.off` and `r` is a branch-to-branch candidate with
    stub relocation `r2`, it takes `r2`'s symbol and addend; otherwise it is `r`. -/
def b2bResolve (blk : CodeBlock) (pl : Placement) (fo : Nat) (r : RelocEntry) : RelocEntry :=
  match (if pl.b2b (fo + r.off) then blk.b2bNext? r else none) with
  | some r2 => { r with sym := r2.sym, addend := r2.addend }
  | none => r

/-- `plainSite` without the "not a branch-to-branch candidate" conjunct, and not a weak
    reference (as in `CodeBlock.checkSegment`). -/
def b2bSite (blk : CodeBlock) (r : RelocEntry) : Bool :=
  !blk.relaxableAt r.off && (r.off < 4 || !blk.relaxableAt (r.off - 4)) && !r.kind.isGotOrTlsIe &&
    !blk.weakRefs.contains r.sym

/-- `CodeBlock.checkSegment` with `b2bSite` in place of `plainSite`. -/
def checkSegmentB2b (blk : CodeBlock) (fo : Nat) (ws : List (BitVec 32)) (R : List RelocEntry) :
    Bool :=
  fo % 4 == 0 && decide (0 < ws.length) &&
  R == blk.segRelocs fo (4 * ws.length) &&
  (blk.relocs.filter fun r => decide (fo ≤ r.off) && decide (r.off < fo + 4 * ws.length)).all
    (b2bSite blk) &&
  CodeBlock.segWordsOk R 0 (blk.code.drop fo) ws

@[simp] theorem b2bResolve_off (blk : CodeBlock) (pl : Placement) (fo : Nat)
    (r : RelocEntry) : (b2bResolve blk pl fo r).off = r.off := by
  unfold b2bResolve; split <;> rfl

@[simp] theorem b2bResolve_kind (blk : CodeBlock) (pl : Placement) (fo : Nat)
    (r : RelocEntry) : (b2bResolve blk pl fo r).kind = r.kind := by
  unfold b2bResolve; split <;> rfl

private theorem b2bNext?_off (blk : CodeBlock) (r : RelocEntry) (o : Nat) :
    blk.b2bNext? { r with off := o } = blk.b2bNext? r := rfl

private theorem relocTarget_eq_b2bResolve (blk : CodeBlock) (pl : Placement) (fo : Nat)
    (r : RelocEntry) {off : Nat} (ho : r.off = off) (h : fo ≤ r.off) :
    blk.relocTarget pl off r =
      addSignedAddr (blk.resolve pl (b2bResolve blk pl fo { r with off := r.off - fo }).sym)
        (b2bResolve blk pl fo { r with off := r.off - fo }).addend := by
  subst ho
  have hoff : fo + (r.off - fo) = r.off := by omega
  unfold b2bResolve CodeBlock.relocTarget CodeBlock.target
  simp only [hoff, b2bNext?_off]
  cases pl.b2b r.off <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    cases blk.b2bNext? r <;> rfl

private theorem find?_map_b2bResolve (blk : CodeBlock) (pl : Placement) (fo k : Nat)
    (R : List RelocEntry) :
    (R.map (b2bResolve blk pl fo)).find? (·.off == k) =
      (R.find? (·.off == k)).map (b2bResolve blk pl fo) := by
  induction R with
  | nil => rfl
  | cons a R ih =>
    simp only [List.map_cons, List.find?_cons, b2bResolve_off]
    cases a.off == k <;> simp [ih]

/-- Segment word and range bridge for `checkSegmentB2b`. -/
theorem hasWords_of_checkSegmentB2b {blk : CodeBlock} {pl : Placement} {prog : Program}
    {fo : Nat} {ws : List (BitVec 32)} {R : List RelocEntry}
    (hP : blk.Placeable pl) (hbase : prog.base = pl.base) (hcode : prog.code = blk.patched pl)
    (hchk : checkSegmentB2b blk fo ws R = true) (hhook : prog.hookFree fo (4 * ws.length)) :
    prog.hasWords (pl.base + BitVec.ofNat 64 fo)
        (patchRelocs (R.map (b2bResolve blk pl fo)) ws (pl.base + BitVec.ofNat 64 fo)
          (blk.resolve pl)) ∧
      ∀ r ∈ R.map (b2bResolve blk pl fo),
        CodeRelocInRange r.kind (pl.base + BitVec.ofNat 64 fo + BitVec.ofNat 64 r.off)
          (addSignedAddr (blk.resolve pl r.sym) r.addend) := by
  simp only [checkSegmentB2b, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨hfo, hpos⟩, hR⟩, hsite⟩, hwords⟩ := hchk
  subst hR
  obtain ⟨hlen, hmatch⟩ := CodeBlock.segWordsOk_spec hwords
  rw [List.length_drop] at hlen
  have hnw := hP.no_wrap
  have hfo_lt : fo < 2 ^ 64 := by omega
  have hoff : (pl.base + BitVec.ofNat 64 fo - prog.base).toNat = fo := by
    rw [hbase, Program.add_ofNat_sub_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfo_lt]
  have hplace : ∀ k, pl.base + BitVec.ofNat 64 (fo + k) =
      pl.base + BitVec.ofNat 64 fo + BitVec.ofNat 64 k := fun k => by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  refine ⟨?_, ?_⟩
  · unfold Program.hasWords Program.hasWordsOff
    rw [hoff]
    have hp_len : (patchRelocs ((blk.segRelocs fo (4 * ws.length)).map (b2bResolve blk pl fo)) ws
        (pl.base + BitVec.ofNat 64 fo) (blk.resolve pl)).length = ws.length := by
      simp [patchRelocs]
    refine ⟨by rw [hp_len]; omega, fun i hi => ?_, by rw [hp_len]; exact hhook⟩
    have hi' : i < ws.length := by omega
    rw [CodeBlock.readWordOff_patched hcode (by omega) (by omega)]
    have hm := hmatch i hi'
    rw [Nat.zero_add, ← getD_eq_drop_getD_word] at hm
    simp only [patchRelocs, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    unfold CodeBlock.wordMatches at hm
    rw [find?_map_b2bResolve, CodeBlock.find?_segRelocs blk (by omega)]
    rw [CodeBlock.find?_segRelocs blk (by omega)] at hm
    cases hfind : blk.relocAt? (fo + 4 * i) with
    | none =>
      simp only [hfind, Option.map_none, beq_iff_eq] at hm ⊢
      rw [CodeBlock.patchedWord_of_relocAt_none hfind]
      exact congrArg some hm
    | some r =>
      simp only [hfind, Option.map_some, beq_iff_eq, b2bResolve_kind] at hm ⊢
      have hroff := CodeBlock.relocAt?_off hfind
      have hs := hsite r (List.mem_filter.2 ⟨CodeBlock.relocAt?_mem hfind, by simp; omega⟩)
      simp only [b2bSite, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
        decide_eq_true_eq] at hs
      obtain ⟨⟨⟨h0, h4⟩, hng⟩, hweak⟩ := hs
      have hfo_le : fo ≤ r.off := by omega
      rw [CodeBlock.patchedWord_of_notRelaxed hfind
        (CodeBlock.relaxedAt_of_relaxableAt_false (by rw [← hroff]; exact h0))
        ((show fo + 4 * i < 4 ∨ blk.relaxableAt (fo + 4 * i - 4) = false by
          rw [← hroff]; exact h4).imp id CodeBlock.relaxedAt_of_relaxableAt_false) hng
          (CodeBlock.undefWeakBranch_of_not_weak hweak),
        relocTarget_eq_b2bResolve blk pl fo r hroff hfo_le, CodeBlock.wordAt,
        patchRelocWord_eq_of_mask hm, hplace]
  · intro r hr
    obtain ⟨r1, hr1, rfl⟩ := List.mem_map.1 hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr1
    have hr0' := List.mem_filter.1 hr0
    have hin : fo ≤ r0.off := by have := hr0'.2; simp at this; omega
    obtain ⟨-, -, hrange⟩ := hP.relocs_ok r0 hr0'.1
    have hs := hsite r0 hr0
    simp only [b2bSite, Bool.and_eq_true, Bool.not_eq_true'] at hs
    rw [CodeBlock.relocInRange_of_not_gotOrTlsIe hs.1.2,
      relocTarget_eq_b2bResolve blk pl fo r0 rfl hin] at hrange
    rw [b2bResolve_kind, b2bResolve_off, ← hplace, show fo + (r0.off - fo) = r0.off by omega]
    exact hrange

/-- The two possible patched forms of one candidate `call26` site `blReloc o f` whose stub `f`
    tail-branches to `g` (`b2bNext? = some r2`, `r2.sym = g`, `r2.addend = 0`). -/
theorem b2bResolve_call26_cases (blk : CodeBlock) (pl : Placement) (fo o : Nat) (f g : String)
    (h : (blk.b2bNext? { off := o, kind := .call26, sym := f, addend := 0 }).map
      (fun r2 => (r2.sym, r2.addend)) = some (g, 0)) :
    b2bResolve blk pl fo { off := o, kind := .call26, sym := f, addend := 0 } =
        { off := o, kind := .call26, sym := f, addend := 0 } ∨
      b2bResolve blk pl fo { off := o, kind := .call26, sym := f, addend := 0 } =
        { off := o, kind := .call26, sym := g, addend := 0 } := by
  unfold b2bResolve
  cases pl.b2b (fo + o) <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · simp
  · cases hn : blk.b2bNext? { off := o, kind := .call26, sym := f, addend := 0 } with
    | none => rw [hn] at h; simp at h
    | some r2 =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, ha⟩ := h
      right
      simp [hs, ha]

/-- A non-candidate site is unchanged. -/
theorem b2bResolve_of_b2bNext_none (blk : CodeBlock) (pl : Placement) (fo : Nat)
    (r : RelocEntry) (h : blk.b2bNext? r = none) : b2bResolve blk pl fo r = r := by
  unfold b2bResolve
  cases pl.b2b (fo + r.off) <;> simp [h]

end CodeBlock

/-- `RelocCodeAtWith` against the placed resolver holds for the per-placement relocations
    `R.map (b2bResolve lib.text pl fo)`. -/
theorem PlacedLib.relocCodeAtWith_of_checkSegmentB2b {lib : PlacedLib} {pl : Placement}
    {X : String → Option (State → State)} {svc : State → State}
    {sym : String} {words : List (BitVec 32)} {R : List RelocEntry} (hP : lib.Placeable pl)
    (hsym : (lookup sym lib.text.symbols).isSome = true)
    (hchk : lib.text.checkSegmentB2b ((lookup sym lib.text.symbols).getD 0) words R = true)
    (hlen : (lookup sym lib.text.symbols).getD 0 + 4 * words.length ≤ lib.text.code.length) :
    RelocCodeAtWith (lib.program pl X (fun _ => none) svc) sym words
      (R.map (lib.text.b2bResolve pl ((lookup sym lib.text.symbols).getD 0)))
      (lib.text.resolve pl) := by
  obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsym
  rw [hoff, Option.getD_some] at hchk hlen
  rw [hoff, Option.getD_some]
  have h := CodeBlock.hasWords_of_checkSegmentB2b
    (prog := lib.program pl X (fun _ => none) svc)
    (fo := off) hP.text (PlacedLib.program_base _ _)
    (PlacedLib.program_code _ _) hchk
    (PlacedLib.hookFree_program_noOverrides hP.text hlen)
  rw [RelocCodeAtWith, fnAddr_program_of_lookup hoff]
  exact h

/-- `relocCodeAtWith_of_checkSegmentB2b` when every relocation symbol and candidate stub target is
    a text symbol. -/
theorem PlacedLib.relocCodeAt_of_checkSegmentB2b {lib : PlacedLib} {pl : Placement}
    {X : String → Option (State → State)} {svc : State → State}
    {sym : String} {words : List (BitVec 32)} {R : List RelocEntry} (hP : lib.Placeable pl)
    (hsym : (lookup sym lib.text.symbols).isSome = true)
    (hchk : lib.text.checkSegmentB2b ((lookup sym lib.text.symbols).getD 0) words R = true)
    (hlen : (lookup sym lib.text.symbols).getD 0 + 4 * words.length ≤ lib.text.code.length)
    (hR : R.all (fun r => (lookup r.sym lib.text.symbols).isSome &&
      match lib.text.b2bNext? r with
      | some r2 => (lookup r2.sym lib.text.symbols).isSome
      | none => true) = true) :
    RelocCodeAt (lib.program pl X (fun _ => none) svc) sym words
      (R.map (lib.text.b2bResolve pl ((lookup sym lib.text.symbols).getD 0))) := by
  refine RelocCodeAt.of_with (fun r hr => ?_) (PlacedLib.relocCodeAtWith_of_checkSegmentB2b hP hsym hchk hlen)
  obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
  have hall := List.all_eq_true.mp hR r0 hr0
  simp only [Bool.and_eq_true] at hall
  obtain ⟨hs0, hs2⟩ := hall
  refine PlacedLib.resolve_eq_fnAddr ?_
  unfold CodeBlock.b2bResolve
  cases hb : pl.b2b ((lookup sym lib.text.symbols).getD 0 + r0.off) <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  · exact hs0
  · cases hn : lib.text.b2bNext? r0 with
    | none => exact hs0
    | some r2 => rw [hn] at hs2; exact hs2

/-! ## Kernel-checked instantiation macros -/

/-- `PlacedLib.codeAt_of_checkSegment hP` with every template side condition closed by
    `decide +kernel`. -/
macro "placed_code_at% " hP:term:max : term =>
  `(Arm64.Obj.PlacedLib.codeAt_of_checkSegment $hP (by decide +kernel) (by decide +kernel)
    (by decide +kernel))

/-- `PlacedLib.relocCodeAtWith_of_checkSegment hP` with every template side condition closed by
    `decide +kernel` (relocations may target text or data symbols). -/
macro "placed_reloc_code_at_with% " hP:term:max : term =>
  `(Arm64.Obj.PlacedLib.relocCodeAtWith_of_checkSegment $hP (by decide +kernel)
    (by decide +kernel) (by decide +kernel))

/-- `PlacedLib.relocCodeAt_of_checkSegment hP` with every template side condition closed by
    `decide +kernel` (every relocation targets a text symbol). -/
macro "placed_reloc_code_at% " hP:term:max : term =>
  `(Arm64.Obj.PlacedLib.relocCodeAt_of_checkSegment $hP (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))

end Obj
end Arm64
