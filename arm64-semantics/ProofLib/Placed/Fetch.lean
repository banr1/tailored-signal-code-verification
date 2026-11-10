/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.RelocDecode
public import Arm64.Trusted.Process.Placed

/-!
# Placed Libraries: Fetching Patched Words

Provides placement-generic instruction-fetch and relocation lemmas for `PlacedLib` and
`CodeBlock` (`readWordOff_patched`, `patchedWord_of_plain`, `patchedWord_of_relaxed`,
`patchedWord_of_relaxedPrev`, `relaxedAtFast_eq`, `fnAddr_program`, and `hookFree_program`).

For straight-line segments without relaxable `ADRP`+`ADD` pairs or branch-to-branch candidates,
`CodeBlock.checkSegment` and `CodeBlock.hasWords_of_checkSegment` establish
`prog.hasWords a (Obj.patchRelocs R ws a (blk.resolve pl))` together with per-site
`CodeRelocInRange` facts at `a = pl.base + fo`.
-/

@[expose] public section

namespace Arm64
namespace Obj

set_option linter.literalFetch false

/-! ## Chunked Byte Lists -/

@[simp] theorem length_bytesOfWordLE (w : BitVec 32) : (bytesOfWordLE w).length = 4 := by
  simp [bytesOfWordLE, bytesLE]

theorem drop_take_flatMap_bytesOfWordLE {α : Type} (g : α → BitVec 32) :
    ∀ (L : List α) (j : Nat) (hj : j < L.length),
      ((L.flatMap fun a => bytesOfWordLE (g a)).drop (4 * j)).take 4 =
        bytesOfWordLE (g (L[j]'hj))
  | [], _, hj => by simp at hj
  | a :: L, 0, _ => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_of_length_le (by simp)
  | a :: L, j + 1, hj => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 4 * (j + 1) = (bytesOfWordLE (g a)).length + 4 * j by simp; omega,
      ← List.drop_drop, List.drop_left]
    exact drop_take_flatMap_bytesOfWordLE g L j (by simp at hj; omega)

theorem length_flatMap_bytesOfWordLE {α : Type} (g : α → BitVec 32) (L : List α) :
    (L.flatMap fun a => bytesOfWordLE (g a)).length = 4 * L.length := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; omega

namespace CodeBlock

/-! ## Patched Code Image -/

theorem length_patched (blk : CodeBlock) (pl : Placement) :
    (blk.patched pl).length = 4 * (blk.code.length / 4) := by
  unfold patched
  rw [length_flatMap_bytesOfWordLE (fun j => blk.patchedWord pl (4 * j)), List.length_range]

theorem length_patched_of_aligned {blk : CodeBlock} (pl : Placement)
    (h : blk.code.length % 4 = 0) : (blk.patched pl).length = blk.code.length := by
  rw [length_patched]; omega

theorem take4_drop_patched {blk : CodeBlock} {pl : Placement} {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    ((blk.patched pl).drop off).take 4 = bytesOfWordLE (blk.patchedWord pl off) := by
  have hj : off / 4 < (List.range (blk.code.length / 4)).length := by
    simp only [List.length_range]; omega
  have h := drop_take_flatMap_bytesOfWordLE (fun j => blk.patchedWord pl (4 * j))
    (List.range (blk.code.length / 4)) (off / 4) hj
  rw [List.getElem_range, show 4 * (off / 4) = off by omega] at h
  exact h

/-- The word at an aligned in-bounds offset of a program whose code is the patched block. -/
theorem readWordOff_patched {blk : CodeBlock} {pl : Placement} {prog : Program} {off : Nat}
    (hcode : prog.code = blk.patched pl) (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    prog.readWordOff off = some (blk.patchedWord pl off) :=
  readWordOff_of_take4_bytesOfWordLE hal (by rw [hcode]; exact take4_drop_patched hal hlen)

/-! ## `patchedWord` Cases -/

theorem patchedWord_of_relocAt_none {blk : CodeBlock} {pl : Placement} {off : Nat}
    (h : blk.relocAt? off = none) : blk.patchedWord pl off = blk.wordAt off := by
  simp [patchedWord, h]

/-- A site is *plain* when neither it nor the word before it starts a relaxable pair, it is not a
    GOT or initial-exec TLS site, and it is not a branch-to-branch candidate; placement-independent
    and decidable. -/
def plainSite (blk : CodeBlock) (r : RelocEntry) : Bool :=
  !blk.relaxableAt r.off && (r.off < 4 || !blk.relaxableAt (r.off - 4)) &&
    !r.kind.isGotOrTlsIe && (blk.b2bNext? r).isNone

theorem relaxedAt_of_relaxableAt_false {blk : CodeBlock} {pl : Placement} {off : Nat}
    (h : blk.relaxableAt off = false) : blk.relaxedAt pl off = false := by
  simp [relaxedAt, h]

theorem relaxableAt_of_relocs_nil {blk : CodeBlock} (h : blk.relocs = []) (off : Nat) :
    blk.relaxableAt off = false := by
  simp [relaxableAt, relocAt?, h]

theorem relaxedAt_of_relocs_nil {blk : CodeBlock} {pl : Placement} (h : blk.relocs = [])
    (off : Nat) : blk.relaxedAt pl off = false :=
  relaxedAt_of_relaxableAt_false (relaxableAt_of_relocs_nil h off)

theorem relaxedAt_of_relax_false {blk : CodeBlock} {pl : Placement} {off : Nat}
    (h : pl.relax off = false) : blk.relaxedAt pl off = false := by
  simp [relaxedAt, h]

/-- Short-circuiting boolean equivalent of `CodeBlock.relaxedAt`: checks `pl.relax off` and
    `!blk.relocs.isEmpty` in `O(1)` before scanning `blk.relocs` and `blk.code` in
    `blk.relaxableAt off`. -/
def relaxedAtFast (blk : CodeBlock) (pl : Placement) (off : Nat) : Bool :=
  pl.relax off && !blk.relocs.isEmpty && blk.relaxedAt pl off

theorem relaxedAtFast_eq (blk : CodeBlock) (pl : Placement) (off : Nat) :
    blk.relaxedAtFast pl off = blk.relaxedAt pl off := by
  unfold relaxedAtFast relaxedAt
  cases hrel : blk.relocs with
  | nil => simp [relaxableAt, relocAt?, hrel]
  | cons _ _ => cases pl.relax off <;> simp

theorem relocTarget_of_b2bNext_none {blk : CodeBlock} {pl : Placement} {off : Nat}
    {r : RelocEntry} (h : blk.b2bNext? r = none) : blk.relocTarget pl off r = blk.target pl r := by
  unfold relocTarget; cases pl.b2b off <;> simp [h]

theorem relocInRange_of_not_gotOrTlsIe {blk : CodeBlock} {pl : Placement} {kind : RelocKind}
    {off : Nat} {place target : BitVec 64} (hng : kind.isGotOrTlsIe = false) :
    blk.relocInRange pl kind off place target = CodeRelocInRange kind place target := by
  cases kind <;> first | rfl | nomatch hng

theorem relocInRange_of_relax_false {blk : CodeBlock} {pl : Placement} {kind : RelocKind}
    {off : Nat} {place target : BitVec 64}
    (h1 : pl.relax off = false) (h2 : pl.relax (off - 4) = false) :
    blk.relocInRange pl kind off place target = CodeRelocInRange kind place target := by
  cases kind <;> simp [relocInRange, CodeRelocInRange, h1, h2]

/-- Only a direct branch can be an undefined-weak branch. -/
@[simp] theorem undefWeakBranch_of_not_branch {blk : CodeBlock} {pl : Placement} {r : RelocEntry}
    (h : (r.kind == .call26 || r.kind == .jump26) = false) : blk.undefWeakBranch pl r = false := by
  simp only [undefWeakBranch, h, Bool.and_false, Bool.false_and]

/-- Only a weak reference can be an undefined-weak branch. -/
theorem undefWeakBranch_of_not_weak {blk : CodeBlock} {pl : Placement} {r : RelocEntry}
    (h : blk.weakRefs.contains r.sym = false) : blk.undefWeakBranch pl r = false := by
  simp only [undefWeakBranch, h, Bool.false_and]

/-- A relocated site that is not part of a relaxed pair (and not a GOT/TLSIE site) is patched by
    `patchRelocWord`. -/
theorem patchedWord_of_notRelaxed {blk : CodeBlock} {pl : Placement} {off : Nat} {r : RelocEntry}
    (hr : blk.relocAt? off = some r) (h0 : blk.relaxedAt pl off = false)
    (h4 : off < 4 ∨ blk.relaxedAt pl (off - 4) = false)
    (hng : r.kind.isGotOrTlsIe = false := by
      first | rfl | decide | simp [*, RelocKind.isGotOrTlsIe])
    (hw : blk.undefWeakBranch pl r = false := by
      first | rfl | decide | simp [*, CodeBlock.undefWeakBranch]) :
    blk.patchedWord pl off = patchRelocWord r.kind (blk.wordAt off)
      (pl.base + BitVec.ofNat 64 off) (blk.relocTarget pl off r) := by
  unfold patchedWord
  rw [hr]
  simp only [h0, hng, hw, Bool.false_and]
  rcases h4 with h4 | h4
  · simp [show ¬ 4 ≤ off by omega]
  · simp [h4]

/-- A plain relocated site is patched by `patchRelocWord` with target `blk.target pl r`. -/
theorem patchedWord_of_plain {blk : CodeBlock} {pl : Placement} {off : Nat} {r : RelocEntry}
    (hr : blk.relocAt? off = some r) (hoff : r.off = off) (hplain : blk.plainSite r = true)
    (hw : blk.undefWeakBranch pl r = false := by
      first | rfl | simp [*, CodeBlock.undefWeakBranch]) :
    blk.patchedWord pl off = patchRelocWord r.kind (blk.wordAt off)
      (pl.base + BitVec.ofNat 64 off) (blk.target pl r) := by
  subst hoff
  simp only [plainSite, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq,
    Option.isNone_iff_eq_none] at hplain
  obtain ⟨⟨⟨h0, h4⟩, hng⟩, hb⟩ := hplain
  rw [patchedWord_of_notRelaxed hr (relaxedAt_of_relaxableAt_false h0)
    (h4.imp id relaxedAt_of_relaxableAt_false) hng hw, relocTarget_of_b2bNext_none hb]

/-- The `ADRP` of a relaxed pair becomes `NOP`. -/
theorem patchedWord_of_relaxed {blk : CodeBlock} {pl : Placement} {off : Nat} {r : RelocEntry}
    (hr : blk.relocAt? off = some r) (h : blk.relaxedAt pl off = true) :
    blk.patchedWord pl off = nopWord := by
  simp [patchedWord, hr, h]

/-- The `ADD` of a relaxed pair becomes `ADR Xd, target`. -/
theorem patchedWord_of_relaxedPrev {blk : CodeBlock} {pl : Placement} {off : Nat}
    {r : RelocEntry} (hr : blk.relocAt? off = some r) (h0 : blk.relaxedAt pl off = false)
    (h4 : 4 ≤ off) (h : blk.relaxedAt pl (off - 4) = true) :
    blk.patchedWord pl off =
      adrWord (adrTemplate (blk.wordAt off)) (pl.base + BitVec.ofNat 64 off) (blk.target pl r) := by
  simp [patchedWord, hr, h0, h, h4]

theorem relocAt?_off {blk : CodeBlock} {off : Nat} {r : RelocEntry}
    (h : blk.relocAt? off = some r) : r.off = off := by
  have := List.find?_some h
  simpa using this

theorem relocAt?_mem {blk : CodeBlock} {off : Nat} {r : RelocEntry}
    (h : blk.relocAt? off = some r) : r ∈ blk.relocs :=
  List.mem_of_find?_eq_some h

theorem find?_off_of_mem : ∀ {rs : List RelocEntry}, (rs.map (·.off)).Nodup →
    ∀ {r : RelocEntry}, r ∈ rs → rs.find? (·.off == r.off) = some r
  | [], _, _, hr => by simp at hr
  | a :: rs, hnd, r, hr => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.1 hr with rfl | hr'
    · simp
    · have hne : a.off ≠ r.off := fun h => hnd.1 ⟨r, hr', h.symm⟩
      simp [hne, find?_off_of_mem hnd.2 hr']

/-! ## Bulk Segment Bridge to `Program.hasWords` and `Obj.patchRelocs` -/

/-- Template word `w'` read from the block matches the expected word `w` at local offset `o`
    of a segment with local relocations `R`: exactly when `o` is unrelocated, and on the opcode
    bits (`relocOpcodeMask`) when relocated, so `w` may carry any relocated immediate. -/
def wordMatches (R : List RelocEntry) (o : Nat) (w' w : BitVec 32) : Bool :=
  match R.find? (·.off == o) with
  | some r => (w' &&& relocOpcodeMask r.kind) == (w &&& relocOpcodeMask r.kind)
  | none => w' == w

/-- Linear walk: the bytes `bs` (the block from the segment start) hold words matching `ws`,
    starting at local word index `j`. -/
def segWordsOk (R : List RelocEntry) : Nat → List (BitVec 8) → List (BitVec 32) → Bool
  | _, _, [] => true
  | j, b0 :: b1 :: b2 :: b3 :: bs, w :: ws =>
    wordMatches R (4 * j) (b3 ++ b2 ++ b1 ++ b0) w && segWordsOk R (j + 1) bs ws
  | _, _, _ => false

/-- The relocations of `blk` in `[fo, fo + len)`, with offsets relative to `fo`. -/
def segRelocs (blk : CodeBlock) (fo len : Nat) : List RelocEntry :=
  (blk.relocs.filter fun r => decide (fo ≤ r.off) && decide (r.off < fo + len)).map
    fun r => { r with off := r.off - fo }

/-- Placement-independent check that the block holds the words `ws` at byte offset `fo` with
    local relocations `R` (exactly the block's relocations in range, shifted by `fo`), and that
    every relocated site in range is plain (`plainSite`: no relaxable pair, no branch-to-branch
    candidate) and not to a weak reference. Costs one `drop fo` plus a linear walk;
    `decide`/`rfl`-friendly. -/
def checkSegment (blk : CodeBlock) (fo : Nat) (ws : List (BitVec 32)) (R : List RelocEntry) :
    Bool :=
  fo % 4 == 0 && decide (0 < ws.length) &&
  R == blk.segRelocs fo (4 * ws.length) &&
  (blk.relocs.filter fun r => decide (fo ≤ r.off) && decide (r.off < fo + 4 * ws.length)).all
    (fun r => blk.plainSite r && !blk.weakRefs.contains r.sym) &&
  segWordsOk R 0 (blk.code.drop fo) ws

end CodeBlock

theorem patchRelocWord_eq_of_mask {kind : RelocKind} {w' w : BitVec 32} {place target : BitVec 64}
    (hm : w' &&& relocOpcodeMask kind = w &&& relocOpcodeMask kind) :
    patchRelocWord kind w' place target = patchRelocWord kind w place target := by
  cases kind <;>
    simp only [relocOpcodeMask, patchRelocWord, branchWord, adrpWord, adrpWordOff, adrWord,
      adrWordOff, lo12Word, imm19Word, imm19WordOff, tstbr14Word, tstbr14WordOff,
      tlsdescAdrPage21Word, tlsdescLd64Lo12Word, tprelHi12Word, movwSignedWord, movwNcWord] at hm ⊢ <;>
    first | rfl | rw [hm] | bv_bits | (split <;> bv_bits)

theorem wordOfBytesLE_cons4 (b0 b1 b2 b3 : BitVec 8) (bs : List (BitVec 8)) (i : Nat) :
    wordOfBytesLE (b0 :: b1 :: b2 :: b3 :: bs) (4 * (i + 1)) = wordOfBytesLE bs (4 * i) := by
  have h : ∀ k, (b0 :: b1 :: b2 :: b3 :: bs).getD (4 * (i + 1) + k) 0#8 = bs.getD (4 * i + k) 0#8 :=
    fun k => by
      rw [show 4 * (i + 1) + k = (4 * i + k) + 1 + 1 + 1 + 1 by omega]
      simp only [List.getD_cons_succ]
  have h0 := h 0
  simp only [Nat.add_zero] at h0
  simp only [wordOfBytesLE, h0, h 1, h 2, h 3]

theorem wordOfBytesLE_cons4_zero (b0 b1 b2 b3 : BitVec 8) (bs : List (BitVec 8)) :
    wordOfBytesLE (b0 :: b1 :: b2 :: b3 :: bs) 0 = b3 ++ b2 ++ b1 ++ b0 :=
  wordOfBytesLE_eq_of_readWordOff (k := 0) (by simp [Program.readWordOff])

theorem getD_eq_drop_getD_word (bs : List (BitVec 8)) (k i : Nat) :
    wordOfBytesLE bs (k + i) = wordOfBytesLE (bs.drop k) i := by
  simp only [wordOfBytesLE, Nat.add_assoc, getD_eq_drop_getD bs k]

namespace CodeBlock

theorem segWordsOk_spec {R : List RelocEntry} :
    ∀ {j : Nat} {bs : List (BitVec 8)} {ws : List (BitVec 32)},
      segWordsOk R j bs ws = true →
        4 * ws.length ≤ bs.length ∧
        ∀ (i : Nat) (hi : i < ws.length),
          wordMatches R (4 * (j + i)) (wordOfBytesLE bs (4 * i)) (ws[i]'hi) = true
  | _, _, [], _ => ⟨by simp, fun _ hi => by simp at hi⟩
  | j, b0 :: b1 :: b2 :: b3 :: bs, w :: ws, h => by
    simp only [segWordsOk, Bool.and_eq_true] at h
    obtain ⟨hw, hrest⟩ := h
    obtain ⟨hlen, hall⟩ := segWordsOk_spec hrest
    refine ⟨by simp; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa [wordOfBytesLE_cons4_zero] using hw
    | succ i =>
      rw [wordOfBytesLE_cons4, show j + (i + 1) = (j + 1) + i by omega]
      exact hall i (by simp at hi; omega)
  | _, [], _ :: _, h | _, [_], _ :: _, h | _, [_, _], _ :: _, h | _, [_, _, _], _ :: _, h => by
    simp [segWordsOk] at h

theorem find?_segRelocs_aux {fo len k : Nat} (hk : k < len) : ∀ rs : List RelocEntry,
    ((rs.filter fun r => decide (fo ≤ r.off) && decide (r.off < fo + len)).map
        fun r => { r with off := r.off - fo }).find? (·.off == k) =
      (rs.find? (·.off == fo + k)).map fun r => { r with off := r.off - fo }
  | [] => rfl
  | a :: rs => by
    have ih := find?_segRelocs_aux (fo := fo) hk rs
    by_cases hin : fo ≤ a.off ∧ a.off < fo + len
    · have h1 : (decide (fo ≤ a.off) && decide (a.off < fo + len)) = true := by simp; omega
      by_cases ha : a.off = fo + k
      · have h2 : (a.off - fo == k) = true := by simp; omega
        have h3 : (a.off == fo + k) = true := by simp; omega
        simp only [List.filter_cons, h1, ↓reduceIte, List.map_cons, List.find?_cons, h2, h3,
          Option.map_some]
      · have h2 : (a.off - fo == k) = false := by simp; omega
        have h3 : (a.off == fo + k) = false := by simp; omega
        simp only [List.filter_cons, h1, ↓reduceIte, List.map_cons, List.find?_cons, h2, h3]
        exact ih
    · have h1 : (decide (fo ≤ a.off) && decide (a.off < fo + len)) = false := by simp; omega
      have h3 : (a.off == fo + k) = false := by simp; omega
      simp only [List.filter_cons, h1, Bool.false_eq_true, ↓reduceIte, List.find?_cons, h3]
      exact ih

theorem find?_segRelocs (blk : CodeBlock) {fo len k : Nat} (hk : k < len) :
    (blk.segRelocs fo len).find? (·.off == k) =
      (blk.relocAt? (fo + k)).map fun r => { r with off := r.off - fo } :=
  find?_segRelocs_aux hk blk.relocs

/-- From `checkSegment blk fo ws R = true` (decidable on the template, for any placement), a
    program whose code is the patched block at `pl.base` holds the patched words
    `patchRelocs R ws a (blk.resolve pl)` at `a = pl.base + fo`, and each local relocation target
    is in range. -/
theorem hasWords_of_checkSegment {blk : CodeBlock} {pl : Placement} {prog : Program} {fo : Nat}
    {ws : List (BitVec 32)} {R : List RelocEntry}
    (hP : blk.Placeable pl) (hbase : prog.base = pl.base) (hcode : prog.code = blk.patched pl)
    (hchk : blk.checkSegment fo ws R = true) (hhook : prog.hookFree fo (4 * ws.length)) :
    prog.hasWords (pl.base + BitVec.ofNat 64 fo)
        (patchRelocs R ws (pl.base + BitVec.ofNat 64 fo) (blk.resolve pl)) ∧
      ∀ r ∈ R, CodeRelocInRange r.kind (pl.base + BitVec.ofNat 64 fo + BitVec.ofNat 64 r.off)
        (addSignedAddr (blk.resolve pl r.sym) r.addend) := by
  simp only [checkSegment, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨hfo, hpos⟩, hR⟩, hplain⟩, hwords⟩ := hchk
  subst hR
  obtain ⟨hlen, hmatch⟩ := segWordsOk_spec hwords
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
    have hp_len : (patchRelocs (blk.segRelocs fo (4 * ws.length)) ws (pl.base + BitVec.ofNat 64 fo) (blk.resolve pl)).length =
        ws.length := by simp [patchRelocs]
    refine ⟨by rw [hp_len]; omega, fun i hi => ?_, by rw [hp_len]; exact hhook⟩
    have hi' : i < ws.length := by omega
    rw [readWordOff_patched hcode (by omega) (by omega)]
    have hm := hmatch i hi'
    rw [Nat.zero_add, ← getD_eq_drop_getD_word] at hm
    simp only [patchRelocs, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    unfold wordMatches at hm
    rw [find?_segRelocs blk (by omega)] at hm ⊢
    cases hfind : blk.relocAt? (fo + 4 * i) with
    | none =>
      simp only [hfind, Option.map_none, beq_iff_eq] at hm ⊢
      rw [patchedWord_of_relocAt_none hfind]
      exact congrArg some hm
    | some r =>
      simp only [hfind, Option.map_some, beq_iff_eq] at hm ⊢
      have hroff := relocAt?_off hfind
      have hpl := hplain r (List.mem_filter.2 ⟨relocAt?_mem hfind, by simp; omega⟩)
      simp only [Bool.not_eq_true'] at hpl
      rw [patchedWord_of_plain hfind hroff hpl.1 (undefWeakBranch_of_not_weak hpl.2), wordAt,
        patchRelocWord_eq_of_mask hm, hplace]
      rfl
  · intro r hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
    have hr0' := List.mem_filter.1 hr0
    have hin : fo ≤ r0.off := by have := hr0'.2; simp at this; omega
    obtain ⟨-, -, hrange⟩ := hP.relocs_ok r0 hr0'.1
    have hpl := (hplain r0 hr0).1
    simp only [plainSite, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hpl
    rw [relocInRange_of_not_gotOrTlsIe hpl.1.2, relocTarget_of_b2bNext_none hpl.2] at hrange
    rw [← hplace, show fo + (r0.off - fo) = r0.off by omega]
    exact hrange

end CodeBlock

/-! ## Placed Program -/

namespace PlacedLib

variable {X O : String → Option (State → State)} {svc : State → State}

@[simp] theorem program_base (lib : PlacedLib) (pl : Placement) :
    (lib.program pl X O svc).base = pl.base := rfl

@[simp] theorem program_code (lib : PlacedLib) (pl : Placement) :
    (lib.program pl X O svc).code = lib.text.patched pl := rfl

/-- The placed program's address of a block symbol is `lib.fnAddr`. -/
theorem fnAddr_program {lib : PlacedLib} {pl : Placement} {name : String} {off : Nat}
    (h : lookup name lib.text.symbols = some off) :
    (lib.program pl X O svc).fnAddr name = lib.fnAddr pl name ∧
      lib.fnAddr pl name = pl.base + BitVec.ofNat 64 off := by
  have h' : (lib.text.symbols.find? (·.1 == name)).map (·.2) = some off := h
  have hs : (lib.program pl X O svc).symbols = lib.text.symbols := rfl
  obtain ⟨p, hf, hp⟩ : ∃ p, lib.text.symbols.find? (·.1 == name) = some p ∧ p.2 = off := by
    cases hf : lib.text.symbols.find? (·.1 == name) with
    | none => rw [hf] at h'; simp at h'
    | some p => rw [hf] at h'; exact ⟨p, rfl, by simpa using h'⟩
  refine ⟨?_, by simp [PlacedLib.fnAddr, h]⟩
  simp only [Program.fnAddr, Program.fnOff, Program.findSymbol?, PlacedLib.fnAddr, program_base,
    hs, hf, h, Option.orElse, Option.map_some, Option.getD_some, hp]

/-- No hook has its entry point inside the block's code range, provided no block symbol in the
    range is overridden (externs sit outside the block by `Placeable.externs_ok`). -/
theorem hookFree_program {lib : PlacedLib} {pl : Placement} {off len : Nat}
    (hP : lib.text.Placeable pl) (hlen : off + len ≤ lib.text.code.length)
    (hO : ∀ s ∈ lib.text.symbols, off ≤ s.2 → s.2 < off + len → O s.1 = none) :
    (lib.program pl X O svc).hookFree off len := by
  unfold Program.hookFree
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    rintro ⟨n, o⟩ hmem
    simp only [PlacedLib.program, List.mem_map] at hmem
    obtain ⟨e, he, heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have := (hP.externs_ok _ he).2
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
    left; right; omega
  · rw [List.all_eq_true]
    rintro ⟨n, o⟩ hmem
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      Option.isNone_iff_eq_none]
    by_cases h1 : off ≤ o
    · by_cases h2 : o < off + len
      · right; exact hO (n, o) hmem h1 h2
      · left; right; exact h2
    · left; left; exact h1

theorem hookFree_program_noOverrides {lib : PlacedLib} {pl : Placement} {off len : Nat}
    (hP : lib.text.Placeable pl) (hlen : off + len ≤ lib.text.code.length) :
    (lib.program pl X (fun _ => none) svc).hookFree off len :=
  hookFree_program hP hlen fun _ _ _ _ => rfl

end PlacedLib

end Obj
end Arm64
