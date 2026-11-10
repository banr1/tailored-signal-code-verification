/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.ProgramReflection
public import ProofLib.GenDecodes
public import ProofLib.Placed.Fetch
public import ProofLib.Placed.Pair
public import ProofLib.Placed.Check
public meta import Lean
public meta import ProofLib.GenDecodes
public meta import Arm64.Trusted.ISA.Decode

/-!
# Fetch Lemmas for Placed Libraries

Placement-generic instruction-fetch, relaxable-pair, and branch-to-branch call lemmas for placed
libraries (`Obj.PlacedLib`), together with the `gen_placed_fetches`, `gen_placed_fnOffs`,
`gen_interned_lib`, and `gen_block_fetches` command elaborators.

Words, relocations, and symbol offsets are resolved through logarithmic-depth trees (`WordTree`,
`RelocTree`, `CharSymVec`) and integer-encoded symbol tables (`EncSymTable`) so kernel checking
avoids linear list scans and `String` decidable equality.
-/

namespace ProofLib.GenPlacedFetches

open Arm64 Arm64.Obj ProofLib.ProgramReflection

@[expose] public section

theorem length_text_of_tree {lib : PlacedLib} {t : WordTree} {n : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n) :
    lib.text.code.length = 4 * n := by
  rw [hcode]; exact WordTree.length_toBytes_of_checkSize? hsize

/-- `hookAtOff?` of a rebased placed program without externs and without overrides. -/
theorem hookAtOff?_rebase_program {lib : PlacedLib} {pl : Placement} {b : BitVec 64}
    {X : String → Option (State → State)} (hext : lib.text.externs = []) (off : Nat) :
    ((lib.program pl).rebase b X).hookAtOff? off = none := by
  have hs : ((lib.program pl).rebase b X).stubs = [] := by
    show lib.text.externs.map _ = []
    rw [hext]; rfl
  exact hookAtOff?_eq_none_of_noStubBefore (textEnd := off + 1) (by rw [hs]; rfl)
    (fun _ => rfl) (Nat.lt_succ_self off)

/-- `hookAtOff?` of a rebased placeable program without overrides, inside the text block. -/
theorem hookAtOff?_rebase_of_placeable {lib : PlacedLib} {pl : Placement} {b : BitVec 64}
    {X : String → Option (State → State)} {t : WordTree} {n off : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hP : lib.Placeable pl) (hlt : off < 4 * n) :
    ((lib.program pl).rebase b X).hookAtOff? off = none := by
  have hlen : 0 + 4 * n ≤ lib.text.code.length := by rw [length_text_of_tree hcode hsize]; omega
  have h := PlacedLib.hookFree_program_noOverrides (lib := lib) (X := X) (svc := Syscall.standard)
    hP.text hlen
  exact Arm64.Program.hookAtOff?_eq_none_of_hookFree (prog := lib.program pl X (fun _ => none)) h
    (Nat.zero_le _) (by omega)

/-- Fetch from a rebased placed program at offset `off` whose word is `w`. -/
theorem fetch_rebase_of_patchedWord {lib : PlacedLib} {pl : Placement} {b : BitVec 64}
    {X : String → Option (State → State)} {off : Nat} {w : BitVec 32}
    (hnh : ((lib.program pl).rebase b X).hookAtOff? off = none) (hal : off % 4 = 0)
    (hlen : off + 4 ≤ lib.text.code.length)
    (hlt : off < 2 ^ 64) (hw : lib.text.patchedWord pl off = w) :
    ((lib.program pl).rebase b X).fetch (b + BitVec.ofNat 64 off) = decode w := by
  have h := Arm64.Program.fetch_of_readWordOff (prog := (lib.program pl).rebase b X) hlt hnh
    ((CodeBlock.readWordOff_patched (blk := lib.text) (pl := pl) rfl hal hlen).trans
      (congrArg some hw))
  exact h

/-- The unrelocated word at `off` read through a `WordTree` of the block's code. -/
theorem wordAt_of_tree {lib : PlacedLib} {t : WordTree} {n : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    {off : Nat} {inst : Instr} (hdec : t.fetchDecodeAt off = some inst) (hlt : off < 2 ^ 64) :
    decode (lib.text.wordAt off) = some inst := by
  let Q : Program := { code := lib.text.code }
  have hf := fetch_of_wordTree (prog := Q) n hcode hsize hdec hlt
  have hf' := Arm64.Program.fetch_base_add (prog := Q) hlt
  rw [hf, show Q.hookAtOff? off = none from
    hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) off] at hf'
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hf'
  cases hr : Q.readWordOff off with
  | none => rw [hr] at hf'; simp at hf'
  | some w =>
    rw [hr] at hf'
    have hw : wordOfBytesLE lib.text.code off = w := Arm64.Obj.wordOfBytesLE_eq_of_readWordOff hr
    show decode (wordOfBytesLE lib.text.code off) = some inst
    rw [hw]; exact hf'.symm

/-- Fetch at an unrelocated offset of a placed library, for every placement without a hook at
    `off`. -/
theorem fetch_rebase_of_noReloc {lib : PlacedLib} {t : WordTree} {n : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    {off : Nat} {inst : Instr}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 4 * n) (hlt : off < 2 ^ 64)
    (hdec : t.fetchDecodeAt off = some inst) (hnr : (lib.text.relocAt? off).isNone = true)
    {pl : Placement} {b : BitVec 64} {X : String → Option (State → State)}
    (hnh : ((lib.program pl).rebase b X).hookAtOff? off = none) :
    ((lib.program pl).rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst := by
  rw [fetch_rebase_of_patchedWord hnh hal (by rw [length_text_of_tree hcode hsize]; exact hlen)
    hlt (CodeBlock.patchedWord_of_relocAt_none (Option.isNone_iff_eq_none.mp hnr))]
  exact wordAt_of_tree hcode hsize hdec hlt

/-- The word at offset `4 * j` of a block whose code is `t.toBytes`, read through the tree in
    $O(\log N)$ steps instead of walking the byte list. -/
theorem wordAt_of_getQuad? {blk : CodeBlock} {t : WordTree} {n j : Nat} {b0 b1 b2 b3 : BitVec 8}
    (hcode : blk.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hget : t.getQuad? j = some (b0, b1, b2, b3)) :
    blk.wordAt (4 * j) = wordOfBytesLE [b0, b1, b2, b3] 0 := by
  obtain ⟨rest, hdrop⟩ := WordTree.toBytes_drop_of_getQuad? hsize hget
  have hk : ∀ k, blk.code.getD (4 * j + k) 0#8 = (b0 :: b1 :: b2 :: b3 :: rest).getD k 0#8 := by
    intro k
    simp only [List.getD_eq_getElem?_getD, ← hdrop, List.getElem?_drop, hcode]
  have h0 := hk 0
  simp only [Nat.add_zero] at h0
  simp only [CodeBlock.wordAt, wordOfBytesLE]
  rw [h0, hk 1, hk 2, hk 3]
  rfl

/-- `relaxableAt` from the two relocations and the two words, each supplied separately (so the
    words can come from `wordAt_of_getQuad?`). -/
theorem relaxableAt_of_words {blk : CodeBlock} {off : Nat} {r1 r2 : RelocEntry}
    {w0 w1 : BitVec 32} (h1 : blk.relocAt? off = some r1) (h2 : blk.relocAt? (off + 4) = some r2)
    (hw0 : blk.wordAt off = w0) (hw1 : blk.wordAt (off + 4) = w1)
    (hchk : (r1.kind == .adrpHi21 && r2.kind == .addLo12 && r1.sym == r2.sym &&
      r1.addend == r2.addend && isAdrpWord w0 && isAddImm64Word w1 &&
      (w0 &&& 0x1f#32) == (w1 &&& 0x1f#32) && ((w1 >>> 5) &&& 0x1f#32) == (w0 &&& 0x1f#32) &&
      (w0 &&& 0x1f#32) != 0x1f#32) =
      true) :
    blk.relaxableAt off = true := by
  unfold CodeBlock.relaxableAt
  rw [h1, h2, hw0, hw1]
  exact hchk

/-- Variant of `relaxableAt_of_words` taking propositional `hsymEq : r1.sym = r2.sym` so the kernel
    discharges symbol equality on literals without evaluating `String` decidable equality. -/
theorem relaxableAt_of_words_eq {blk : CodeBlock} {off : Nat} {r1 r2 : RelocEntry}
    {w0 w1 : BitVec 32} (h1 : blk.relocAt? off = some r1) (h2 : blk.relocAt? (off + 4) = some r2)
    (hw0 : blk.wordAt off = w0) (hw1 : blk.wordAt (off + 4) = w1)
    (hsymEq : r1.sym = r2.sym)
    (hchk : (r1.kind == .adrpHi21 && r2.kind == .addLo12 &&
      r1.addend == r2.addend && isAdrpWord w0 && isAddImm64Word w1 &&
      (w0 &&& 0x1f#32) == (w1 &&& 0x1f#32) && ((w1 >>> 5) &&& 0x1f#32) == (w0 &&& 0x1f#32) &&
      (w0 &&& 0x1f#32) != 0x1f#32) =
      true) :
    blk.relaxableAt off = true := by
  unfold CodeBlock.relaxableAt
  rw [h1, h2, hw0, hw1]
  dsimp only
  rw [hsymEq]
  simpa only [beq_self_eq_true, Bool.true_and, Bool.and_true] using hchk

/-- Prove `Arm64.Obj.lookup name tbl = res` via a pre-encoded `EncSymTable Nat` without invoking
    `String` decidable equality in the kernel. -/
theorem lookup_of_enc {tbl : List (String × Nat)}
    {xs : List (List Char × Nat)} {enc : ProofLib.ObjectLoad.EncSymTable Nat}
    (htbl : tbl = toStringSymbols xs) (heq : ProofLib.ObjectLoad.prepareCharAssocVal xs = enc)
    {name : String} {cs : List Char} {ek : Nat × List Nat} {res : Option Nat}
    (hname : name = String.ofList cs) (hek : encodeCharKey cs = ek)
    (hlookup : ProofLib.ObjectLoad.lookupEnc ek enc = res) :
    Arm64.Obj.lookup name tbl = res := by
  rw [ProofLib.ObjectLoad.lookupSymbols_eq_lookupEnc htbl heq hname, hek, hlookup]

/-- If `xs.map f` has no duplicates, `f` is injective on `xs`. -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} {xs : List α} (hnd : (xs.map f).Nodup)
    {x y : α} (hx : x ∈ xs) (hy : y ∈ xs) (heq : f x = f y) : x = y := by
  induction xs with
  | nil => cases hx
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    cases hx with
    | head =>
      cases hy with
      | head => rfl
      | tail _ hy' => exact absurd (heq ▸ List.mem_map_of_mem hy') hnd.1
    | tail _ hx' =>
      cases hy with
      | head => exact absurd (heq.symm ▸ List.mem_map_of_mem hx') hnd.1
      | tail _ hy' => exact ih hnd.2 hx' hy'

/-- Pairwise-distinct extern addresses imply equal extern names whenever their offsets from
    `pl.base` agree. -/
theorem eq_of_externs_nodup {externs : List String} {pl : Placement}
    (hnd : (externs.map pl.ρ).Nodup)
    {e e' : String} (he : e ∈ externs) (he' : e' ∈ externs)
    (hoff : pl.ρ e - pl.base = pl.ρ e' - pl.base) : e = e' := by
  refine eq_of_nodup_map hnd he he' ?_
  have h := congrArg (· + pl.base) hoff
  simpa only [BitVec.sub_add_cancel] using h

/-- Fetch at a plain `call26`/`jump26` site targeting block symbol `r.sym` at offset `symOff`,
    for every placement without a hook at `off`: the branch word is PC-relative, so it is computed
    at base `0`. -/
theorem fetch_rebase_of_call26 {lib : PlacedLib} {t : WordTree} {n : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    {off symOff : Nat} {r : RelocEntry} {inst : Instr} {isCall : Bool}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 4 * n) (hlt : off < 2 ^ 64)
    (hr : lib.text.relocAt? off = some r) (hoff : r.off = off)
    (hkind : r.kind = if isCall then .call26 else .jump26)
    (hplain : lib.text.plainSite r = true) (haddend : r.addend = 0)
    (hsym : lookup r.sym lib.text.symbols = some symOff) {w : BitVec 32}
    (hw : lib.text.wordAt off = w)
    (hdec : decode (branchWord w (BitVec.ofNat 64 off) (BitVec.ofNat 64 symOff)) = some inst)
    {pl : Placement} {b : BitVec 64} {X : String → Option (State → State)}
    (hnh : ((lib.program pl).rebase b X).hookAtOff? off = none)
    (hweak : lib.text.weakRefs.contains r.sym = false := by first | rfl | simp [*]) :
    ((lib.program pl).rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst := by
  rw [fetch_rebase_of_patchedWord hnh hal (by rw [length_text_of_tree hcode hsize]; exact hlen)
    hlt (CodeBlock.patchedWord_of_plain hr hoff hplain (CodeBlock.undefWeakBranch_of_not_weak hweak))]
  rw [← hdec, ← hw, hkind]
  congr 1
  cases isCall <;>
  · simp only [patchRelocWord, branchWord, CodeBlock.target, CodeBlock.resolve, hsym, haddend,
      addSignedAddr, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
    congr 3
    rw [BitVec.add_sub_add_left]

set_option linter.literalFetch false in
/-- Fetch at a plain `call26`/`jump26` site targeting an extern `e` (addend `0`, not a block
    symbol) of a placeable library: a `BL`/`B` whose offset `(pl.ρ e - pl.base) - off` depends on
    the placement only through the stub offset `pl.ρ e - pl.base`. `isCall` selects `BL`. -/
theorem fetch_rebase_of_externBranch {lib : PlacedLib} {t : WordTree} {n : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    {off : Nat} {r : RelocEntry} {e : String} (isCall : Bool)
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 4 * n) (hlt : off < 2 ^ 64)
    (hr : lib.text.relocAt? off = some r) (hoff : r.off = off)
    (hkind : r.kind = if isCall then .call26 else .jump26)
    (hplain : lib.text.plainSite r = true) (haddend : r.addend = 0) (hsymE : r.sym = e)
    (hsym : lookup e lib.text.symbols = none) {w : BitVec 32} (hw : lib.text.wordAt off = w)
    (hop : w &&& 0xfc000000#32 = if isCall then 0x94000000#32 else 0x14000000#32)
    {pl : Placement} {b : BitVec 64} {X : String → Option (State → State)}
    (hP : lib.Placeable pl)
    (hnh : ((lib.program pl).rebase b X).hookAtOff? off = none)
    (hweak : lib.text.weakRefs.contains r.sym = false := by first | rfl | simp [*]) :
    ((lib.program pl).rebase b X).fetch (b + BitVec.ofNat 64 off) =
      some (if isCall then .bl ((pl.ρ e - pl.base) - BitVec.ofNat 64 off)
        else .b ((pl.ρ e - pl.base) - BitVec.ofNat 64 off)) := by
  have hlen' : off + 4 ≤ lib.text.code.length := by rw [length_text_of_tree hcode hsize]; exact hlen
  have hrange := (hP.text.relocs_ok r (CodeBlock.relocAt?_mem hr)).2.2
  subst hw
  have hplain' := hplain
  simp only [CodeBlock.plainSite, Bool.and_eq_true, Option.isNone_iff_eq_none] at hplain'
  rw [CodeBlock.relocTarget_of_b2bNext_none hplain'.2] at hrange
  have htgt : lib.text.target pl r = pl.ρ e := by
    simp only [CodeBlock.target, CodeBlock.resolve, hsymE, hsym, haddend, addSignedAddr,
      beq_self_eq_true, ↓reduceIte]
  rw [htgt, hoff] at hrange
  rw [fetch_rebase_of_patchedWord hnh hal hlen' hlt (CodeBlock.patchedWord_of_plain hr hoff hplain
    (CodeBlock.undefWeakBranch_of_not_weak hweak)), htgt]
  have hsub : pl.ρ e - (pl.base + BitVec.ofNat 64 off) =
      (pl.ρ e - pl.base) - BitVec.ofNat 64 off := by bv_omega
  cases isCall with
  | true =>
    simp only [↓reduceIte] at hkind hop ⊢
    rw [hkind] at hrange ⊢
    show decode (branchWord _ _ _) = _
    rw [decode_branchWord_bl hop hrange, hsub]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hkind hop ⊢
    rw [hkind] at hrange ⊢
    show decode (branchWord _ _ _) = _
    rw [decode_branchWord_b hop hrange, hsub]

/-- The target of a relocation to block symbol `r.sym` at offset `symOff` with addend `0`, when
    `b = pl.base`. -/
theorem target_of_blockSym {blk : CodeBlock} {pl : Placement} {r : RelocEntry} {symOff : Nat}
    {b : BitVec 64} (hsym : lookup r.sym blk.symbols = some symOff) (haddend : r.addend = 0)
    (hb : b = pl.base) : blk.target pl r = b + BitVec.ofNat 64 symOff := by
  subst hb
  simp only [CodeBlock.target, CodeBlock.resolve, hsym, haddend, addSignedAddr, beq_self_eq_true,
    ↓reduceIte]

/-- The target of a relocation to a non-block symbol `sym` with addend `0`. -/
theorem target_of_extern_zero {blk : CodeBlock} {pl : Placement} {r : RelocEntry} {sym : String}
    (hsymE : r.sym = sym) (hsym : lookup sym blk.symbols = none) (haddend : r.addend = 0) :
    blk.target pl r = pl.ρ sym := by
  simp only [CodeBlock.target, CodeBlock.resolve, hsymE, hsym, haddend, addSignedAddr,
    beq_self_eq_true, ↓reduceIte]

/-- The target of a relocation to a non-block symbol `sym` with positive addend `k > 0`. -/
theorem target_of_extern_pos {blk : CodeBlock} {pl : Placement} {r : RelocEntry} {sym : String}
    {k : Nat} (hsymE : r.sym = sym) (hsym : lookup sym blk.symbols = none)
    (haddend : r.addend = Int.ofNat k) (hk0 : (Int.ofNat k == 0) = false) :
    blk.target pl r = pl.ρ sym + BitVec.ofNat 64 k := by
  simp only [CodeBlock.target, CodeBlock.resolve, hsymE, hsym, haddend, addSignedAddr,
    hk0, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem isNone_of_eq_none {α : Type} {o : Option α} (h : o = none) : o.isNone = true := by
  rw [h]; rfl

/-- A branch relocation `r` (`call26` or `jump26`) at aligned offset `off` is `plainSite` whenever
    `b2bNext? r` is `none`, with zero extra `relocAt?` scans. -/
theorem plainSite_of_branch {blk : CodeBlock} {off : Nat} {r : RelocEntry} {isCall : Bool}
    (hal : off % 4 = 0) (hr : blk.relocAt? off = some r) (hoff : r.off = off)
    (hkind : r.kind = if isCall then .call26 else .jump26)
    (hb2b : (blk.b2bNext? r).isNone = true) :
    blk.plainSite r = true := by
  subst hoff
  have h1 : blk.relaxableAt r.off = false :=
    CodeBlock.relaxableAt_false_of_kind hr (by rw [hkind]; cases isCall <;> decide)
  have h2 : (decide (r.off < 4) || !blk.relaxableAt (r.off - 4)) = true := by
    by_cases hlt : r.off < 4
    · simp [hlt]
    · have hnr : blk.relaxableAt (r.off - 4) = false :=
        CodeBlock.relaxableAt_false_of_next_kind
          (by rw [show r.off - 4 + 4 = r.off by omega]; exact hr)
          (by rw [hkind]; cases isCall <;> decide)
      simp [hnr]
  have h3 : (!r.kind.isGotOrTlsIe) = true := by
    rw [hkind]; cases isCall <;> rfl
  unfold CodeBlock.plainSite
  rw [h1, h2, h3, hb2b]
  rfl

/-- `b2bNext?` is `none` when `r.sym` is not a block symbol. -/
theorem b2bNext?_isNone_of_extern {blk : CodeBlock} {r : RelocEntry} {e : String}
    (hsymE : r.sym = e) (hsym : lookup e blk.symbols = none) :
    (blk.b2bNext? r).isNone = true := by
  unfold CodeBlock.b2bNext?
  rw [hsymE, hsym]
  split <;> rfl

/-- `b2bNext?` is `none` when `r` targets block symbol `symOff` (addend `0`) and `symOff` has no
    relocation. -/
theorem b2bNext?_isNone_of_noReloc {blk : CodeBlock} {r : RelocEntry} {symOff : Nat}
    (hsym : lookup r.sym blk.symbols = some symOff) (haddend : r.addend = 0)
    (hnr : blk.relocAt? symOff = none) :
    (blk.b2bNext? r).isNone = true := by
  unfold CodeBlock.b2bNext?
  rw [hsym, haddend]
  simp only [Int.add_zero, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast, hnr]
  split <;> rfl

/-- `b2bNext?` is `none` when `r` targets block symbol `symOff` (addend `0`) whose relocation is not
    `jump26`. -/
theorem b2bNext?_isNone_of_reloc_notJump {blk : CodeBlock} {r r2 : RelocEntry} {symOff : Nat}
    (hsym : lookup r.sym blk.symbols = some symOff) (haddend : r.addend = 0)
    (hr2 : blk.relocAt? symOff = some r2) (hnotJump : (r2.kind == .jump26) = false) :
    (blk.b2bNext? r).isNone = true := by
  unfold CodeBlock.b2bNext?
  rw [hsym, haddend]
  simp only [Int.add_zero, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast, hr2,
    hnotJump, Bool.false_and]
  split <;> rfl

/-- At an aligned `call26` site `off`, `relaxableAt (off - 4)` is always `false` with zero extra
    `relocAt?` scans. -/
theorem relaxableAt_prev_false_of_call26 {blk : CodeBlock} {off : Nat} {r : RelocEntry}
    (hal : off % 4 = 0) (hr : blk.relocAt? off = some r) (hkind : r.kind = .call26) :
    blk.relaxableAt (off - 4) = false := by
  by_cases hlt : off < 4
  · have hoff0 : off = 0 := by omega
    subst hoff0
    exact CodeBlock.relaxableAt_false_of_kind hr (by rw [hkind]; decide)
  · exact CodeBlock.relaxableAt_false_of_next_kind
      (by rw [show off - 4 + 4 = off by omega]; exact hr)
      (by rw [hkind]; decide)

/-- `b2bNext? r = some r2` from the already-checked hypotheses of `sepWP_rebase_b2bCall`. -/
theorem b2bNext?_of_call26 {blk : CodeBlock} {r r2 : RelocEntry} {symOff : Nat}
    (hkind : r.kind = .call26) (hsym : lookup r.sym blk.symbols = some symOff)
    (haddend : r.addend = 0) (hr2 : blk.relocAt? symOff = some r2)
    (hkind2 : r2.kind = .jump26) (hop2 : blk.wordAt symOff &&& 0xfc000000#32 = 0x14000000#32) :
    blk.b2bNext? r = some r2 := by
  unfold CodeBlock.b2bNext? isBWord
  rw [hkind, hsym, haddend]
  simp only [beq_self_eq_true, Bool.true_or, ↓reduceIte, Int.add_zero, Int.natCast_nonneg,
    Int.toNat_natCast, hr2, hkind2, hop2, Bool.and_self]

theorem fetch_rebase_base_of_zero {prog : Program} {b : BitVec 64} {inst : Instr}
    (h : prog.fetch (b + BitVec.ofNat 64 0) = some inst) : prog.fetch b = some inst := by
  simpa using h

/-- Two-instruction rule at a relaxable `ADRP`+`ADD` pair of a placed library, for
    `prog.rebase b X` with `prog = lib.program pl` and `b = pl.base`, when no hook sits at `off`
    or `off + 4`: under either encoding the pair sets `Xd := v` (the relocation target) and
    continues at `b + (off + 8)`. The hypotheses up to `hh4` are decidable from the library (or
    follow from `Placeable`); `hP`, `hb`, `hpc`, `hrun` come from the proof context, and `hv`
    may use `hb`. This is the shape of the `P_pairStep_0x<off>` lemmas that `gen_placed_fetches`
    emits. -/
theorem sepWP_rebase_relaxablePair {lib : PlacedLib} {prog : Program} {pl : Placement}
    {b : BitVec 64} {X : String → Option (State → State)} {off off8 : Nat} {r : RelocEntry}
    {rd : BitVec 5} {v : BitVec 64}
    (hprog : prog = lib.program pl)
    (hrel : lib.text.relaxableAt off = true) (hr : lib.text.relocAt? off = some r)
    (hrd : (lib.text.wordAt off).extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (h8 : off + 8 = off8)
    (hh0 : ((lib.program pl).rebase b X).hookAtOff? off = none)
    (hh4 : ((lib.program pl).rebase b X).hookAtOff? (off + 4) = none)
    (hP : lib.Placeable pl) (hb : b = pl.base) (hv : b = pl.base → lib.text.target pl r = v)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 off)
    (hrun : s.status = .Running)
    (hnext : SepWP (prog.rebase b X) tgt
      ((s.writeReg64 (.gpr rd) v).setPC (b + BitVec.ofNat 64 off8)) P post oom) :
    SepWP (prog.rebase b X) tgt s P post oom := by
  have hv' := hv hb
  clear hv
  subst hprog hb hv' h8
  exact CodeBlock.sepWP_relaxablePair hP.text rfl rfl hrel hr hrd hrd31 hh0 hh4 hpc hrun hnext

theorem add_add_sub_add_cancel (b o B t : BitVec 64) : b + o + (B + t - (B + o)) = b + t := by
  rw [BitVec.add_sub_add_left, BitVec.add_assoc, BitVec.add_comm o, BitVec.sub_add_cancel]

/-- Branch-to-branch call rule: at a `call26` site `off` whose target `A` (block offset `symOff`)
    is a `B` with a plain `jump26` relocation `r2` to block offset `C`, executing from `pc = b + off`
    reaches `pc = b + C` with `X30 = b + off + 4`, whether or not the linker retargeted the call
    (`pl.b2b off`: `BL C`; otherwise `BL A` then `B C`). Holds for every `b` because both branches
    are PC-relative. -/
theorem sepWP_rebase_b2bCall {lib : PlacedLib} {prog : Program} {pl : Placement}
    {b : BitVec 64} {X : String → Option (State → State)} {off symOff tOff : Nat}
    {r r2 : RelocEntry}
    (hprog : prog = lib.program pl)
    (hr : lib.text.relocAt? off = some r) (hkind : r.kind = .call26)
    (hnr : lib.text.relaxableAt (off - 4) = false)
    (haddend : r.addend = 0) (hsym : lookup r.sym lib.text.symbols = some symOff)
    (hnext2 : lib.text.b2bNext? r = some r2)
    (hr2 : lib.text.relocAt? symOff = some r2) (hkind2 : r2.kind = .jump26)
    (hplain2 : lib.text.plainSite r2 = true) (haddend2 : r2.addend = 0)
    (hsym2 : lookup r2.sym lib.text.symbols = some tOff)
    (hop : lib.text.wordAt off &&& 0xfc000000#32 = 0x94000000#32)
    (hop2 : lib.text.wordAt symOff &&& 0xfc000000#32 = 0x14000000#32)
    (hh0 : ((lib.program pl).rebase b X).hookAtOff? off = none)
    (hh1 : ((lib.program pl).rebase b X).hookAtOff? symOff = none)
    (hP : lib.Placeable pl)
    {tgt : BitVec 64} {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = b + BitVec.ofNat 64 off)
    (hrun : s.status = .Running)
    (hnext : SepWP (prog.rebase b X) tgt
      ((s.writeReg64 Reg.lr (b + BitVec.ofNat 64 off + 4#64)).setPC
        (b + BitVec.ofNat 64 tOff)) P post oom)
    (hweak : lib.text.weakRefs.contains r.sym = false := by first | rfl | simp [*])
    (hweak2 : lib.text.weakRefs.contains r2.sym = false := by first | rfl | simp [*]) :
    SepWP (prog.rebase b X) tgt s P post oom := by
  subst hprog
  have hroff := CodeBlock.relocAt?_off hr
  have hr2off := CodeBlock.relocAt?_off hr2
  obtain ⟨hal, hlen, hrange⟩ := hP.text.relocs_ok r (CodeBlock.relocAt?_mem hr)
  obtain ⟨hal2, hlen2, hrange2⟩ := hP.text.relocs_ok r2 (CodeBlock.relocAt?_mem hr2)
  rw [hroff] at hal hlen hrange
  rw [hr2off] at hal2 hlen2 hrange2
  have hnw := hP.text.no_wrap
  have hlt : off < 2 ^ 64 := by omega
  have hlt2 : symOff < 2 ^ 64 := by omega
  have hb2 : lib.text.b2bNext? r2 = none := by
    simp only [CodeBlock.plainSite, Bool.and_eq_true, Option.isNone_iff_eq_none] at hplain2
    exact hplain2.2
  have hT2 : lib.text.target pl r2 = pl.base + BitVec.ofNat 64 tOff := by
    simp only [CodeBlock.target, CodeBlock.resolve, hsym2, haddend2, addSignedAddr,
      beq_self_eq_true, ↓reduceIte]
  have hT1 : lib.text.target pl r = pl.base + BitVec.ofNat 64 symOff := by
    simp only [CodeBlock.target, CodeBlock.resolve, hsym, haddend, addSignedAddr,
      beq_self_eq_true, ↓reduceIte]
  have hw2 := CodeBlock.patchedWord_of_plain (pl := pl) hr2 hr2off hplain2
    (CodeBlock.undefWeakBranch_of_not_weak hweak2)
  rw [hkind2, hT2] at hw2
  rw [CodeBlock.relocTarget_of_b2bNext_none hb2, hkind2, hT2] at hrange2
  have hf2 := fetch_rebase_of_patchedWord (X := X) (b := b) hh1 hal2 hlen2 hlt2 hw2
  change _ = decode (branchWord _ _ _) at hf2
  rw [decode_branchWord_b hop2 hrange2] at hf2
  have h0 : lib.text.relaxedAt pl off = false :=
    CodeBlock.relaxedAt_of_relaxableAt_false
      (CodeBlock.relaxableAt_false_of_kind hr (by rw [hkind]; decide))
  have h4 : off < 4 ∨ lib.text.relaxedAt pl (off - 4) = false :=
    .inr (CodeBlock.relaxedAt_of_relaxableAt_false hnr)
  have hw1 := CodeBlock.patchedWord_of_notRelaxed (pl := pl) hr h0 h4
    (hw := CodeBlock.undefWeakBranch_of_not_weak hweak)
  rw [hkind] at hw1 hrange
  have hf1 := fetch_rebase_of_patchedWord (X := X) (b := b) hh0 hal hlen hlt hw1
  change _ = decode (branchWord _ _ _) at hf1
  rw [decode_branchWord_bl hop hrange] at hf1
  unfold CodeBlock.relocTarget at hf1
  have hm : ∀ (pc v pc' : BitVec 64),
      (((s.setPC pc).writeReg64 Reg.lr v).setPC pc').mem = s.mem := fun _ _ _ => by
    rw [State.mem_setPC, State.mem_writeReg64, State.mem_setPC]
  have hex : ∀ (pc imm : BitVec 64), ((lib.program pl).rebase b X).evalInst (.bl imm)
      (s.setPC pc) = ((s.setPC pc).writeReg64 Reg.lr (pc + 4#64)).setPC (pc + imm) :=
    fun _ _ => by simp only [Program.evalInst, execInstWithSvc, State.pc_setPC]
  cases hbb : pl.b2b off with
  | true =>
    simp only [hbb, ↓reduceIte, hnext2, hT2] at hf1
    have himm : b + BitVec.ofNat 64 off +
        (pl.base + BitVec.ofNat 64 tOff - (pl.base + BitVec.ofNat 64 off)) =
        b + BitVec.ofNat 64 tOff := add_add_sub_add_cancel _ _ _ _
    refine SepWP.step_pure hpc hrun hf1 (hex _ _) (hm _ _ _) ?_
    rw [himm, State.writeReg64_setPC, State.setPC_setPC]
    exact hnext
  | false =>
    simp only [hbb, Bool.false_eq_true, ↓reduceIte, hT1] at hf1
    have himm : b + BitVec.ofNat 64 off +
        (pl.base + BitVec.ofNat 64 symOff - (pl.base + BitVec.ofNat 64 off)) =
        b + BitVec.ofNat 64 symOff := add_add_sub_add_cancel _ _ _ _
    have himm2 : b + BitVec.ofNat 64 symOff +
        (pl.base + BitVec.ofNat 64 tOff - (pl.base + BitVec.ofNat 64 symOff)) =
        b + BitVec.ofNat 64 tOff := add_add_sub_add_cancel _ _ _ _
    refine SepWP.step_pure hpc hrun hf1 (hex _ _) (hm _ _ _) ?_
    rw [himm]
    refine SepWP.step_pure (State.pc_setPC _ _)
      (by rw [State.status_setPC, State.status_writeReg64, State.status_setPC, hrun]) hf2
      (s' := ((((s.setPC (b + BitVec.ofNat 64 off)).writeReg64 Reg.lr
        (b + BitVec.ofNat 64 off + 4#64)).setPC (b + BitVec.ofNat 64 symOff)).setPC
          (b + BitVec.ofNat 64 symOff)).setPC (b + BitVec.ofNat 64 symOff +
            (pl.base + BitVec.ofNat 64 tOff - (pl.base + BitVec.ofNat 64 symOff))))
      (by simp only [Program.evalInst, execInstWithSvc, State.pc_setPC])
      (by rw [State.mem_setPC, State.mem_setPC, hm]) ?_
    rw [himm2, State.setPC_setPC, State.setPC_setPC, State.writeReg64_setPC,
      State.setPC_setPC]
    exact hnext

/-! ## `RelocTree` for $O(\log R)$ Relocation Lookups and Range Queries -/

/-- Interval-annotated binary tree of `RelocEntry`s for $O(\log R)$ relocation lookup
    (`RelocTree.lookup?`) and relocation-free range checks (`RelocTree.noRelocIn`). -/
inductive RelocTree where
  | empty : RelocTree
  | leaf (r : RelocEntry) : RelocTree
  | node (lo hi : Nat) (left right : RelocTree) : RelocTree

/-- Flatten a `RelocTree` onto `acc` in $O(R)$ steps without `++`. -/
def RelocTree.toListAux : RelocTree → List RelocEntry → List RelocEntry
  | .empty, acc => acc
  | .leaf r, acc => r :: acc
  | .node _ _ l r, acc => l.toListAux (r.toListAux acc)

/-- Flatten a `RelocTree` to its `List RelocEntry`. -/
def RelocTree.toList (t : RelocTree) : List RelocEntry :=
  t.toListAux []

/-- Linear $O(R)$ check that every relocation in `t` has offset in `[lo, hi]` and every internal
    node's `[nlo, nhi]` bounds its children. -/
def RelocTree.inSpan (lo hi : Nat) : RelocTree → Bool
  | .empty => true
  | .leaf r => decide (lo ≤ r.off ∧ r.off ≤ hi)
  | .node nlo nhi l r =>
    decide (lo ≤ nlo ∧ nhi ≤ hi) && l.inSpan nlo nhi && r.inSpan nlo nhi

/-- Linear $O(R)$ well-formedness check on `RelocTree`. -/
def RelocTree.wf : RelocTree → Bool
  | .empty => true
  | .leaf _ => true
  | .node lo hi l r => l.inSpan lo hi && r.inSpan lo hi

/-- Look up the first relocation at byte offset `off` in $O(\log R)$ steps. -/
def RelocTree.lookup? : RelocTree → Nat → Option RelocEntry
  | .empty, _ => none
  | .leaf r, off => if r.off == off then some r else none
  | .node lo hi l r, off =>
    if decide (off < lo ∨ hi < off) then none
    else
      match l.lookup? off with
      | some e => some e
      | none => r.lookup? off

/-- Check in $O(\log R)$ steps that no relocation in `t` has offset in `[qlo, qhi]`. -/
def RelocTree.noRelocIn : RelocTree → Nat → Nat → Bool
  | .empty, _, _ => true
  | .leaf r, qlo, qhi => decide (r.off < qlo ∨ qhi < r.off)
  | .node lo hi l r, qlo, qhi =>
    if decide (hi < qlo ∨ qhi < lo) then true
    else l.noRelocIn qlo qhi && r.noRelocIn qlo qhi

private theorem RelocTree.toListAux_eq_append :
    ∀ (t : RelocTree) (acc : List RelocEntry),
      t.toListAux acc = t.toListAux [] ++ acc
  | .empty, _ => rfl
  | .leaf _, _ => rfl
  | .node _ _ l r, acc => by
    simp only [RelocTree.toListAux]
    rw [toListAux_eq_append l (r.toListAux acc),
        toListAux_eq_append r acc,
        toListAux_eq_append l (r.toListAux []),
        List.append_assoc]

private theorem RelocTree.inSpan_wf {lo hi : Nat} {t : RelocTree}
    (h : t.inSpan lo hi = true) : t.wf = true := by
  cases t with
  | empty => rfl
  | leaf _ => rfl
  | node nlo nhi l r =>
    simp only [RelocTree.inSpan, RelocTree.wf, Bool.and_eq_true] at h ⊢
    exact ⟨h.1.2, h.2⟩

private theorem RelocTree.mem_bounds_of_inSpan :
    ∀ (t : RelocTree) {lo hi : Nat},
      t.inSpan lo hi = true →
      ∀ r ∈ t.toListAux [], lo ≤ r.off ∧ r.off ≤ hi
  | .empty, _, _, _, _, hm => nomatch hm
  | .leaf _, _, _, h, _, hm => by
    simp only [RelocTree.inSpan, decide_eq_true_eq] at h
    cases hm with
    | head => exact h
    | tail _ htl => nomatch htl
  | .node nlo nhi l r, _, _, h, e, hm => by
    simp only [RelocTree.inSpan, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [RelocTree.toListAux, toListAux_eq_append l, List.mem_append] at hm
    rcases hm with hml | hmr
    · have hb := mem_bounds_of_inSpan l h.1.2 e hml
      exact ⟨Nat.le_trans h.1.1.1 hb.1, Nat.le_trans hb.2 h.1.1.2⟩
    · have hb := mem_bounds_of_inSpan r h.2 e hmr
      exact ⟨Nat.le_trans h.1.1.1 hb.1, Nat.le_trans hb.2 h.1.1.2⟩

private theorem RelocTree.find?_toListAux_eq_lookup? :
    ∀ (t : RelocTree) (off : Nat),
      t.wf = true →
      (t.toListAux []).find? (·.off == off) = t.lookup? off
  | .empty, _, _ => rfl
  | .leaf r, off, _ => by
    simp only [RelocTree.toListAux, List.find?_cons, List.find?_nil, RelocTree.lookup?]
    cases (r.off == off) <;> rfl
  | .node lo hi l r, off, hwf => by
    simp only [RelocTree.wf, Bool.and_eq_true] at hwf
    rw [RelocTree.toListAux, toListAux_eq_append l, List.find?_append,
        find?_toListAux_eq_lookup? l off (inSpan_wf hwf.1),
        find?_toListAux_eq_lookup? r off (inSpan_wf hwf.2)]
    simp only [RelocTree.lookup?]
    split
    · rename_i hout
      simp only [decide_eq_true_eq] at hout
      have hl : l.lookup? off = none := by
        rw [← find?_toListAux_eq_lookup? l off (inSpan_wf hwf.1), List.find?_eq_none]
        intro e he
        have hb := mem_bounds_of_inSpan l hwf.1 e he
        simp only [beq_iff_eq]; omega
      have hr : r.lookup? off = none := by
        rw [← find?_toListAux_eq_lookup? r off (inSpan_wf hwf.2), List.find?_eq_none]
        intro e he
        have hb := mem_bounds_of_inSpan r hwf.2 e he
        simp only [beq_iff_eq]; omega
      rw [hl, hr]; rfl
    · cases l.lookup? off <;> rfl

/-- Evaluate `blk.relocAt? off` in $O(\log R)$ steps via a well-formed `RelocTree`. -/
theorem relocAt?_of_tree {blk : CodeBlock} {rt : RelocTree} {off : Nat}
    {res : Option RelocEntry}
    (hrelocs : blk.relocs = rt.toList)
    (hwf : rt.wf = true)
    (hlookup : rt.lookup? off = res) :
    blk.relocAt? off = res := by
  unfold CodeBlock.relocAt?
  rw [hrelocs, RelocTree.toList, RelocTree.find?_toListAux_eq_lookup? rt off hwf, hlookup]

private theorem RelocTree.noRelocInRange_of_noRelocIn :
    ∀ (t : RelocTree) {qlo qhi : Nat},
      t.wf = true →
      t.noRelocIn qlo qhi = true →
      ∀ e ∈ t.toListAux [], e.off < qlo ∨ qhi < e.off
  | .empty, _, _, _, _, _, hm => nomatch hm
  | .leaf _, _, _, _, h, _, hm => by
    simp only [RelocTree.noRelocIn, decide_eq_true_eq] at h
    cases hm with
    | head => exact h
    | tail _ htl => nomatch htl
  | .node lo hi l r, qlo, qhi, hwf, h, e, hm => by
    simp only [RelocTree.wf, Bool.and_eq_true] at hwf
    simp only [RelocTree.noRelocIn] at h
    rw [RelocTree.toListAux, toListAux_eq_append l, List.mem_append] at hm
    split at h
    · rename_i hdisj
      simp only [decide_eq_true_eq] at hdisj
      have hb : lo ≤ e.off ∧ e.off ≤ hi := by
        rcases hm with hml | hmr
        · exact mem_bounds_of_inSpan l hwf.1 e hml
        · exact mem_bounds_of_inSpan r hwf.2 e hmr
      omega
    · simp only [Bool.and_eq_true] at h
      rcases hm with hml | hmr
      · exact noRelocInRange_of_noRelocIn l (inSpan_wf hwf.1) h.1 e hml
      · exact noRelocInRange_of_noRelocIn r (inSpan_wf hwf.2) h.2 e hmr

theorem relocAt?_isNone_of_tree_noRelocIn {blk : CodeBlock} {rt : RelocTree}
    {lo hi off : Nat}
    (hrelocs : blk.relocs = rt.toList)
    (hwf : rt.wf = true)
    (hrange : rt.noRelocIn lo hi = true)
    (hlo : lo ≤ off) (hhi : off ≤ hi) :
    (blk.relocAt? off).isNone = true := by
  unfold CodeBlock.relocAt?
  rw [hrelocs, RelocTree.toList, Option.isNone_iff_eq_none, List.find?_eq_none]
  intro r hr
  have hall := RelocTree.noRelocInRange_of_noRelocIn rt hwf hrange r hr
  simp only [beq_iff_eq]; omega

/-- True when every relocation in `rs` lies strictly outside the inclusive byte range `[lo, hi]`. -/
def noRelocInRange (rs : List RelocEntry) (lo hi : Nat) : Bool :=
  rs.all fun r => decide (r.off < lo ∨ hi < r.off)

/-- True when `off` is a 4-byte-aligned offset inside `[lo, hi]`. -/
def offInChunk (lo hi off : Nat) : Bool :=
  decide (lo ≤ off ∧ off ≤ hi ∧ off % 4 = 0)

/-- True when the chunk upper bound `hi` fits in `4 * n` bytes and `2 ^ 64`. -/
def chunkBoundsOk (hi n : Nat) : Bool :=
  decide (hi + 4 ≤ 4 * n ∧ hi < 2 ^ 64)

theorem relocAt?_isNone_of_noRelocInRange {blk : CodeBlock} {rs : List RelocEntry}
    {lo hi off : Nat}
    (hrelocs : blk.relocs = rs)
    (hrange : noRelocInRange rs lo hi = true)
    (hlo : lo ≤ off) (hhi : off ≤ hi) :
    (blk.relocAt? off).isNone = true := by
  unfold CodeBlock.relocAt?
  rw [hrelocs, Option.isNone_iff_eq_none, List.find?_eq_none]
  intro r hr
  have hall := List.all_eq_true.mp hrange r hr
  simp only [decide_eq_true_eq] at hall
  simp only [beq_iff_eq]
  omega

theorem relocAt?_of_relocs_eq {blk : CodeBlock} {rs : List RelocEntry} {off : Nat}
    {res : Option RelocEntry}
    (hrelocs : blk.relocs = rs)
    (hfind : rs.find? (·.off == off) = res) :
    blk.relocAt? off = res := by
  unfold CodeBlock.relocAt?; rw [hrelocs]; exact hfind

theorem lookup_symbols_of_eq {blk : CodeBlock} {ss : List (String × Nat)} {sym : String}
    {res : Option Nat}
    (hsyms : blk.symbols = ss)
    (hlookup : lookup sym ss = res) :
    lookup sym blk.symbols = res := by
  rw [hsyms]; exact hlookup

theorem fetch_rebase_congr_prog {p1 p2 : Program} {b pc : BitVec 64}
    {X : String → Option (State → State)} {rhs : Option Instr}
    (hprog : p1 = p2)
    (hf : (p2.rebase b X).fetch pc = rhs) :
    (p1.rebase b X).fetch pc = rhs := by
  rw [hprog]; exact hf

theorem fetch_rebase_of_chunk_noExterns {P : Placement → Program}
    {lib : PlacedLib} {t : WordTree} {n : Nat} {rs : List RelocEntry} {lo hi : Nat}
    (hprog : ∀ pl, P pl = lib.program pl)
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hext : lib.text.externs = [])
    (hrelocs : lib.text.relocs = rs)
    (hrange : noRelocInRange rs lo hi = true)
    (hbounds : chunkBoundsOk hi n = true) :
    ∀ (off : Nat) (inst : Instr),
      offInChunk lo hi off = true →
      t.fetchDecodeAt off = some inst →
      ∀ (a : Placement) (b : BitVec 64) (X : String → Option (State → State)),
        ((P a).rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst := by
  intro off inst hoff hdec a b X
  simp only [chunkBoundsOk, offInChunk, decide_eq_true_eq] at hbounds hoff
  rw [hprog a]
  exact fetch_rebase_of_noReloc hcode hsize hoff.2.2 (by omega) (by omega) hdec
    (relocAt?_isNone_of_noRelocInRange hrelocs hrange hoff.1 hoff.2.1)
    (hookAtOff?_rebase_program hext off)

theorem fetch_rebase_of_chunk_placeable {α : Sort _} {P : α → Program} {plOf : α → Placement}
    {lib : PlacedLib} {t : WordTree} {n : Nat} {rs : List RelocEntry} {lo hi : Nat}
    (hprog : ∀ a, P a = lib.program (plOf a))
    (hPOf : ∀ a, lib.Placeable (plOf a))
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hrelocs : lib.text.relocs = rs)
    (hrange : noRelocInRange rs lo hi = true)
    (hbounds : chunkBoundsOk hi n = true) :
    ∀ (off : Nat) (inst : Instr),
      offInChunk lo hi off = true →
      t.fetchDecodeAt off = some inst →
      ∀ (a : α) (b : BitVec 64) (X : String → Option (State → State)),
        ((P a).rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst := by
  intro off inst hoff hdec a b X
  simp only [chunkBoundsOk, offInChunk, decide_eq_true_eq] at hbounds hoff
  rw [hprog a]
  exact fetch_rebase_of_noReloc hcode hsize hoff.2.2 (by omega) (by omega) hdec
    (relocAt?_isNone_of_noRelocInRange hrelocs hrange hoff.1 hoff.2.1)
    (hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) (by omega))

theorem fetch_rebase_of_chunk_noExterns_tree {P : Placement → Program}
    {lib : PlacedLib} {t : WordTree} {n : Nat} {rt : RelocTree} {lo hi : Nat}
    (hprog : ∀ pl, P pl = lib.program pl)
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hext : lib.text.externs = [])
    (hrelocs : lib.text.relocs = rt.toList) (hwf : rt.wf = true)
    (hrange : rt.noRelocIn lo hi = true)
    (hbounds : chunkBoundsOk hi n = true) :
    ∀ (off : Nat) (inst : Instr),
      offInChunk lo hi off = true →
      t.fetchDecodeAt off = some inst →
      ∀ (a : Placement) (b : BitVec 64) (X : String → Option (State → State)),
        ((P a).rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst := by
  intro off inst hoff hdec a b X
  simp only [chunkBoundsOk, offInChunk, decide_eq_true_eq] at hbounds hoff
  rw [hprog a]
  exact fetch_rebase_of_noReloc hcode hsize hoff.2.2 (by omega) (by omega) hdec
    (relocAt?_isNone_of_tree_noRelocIn hrelocs hwf hrange hoff.1 hoff.2.1)
    (hookAtOff?_rebase_program hext off)

theorem fetch_rebase_of_chunk_placeable_tree {α : Sort _} {P : α → Program} {plOf : α → Placement}
    {lib : PlacedLib} {t : WordTree} {n : Nat} {rt : RelocTree} {lo hi : Nat}
    (hprog : ∀ a, P a = lib.program (plOf a))
    (hPOf : ∀ a, lib.Placeable (plOf a))
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hrelocs : lib.text.relocs = rt.toList) (hwf : rt.wf = true)
    (hrange : rt.noRelocIn lo hi = true)
    (hbounds : chunkBoundsOk hi n = true) :
    ∀ (off : Nat) (inst : Instr),
      offInChunk lo hi off = true →
      t.fetchDecodeAt off = some inst →
      ∀ (a : α) (b : BitVec 64) (X : String → Option (State → State)),
        ((P a).rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst := by
  intro off inst hoff hdec a b X
  simp only [chunkBoundsOk, offInChunk, decide_eq_true_eq] at hbounds hoff
  rw [hprog a]
  exact fetch_rebase_of_noReloc hcode hsize hoff.2.2 (by omega) (by omega) hdec
    (relocAt?_isNone_of_tree_noRelocIn hrelocs hwf hrange hoff.1 hoff.2.1)
    (hookAtOff?_rebase_of_placeable hcode hsize (hPOf a) (by omega))

/-! ## `CharSymVec` for $O(\log S)$ Symbol Indexing -/

/-- Balanced binary tree over `List (List Char × Nat)` for $O(\log S)$ index lookup. -/
inductive CharSymVec where
  | empty : CharSymVec
  | leaf (cs : List Char) (off : Nat) : CharSymVec
  | node (leftLen : Nat) (left right : CharSymVec) : CharSymVec

/-- Flatten a `CharSymVec` onto `acc` in $O(S)$ steps without `++`. -/
def CharSymVec.toListAux : CharSymVec → List (List Char × Nat) → List (List Char × Nat)
  | .empty, acc => acc
  | .leaf cs off, acc => (cs, off) :: acc
  | .node _ l r, acc => l.toListAux (r.toListAux acc)

/-- Flatten a `CharSymVec` to its `List (List Char × Nat)`. -/
def CharSymVec.toList (t : CharSymVec) : List (List Char × Nat) :=
  t.toListAux []

/-- Verify in a single $O(S)$ bottom-up pass that every `node lw l r` annotation `lw` equals
    the number of leaves in `l`. -/
def CharSymVec.checkSize? : CharSymVec → Option Nat
  | .empty => some 0
  | .leaf _ _ => some 1
  | .node lw l r =>
    match l.checkSize?, r.checkSize? with
    | some nl, some nr => if lw == nl then some (nl + nr) else none
    | _, _ => none

/-- Look up index `k` in a `CharSymVec` in $O(\log S)$ steps. -/
def CharSymVec.get? : CharSymVec → Nat → Option (List Char × Nat)
  | .empty, _ => none
  | .leaf cs off, 0 => some (cs, off)
  | .leaf _ _, _ + 1 => none
  | .node lw l r, k => if k < lw then l.get? k else r.get? (k - lw)

private theorem CharSymVec.toListAux_eq_append :
    ∀ (t : CharSymVec) (acc : List (List Char × Nat)),
      t.toListAux acc = t.toListAux [] ++ acc
  | .empty, _ => rfl
  | .leaf _ _, _ => rfl
  | .node _ l r, acc => by
    simp only [CharSymVec.toListAux]
    rw [toListAux_eq_append l (r.toListAux acc),
        toListAux_eq_append r acc,
        toListAux_eq_append l (r.toListAux []),
        List.append_assoc]

private theorem CharSymVec.length_toListAux_nil :
    ∀ (t : CharSymVec) {n : Nat},
      t.checkSize? = some n →
      (t.toListAux []).length = n
  | .empty, _, h => by simp only [CharSymVec.checkSize?, Option.some.injEq] at h; subst h; rfl
  | .leaf _ _, _, h => by simp only [CharSymVec.checkSize?, Option.some.injEq] at h; subst h; rfl
  | .node lw l r, _, h => by
    simp only [CharSymVec.checkSize?] at h
    split at h <;> try contradiction
    rename_i nl nr hl hr
    split at h <;> try contradiction
    simp only [Option.some.injEq] at h; subst h
    rw [CharSymVec.toListAux, toListAux_eq_append l, List.length_append,
        length_toListAux_nil l hl, length_toListAux_nil r hr]

private theorem CharSymVec.getElem?_toListAux_of_get? :
    ∀ (t : CharSymVec) {n : Nat} (k : Nat) {p : List Char × Nat},
      t.checkSize? = some n →
      t.get? k = some p →
      (t.toListAux [])[k]? = some p
  | .empty, _, _, _, _, hg => nomatch hg
  | .leaf _ _, _, 0, _, _, hg => by
    simp only [CharSymVec.get?, Option.some.injEq] at hg; subst hg; rfl
  | .leaf _ _, _, _ + 1, _, _, hg => nomatch hg
  | .node lw l r, _, k, _, hsz, hg => by
    simp only [CharSymVec.checkSize?] at hsz
    split at hsz <;> try contradiction
    rename_i nl nr hl hr
    split at hsz <;> try contradiction
    rename_i hlw
    have hlw_eq : lw = nl := beq_iff_eq.mp hlw
    subst hlw_eq
    have hlen_l := length_toListAux_nil l hl
    rw [CharSymVec.toListAux, toListAux_eq_append l]
    simp only [CharSymVec.get?] at hg
    split at hg
    · rename_i hlt
      rw [List.getElem?_append_left (by omega)]
      exact getElem?_toListAux_of_get? l k hl hg
    · rename_i hge
      rw [List.getElem?_append_right (by omega), hlen_l]
      exact getElem?_toListAux_of_get? r (k - lw) hr hg

theorem placed_toStringSymbols_getElem? :
    ∀ (xs : List (List Char × Nat)) (k : Nat) {cs : List Char} {off : Nat},
      xs[k]? = some (cs, off) →
      (toStringSymbols xs)[k]? = some (String.ofList cs, off)
  | [], _, _, _, h => by simp at h
  | (_, _) :: _, 0, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | _ :: rest, k + 1, _, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact placed_toStringSymbols_getElem? rest k h

theorem placed_fnOff_of_allFresh_chars {α : Sort _} {P : α → Program}
    {charSyms : List (List Char × Nat)}
    (hsyms : ∀ a, (P a).symbols = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : String.ofList cs = name)
    (hk : charSyms[k]? = some (cs, off))
    (a : α) :
    (P a).fnOff name = off :=
  fnOff_of_allFresh charSyms (hsyms a) hfresh k
    (by rw [hsyms a, ← hname]; exact placed_toStringSymbols_getElem? charSyms k hk)

theorem placed_fnOff_of_allFresh_vec {α : Sort _} {P : α → Program}
    {charSyms : List (List Char × Nat)} {vec : CharSymVec} {n : Nat}
    (hsyms : ∀ a, (P a).symbols = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (hvec : charSyms = vec.toList)
    (hsize : vec.checkSize? = some n)
    (k : Nat) {name : String} {cs : List Char} {off : Nat}
    (hname : String.ofList cs = name)
    (hk : vec.get? k = some (cs, off))
    (a : α) :
    (P a).fnOff name = off :=
  placed_fnOff_of_allFresh_chars hsyms hfresh k hname
    (by rw [hvec, CharSymVec.toList]; exact CharSymVec.getElem?_toListAux_of_get? vec k hsize hk) a
end

syntax (name := genPlacedFetchesStx)
  "gen_placed_fetches " ident ident ident ident ident (" via_placement " ident ident)?
    " [" decodeRange,* "]" : command

public meta section

open Lean Meta Elab Term Command

def rangeOffsets (r : TSyntax `decodeRange) : CommandElabM (Array Nat) := do
  match r with
  | `(decodeRange| $a:num) => return #[a.getNat]
  | `(decodeRange| $a:num → $b:num) =>
    let (a, b) := (a.getNat, b.getNat)
    unless a ≤ b && (b - a) % 4 == 0 do
      throwErrorAt r "gen_placed_fetches: bad range {a} → {b}"
    return (List.range ((b - a) / 4 + 1)).toArray.map (a + 4 * ·)
  | _ => throwUnsupportedSyntax

def hexName (pfx : String) (kind : String) (off : Nat) : Name :=
  Name.mkSimple s!"{pfx}_{kind}_0x{String.ofList (Nat.toDigits 16 off)}"

private def whnfAll (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

private def decodeRelocEntry (e : Expr) : MetaM (Nat × Name × Expr × Expr) := do
  if e.isAppOfArity ``RelocEntry.mk 5 then
    let off ← ProofLib.GenDecodes.natOf (e.getArg! 0)
    let kArg := e.getArg! 1
    let kn ← match kArg.constName? with
      | some nm => pure nm
      | none =>
        let kw ← whnfAll kArg
        let some nm := kw.constName?
          | throwError "gen_placed_fetches: cannot evaluate reloc kind {kw}"
        pure nm
    return (off, kn, mkApp (Lean.mkConst ``RelocEntry.sym) e, e)
  let off ← ProofLib.GenDecodes.natOf (mkApp (Lean.mkConst ``RelocEntry.off) e)
  let k ← whnfAll (mkApp (Lean.mkConst ``RelocEntry.kind) e)
  let some kn := k.constName? | throwError "gen_placed_fetches: cannot evaluate reloc kind {k}"
  return (off, kn, mkApp (Lean.mkConst ``RelocEntry.sym) e, e)

/-- Decode the relocation entries of `lib.text` into `Array (off, kindName, symExpr, entryExpr)`. -/
def relocEntries (lib : Expr) :
    MetaM (Array (Nat × Name × Expr × Expr)) := do
  let relocs := mkApp (Lean.mkConst ``CodeBlock.relocs) (mkApp (Lean.mkConst ``PlacedLib.text) lib)
  let elems ← ProofLib.ProgramReflection.listElemsWhnf relocs
  elems.mapM decodeRelocEntry

/-- Extract relocation entries directly from an exposed `RelocTree` value without `whnf` list spine traversal. -/
partial def collectRelocsFromTree (tE : Expr)
    (acc : Array (Nat × Name × Expr × Expr)) : MetaM (Array (Nat × Name × Expr × Expr)) := do
  if tE.isConstOf ``RelocTree.empty then
    return acc
  if tE.isAppOfArity ``RelocTree.leaf 1 then
    let entry ← decodeRelocEntry (tE.getArg! 0)
    return acc.push entry
  if tE.isAppOfArity ``RelocTree.node 4 then
    let acc ← collectRelocsFromTree (tE.getArg! 2) acc
    return (← collectRelocsFromTree (tE.getArg! 3) acc)
  throwError "gen_placed_fetches: unexpected RelocTree node {tE}"

private def natLitVal? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getArg! 1 with
      | .lit (.natVal n) => some n
      | _ => none
    else if e.isConstOf ``Nat.zero then some 0
    else none

private def natListVal? (e : Expr) : Option (List Nat) := Id.run do
  let mut cur := e
  let mut acc : Array Nat := #[]
  while cur.isAppOfArity ``List.cons 3 do
    let some n := natLitVal? (cur.getArg! 1) | return none
    acc := acc.push n
    cur := cur.getArg! 2
  if cur.isAppOfArity ``List.nil 1 then
    return some acc.toList
  return none

/-- Extract `symMap` in pure `Expr` traversal from a shared `EncSymTable Nat` value. -/
def extractSymMapFromEnc? (encVal : Expr) : Option (Std.HashMap String Nat) := Id.run do
  let mut cur := encVal
  let mut m : Std.HashMap String Nat := {}
  while cur.isAppOfArity ``List.cons 3 do
    let entry := cur.getArg! 1
    if !entry.isAppOfArity ``Prod.mk 4 then return none
    let key := entry.getArg! 2
    let offE := entry.getArg! 3
    if !key.isAppOfArity ``Prod.mk 4 then return none
    let some cps := natListVal? (key.getArg! 3) | return none
    let some off := natLitVal? offE | return none
    let s := String.ofList (cps.map Char.ofNat)
    if !m.contains s then
      m := m.insert s off
    cur := cur.getArg! 2
  if cur.isAppOfArity ``List.nil 1 then
    return some m
  return none

private def hasRelocIn (offs : Array Nat) (lo hi : Nat) : Bool := Id.run do
  let mut l := 0
  let mut r := offs.size
  while l < r do
    let mid := (l + r) / 2
    if offs[mid]! < lo then
      l := mid + 1
    else
      r := mid
  return l < offs.size && offs[l]! ≤ hi

def symStringOf (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  if let .app (.const ``RelocEntry.sym _) r := e then
    if r.isAppOfArity ``RelocEntry.mk 5 || r.isAppOfArity ``RelocEntry.mk 4 then
      if let .lit (.strVal s) := r.getArg! 2 then return s
  let r ← withTransparency .all (reduce e)
  match r with
  | .lit (.strVal s) => return s
  | _ => throwError "gen_placed_fetches: cannot evaluate relocation symbol {e}"

private def charListStringOf (csE : Expr) : MetaM String := do
  let cs ← ProofLib.ProgramReflection.listElemsWhnf csE
  let chars ← cs.mapM fun cE => do
    let n ← ProofLib.GenDecodes.natOf (mkApp (Lean.mkConst ``Char.toNat) cE)
    return Char.ofNat n
  return String.ofList chars.toList

def symbolOffsets (lib : Expr) : MetaM (Array (String × Nat × Expr)) := do
  let syms := mkApp (Lean.mkConst ``CodeBlock.symbols) (mkApp (Lean.mkConst ``PlacedLib.text) lib)
  let elems ← ProofLib.ProgramReflection.listElemsWhnf syms
  elems.mapM fun e => do
    let e ← if e.isAppOfArity ``Prod.mk 4 then pure e else whnfAll e
    unless e.isAppOfArity ``Prod.mk 4 do throwError "gen_placed_fetches: bad symbol entry {e}"
    let offE := e.getArg! 3
    return (← symStringOf (e.getArg! 2), ← ProofLib.GenDecodes.natOf offE, offE)

/-- The relocation addend as an integer. -/
def addendOf (r : Expr) : MetaM Int := do
  if r.isAppOfArity ``RelocEntry.mk 5 || r.isAppOfArity ``RelocEntry.mk 4 then
    let a := r.getArg! 3
    if let .app (.const ``Int.ofNat _) nE := a then
      return (← ProofLib.GenDecodes.natOf nE)
    if let .lit (.natVal n) := a then
      return (n : Int)
  let a ← withTransparency .all (reduce (mkApp (Lean.mkConst ``RelocEntry.addend) r))
  match a with
  | .app (.const ``Int.ofNat _) n => return (← ProofLib.GenDecodes.natOf n)
  | .app (.const ``Int.negSucc _) n => return -((← ProofLib.GenDecodes.natOf n) + 1)
  | _ => throwError "gen_placed_fetches: cannot evaluate addend {a}"

private def decideProp (p : Expr) : MetaM Expr := mkDecideProof p

private def programE (lib pl : Expr) : MetaM Expr := do
  let mut e := mkApp2 (Lean.mkConst ``PlacedLib.program) lib pl
  let mut ty ← whnfD (← inferType e)
  while ty.isForall do
    let some v := ty.bindingDomain!.getOptParamDefault? | break
    e := mkApp e v
    ty ← whnfD (ty.bindingBody!.instantiate1 v)
  return e

/-- The 32-bit little-endian word at `off` of the tree value. -/
def wordOfTreeVal (treeVal : Expr) (off : Nat) : MetaM Nat := do
  let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal treeVal off
  return b0 + 256 * (b1 + 256 * (b2 + 256 * b3))

private def mkPrivHelperName (progNs : Name) (pfxStr tag : String) : MetaM Name := do
  let env ← getEnv
  let mut idx := 0
  repeat do
    let s := if idx == 0 then s!"_{pfxStr}_{tag}" else s!"_{pfxStr}_{tag}_{idx}"
    let priv := mkPrivateName env (progNs ++ Name.mkSimple s)
    if !env.contains priv then
      return priv
    idx := idx + 1
  unreachable!

private partial def buildRelocTreeExpr (relocs : Array (Nat × Name × Expr × Expr)) : Expr :=
  let emptyE := Lean.mkConst ``RelocTree.empty
  let leafFn := Lean.mkConst ``RelocTree.leaf
  let nodeFn := Lean.mkConst ``RelocTree.node
  let rec go (loIdx hiIdx : Nat) : Expr × Nat × Nat :=
    let len := hiIdx - loIdx
    if len == 0 then
      (emptyE, 0, 0)
    else if len == 1 then
      let (off, _, _, rE) := relocs[loIdx]!
      (mkApp leafFn rE, off, off)
    else
      let mid := loIdx + len / 2
      let (lE, llo, lhi) := go loIdx mid
      let (rE, rlo, rhi) := go mid hiIdx
      let lo := Nat.min llo rlo
      let hi := Nat.max lhi rhi
      (mkApp4 nodeFn (mkRawNatLit lo) (mkRawNatLit hi) lE rE, lo, hi)
  (go 0 relocs.size).1

private partial def buildCharSymVecExpr (entries : Array (Expr × Expr)) : Expr :=
  let emptyE := Lean.mkConst ``CharSymVec.empty
  let leafFn := Lean.mkConst ``CharSymVec.leaf
  let nodeFn := Lean.mkConst ``CharSymVec.node
  let rec go (loIdx hiIdx : Nat) : Expr :=
    let len := hiIdx - loIdx
    if len == 0 then
      emptyE
    else if len == 1 then
      let (csE, offE) := entries[loIdx]!
      mkApp2 leafFn csE offE
    else
      let half := len / 2
      let mid := loIdx + half
      let lE := go loIdx mid
      let rE := go mid hiIdx
      mkApp3 nodeFn (mkRawNatLit half) lE rE
  go 0 entries.size

/-- Static data shared by every generated lemma. -/
structure Ctx where
  progName : Name
  libName : Name
  libE : Expr
  textE : Expr
  treeE : Expr
  treeVal : Expr
  nE : Expr
  n : Nat
  hcodeE : Expr
  hsizeE : Expr
  relocs : Array (Nat × Name × Expr × Expr)
  relocMap : Std.HashMap Nat (Nat × Name × Expr × Expr)
  syms : Array (String × Nat × Expr)
  symMap : Std.HashMap String Nat
  /-- `none`: `P : Placement → Program` and the library has no externs. `some (plOf, hPOf)`:
      `P : (a : A) → Program` with `P a ≡ lib.program (plOf a)` and `hPOf a : lib.Placeable (plOf a)`. -/
  viaPl : Option (Expr × Expr)
  /-- Type and binder info of the parameter `a` (or `pl`). -/
  paramTy : Expr
  paramBi : BinderInfo
  hprogRef : IO.Ref (Option Name)
  hextRef : IO.Ref (Option Name)
  rtRef : IO.Ref (Option (Expr × Expr × Expr))
  symEncRef : IO.Ref (Option (Expr × Expr × Expr × Expr))
  symProofCache : IO.Ref (Std.HashMap String Expr)

def getHProg (c : Ctx) : MetaM Expr := do
  if let some nm ← c.hprogRef.get then
    return Lean.mkConst nm
  let env ← getEnv
  let modNm ← getMainModule
  let priv := mkPrivateName env (modNm ++ c.progName ++ `_gpf_hprog)
  if env.contains priv then
    c.hprogRef.set (some priv)
    return Lean.mkConst priv
  let (ty, val) ← withLocalDecl `a .default c.paramTy fun a => do
    let pl := match c.viaPl with
      | none => a
      | some (plOf, _) => mkApp plOf a
    let progE := mkApp (Lean.mkConst c.progName) a
    let rhs ← programE c.libE pl
    let eqTy ← mkEq progE rhs
    let prf ← mkExpectedTypeHint (← mkEqRefl progE) eqTy
    return (← mkForallFVars #[a] eqTy, ← mkLambdaFVars #[a] prf)
  addDecl (.thmDecl { name := priv, levelParams := [], type := ty, value := val })
  c.hprogRef.set (some priv)
  return Lean.mkConst priv

private def getHExt (c : Ctx) : MetaM Expr := do
  if let some nm ← c.hextRef.get then
    return Lean.mkConst nm
  let env ← getEnv
  let modNm ← getMainModule
  let priv := mkPrivateName env (modNm ++ c.libName ++ `_gpf_hext)
  if env.contains priv then
    c.hextRef.set (some priv)
    return Lean.mkConst priv
  let externsE := mkApp (Lean.mkConst ``CodeBlock.externs) c.textE
  let nilE ← mkAppOptM ``List.nil #[Lean.mkConst ``String]
  let ty ← mkEq externsE nilE
  let val := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
    (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``String)) nilE
  addDecl (.thmDecl { name := priv, levelParams := [], type := ty, value := val })
  c.hextRef.set (some priv)
  return Lean.mkConst priv

def sharedRelocTreeNames (progName : Name) : Name × Name × Name :=
  (progName ++ `_gpf_shared_relocTree,
   progName ++ `_gpf_shared_relocTree_eq,
   progName ++ `_gpf_shared_relocTree_wf)

def sharedSymEncNames (progName : Name) : Name × Name × Name × Name :=
  (progName ++ `_gpf_shared_symChars,
   progName ++ `_gpf_shared_symEnc,
   progName ++ `_gpf_shared_symChars_eq,
   progName ++ `_gpf_shared_symEnc_eq)

private def getRelocTree (c : Ctx) : MetaM (Expr × Expr × Expr) := do
  if let some res ← c.rtRef.get then
    return res
  let env ← getEnv
  let (shRtNm, shEqNm, shWfNm) := sharedRelocTreeNames c.progName
  if let some rtCi := env.find? shRtNm then
    if let some eqCi := env.find? shEqNm then
      if rtCi.hasValue && env.contains shWfNm &&
          eqCi.type.eq?.any (fun (_, lhs, _) =>
            lhs == mkApp (Lean.mkConst ``CodeBlock.relocs) c.textE) then
        let res := (Lean.mkConst shRtNm, Lean.mkConst shEqNm, Lean.mkConst shWfNm)
        c.rtRef.set (some res)
        return res
  let modNm ← getMainModule
  let rtNm := mkPrivateName env (modNm ++ c.libName ++ `_gpf_relocTree)
  let eqNm := mkPrivateName env (modNm ++ c.libName ++ `_gpf_relocTree_eq)
  let wfNm := mkPrivateName env (modNm ++ c.libName ++ `_gpf_relocTree_wf)
  if env.contains rtNm && env.contains eqNm && env.contains wfNm then
    let res := (Lean.mkConst rtNm, Lean.mkConst eqNm, Lean.mkConst wfNm)
    c.rtRef.set (some res)
    return res
  let rtVal := buildRelocTreeExpr c.relocs
  let rtTy := Lean.mkConst ``RelocTree
  addDecl (.defnDecl {
    name := rtNm, levelParams := [], type := rtTy, value := rtVal,
    hints := .abbrev, safety := .safe
  })
  let rtE := Lean.mkConst rtNm
  let lhsEq := mkApp (Lean.mkConst ``CodeBlock.relocs) c.textE
  let rhsEq := mkApp (Lean.mkConst ``RelocTree.toList) rtE
  let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``RelocEntry)
  let eqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) listTy lhsEq rhsEq
  let eqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) listTy lhsEq
  addDecl (.thmDecl { name := eqNm, levelParams := [], type := eqTy, value := eqVal })
  let wfLhs := mkApp (Lean.mkConst ``RelocTree.wf) rtE
  let trueE := Lean.mkConst ``Bool.true
  let boolTy := Lean.mkConst ``Bool
  let wfTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) boolTy wfLhs trueE
  let wfVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy trueE
  addDecl (.thmDecl { name := wfNm, levelParams := [], type := wfTy, value := wfVal })
  let res := (rtE, Lean.mkConst eqNm, Lean.mkConst wfNm)
  c.rtRef.set (some res)
  return res

private def relocAtTreeProof (c : Ctx) (offE resE : Expr) : MetaM Expr := do
  let (rtE, hrelocsE, hwfE) ← getRelocTree c
  let optTy := mkApp (Lean.mkConst ``Option [.zero]) (Lean.mkConst ``RelocEntry)
  let hlookup := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optTy resE
  return mkAppN (Lean.mkConst ``relocAt?_of_tree) #[c.textE, rtE, offE, resE, hrelocsE, hwfE, hlookup]

def relocAtSomeProof (c : Ctx) (offE rE : Expr) : MetaM Expr := do
  let someRE := mkApp2 (Lean.mkConst ``Option.some [.zero]) (Lean.mkConst ``RelocEntry) rE
  relocAtTreeProof c offE someRE

def relocAtNoneProof (c : Ctx) (offE : Expr) : MetaM Expr := do
  let noneRE := mkApp (Lean.mkConst ``Option.none [.zero]) (Lean.mkConst ``RelocEntry)
  relocAtTreeProof c offE noneRE

private def buildListExpr0 (elemTy : Expr) (elems : Array Expr) : Expr := Id.run do
  let nilE := mkApp (Lean.mkConst ``List.nil [.zero]) elemTy
  let consFn := mkApp (Lean.mkConst ``List.cons [.zero]) elemTy
  let mut acc := nilE
  for i in [0 : elems.size] do
    acc := mkApp2 consFn elems[elems.size - 1 - i]! acc
  return acc

private def getSymEncTable (c : Ctx) : MetaM (Expr × Expr × Expr × Expr) := do
  if let some res ← c.symEncRef.get then
    return res
  let env ← getEnv
  let (shXsNm, shEncNm, shHtblNm, shHeqNm) := sharedSymEncNames c.progName
  if let some xsCi := env.find? shXsNm then
    if let some encCi := env.find? shEncNm then
      if let some htblCi := env.find? shHtblNm then
        if xsCi.hasValue && encCi.hasValue && env.contains shHeqNm &&
            htblCi.type.eq?.any (fun (_, lhs, _) =>
              lhs == mkApp (Lean.mkConst ``CodeBlock.symbols) c.textE) then
          let res := (Lean.mkConst shXsNm, Lean.mkConst shEncNm,
                      Lean.mkConst shHtblNm, Lean.mkConst shHeqNm)
          c.symEncRef.set (some res)
          return res
  let modNm ← getMainModule
  let xsNm := mkPrivateName env (modNm ++ c.libName ++ `_gpf_symChars)
  let encNm := mkPrivateName env (modNm ++ c.libName ++ `_gpf_symEnc)
  let htblNm := mkPrivateName env (modNm ++ c.libName ++ `_gpf_symChars_eq)
  let heqNm := mkPrivateName env (modNm ++ c.libName ++ `_gpf_symEnc_eq)
  if env.contains xsNm && env.contains encNm && env.contains htblNm && env.contains heqNm then
    let res := (Lean.mkConst xsNm, Lean.mkConst encNm, Lean.mkConst htblNm, Lean.mkConst heqNm)
    c.symEncRef.set (some res)
    return res
  let charListTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Char)
  let natTy := Lean.mkConst ``Nat
  let strTy := Lean.mkConst ``String
  let charPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) charListTy natTy
  let charPairMk := mkApp2 (Lean.mkConst ``Prod.mk [.zero, .zero]) charListTy natTy
  let xsTy := mkApp (Lean.mkConst ``List [.zero]) charPairTy
  let natListTy := mkApp (Lean.mkConst ``List [.zero]) natTy
  let encKeyTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natListTy
  let encEntryTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) encKeyTy natTy
  let encEntryMk := mkApp2 (Lean.mkConst ``Prod.mk [.zero, .zero]) encKeyTy natTy
  let encTy := mkApp (Lean.mkConst ``ProofLib.ObjectLoad.EncSymTable) natTy
  let xsElems := c.syms.map fun (s, _, offE) =>
    mkApp2 charPairMk (toExpr s.toList) offE
  let encElems := c.syms.map fun (s, off, _) =>
    let ekE := toExpr (s.length, s.toList.map (fun ch => ch.val.toNat))
    mkApp2 encEntryMk ekE (mkNatLit off)
  let xsVal := buildListExpr0 charPairTy xsElems
  let encVal := buildListExpr0 encEntryTy encElems
  addDecl (.defnDecl {
    name := xsNm, levelParams := [], type := xsTy, value := xsVal,
    hints := .abbrev, safety := .safe
  })
  addDecl (.defnDecl {
    name := encNm, levelParams := [], type := encTy, value := encVal,
    hints := .abbrev, safety := .safe
  })
  let xsE := Lean.mkConst xsNm
  let encE := Lean.mkConst encNm
  let strPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
  let strListTy := mkApp (Lean.mkConst ``List [.zero]) strPairTy
  let symsLhs := mkApp (Lean.mkConst ``CodeBlock.symbols) c.textE
  let symsRhs := mkApp (Lean.mkConst ``toStringSymbols) xsE
  let htblTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) strListTy symsLhs symsRhs
  let htblVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strListTy symsLhs
  addDecl (.thmDecl { name := htblNm, levelParams := [], type := htblTy, value := htblVal })
  let prepLhs := mkApp2 (Lean.mkConst ``ProofLib.ObjectLoad.prepareCharAssocVal) natTy xsE
  let heqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) encTy prepLhs encE
  let heqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) encTy encE
  addDecl (.thmDecl { name := heqNm, levelParams := [], type := heqTy, value := heqVal })
  let res := (xsE, encE, Lean.mkConst htblNm, Lean.mkConst heqNm)
  c.symEncRef.set (some res)
  return res

/-- Get or create a cached module-level theorem `lookup symStr c.textE.symbols = resE`,
    proved via `lookup_of_enc` so the kernel compares integer codepoints instead of `String`s. -/
def lookupSymProof (c : Ctx) (symStr : String) (_symE resE : Expr) : MetaM Expr := do
  let cache ← c.symProofCache.get
  match cache.get? symStr with
  | some p => return p
  | none =>
    let (xsE, encE, htblE, heqE) ← getSymEncTable c
    let env ← getEnv
    let modNm ← getMainModule
    let symHash := s!"{symStr.hash}"
    let thmNm := mkPrivateName env (modNm ++ c.libName ++ Name.mkSimple s!"_gpf_sym_{symHash}_{cache.size}")
    let symLit := mkStrLit symStr
    let strTy := Lean.mkConst ``String
    let natTy := Lean.mkConst ``Nat
    let optNatTy := mkApp (Lean.mkConst ``Option [.zero]) natTy
    let natListTy := mkApp (Lean.mkConst ``List [.zero]) natTy
    let encKeyTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natListTy
    let csList := symStr.toList
    let csE := toExpr csList
    let ekE := toExpr (symStr.length, csList.map (fun ch => ch.val.toNat))
    let hname := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy symLit
    let hek := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) encKeyTy ekE
    let hlookup := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optNatTy resE
    let tblE := mkApp (Lean.mkConst ``CodeBlock.symbols) c.textE
    let lhs ← mkAppM ``Arm64.Obj.lookup #[symLit, tblE]
    let ty := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) optNatTy lhs resE
    let val := mkAppN (Lean.mkConst ``lookup_of_enc)
      #[tblE, xsE, encE, htblE, heqE, symLit, csE, ekE, resE, hname, hek, hlookup]
    addDecl (.thmDecl { name := thmNm, levelParams := [], type := ty, value := val })
    let p := Lean.mkConst thmNm
    c.symProofCache.set (cache.insert symStr p)
    return p

/-- Runs `k a pl hP? b X` under fresh locals for the parameter `a` (or `pl`), `b`, `X`, and
    abstracts the result `(type, proof)` over `#[a, b, X] ++ extra`. -/
def withParams (c : Ctx)
    (k : Expr → Expr → Option Expr → Expr → Expr → MetaM (Array Expr × Expr × Expr)) :
    MetaM (Expr × Expr) := do
  let bv64 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
  let hookTy ← mkArrow (Lean.mkConst ``String)
    (mkApp (Lean.mkConst ``Option [.zero])
      (← mkArrow (Lean.mkConst ``Arm64.State) (Lean.mkConst ``Arm64.State)))
  withLocalDecl `a c.paramBi c.paramTy fun a =>
    withLocalDeclD `b bv64 fun b => withLocalDeclD `X hookTy fun X => do
      let (pl, hP?) := match c.viaPl with
        | none => (a, none)
        | some (plOf, hPOf) => (mkApp plOf a, some (mkApp hPOf a))
      let (extra, ty, prf) ← k a pl hP? b X
      let xs := #[a, b, X] ++ extra
      return (← mkForallFVars xs ty, ← mkLambdaFVars xs prf)

/-- `((lib.program pl).rebase b X).hookAtOff? off = none`. -/
def hnhOf (c : Ctx) (pl : Expr) (hP? : Option Expr) (b X : Expr) (off : Nat) :
    MetaM Expr := do
  match hP? with
  | none =>
    let hext ← getHExt c
    return mkAppN (Lean.mkConst ``hookAtOff?_rebase_program) #[c.libE, pl, b, X, hext, mkNatLit off]
  | some hP =>
    let hlt ← decideProp (← mkAppM ``LT.lt #[mkNatLit off,
      ← mkAppM ``HMul.hMul #[mkNatLit 4, c.nE]])
    return mkAppN (Lean.mkConst ``hookAtOff?_rebase_of_placeable)
      #[c.libE, pl, b, X, c.treeE, c.nE, mkNatLit off, c.hcodeE, c.hsizeE, hP, hlt]

/-- `(w, hw : lib.text.wordAt off = w)` with `w` read through the tree (`wordAt_of_getQuad?`), so
    the kernel never walks the byte list. -/
def wordAtProof (c : Ctx) (off : Nat) : MetaM (Expr × Expr) := do
  let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal c.treeVal off
  let bv8 (k : Nat) := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit k)
  let bv8Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 8)
  let bs := [bv8 b0, bv8 b1, bv8 b2, bv8 b3]
  let listE ← mkListLit bv8Ty bs
  let wE := mkApp2 (Lean.mkConst ``Arm64.Obj.wordOfBytesLE) listE (mkNatLit 0)
  let j := off / 4
  let quadE ← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[bv8 b0, ← mkAppM ``Prod.mk #[bv8 b1,
    ← mkAppM ``Prod.mk #[bv8 b2, bv8 b3]]]]
  let optQuadTy ← inferType quadE
  let hget := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optQuadTy quadE
  let p := mkAppN (Lean.mkConst ``wordAt_of_getQuad?)
    #[c.textE, c.treeE, c.nE, mkNatLit j, bv8 b0, bv8 b1, bv8 b2, bv8 b3, c.hcodeE, c.hsizeE, hget]
  return (wE, p)

private def b2bNextIsNoneBlockProof (c : Ctx) (rE hsym haddend : Expr) (symOff : Nat) :
    MetaM Expr := do
  let symOffE := mkNatLit symOff
  match c.relocMap.get? symOff with
  | none =>
    let hnr ← relocAtNoneProof c symOffE
    return mkAppN (Lean.mkConst ``b2bNext?_isNone_of_noReloc)
      #[c.textE, rE, symOffE, hsym, haddend, hnr]
  | some (_, k2, _, r2E) =>
    let hr2 ← relocAtSomeProof c symOffE r2E
    let falseE := Lean.mkConst ``Bool.false
    let hnotJump := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Bool) falseE
    let _ := k2
    return mkAppN (Lean.mkConst ``b2bNext?_isNone_of_reloc_notJump)
      #[c.textE, rE, r2E, symOffE, hsym, haddend, hr2, hnotJump]

private def notWeakProof? (c : Ctx) (rE : Expr) : MetaM (Option Expr) := do
  let boolTy := Lean.mkConst ``Bool
  let falseE := Lean.mkConst ``Bool.false
  let lhs ← mkAppM ``List.contains
    #[mkApp (Lean.mkConst ``CodeBlock.weakRefs) c.textE, mkApp (Lean.mkConst ``RelocEntry.sym) rE]
  let ok ← withTransparency .all <| isDefEq lhs falseE
  if !ok then return none
  return some (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy falseE)

private def pairStepLemma? (c : Ctx) (off : Nat) : MetaM (Option (Expr × Expr)) := do
  let some (_, k1, sym1E, r1E) := c.relocMap.get? off | return none
  let some (_, k2, sym2E, r2E) := c.relocMap.get? (off + 4) | return none
  unless k1 == ``RelocKind.adrpHi21 && k2 == ``RelocKind.addLo12 do return none
  let sym ← symStringOf sym1E
  unless sym == (← symStringOf sym2E) do return none
  let blockOff? := c.symMap.get? sym
  let addend ← addendOf r1E
  if addend < 0 || (addend != 0 && blockOff?.isSome) then
    throwError "gen_placed_fetches: relaxable pair at {off} has unsupported addend {addend}"
  if c.viaPl.isNone && blockOff?.isSome then return none
  let w0 ← wordOfTreeVal c.treeVal off
  let w1 ← wordOfTreeVal c.treeVal (off + 4)
  let rd := w0 % 32
  unless w0 &&& 0x9f000000 == 0x90000000 && w1 &&& 0xffc00000 == 0x91000000 &&
      w1 % 32 == rd && (w1 >>> 5) % 32 == rd && rd != 31 do
    return none
  let offE := mkNatLit off
  let trueE := Lean.mkConst ``Bool.true
  let symLit := mkStrLit sym
  let hsymE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``String) symLit
  let hr ← relocAtSomeProof c offE r1E
  let hr4 ← relocAtSomeProof c (mkNatLit (off + 4)) r2E
  let (w0E, hw0) ← wordAtProof c off
  let (w1E, hw1) ← wordAtProof c (off + 4)
  let hchk := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Bool) trueE
  let hrel := mkAppN (Lean.mkConst ``relaxableAt_of_words_eq)
    #[c.textE, offE, r1E, r2E, w0E, w1E, hr, hr4, hw0, hw1, hsymE, hchk]
  let rdE := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit rd)
  let bv5Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 5)
  let hrdW := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv5Ty rdE
  let motive ← withLocalDeclD `x (mkApp (Lean.mkConst ``BitVec) (mkNatLit 32)) fun x => do
    mkLambdaFVars #[x] (← mkEq (← mkAppM ``BitVec.extractLsb' #[mkNatLit 0, mkNatLit 5, x]) rdE)
  let hrd ← mkEqNDRec motive hrdW (← mkEqSymm hw0)
  let r31E := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 5) (mkNatLit 31)
  let hrd31 ← decideProp (mkNot (← mkEq rdE r31E))
  let off8E := mkNatLit (off + 8)
  let h8 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Nat) off8E
  let hprogFn ← getHProg c
  let intTy := Lean.mkConst ``Int
  let hsymCached ← match blockOff? with
    | some symOff => lookupSymProof c sym sym1E (← mkAppM ``Option.some #[mkNatLit symOff])
    | none => lookupSymProof c sym symLit (← mkAppOptM ``Option.none #[Lean.mkConst ``Nat])
  let r ← withParams c fun a pl hP? b X => do
    let progE := mkApp (Lean.mkConst c.progName) a
    let hprog := mkApp hprogFn a
    let hh0 ← hnhOf c pl hP? b X off
    let hh4 ← hnhOf c pl hP? b X (off + 4)
    let placeableTy := mkApp2 (Lean.mkConst ``PlacedLib.Placeable) c.libE pl
    let baseE := mkApp (Lean.mkConst ``Placement.base) pl
    let hbTy ← mkEq b baseE
    let k (hP : Expr) (pre : Array Expr) : MetaM (Array Expr × Expr × Expr) :=
      withLocalDeclD `hb hbTy fun hb => do
        let (v, hv) ← match blockOff? with
          | some symOff =>
            let v ← mkAppM ``HAdd.hAdd #[b, mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64)
              (mkNatLit symOff)]
            let haddend := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) intTy (toExpr (0 : Int))
            let hv ← withLocalDeclD `hb' hbTy fun hb' => do
              mkLambdaFVars #[hb'] (mkAppN (Lean.mkConst ``target_of_blockSym)
                #[c.textE, pl, r1E, mkNatLit symOff, b, hsymCached, haddend, hb'])
            pure (v, hv)
          | none =>
            let rho := mkApp2 (Lean.mkConst ``Placement.ρ) pl symLit
            if addend == 0 then
              let haddend := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) intTy (toExpr (0 : Int))
              let hv0 := mkAppN (Lean.mkConst ``target_of_extern_zero)
                #[c.textE, pl, r1E, symLit, hsymE, hsymCached, haddend]
              let hv ← withLocalDeclD `hb' hbTy fun hb' => mkLambdaFVars #[hb'] hv0
              pure (rho, hv)
            else
              let kNat := addend.toNat
              let kE := mkNatLit kNat
              let v ← mkAppM ``HAdd.hAdd #[rho, mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) kE]
              let haddend := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) intTy (toExpr addend)
              let hk0 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Bool)
                (Lean.mkConst ``Bool.false)
              let hv0 := mkAppN (Lean.mkConst ``target_of_extern_pos)
                #[c.textE, pl, r1E, symLit, kE, hsymE, hsymCached, haddend, hk0]
              let hv ← withLocalDeclD `hb' hbTy fun hb' => mkLambdaFVars #[hb'] hv0
              pure (v, hv)
        let p := mkAppN (Lean.mkConst ``sepWP_rebase_relaxablePair)
          #[c.libE, progE, pl, b, X, offE, off8E, r1E, rdE, v,
            hprog, hrel, hr, hrd, hrd31, h8, hh0, hh4, hP, hb, hv]
        let xs := pre ++ #[hb]
        return (#[], ← mkForallFVars xs (← inferType p), ← mkLambdaFVars xs p)
    match hP? with
    | some hP => k hP #[]
    | none => withLocalDeclD `hP placeableTy fun hP => k hP #[hP]
  return some r

private def opcodeProof? (c : Ctx) (off op : Nat) : MetaM (Option Expr) := do
  unless (← wordOfTreeVal c.treeVal off) &&& 0xfc000000 == op do return none
  let bv32 (k : Nat) := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit k)
  let (_, hw) ← wordAtProof c off
  let bv32Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 32)
  let maskF ← withLocalDeclD `x bv32Ty fun x => do
    mkLambdaFVars #[x] (← mkAppM ``HAnd.hAnd #[x, bv32 0xfc000000])
  let hmask ← mkCongrArg maskF hw
  let hval := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32Ty (bv32 op)
  return some (← mkEqTrans hmask hval)

private def callStepLemma? (c : Ctx) (off : Nat) : MetaM (Option (Expr × Expr)) := do
  let some (_, k1, sym1E, r1E) := c.relocMap.get? off | return none
  unless k1 == ``RelocKind.call26 do return none
  let sym1 ← symStringOf sym1E
  let some symOff := c.symMap.get? sym1 | return none
  let some (_, k2, sym2E, r2E) := c.relocMap.get? symOff | return none
  unless k2 == ``RelocKind.jump26 do return none
  let sym2 ← symStringOf sym2E
  let some tOff := c.symMap.get? sym2 | return none
  if (← addendOf r1E) != 0 || (← addendOf r2E) != 0 then return none
  -- The final target must not itself be retargetable.
  if let some (_, kt, _, _) := c.relocMap.get? tOff then
    if kt == ``RelocKind.jump26 then return none
  let some hop ← opcodeProof? c off 0x94000000 | return none
  let some hop2 ← opcodeProof? c symOff 0x14000000 | return none
  let offE := mkNatLit off
  let symOffE := mkNatLit symOff
  let tOffE := mkNatLit tOff
  let hr ← relocAtSomeProof c offE r1E
  let hr2 ← relocAtSomeProof c symOffE r2E
  let relocKindTy := Lean.mkConst ``RelocKind
  let hkind := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) relocKindTy
    (Lean.mkConst ``RelocKind.call26)
  let hkind2 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) relocKindTy
    (Lean.mkConst ``RelocKind.jump26)
  let natTy := Lean.mkConst ``Nat
  let hal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy (mkNatLit 0)
  let hnr := mkAppN (Lean.mkConst ``relaxableAt_prev_false_of_call26)
    #[c.textE, offE, r1E, hal, hr, hkind]
  let intTy := Lean.mkConst ``Int
  let zeroIntE := toExpr (0 : Int)
  let haddend := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) intTy zeroIntE
  let haddend2 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) intTy zeroIntE
  let hsym ← lookupSymProof c sym1 sym1E (← mkAppM ``Option.some #[symOffE])
  let hsym2 ← lookupSymProof c sym2 sym2E (← mkAppM ``Option.some #[tOffE])
  let hnext2 := mkAppN (Lean.mkConst ``b2bNext?_of_call26)
    #[c.textE, r1E, r2E, symOffE, hkind, hsym, haddend, hr2, hkind2, hop2]
  let hal2 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy (mkNatLit 0)
  let hoff2 := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy symOffE
  let hb2b2 ← b2bNextIsNoneBlockProof c r2E hsym2 haddend2 tOff
  let some notWeak2 ← notWeakProof? c r2E | return none
  let some notWeak1 ← notWeakProof? c r1E | return none
  let hplain2 := mkAppN (Lean.mkConst ``plainSite_of_branch)
    #[c.textE, symOffE, r2E, Lean.mkConst ``Bool.false, hal2, hr2, hoff2, hkind2, hb2b2]
  let hprogFn ← getHProg c
  let r ← withParams c fun a pl hP? b X => do
    let progE := mkApp (Lean.mkConst c.progName) a
    let hprog := mkApp hprogFn a
    let hh0 ← hnhOf c pl hP? b X off
    let hh1 ← hnhOf c pl hP? b X symOff
    let placeableTy := mkApp2 (Lean.mkConst ``PlacedLib.Placeable) c.libE pl
    let k (hP : Expr) (pre : Array Expr) : MetaM (Array Expr × Expr × Expr) := do
      let p0 := mkAppN (Lean.mkConst ``sepWP_rebase_b2bCall)
        #[c.libE, progE, pl, b, X, offE, symOffE, tOffE, r1E, r2E, hprog, hr, hkind, hnr,
          haddend, hsym, hnext2, hr2, hkind2, hplain2, haddend2, hsym2, hop, hop2, hh0, hh1, hP]
      let p ← forallBoundedTelescope (← inferType p0) (some 8) fun xs _ =>
        mkLambdaFVars xs (mkAppN p0 (xs ++ #[notWeak1, notWeak2]))
      return (#[], ← mkForallFVars pre (← inferType p), ← mkLambdaFVars pre p)
    match hP? with
    | some hP => k hP #[]
    | none => withLocalDeclD `hP placeableTy fun hP => k hP #[hP]
  return some r

private def fetchAt? (c : Ctx) (off : Nat) (pl : Expr) (hP? : Option Expr) (b X : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let offE := mkNatLit off
  let natTy := Lean.mkConst ``Nat
  let hal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy (mkNatLit 0)
  let hlen ← decideProp (← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[offE, mkNatLit 4],
    ← mkAppM ``HMul.hMul #[mkNatLit 4, c.nE]])
  let twoPow64 ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]
  let hlt ← decideProp (← mkAppM ``LT.lt #[offE, twoPow64])
  match c.relocMap.get? off with
  | none =>
    let (_, rhs?) ← ProofLib.GenDecodes.instrRhs? c.treeVal off
    let some rhs := rhs? | return none
    let inst := rhs.appArg!
    let hdec := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) ProofLib.GenDecodes.optInstr rhs
    let hnrNone ← relocAtNoneProof c offE
    let hnr ← mkAppM ``isNone_of_eq_none #[hnrNone]
    let hnh ← hnhOf c pl hP? b X off
    let prf := mkAppN (Lean.mkConst ``fetch_rebase_of_noReloc)
      #[c.libE, c.treeE, c.nE, c.hcodeE, c.hsizeE, offE, inst, hal, hlen, hlt, hdec, hnr,
        pl, b, X, hnh]
    return some (prf, rhs)
  | some (_, kn, symE, entryE) =>
    unless kn == ``RelocKind.call26 || kn == ``RelocKind.jump26 do return none
    let symStr ← symStringOf symE
    -- Only plain sites with addend `0`: a branch site is never part of a relaxable pair, so it
    -- is plain unless it is a branch-to-branch candidate (its target starts with a `jump26` `B`).
    if (← addendOf entryE) != 0 then
      logInfo m!"gen_placed_fetches: skipping branch at {off} (nonzero addend)"
      return none
    if let some symOff := c.symMap.get? symStr then
      if let some (_, kt, _, _) := c.relocMap.get? symOff then
        if kt == ``RelocKind.jump26 then
          logInfo m!"gen_placed_fetches: skipping branch-to-branch candidate at {off} → {symStr}"
          return none
    let hr ← relocAtSomeProof c offE entryE
    let hoff := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) natTy offE
    let haddend := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Int) (toExpr (0 : Int))
    let isCall := kn == ``RelocKind.call26
    let isCallE := toExpr isCall
    let kindE := Lean.mkConst kn
    let hkind := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``RelocKind) kindE
    match c.symMap.get? symStr with
    | some symOff =>
      let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal c.treeVal off
      let w : BitVec 32 := BitVec.ofNat 8 b3 ++ BitVec.ofNat 8 b2 ++ BitVec.ofNat 8 b1 ++
        BitVec.ofNat 8 b0
      let d : BitVec 64 := BitVec.ofNat 64 symOff - BitVec.ofNat 64 off
      let bw : BitVec 32 := (w &&& 0xfc000000#32) ||| ((d >>> 2).setWidth 32 &&& 0x03ffffff#32)
      let some i := Arm64.decode bw | return none
      let rhs ← ProofLib.GenDecodes.formatInstrRhs i
      let inst := rhs.appArg!
      let symOffE := mkNatLit symOff
      let hsym ← lookupSymProof c symStr symE (← mkAppM ``Option.some #[symOffE])
      let hb2b ← b2bNextIsNoneBlockProof c entryE hsym haddend symOff
      let some notWeakProof ← notWeakProof? c entryE | return none
      let hplain := mkAppN (Lean.mkConst ``plainSite_of_branch)
        #[c.textE, offE, entryE, isCallE, hal, hr, hoff, hkind, hb2b]
      let (wE, hw) ← wordAtProof c off
      let hdec := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) ProofLib.GenDecodes.optInstr rhs
      let hnh ← hnhOf c pl hP? b X off
      let prf := mkAppN (Lean.mkConst ``fetch_rebase_of_call26)
        #[c.libE, c.treeE, c.nE, c.hcodeE, c.hsizeE, offE, symOffE, entryE, inst,
          isCallE, hal, hlen, hlt, hr, hoff, hkind, hplain, haddend, hsym, wE, hw, hdec, pl, b, X, hnh,
          notWeakProof]
      return some (prf, rhs)
    | none =>
      let some hP := hP? | return none
      let eE := mkStrLit symStr
      let hsymE := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``String) eE
      let hsym ← lookupSymProof c symStr eE (← mkAppOptM ``Option.none #[Lean.mkConst ``Nat])
      let hb2b := mkAppN (Lean.mkConst ``b2bNext?_isNone_of_extern)
        #[c.textE, entryE, eE, hsymE, hsym]
      let some notWeakProof ← notWeakProof? c entryE | return none
      let hplain := mkAppN (Lean.mkConst ``plainSite_of_branch)
        #[c.textE, offE, entryE, isCallE, hal, hr, hoff, hkind, hb2b]
      let opE := if isCall then (0x94000000 : Nat) else 0x14000000
      let bv32 (k : Nat) := mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit k)
      let bv32Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 32)
      let (wE, hw) ← wordAtProof c off
      let hop := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) bv32Ty (bv32 opE)
      let hnh ← hnhOf c pl hP? b X off
      let prf := mkAppN (Lean.mkConst ``fetch_rebase_of_externBranch)
        #[c.libE, c.treeE, c.nE, c.hcodeE, c.hsizeE, offE, entryE, eE, isCallE, hal, hlen, hlt,
          hr, hoff, hkind, hplain, haddend, hsymE, hsym, wE, hw, hop, pl, b, X, hP, hnh, notWeakProof]
      let rho := mkApp2 (Lean.mkConst ``Placement.ρ) pl eE
      let stubE ← mkAppM ``HSub.hSub #[rho, mkApp (Lean.mkConst ``Placement.base) pl]
      let immE ← mkAppM ``HSub.hSub #[stubE, mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64)
        offE]
      let inst := mkApp (Lean.mkConst (if isCall then ``Arm64.Instr.bl else ``Arm64.Instr.b)) immE
      return some (prf, ← mkAppM ``Option.some #[inst])

@[command_elab genPlacedFetchesStx] def elabGenPlacedFetches : CommandElab := fun stx => do
  match stx with
  | `(gen_placed_fetches $prog:ident $lib:ident $tree:ident $hcode:ident $hsize:ident
        $[via_placement $plOf?:ident $hPOf?:ident]? [$rs:decodeRange,*]) =>
    let mut offs := #[]
    for r in rs.getElems do offs := offs ++ (← rangeOffsets r)
    let attrStx ← `(Lean.Parser.Term.attrInstance| simp)
    let attrStx2 ← `(Lean.Parser.Term.attrInstance| arm64_norm)
    liftTermElabM do
      let attrs ← elabAttrs #[attrStx, attrStx2]
      let progName ← realizeGlobalConstNoOverloadWithInfo prog
      let libName ← realizeGlobalConstNoOverloadWithInfo lib
      let treeName ← realizeGlobalConstNoOverloadWithInfo tree
      let hcodeName ← realizeGlobalConstNoOverloadWithInfo hcode
      let hsizeName ← realizeGlobalConstNoOverloadWithInfo hsize
      let viaPl ← match plOf?, hPOf? with
        | some p, some h => pure (some (Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo p),
            Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo h)))
        | _, _ => pure none
      let libE := Lean.mkConst libName
      let treeVal ← ProofLib.GenDecodes.treeValueOf treeName
      let hsizeTy ← inferType (Lean.mkConst hsizeName)
      let some (_, _, someN) := hsizeTy.eq? | throwError "gen_placed_fetches: bad {hsizeName}"
      let nE := someN.appArg!
      let n ← ProofLib.GenDecodes.natOf nE
      let progTy ← inferType (Lean.mkConst progName)
      let .forallE _ paramTy _ paramBi := progTy
        | throwError "gen_placed_fetches: {progName} must take one parameter"
      let env0 ← getEnv
      let textE := mkApp (Lean.mkConst ``PlacedLib.text) libE
      let (shRtNm, shRtEqNm, shRtWfNm) := sharedRelocTreeNames progName
      let sharedRtVal? : Option Expr :=
        match env0.find? shRtNm, env0.find? shRtEqNm with
        | some rtCi, some eqCi =>
          if rtCi.hasValue && env0.contains shRtWfNm &&
              eqCi.type.eq?.any (fun (_, lhs, _) =>
                lhs == mkApp (Lean.mkConst ``CodeBlock.relocs) textE) then
            rtCi.value?
          else none
        | _, _ => none
      let relocs ← match sharedRtVal? with
        | some rtV => collectRelocsFromTree rtV #[]
        | none => relocEntries libE
      let mut relocMap : Std.HashMap Nat (Nat × Name × Expr × Expr) := {}
      for entry in relocs do
        if !relocMap.contains entry.1 then
          relocMap := relocMap.insert entry.1 entry
      let sortedRelocOffs := (relocs.map (·.1)).qsort (· < ·)
      let (shXsNm, shEncNm, shHtblNm, shHeqNm) := sharedSymEncNames progName
      let sharedSymMap? : Option (Std.HashMap String Nat) :=
        match env0.find? shXsNm, env0.find? shEncNm, env0.find? shHtblNm with
        | some xsCi, some encCi, some htblCi =>
          if xsCi.hasValue && encCi.hasValue && env0.contains shHeqNm &&
              htblCi.type.eq?.any (fun (_, lhs, _) =>
                lhs == mkApp (Lean.mkConst ``CodeBlock.symbols) textE) then
            encCi.value?.bind extractSymMapFromEnc?
          else none
        | _, _, _ => none
      let (syms, symMap) ← match sharedSymMap? with
        | some sm => pure (#[], sm)
        | none =>
          let ss ← symbolOffsets libE
          let mut sm : Std.HashMap String Nat := {}
          for (s, o, _) in ss do
            if !sm.contains s then
              sm := sm.insert s o
          pure (ss, sm)
      let c : Ctx :=
        { progName := progName, libName := libName, libE := libE
          textE := textE
          treeE := Lean.mkConst treeName, treeVal := treeVal, nE := nE, n := n
          hcodeE := Lean.mkConst hcodeName, hsizeE := Lean.mkConst hsizeName
          relocs := relocs, relocMap := relocMap, syms := syms, symMap := symMap
          viaPl := viaPl, paramTy := paramTy, paramBi := paramBi
          hprogRef := ← IO.mkRef none, hextRef := ← IO.mkRef none
          rtRef := ← IO.mkRef none, symEncRef := ← IO.mkRef none
          symProofCache := ← IO.mkRef {} }
      let pfxStr := progName.getString!
      let progNs := progName.getPrefix
      for off in offs do
        if off + 4 > 4 * n then
          throwError "gen_placed_fetches: offset {off} is out of bounds"
      let mut chunks : Array (Nat × Nat) := #[]
      let mut offChunkIdx : Std.HashMap Nat Nat := {}
      let mut curChunk? : Option (Nat × Nat × Nat) := none
      for off in offs do
        if c.relocMap.contains off then
          if let some (lo, hi, _) := curChunk? then
            chunks := chunks.push (lo, hi)
            curChunk? := none
        else
          match curChunk? with
          | none =>
            offChunkIdx := offChunkIdx.insert off chunks.size
            curChunk? := some (off, off, 1)
          | some (lo, hi, cnt) =>
            if lo ≤ off && cnt < 64 && !hasRelocIn sortedRelocOffs lo off then
              offChunkIdx := offChunkIdx.insert off chunks.size
              curChunk? := some (lo, Nat.max hi off, cnt + 1)
            else
              chunks := chunks.push (lo, hi)
              offChunkIdx := offChunkIdx.insert off chunks.size
              curChunk? := some (off, off, 1)
      if let some (lo, hi, _) := curChunk? then
        chunks := chunks.push (lo, hi)
      let reflBoolTrue := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero])
        (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)
      let paramLvl ← getLevel paramTy
      let mut chunkThms : Array Name := #[]
      if !chunks.isEmpty then
        let hprogE ← getHProg c
        let (rtE, hrelocsE, hwfE) ← getRelocTree c
        let viaLams? := viaPl.map fun (plOf, hPOf) =>
          (Expr.lam `a paramTy (mkApp plOf (.bvar 0)) .default,
           Expr.lam `a paramTy (mkApp hPOf (.bvar 0)) .default)
        let hextE? ← if viaPl.isNone then some <$> getHExt c else pure none
        for h : ci in [0:chunks.size] do
          let (lo, hi) := chunks[ci]
          let chunkNm ← mkPrivHelperName progNs pfxStr s!"chunk_{ci}"
          let chunkVal := match viaLams?, hextE? with
            | some (plOfLam, hPOfLam), _ =>
              mkAppN (Lean.mkConst ``fetch_rebase_of_chunk_placeable_tree [paramLvl])
                #[paramTy, Lean.mkConst progName, plOfLam, c.libE, c.treeE, c.nE, rtE,
                  mkNatLit lo, mkNatLit hi, hprogE, hPOfLam, c.hcodeE, c.hsizeE, hrelocsE, hwfE,
                  reflBoolTrue, reflBoolTrue]
            | none, some hextE =>
              mkAppN (Lean.mkConst ``fetch_rebase_of_chunk_noExterns_tree)
                #[Lean.mkConst progName, c.libE, c.treeE, c.nE, rtE,
                  mkNatLit lo, mkNatLit hi, hprogE, c.hcodeE, c.hsizeE, hextE, hrelocsE, hwfE,
                  reflBoolTrue, reflBoolTrue]
            | none, none => unreachable!
          let chunkTy ← inferType chunkVal
          addDecl (.thmDecl { name := chunkNm, levelParams := [], type := chunkTy, value := chunkVal })
          chunkThms := chunkThms.push chunkNm
      let bv64 := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
      let hookTy ← mkArrow (Lean.mkConst ``String)
        (mkApp (Lean.mkConst ``Option [.zero])
          (← mkArrow (Lean.mkConst ``Arm64.State) (Lean.mkConst ``Arm64.State)))
      let haddBv64 ← withLocalDeclD `b bv64 fun b => do
        return (← mkAppM ``HAdd.hAdd #[b, b]).appFn!.appFn!
      let noOvr ← withLocalDeclD `x (Lean.mkConst ``String) fun x => do
        mkLambdaFVars #[x] (← mkAppOptM ``Option.none
          #[← mkArrow (Lean.mkConst ``Arm64.State) (Lean.mkConst ``Arm64.State)])
      for off in offs do
        if let some (_, kn, _, _) := c.relocMap.get? off then
          if kn == ``RelocKind.adrpHi21 then
            if let some (pTy, pPrf) ← pairStepLemma? c off then
              ProofLib.GenDecodes.addThm (progNs ++ hexName pfxStr "pairStep" off) pTy pPrf
              continue
          if kn == ``RelocKind.call26 then
            if let some (pTy, pPrf) ← callStepLemma? c off then
              ProofLib.GenDecodes.addThm (progNs ++ hexName pfxStr "callStep" off) pTy pPrf
              continue
          let (rTy, rPrf) ← withParams c fun a pl hP? b X => do
            let some (p, rhs) ← fetchAt? c off pl hP? b X
              | return (#[], Lean.mkConst ``True, Lean.mkConst ``True.intro)
            let pTy ← inferType p
            let some (_, lhs, _) := pTy.eq? | throwError "gen_placed_fetches: bad proof type"
            let pc := lhs.appArg!
            let progA := mkApp (Lean.mkConst progName) a
            let progPl ← programE c.libE pl
            let progR := mkAppN (Lean.mkConst ``Program.rebase) #[progA, b, X, noOvr]
            let ty ← mkEq (mkApp2 (Lean.mkConst ``Program.fetch) progR pc) rhs
            let hprogFn ← getHProg c
            let prf := mkAppN (Lean.mkConst ``fetch_rebase_congr_prog)
              #[progA, progPl, b, pc, X, rhs, mkApp hprogFn a, p]
            return (#[], ty, prf)
          if rTy.getForallBody.isConstOf ``True then continue
          let rName := progNs ++ hexName pfxStr "rebase_fetch" off
          ProofLib.GenDecodes.addThm rName rTy rPrf
          for a in attrs do Term.applyAttributes rName #[a]
          if off == 0 then
            let (bTy, bPrf) ← withParams c fun a _ _ b X => do
              let p ← mkAppM ``fetch_rebase_base_of_zero #[mkAppN (Lean.mkConst rName) #[a, b, X]]
              return (#[], ← inferType p, p)
            let bName := progNs ++ Name.mkSimple s!"{pfxStr}_rebase_fetch_base"
            ProofLib.GenDecodes.addThm bName bTy bPrf
            for a in attrs do Term.applyAttributes bName #[a]
        else
          let (_, rhs?) ← ProofLib.GenDecodes.instrRhs? c.treeVal off
          let some rhs := rhs? | continue
          let inst := rhs.appArg!
          let offE := mkNatLit off
          let hdec := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) ProofLib.GenDecodes.optInstr rhs
          let chunkNm := chunkThms[offChunkIdx.get! off]!
          let corePrf := mkApp4 (Lean.mkConst chunkNm) offE inst reflBoolTrue hdec
          let rPrf :=
            if paramBi == .default then corePrf
            else Expr.lam `a paramTy (mkApp corePrf (.bvar 0)) paramBi
          let pc := mkApp2 haddBv64 (.bvar 1) (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) offE)
          let progR := mkApp4 (Lean.mkConst ``Program.rebase)
            (mkApp (Lean.mkConst progName) (.bvar 2)) (.bvar 1) (.bvar 0) noOvr
          let eqBody := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) ProofLib.GenDecodes.optInstr
            (mkApp2 (Lean.mkConst ``Program.fetch) progR pc) rhs
          let rTy := Expr.forallE `a paramTy
            (Expr.forallE `b bv64 (Expr.forallE `X hookTy eqBody .default) .default) paramBi
          let rName := progNs ++ hexName pfxStr "rebase_fetch" off
          ProofLib.GenDecodes.addThm rName rTy rPrf
          for a in attrs do Term.applyAttributes rName #[a]
          if off == 0 then
            let (bTy, bPrf) ← withParams c fun a _ _ b X => do
              let p ← mkAppM ``fetch_rebase_base_of_zero #[mkAppN (Lean.mkConst rName) #[a, b, X]]
              return (#[], ← inferType p, p)
            let bName := progNs ++ Name.mkSimple s!"{pfxStr}_rebase_fetch_base"
            ProofLib.GenDecodes.addThm bName bTy bPrf
            for a in attrs do Term.applyAttributes bName #[a]
  | _ => throwUnsupportedSyntax

/-- `gen_placed_fnOffs P lib syms hsyms hfresh`, where `P : (a : A) → Program` has
    `(P a).symbols ≡ lib.text.symbols`, `hsyms : lib.text.symbols = toStringSymbols syms` and
    `hfresh : allFreshCharSymbols syms = true`, elaborates
    `@[simp, arm64_norm] P_fnOff_0x<off> a : (P a).fnOff "<name>" = <off>` for each block
    symbol (suffix `_<k>` for a second symbol at the same offset), and registers each symbol in
    `fnEntryExt` (placed mode, size up to the next symbol, `0` for the last one) so that
    `wp_entry "<name>"` works on `(P a).rebase b H`. -/
syntax (name := genPlacedFnOffsStx)
  "gen_placed_fnOffs " ident ident ident ident ident : command

@[command_elab genPlacedFnOffsStx] def elabGenPlacedFnOffs : CommandElab := fun stx => do
  match stx with
  | `(gen_placed_fnOffs $prog:ident $lib:ident $syms:ident $hsyms:ident $hfresh:ident) =>
    let attrStx ← `(Lean.Parser.Term.attrInstance| simp)
    let attrStx2 ← `(Lean.Parser.Term.attrInstance| arm64_norm)
    let scope ← getScope
    liftTermElabM do
      let attrs ← elabAttrs #[attrStx, attrStx2]
      let progName ← realizeGlobalConstNoOverloadWithInfo prog
      let libName ← realizeGlobalConstNoOverloadWithInfo lib
      let symsE := Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo syms)
      let hsymsE := Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo hsyms)
      let hfreshE := Lean.mkConst (← realizeGlobalConstNoOverloadWithInfo hfresh)
      let progTy ← inferType (Lean.mkConst progName)
      let .forallE _ paramTy _ paramBi := progTy
        | throwError "gen_placed_fnOffs: {progName} must take one parameter"
      let charElems ← ProofLib.ProgramReflection.listElemsWhnf symsE
      let parsedEntries ← charElems.mapM fun e => do
        let e ← whnfAll e
        unless e.isAppOfArity ``Prod.mk 4 do throwError "gen_placed_fnOffs: bad char-symbol entry {e}"
        let csE := e.getArg! 2
        let offE := e.getArg! 3
        let name ← charListStringOf csE
        let off ← ProofLib.GenDecodes.natOf offE
        return (csE, offE, name, off)
      let entries := parsedEntries.map fun (_, _, name, off) => (name, off)
      let pfxStr := progName.getString!
      let progNs := progName.getPrefix
      if !parsedEntries.isEmpty then
        let paramLvl ← getLevel paramTy
        let hsymsAllNm ← mkPrivHelperName progNs pfxStr "hsyms_fnOff"
        let (hsymsAllTy, hsymsAllVal) ← withLocalDecl `a .default paramTy fun a => do
          let progE := mkApp (Lean.mkConst progName) a
          let symsOf := mkApp (Lean.mkConst ``Program.symbols) progE
          let eqTy ← mkEq symsOf (mkApp (Lean.mkConst ``toStringSymbols) symsE)
          let prf ← mkExpectedTypeHint hsymsE eqTy
          return (← mkForallFVars #[a] eqTy, ← mkLambdaFVars #[a] prf)
        addDecl (.thmDecl { name := hsymsAllNm, levelParams := [], type := hsymsAllTy, value := hsymsAllVal })
        let natTy := Lean.mkConst ``Nat
        let strTy := Lean.mkConst ``String
        let charListTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Char)
        let charPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) charListTy natTy
        let charListListTy := mkApp (Lean.mkConst ``List [.zero]) charPairTy
        let optCharPairTy := mkApp (Lean.mkConst ``Option [.zero]) charPairTy
        let optNatTy := mkApp (Lean.mkConst ``Option [.zero]) natTy
        let vecNm ← mkPrivHelperName progNs pfxStr "symVec"
        let vecVal := buildCharSymVecExpr (parsedEntries.map fun (csE, offE, _, _) => (csE, offE))
        addDecl (.defnDecl {
          name := vecNm, levelParams := [], type := Lean.mkConst ``CharSymVec, value := vecVal,
          hints := .abbrev, safety := .safe
        })
        let vecE := Lean.mkConst vecNm
        let hvecNm ← mkPrivHelperName progNs pfxStr "hvec_fnOff"
        let hvecTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) charListListTy symsE
          (mkApp (Lean.mkConst ``CharSymVec.toList) vecE)
        let hvecVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) charListListTy symsE
        addDecl (.thmDecl { name := hvecNm, levelParams := [], type := hvecTy, value := hvecVal })
        let hsizeNm ← mkPrivHelperName progNs pfxStr "hvec_size_fnOff"
        let nSymsE := mkNatLit parsedEntries.size
        let someNSymsE := mkApp2 (Lean.mkConst ``Option.some [.zero]) natTy nSymsE
        let hsizeTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) optNatTy
          (mkApp (Lean.mkConst ``CharSymVec.checkSize?) vecE) someNSymsE
        let hsizeVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optNatTy someNSymsE
        addDecl (.thmDecl { name := hsizeNm, levelParams := [], type := hsizeTy, value := hsizeVal })
        let mut seen : Std.HashMap Nat Nat := {}
        for h : k in [0:parsedEntries.size] do
          let (csE, _, name, off) := parsedEntries[k]
          let dup := seen.getD off 0
          seen := seen.insert off (dup + 1)
          let base := hexName pfxStr "fnOff" off
          let thmName := progNs ++ (if dup == 0 then base else base.appendAfter s!"_{dup}")
          let nameE := mkStrLit name
          let offE := mkNatLit off
          let somePairE := mkApp2 (Lean.mkConst ``Option.some [.zero]) charPairTy
            (mkApp4 (Lean.mkConst ``Prod.mk [.zero, .zero]) charListTy natTy csE offE)
          let hname := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strTy nameE
          let hk := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) optCharPairTy somePairE
          let corePrf := mkAppN (Lean.mkConst ``placed_fnOff_of_allFresh_vec [paramLvl])
            #[paramTy, Lean.mkConst progName, symsE, vecE, nSymsE,
              Lean.mkConst hsymsAllNm, hfreshE, Lean.mkConst hvecNm, Lean.mkConst hsizeNm,
              mkNatLit k, nameE, csE, offE, hname, hk]
          let prf :=
            if paramBi == .default then corePrf
            else Expr.lam `a paramTy (mkApp corePrf (.bvar 0)) paramBi
          let eqBody := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) natTy
            (mkApp2 (Lean.mkConst ``Program.fnOff) (mkApp (Lean.mkConst progName) (.bvar 0)) nameE) offE
          let ty := Expr.forallE `a paramTy eqBody paramBi
          ProofLib.GenDecodes.addThm thmName ty prf
          for attr in attrs do Term.applyAttributes thmName #[attr]
          let nextOff? := (entries.filter (·.2 > off)).foldl (init := none) fun acc (_, o) =>
            match acc with
            | some m => some (min m o)
            | none => some o
          modifyEnv fun env => fnEntryExt.addEntry env {
            sym := name, codeConst := progName, decPrefix := progName, fnOffLemma := thmName,
            off, sizeBytes := nextOff?.elim 0 (· - off), placed := true }
      let isPub := !(← getEnv).header.isModule || scope.isPublic
      if isPub then
        withExporting (isExporting := true) do
          let libE := Lean.mkConst libName
          let textE := mkApp (Lean.mkConst ``PlacedLib.text) libE
          let (shXsNm, shEncNm, shHtblNm, shHeqNm) := sharedSymEncNames progName
          if !(← getEnv).contains shXsNm then
            let natTy := Lean.mkConst ``Nat
            let strTy := Lean.mkConst ``String
            let charListTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Char)
            let charPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) charListTy natTy
            let xsTy := mkApp (Lean.mkConst ``List [.zero]) charPairTy
            let strPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) strTy natTy
            let strListTy := mkApp (Lean.mkConst ``List [.zero]) strPairTy
            let symsLhs := mkApp (Lean.mkConst ``CodeBlock.symbols) textE
            let symsRhs := mkApp (Lean.mkConst ``toStringSymbols) symsE
            let targetHtblTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) strListTy symsLhs symsRhs
            let hsymsMatches ← try isDefEq (← inferType hsymsE) targetHtblTy catch _ => pure false
            if hsymsMatches then
              let natListTy := mkApp (Lean.mkConst ``List [.zero]) natTy
              let encKeyTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natListTy
              let encEntryTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) encKeyTy natTy
              let encEntryMk := mkApp2 (Lean.mkConst ``Prod.mk [.zero, .zero]) encKeyTy natTy
              let encTy := mkApp (Lean.mkConst ``ProofLib.ObjectLoad.EncSymTable) natTy
              let encElems := parsedEntries.map fun (_, _, s, off) =>
                let ekE := toExpr (s.length, s.toList.map (fun ch => ch.val.toNat))
                mkApp2 encEntryMk ekE (mkNatLit off)
              let encVal := buildListExpr0 encEntryTy encElems
              addDecl (.defnDecl {
                name := shXsNm, levelParams := [], type := xsTy, value := symsE,
                hints := .abbrev, safety := .safe
              })
              addDecl (.defnDecl {
                name := shEncNm, levelParams := [], type := encTy, value := encVal,
                hints := .abbrev, safety := .safe
              })
              let shXsE := Lean.mkConst shXsNm
              let shEncE := Lean.mkConst shEncNm
              let htblTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) strListTy symsLhs
                (mkApp (Lean.mkConst ``toStringSymbols) shXsE)
              addDecl (.thmDecl { name := shHtblNm, levelParams := [], type := htblTy, value := hsymsE })
              let prepLhs := mkApp2 (Lean.mkConst ``ProofLib.ObjectLoad.prepareCharAssocVal) natTy shXsE
              let heqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) encTy prepLhs shEncE
              let heqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) encTy shEncE
              addDecl (.thmDecl { name := shHeqNm, levelParams := [], type := heqTy, value := heqVal })
          let (shRtNm, shRtEqNm, shRtWfNm) := sharedRelocTreeNames progName
          let envCur ← getEnv
          let isDirectPlacedLib :=
            match envCur.find? libName with
            | some ci => match ci.value? with
              | some v => v.isAppOf ``PlacedLib.mk ||
                  (v.constName?.bind envCur.find? |>.bind (·.value?) |>.any (·.isAppOf ``PlacedLib.mk))
              | none => false
            | none => false
          if isDirectPlacedLib && !envCur.contains shRtNm then
            let relocs ← relocEntries libE
            let rtVal := buildRelocTreeExpr relocs
            addDecl (.defnDecl {
              name := shRtNm, levelParams := [], type := Lean.mkConst ``RelocTree, value := rtVal,
              hints := .abbrev, safety := .safe
            })
            let shRtE := Lean.mkConst shRtNm
            let listTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``RelocEntry)
            let lhsEq := mkApp (Lean.mkConst ``CodeBlock.relocs) textE
            let rhsEq := mkApp (Lean.mkConst ``RelocTree.toList) shRtE
            let eqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) listTy lhsEq rhsEq
            let eqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) listTy lhsEq
            addDecl (.thmDecl { name := shRtEqNm, levelParams := [], type := eqTy, value := eqVal })
            let boolTy := Lean.mkConst ``Bool
            let trueE := Lean.mkConst ``Bool.true
            let wfTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) boolTy
              (mkApp (Lean.mkConst ``RelocTree.wf) shRtE) trueE
            let wfVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) boolTy trueE
            addDecl (.thmDecl { name := shRtWfNm, levelParams := [], type := wfTy, value := wfVal })
  | _ => throwUnsupportedSyntax

private def parseRelocEntriesForInterned (listE : Expr) :
    MetaM (Array (Expr × Expr × String × Expr × Expr)) := do
  let elems ← ProofLib.ProgramReflection.listElemsWhnf listE
  elems.mapM fun r => do
    let r ← if r.isAppOfArity ``RelocEntry.mk 5 then pure r else whnfAll r
    unless r.isAppOfArity ``RelocEntry.mk 5 do
      throwError "gen_interned_lib: bad RelocEntry {r}"
    return (r.getArg! 0, r.getArg! 1, ← symStringOf (r.getArg! 2), r.getArg! 3, r.getArg! 4)

/-- `gen_interned_lib <pfx> <lib> <base> <extBase> <dataBase>` elaborates `<pfx>_lib :
    Obj.Interned.Lib`, `<pfx>_nameChars : List (List Char)`, `<pfx>_layout : Obj.Interned.Layout`,
    `<pfx>_lib_eq : <lib> = <pfx>_lib.toLib`, and `<pfx>_names_eq : <pfx>_lib.names =
    <pfx>_nameChars.map String.ofList`, reusing `<lib>`'s code and data byte constants without
    unfolding so `Obj.Interned.checkPlaceableExt` checks placeability and extern distinctness in
    logarithmic symbol-resolution time. -/
syntax (name := genInternedLibStx)
  "gen_interned_lib " ident ident num num num : command

@[command_elab genInternedLibStx] def elabGenInternedLib : CommandElab := fun stx => do
  match stx with
  | `(gen_interned_lib $pfx:ident $lib:ident $base:num $extBase:num $dataBase:num) =>
    liftTermElabM do
      let curNs ← getCurrNamespace
      let pfxStr := pfx.getId.toString
      let libName ← realizeGlobalConstNoOverloadWithInfo lib
      let libE := Lean.mkConst libName
      let baseNat := base.getNat
      let extBaseNat := extBase.getNat
      let dataBaseNat := dataBase.getNat
      let libWhnf ← whnfAll libE
      unless libWhnf.isAppOfArity ``PlacedLib.mk 4 do
        throwError "gen_interned_lib: cannot unfold {libName} to PlacedLib.mk"
      let nameE := libWhnf.getArg! 0
      let textE := libWhnf.getArg! 1
      let dataListE := libWhnf.getArg! 2
      let exportsListE := libWhnf.getArg! 3
      let textWhnf ← whnfAll textE
      unless textWhnf.isAppOfArity ``CodeBlock.mk 6 do
        throwError "gen_interned_lib: cannot unfold {libName}.text to CodeBlock.mk"
      unless (← whnfAll (textWhnf.getArg! 5)).isAppOf ``List.nil do
        throwError "gen_interned_lib: {libName}.text has weak references (unsupported)"
      let codeE := textWhnf.getArg! 0
      let alignE := textWhnf.getArg! 1
      let symbolsListE := textWhnf.getArg! 2
      let relocsListE := textWhnf.getArg! 3
      let externsListE := textWhnf.getArg! 4
      let symElems ← ProofLib.ProgramReflection.listElemsWhnf symbolsListE
      let parsedSyms ← symElems.mapM fun e => do
        let e ← if e.isAppOfArity ``Prod.mk 4 then pure e else whnfAll e
        unless e.isAppOfArity ``Prod.mk 4 do
          throwError "gen_interned_lib: bad symbol entry {e}"
        return (← symStringOf (e.getArg! 2), e.getArg! 3)
      let textRelocs ← parseRelocEntriesForInterned relocsListE
      let externs ← (← ProofLib.ProgramReflection.listElemsWhnf externsListE).mapM (m := MetaM) symStringOf
      let exports ← (← ProofLib.ProgramReflection.listElemsWhnf exportsListE).mapM (m := MetaM) symStringOf
      let dataElems ← ProofLib.ProgramReflection.listElemsWhnf dataListE
      let parsedData ← dataElems.mapM fun d => do
        let d ← if d.isAppOfArity ``SymDataInfo.mk 6 then pure d else whnfAll d
        unless d.isAppOfArity ``SymDataInfo.mk 6 do
          throwError "gen_interned_lib: bad SymDataInfo {d}"
        let dSym ← symStringOf (d.getArg! 0)
        let dAlignE := d.getArg! 1
        let dAlign ← ProofLib.GenDecodes.natOf dAlignE
        let dRoE := d.getArg! 2
        let dBytesE := d.getArg! 3
        let dBytesLen := (← ProofLib.ProgramReflection.listElemsWhnf dBytesE).size
        let dZeroTailE := d.getArg! 4
        let dZeroTail ← ProofLib.GenDecodes.natOf dZeroTailE
        let dRelocs ← parseRelocEntriesForInterned (d.getArg! 5)
        return (dSym, dAlignE, dAlign, dRoE, dBytesE, dBytesLen, dZeroTailE, dZeroTail, dRelocs)
      let mut nameSet : Std.HashSet String := {}
      for (s, _) in parsedSyms do nameSet := nameSet.insert s
      for (_, _, s, _, _) in textRelocs do nameSet := nameSet.insert s
      for s in externs do nameSet := nameSet.insert s
      for s in exports do nameSet := nameSet.insert s
      for (dSym, _, _, _, _, _, _, _, dRelocs) in parsedData do
        nameSet := nameSet.insert dSym
        for (_, _, rs, _, _) in dRelocs do nameSet := nameSet.insert rs
      let sortedNames := nameSet.toArray.qsort fun a b =>
        ProofLib.ProgramReflection.charListLt a.toList b.toList
      let mut nameIdx : Std.HashMap String Nat := {}
      for h : i in [0 : sortedNames.size] do
        nameIdx := nameIdx.insert sortedNames[i] i
      let mut extAddrMap : Std.HashMap String Nat := {}
      for h : k in [0 : externs.size] do
        let e := externs[k]
        if !extAddrMap.contains e then
          extAddrMap := extAddrMap.insert e (extBaseNat + 64 * k)
      let mut dataAddrMap : Std.HashMap String Nat := {}
      let mut curData := dataBaseNat
      for (dSym, _, dAlign, _, _, dBytesLen, _, dZeroTail, _) in parsedData do
        let al := Nat.max dAlign 8
        curData := ((curData + al - 1) / al) * al
        dataAddrMap := dataAddrMap.insert dSym curData
        curData := curData + Nat.max (dBytesLen + dZeroTail) 8
      let natTy := Lean.mkConst ``Nat
      let strTy := Lean.mkConst ``String
      let charListTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``Char)
      let nameCharsTy := mkApp (Lean.mkConst ``List [.zero]) charListTy
      let strListTy := mkApp (Lean.mkConst ``List [.zero]) strTy
      let bv64Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
      let natPairTy := mkApp2 (Lean.mkConst ``Prod [.zero, .zero]) natTy natTy
      let natPairMk := mkApp2 (Lean.mkConst ``Prod.mk [.zero, .zero]) natTy natTy
      let iRelocTy := Lean.mkConst ``Arm64.Obj.Interned.Reloc
      let iRelocMk := Lean.mkConst ``Arm64.Obj.Interned.Reloc.mk
      let iDataTy := Lean.mkConst ``Arm64.Obj.Interned.Data
      let iDataMk := Lean.mkConst ``Arm64.Obj.Interned.Data.mk
      let mkIRelocs (rs : Array (Expr × Expr × String × Expr × Expr)) : Expr :=
        buildListExpr0 iRelocTy (rs.map fun (offE, kindE, s, addE, locE) =>
          mkApp5 iRelocMk offE kindE (mkRawNatLit (nameIdx.get! s)) addE locE)
      let nameCharsVal := buildListExpr0 charListTy (sortedNames.map fun s => toExpr s.toList)
      let namesVal := buildListExpr0 strTy (sortedNames.map mkStrLit)
      let iSymsVal := buildListExpr0 natPairTy (parsedSyms.map fun (s, offE) =>
        mkApp2 natPairMk (mkRawNatLit (nameIdx.get! s)) offE)
      let iRelocsVal := mkIRelocs textRelocs
      let iExternsVal := buildListExpr0 natTy (externs.map fun s => mkRawNatLit (nameIdx.get! s))
      let iExportsVal := buildListExpr0 natTy (exports.map fun s => mkRawNatLit (nameIdx.get! s))
      let iDataVal := buildListExpr0 iDataTy (parsedData.map fun
        (dSym, dAlignE, _, dRoE, dBytesE, _, dZeroTailE, _, dRelocs) =>
          mkAppN iDataMk #[mkRawNatLit (nameIdx.get! dSym), dAlignE, dRoE, dBytesE, dZeroTailE,
            mkIRelocs dRelocs])
      let addrsVal := buildListExpr0 bv64Ty (sortedNames.map fun nm =>
        let a := match extAddrMap.get? nm with
          | some x => x
          | none => (dataAddrMap.get? nm).getD 0
        mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit a))
      let nameCharsNm := curNs ++ Name.mkSimple s!"{pfxStr}_nameChars"
      let iLibNm := curNs ++ Name.mkSimple s!"{pfxStr}_lib"
      let iLayoutNm := curNs ++ Name.mkSimple s!"{pfxStr}_layout"
      let libEqNm := curNs ++ Name.mkSimple s!"{pfxStr}_lib_eq"
      let namesEqNm := curNs ++ Name.mkSimple s!"{pfxStr}_names_eq"
      addAndCompile (.defnDecl {
        name := nameCharsNm, levelParams := [], type := nameCharsTy, value := nameCharsVal,
        hints := .abbrev, safety := .safe
      })
      let iLibVal := mkAppN (Lean.mkConst ``Arm64.Obj.Interned.Lib.mk)
        #[nameE, namesVal, codeE, alignE, iSymsVal, iRelocsVal, iExternsVal, buildListExpr0 natTy #[],
          iDataVal, iExportsVal]
      addAndCompile (.defnDecl {
        name := iLibNm, levelParams := [], type := Lean.mkConst ``Arm64.Obj.Interned.Lib,
        value := iLibVal, hints := .abbrev, safety := .safe
      })
      let nilNatE := buildListExpr0 natTy #[]
      let iLayoutVal := mkApp5 (Lean.mkConst ``Arm64.Obj.Interned.Layout.mk)
        (mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit baseNat))
        addrsVal nilNatE nilNatE nilNatE
      addAndCompile (.defnDecl {
        name := iLayoutNm, levelParams := [], type := Lean.mkConst ``Arm64.Obj.Interned.Layout,
        value := iLayoutVal, hints := .abbrev, safety := .safe
      })
      let iLibE := Lean.mkConst iLibNm
      let nameCharsE := Lean.mkConst nameCharsNm
      let placedLibTy := Lean.mkConst ``PlacedLib
      let toLibRhs := mkApp (Lean.mkConst ``Arm64.Obj.Interned.Lib.toLib) iLibE
      let libEqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) placedLibTy libE toLibRhs
      let libEqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) placedLibTy libE
      addDecl (.thmDecl { name := libEqNm, levelParams := [], type := libEqTy, value := libEqVal })
      let namesLhs := mkApp (Lean.mkConst ``Arm64.Obj.Interned.Lib.names) iLibE
      let mapRhs ← mkAppM ``List.map #[Lean.mkConst ``String.ofList, nameCharsE]
      let namesEqTy := mkApp3 (Lean.mkConst ``Eq [.succ .zero]) strListTy namesLhs mapRhs
      let namesEqVal := mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) strListTy namesLhs
      addDecl (.thmDecl { name := namesEqNm, levelParams := [], type := namesEqTy, value := namesEqVal })
  | _ => throwUnsupportedSyntax


/-- `gen_block_fetches <pfx> <N> <mlib> <Cls> <n> [rebase] [rho] [sub] [irreducible] [ranges]?`
    elaborates the per-block boilerplate for block `N` of a multi-block placed library
    `mlib : MultiPlacedLib`, for a class `Cls` with field `placeable : mlib.Placeable <pfx>Mpl`
    and an existing `<pfx>Mpl [Cls] : MultiPlacement` (normally `abbrev <pfx>Mpl := Cls.mpl`).
    The numeral `N` is used verbatim in names (`00` gives `<pfx>Lib00`) and as the block index.
    With `n` the block's word count it emits
    - `<pfx>LibN := mlib.blockLib N`, `<pfx>PlN [Cls] := mlib.blockPlacement <pfx>Mpl N`,
      `<pfx>PlaceableN [Cls]`, `<pfx>PCN [Cls] := <pfx>LibN.program <pfx>PlN`;
    - `<pfx>ProgN`, `<pfx>TreeN := word_tree_of% <pfx>ProgN`, `<pfx>N_code_eq` and
      `<pfx>N_tree_size : <pfx>TreeN.checkSize? = some n` (both `rfl_kernel`);
    - `gen_placed_fetches <pfx>PCN ... via_placement <pfx>PlN <pfx>PlaceableN [ranges]`, with
      `ranges` defaulting to the whole block `[0x0 -> 4 * (n - 1)]`;
    - with `rebase`: `<pfx>PCN_rebase` (block program rebased at `<pfx>Mpl.base N` equals
      `<pfx>PCN` rebased at `<pfx>PlN.base`) and `<pfx>PlN_base`, both `rfl`;
    - with `rho`: `<pfx>PlN_rho sym : mlib.resolve <pfx>Mpl sym = <pfx>PlN.ρ sym`;
    - with `sub`: `<pfx>PCN_sub`, moving a `subroutine_ok` contract from
      `mlib.blockProgram <pfx>Mpl N` onto `<pfx>PCN.rebase <pfx>PlN.base (fun _ => none)`;
    - with `irreducible`: `attribute [irreducible] <pfx>PlN` (after the lemmas above). -/
syntax (name := genBlockFetchesStx)
  "gen_block_fetches " ident num ident ident num (&" rebase")? (&" rho")? (&" sub")?
    (&" irreducible")? (" [" decodeRange,* "]")? : command

@[command_elab genBlockFetchesStx] def elabGenBlockFetches : CommandElab := fun stx => do
  let pfx : Ident := ⟨stx[1]⟩
  let blkNum : NumLit := ⟨stx[2]⟩
  let mlib : Ident := ⟨stx[3]⟩
  let cls : Ident := ⟨stx[4]⟩
  let nLit : NumLit := ⟨stx[5]⟩
  let (rebase, rho, sub, irr) :=
    (!stx[6].isNone, !stx[7].isNone, !stx[8].isNone, !stx[9].isNone)
  let sfx := blkNum.raw[0].getAtomVal
  unless !sfx.isEmpty && sfx.all Char.isDigit do
    throwErrorAt blkNum "gen_block_fetches: expected a decimal block index, got {sfx}"
  let i := blkNum.getNat
  let n := nLit.getNat
  if n == 0 then throwErrorAt nLit "gen_block_fetches: the word count must be positive"
  let .str .anonymous p := pfx.getId
    | throwErrorAt pfx "gen_block_fetches: the prefix must be an atomic identifier"
  let mk (s : String) : Ident := mkIdentFrom pfx (Name.mkSimple s)
  let mplId := mk s!"{p}Mpl"
  discard <| liftCoreM <| realizeGlobalConstNoOverload mplId
  let clsName ← liftCoreM <| realizeGlobalConstNoOverload cls
  let clsPlaceable : Ident := mkIdentFrom cls (clsName ++ `placeable)
  let libT : Term := mlib
  let clsT : Term := cls
  let mplT : Term := mplId
  let blockLibF : Ident := mkIdentFrom mlib (mlib.getId ++ `blockLib)
  let blockPlF : Ident := mkIdentFrom mlib (mlib.getId ++ `blockPlacement)
  let placeableF : Ident := mkIdentFrom mlib (mlib.getId ++ `placeable_blockLib)
  let blockProgF : Ident := mkIdentFrom mlib (mlib.getId ++ `blockProgram)
  let resolveF : Ident := mkIdentFrom mlib (mlib.getId ++ `resolve)
  let iT : Term := Syntax.mkNumLit (toString i)
  let nT : Term := Syntax.mkNumLit (toString n)
  let (lib, pl, plc, pc) := (mk s!"{p}Lib{sfx}", mk s!"{p}Pl{sfx}", mk s!"{p}Placeable{sfx}",
    mk s!"{p}PC{sfx}")
  let (prog, tree) := (mk s!"{p}Prog{sfx}", mk s!"{p}Tree{sfx}")
  let (codeEq, treeSize) := (mk s!"{p}{sfx}_code_eq", mk s!"{p}{sfx}_tree_size")
  let (libT', plT, pcT, progT, treeT) :=
    ((lib : Term), (pl : Term), (pc : Term), (prog : Term), (tree : Term))
  let ranges : Array (TSyntax `decodeRange) ←
    if stx[10].isNone then
      let hi := Syntax.mkNumLit s!"0x{String.ofList (Nat.toDigits 16 (4 * (n - 1)))}"
      pure #[← `(decodeRange| 0x0 → $hi:num)]
    else pure (stx[10][1].getSepArgs.map (⟨·⟩))
  let rangesSep : Syntax.TSepArray `decodeRange "," := Syntax.TSepArray.ofElems ranges
  let mut cmds : Array (TSyntax `command) := #[
    ← `(def $lib : PlacedLib := $blockLibF $iT),
    ← `(def $pl [$clsT] : Placement := $blockPlF $mplT $iT),
    ← `(theorem $plc [$clsT] : ($libT').Placeable $plT :=
          $placeableF (by decide) $clsPlaceable),
    ← `(def $pc [$clsT] : Program := ($libT').program $plT),
    ← `(def $prog : Program := { code := ($libT').text.code, symbols := ($libT').text.symbols }),
    ← `(def $tree : WordTree := word_tree_of% $prog),
    ← `(theorem $codeEq : ($libT').text.code = ($treeT).toBytes := by rfl_kernel),
    ← `(theorem $treeSize : ($treeT).checkSize? = some $nT := by rfl_kernel),
    ← `(gen_placed_fetches $pc $lib $tree $codeEq $treeSize via_placement $pl $plc
          [$rangesSep,*])]
  if rebase then
    cmds := cmds.push (← `(theorem $(mk s!"{p}PC{sfx}_rebase") [$clsT] :
        ($blockProgF $mplT $iT).rebase (($mplT).base $iT) (fun _ => none) =
          ($pcT).rebase ($plT).base (fun _ => none) := rfl))
    cmds := cmds.push (← `(theorem $(mk s!"{p}Pl{sfx}_base") [$clsT] :
        ($plT).base = ($mplT).base $iT := rfl))
  if rho then
    cmds := cmds.push (← `(theorem $(mk s!"{p}Pl{sfx}_rho") [$clsT] (sym : String) :
        $resolveF $mplT sym = ($plT).ρ sym := rfl))
  if sub then
    cmds := cmds.push (← `(theorem $(mk s!"{p}PC{sfx}_sub") [$clsT]
          {α : Type} {e : BitVec 64} {spec : Spec α}
          (h : subroutine_ok ($blockProgF $mplT $iT) e spec) :
          subroutine_ok (($pcT).rebase ($plT).base (fun _ => none)) e spec := h))
  if irr then
    cmds := cmds.push (← `(attribute [irreducible] $pl))
  let reflNs := mkIdent `ProofLib.ProgramReflection
  for c in cmds do
    elabCommand (← `(open $reflNs:ident in $c:command))

end

end ProofLib.GenPlacedFetches
