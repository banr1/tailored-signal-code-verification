/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Interned

/-!
# Kernel-Fast Text Checker for Placed Libraries

Boolean relocation-range checks and linear text walk (`Obj.Interned.walk`, `Obj.Interned.walk_sound`)
verifying that a placed library's patched `.text` bytes are a prefix of an image segment and that
every relocation and relaxed `ADR` pair is in range.

`walk` consumes template code bytes, sorted relocations, and image bytes in lockstep from the head
of each list instead of indexing with `List.getD`, keeping kernel reduction linear in text length.
-/

@[expose] public section

namespace Arm64.Obj.Interned

set_option linter.literalFetch false

/-! ## Range checks -/

/-- `-(2^k) ≤ d.toInt < 2^k` with literal bounds. -/
def sInRange (lo hi : Int) (d : BitVec 64) : Bool := decide (lo ≤ d.toInt) && decide (d.toInt < hi)

/-- `CodeRelocInRange` as a `Bool`. -/
def codeRelocInRangeB (kind : RelocKind) (place target : BitVec 64) : Bool :=
  match kind with
  | .call26 | .jump26 =>
    Nat.beq ((target - place).toNat % 4) 0 && sInRange (-134217728) 134217728 (target - place)
  | .adrpHi21 | .adrGotPage | .tlsieAdrGottprelPage21 =>
    sInRange (-4294967296) 4294967296 (pageOf target - pageOf place)
  | .adrpHi21Nc => true
  | .addLo12 | .ldst8Lo12 => true
  | .ldst16Lo12 => (target &&& 1#64) == 0#64
  | .ldst32Lo12 => (target &&& 3#64) == 0#64
  | .ldst64Lo12 | .ld64GotLo12Nc | .tlsieLd64GottprelLo12Nc => (target &&& 7#64) == 0#64
  | .ldst128Lo12 => (target &&& 15#64) == 0#64
  | .condbr19 | .ldPrelLo19 =>
    Nat.beq ((target - place).toNat % 4) 0 && sInRange (-1048576) 1048576 (target - place)
  | .tstbr14 => Nat.beq ((target - place).toNat % 4) 0 && sInRange (-32768) 32768 (target - place)
  | .adrPrelLo21 => sInRange (-1048576) 1048576 (target - place)
  | .prel32 => sInRange (-2147483648) 2147483648 (target - place)
  | .abs64 | .abs32 => false
  | .tlsdescAdrPage21 | .tlsdescLd64Lo12 | .tlsdescAddLo12 | .tlsdescCall =>
    sInRange 0 4294967296 target
  | .tlsleAddTprelHi12 => sInRange 0 16777216 target
  | .tlsleAddTprelLo12 => sInRange 0 4096 target
  | .tlsleAddTprelLo12Nc | .tlsleLdst8TprelLo12Nc => true
  | .tlsleLdst16TprelLo12Nc => (target &&& 1#64) == 0#64
  | .tlsleLdst32TprelLo12Nc => (target &&& 3#64) == 0#64
  | .tlsleLdst64TprelLo12Nc => (target &&& 7#64) == 0#64
  | .tlsleLdst128TprelLo12Nc => (target &&& 15#64) == 0#64
  | .tlsleMovwTprelG1 => sInRange (-4294967296) 4294967296 target
  | .tlsleMovwTprelG1Nc => true
  | .tlsleMovwTprelG0 => sInRange (-65536) 65536 target
  | .tlsleMovwTprelG0Nc => true

/-- `CodeBlock.relocInRange` as a `Bool` on an interned `Lib` and `Layout`. -/
def relocInRangeB (L : Lib) (ly : Layout) (kind : RelocKind) (o : Nat)
    (place target : BitVec 64) : Bool :=
  match kind with
  | .adrGotPage =>
    if memNat o ly.relax && gotPairId L o then true
    else sInRange (-4294967296) 4294967296 (pageOf target - pageOf place)
  | .ld64GotLo12Nc =>
    if 4 ≤ o && memNat (o - 4) ly.relax && gotPairId L (o - 4) then
      sInRange (-1048576) 1048576 (target - place)
    else if 4 ≤ o && memNat o ly.relax && gotPairId L (o - 4) then true
    else (target &&& 7#64) == 0#64
  | .tlsieAdrGottprelPage21 =>
    if memNat o ly.relax && tlsieRelaxableId L o then
      Nat.blt target.toNat 4294967296
    else sInRange (-4294967296) 4294967296 (pageOf target - pageOf place)
  | .tlsieLd64GottprelLo12Nc =>
    if memNat o ly.relax && tlsieRelaxableId L o then
      Nat.blt target.toNat 4294967296
    else (target &&& 7#64) == 0#64
  | _ => codeRelocInRangeB kind place target

theorem sInRange_iff {lo hi : Int} {d : BitVec 64} :
    sInRange lo hi d = true ↔ lo ≤ d.toInt ∧ d.toInt < hi := by
  simp [sInRange]

theorem adrInRange_of {place target : BitVec 64}
    (h : sInRange (-1048576) 1048576 (target - place) = true) : AdrInRange place target := by
  rw [sInRange_iff] at h
  unfold AdrInRange
  exact ⟨by omega, by omega⟩

theorem codeRelocInRange_of {kind : RelocKind} {place target : BitVec 64}
    (h : codeRelocInRangeB kind place target = true) : CodeRelocInRange kind place target := by
  cases kind <;>
    simp only [codeRelocInRangeB, Bool.and_eq_true, sInRange_iff, Nat.beq_eq, beq_iff_eq,
      Bool.false_eq_true] at h <;>
    simp only [CodeRelocInRange, BranchInRange, AdrpInRange, Lo12Aligned, lo12AlignMask,
      Imm19InRange, TstBr14InRange, AdrInRange, Prel32InRange,
      TlsUInt32InRange, TprelHi12InRange, TprelLo12InRange, TprelG1InRange, TprelG0InRange] <;>
    first | trivial | exact h | omega | (refine ⟨?_, ?_⟩ <;> omega) | (refine ⟨h.1, ?_, ?_⟩ <;> omega)

theorem relocInRange_of {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    {kind : RelocKind} {o : Nat} {place target : BitVec 64}
    (h : relocInRangeB L ly kind o place target = true) :
    L.block.relocInRange (ly.toPlacement L.names) kind o place target := by
  cases kind <;>
    (dsimp only [relocInRangeB, CodeBlock.relocInRange] at h ⊢; try exact codeRelocInRange_of h)
  · rw [gotPairAt_block hnd hok, toPlacement_relax]
    rw [Bool.and_comm (memNat o ly.relax)] at h
    split <;> rename_i hcond <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
    · trivial
    · rw [sInRange_iff] at h
      exact ⟨by omega, by omega⟩
  · rw [gotPairAt_block hnd hok, toPlacement_relax, toPlacement_relax]
    revert h
    by_cases h4 : 4 ≤ o <;> cases memNat (o - 4) ly.relax <;> cases memNat o ly.relax <;>
      cases gotPairId L (o - 4) <;>
      simp [h4, Lo12Aligned, lo12AlignMask]
    all_goals exact adrInRange_of
  · rw [tlsieRelaxableAt_block, toPlacement_relax]
    rw [Bool.and_comm (memNat o ly.relax)] at h
    split <;> rename_i hcond <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
    · rw [Nat.blt_eq] at h
      exact h
    · rw [sInRange_iff] at h
      exact ⟨by omega, by omega⟩
  · rw [tlsieRelaxableAt_block, toPlacement_relax]
    rw [Bool.and_comm (memNat o ly.relax)] at h
    split <;> rename_i hcond <;> simp only [hcond, Bool.false_eq_true, ↓reduceIte] at h
    · rw [Nat.blt_eq] at h
      exact h
    · simpa [Lo12Aligned, lo12AlignMask] using h

/-! ## Well-formed relocation lists -/

/-- The relocations `rs` are 4-aligned, end within `len` bytes, are strictly increasing, and
    start at or after offset `lo`. -/
def relocsWf (len : Nat) : Nat → List Reloc → Bool
  | _, [] => true
  | lo, r :: rs =>
    Nat.ble lo r.off && Nat.beq (r.off % 4) 0 && Nat.ble (r.off + 4) len && relocsWf len (r.off + 1) rs

theorem relocsWf_cons {len lo : Nat} {r : Reloc} {rs : List Reloc} :
    relocsWf len lo (r :: rs) = true ↔
      lo ≤ r.off ∧ r.off % 4 = 0 ∧ r.off + 4 ≤ len ∧ relocsWf len (r.off + 1) rs = true := by
  simp [relocsWf, Nat.ble_eq, Bool.and_eq_true, Nat.beq_eq, and_assoc]

theorem relocsWf_mem {len : Nat} : ∀ {lo : Nat} {rs : List Reloc}, relocsWf len lo rs = true →
    ∀ r ∈ rs, lo ≤ r.off ∧ r.off % 4 = 0 ∧ r.off + 4 ≤ len
  | _, [], _, _, hr => nomatch hr
  | lo, r :: rs, h, r', hr' => by
    rw [relocsWf_cons] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    rcases List.mem_cons.1 hr' with rfl | hm
    · exact ⟨h1, h2, h3⟩
    · have := relocsWf_mem h4 r' hm
      exact ⟨by omega, this.2⟩

theorem relocsWf_pairwise {len : Nat} : ∀ {lo : Nat} {rs : List Reloc}, relocsWf len lo rs = true →
    rs.Pairwise (fun a b => a.off < b.off)
  | _, [], _ => List.Pairwise.nil
  | _, r :: rs, h => by
    rw [relocsWf_cons] at h
    refine List.Pairwise.cons (fun b hb => ?_) (relocsWf_pairwise h.2.2.2)
    have := relocsWf_mem h.2.2.2 b hb
    omega

theorem relocsWf_nodup {len lo : Nat} {rs : List Reloc} (h : relocsWf len lo rs = true) :
    (rs.map (·.off)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact (relocsWf_pairwise h).imp (fun h' => Nat.ne_of_lt h')

theorem relocAtId?_append_of_lt {pre rs : List Reloc} {o : Nat} (h : ∀ r ∈ pre, r.off < o) :
    relocAtId? (pre ++ rs) o = relocAtId? rs o := by
  unfold relocAtId?
  rw [List.find?_append]
  have : pre.find? (fun r => Nat.beq r.off o) = none := by
    rw [List.find?_eq_none]
    intro r hr
    have := h r hr
    simp only [Nat.beq_eq]
    omega
  rw [this]; rfl

theorem relocAtId?_cons_eq {r : Reloc} {rs : List Reloc} {o : Nat} (h : r.off = o) :
    relocAtId? (r :: rs) o = some r := by
  simp [relocAtId?, h, Nat.beq_refl]

theorem relocAtId?_cons_ne {r : Reloc} {rs : List Reloc} {o : Nat} (h : r.off ≠ o) :
    relocAtId? (r :: rs) o = relocAtId? rs o := by
  simp [relocAtId?, nat_beq_false_of_ne h]

theorem relocAtId?_of_lt {rs : List Reloc} {o : Nat} (h : ∀ r ∈ rs, o < r.off) :
    relocAtId? rs o = none := by
  unfold relocAtId?
  rw [List.find?_eq_none]
  intro r hr
  have := h r hr
  simp only [Nat.beq_eq]
  omega

/-! ## Text walk -/

/-- The template words `w1` (at offset `o`, relocation `r`) and `w2` (at `o + 4`, relocation
    `r2`) form a relaxable `ADRP` + `ADD` pair (the word-level body of `pairOk`). -/
def pairOkW (r1 r2 : Reloc) (w1 w2 : BitVec 32) : Bool :=
  r1.kind == .adrpHi21 && r2.kind == .addLo12 && Nat.beq r1.sym r2.sym &&
    r1.addend == r2.addend &&
    isAdrpWord w1 && isAddImm64Word w2 &&
    (w1 &&& 0x1f#32) == (w2 &&& 0x1f#32) &&
    ((w2 >>> 5) &&& 0x1f#32) == (w1 &&& 0x1f#32) &&
    (w1 &&& 0x1f#32) != 0x1f#32

theorem pairOk_eq_pairOkW (code : List (BitVec 8)) (off : Nat) (r1 r2 : Reloc) :
    pairOk code off r1 r2 = pairOkW r1 r2 (wordOfBytesLE code off) (wordOfBytesLE code (off + 4)) :=
  rfl

/-- The pair at offset `o` (relocation `r`, template word `w`, remaining relocations `rs`,
    template bytes `rest` after the word) is relaxed. -/
def relaxHead (ly : Layout) (o : Nat) (r : Reloc) (w : BitVec 32) (rs : List Reloc)
    (rest : List (BitVec 8)) : Bool :=
  match rs with
  | r2 :: _ => memNat o ly.relax && Nat.beq r2.off (o + 4) && pairOkW r r2 w (wordOfBytesLE rest 0)
  | [] => false

/-- The patched word at relocation site `r` (offset `o`, template word `w`), given whether this
    site (`rel`) and the previous word (`prev`) are the `ADRP` of a relaxed pair. Mirrors
    `sitePatched`. -/
def siteOut (L : Lib) (ly : Layout) (o : Nat) (r : Reloc) (w : BitVec 32) (rel prev : Bool) :
    BitVec 32 :=
  let place := ly.base + BitVec.ofNat 64 o
  if rel then nopWord
  else if prev then adrWord (adrTemplate w) place (targetId L ly r)
  else if r.kind.isGotOrTlsIe && 4 ≤ o &&
      (memNat (o - 4) ly.relax && gotPairId L (o - 4)) then
    adrWord (adrTemplate w) place (targetId L ly r)
  else if r.kind.isGotOrTlsIe && memNat o ly.relax &&
      (gotPairId L o || tlsieRelaxableId L o ||
        (4 ≤ o && gotPairId L (o - 4))) then
    CodeBlock.patchGotOrTlsIeRelaxed w place (targetId L ly r) r.kind
  else patchRelocWord r.kind w place
    (if undefWeakId L ly r then place + 4 else relocTargetId L ly o r)

/-- Range facts at relocation site `r` (offset `o`): `relocInRange` for the relocation, and
    `AdrInRange` for the `ADD` of a relaxed pair (`prev`). -/
def siteRangeOk (L : Lib) (ly : Layout) (o : Nat) (r : Reloc) (prev : Bool) : Bool :=
  let place := ly.base + BitVec.ofNat 64 o
  relocInRangeB L ly r.kind o place (relocTargetId L ly o r) &&
    (!prev || sInRange (-1048576) 1048576 (targetId L ly r - place))

/-- One pass over template code bytes `cs` (at offset `o`), the relocations `rs` at or after
    `o`, and the claimed image bytes `seg`: every patched word equals the next word of `seg`
    and every relocation site is in range. `prev` says whether the word at `o - 4` is the
    `ADRP` of a relaxed pair. -/
def walk (L : Lib) (ly : Layout) :
    Nat → Bool → List Reloc → List (BitVec 8) → List (BitVec 8) → Bool
  | _, _, _, [], _ => true
  | o, prev, rs, b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss =>
    match rs with
    | r :: rs' =>
      if Nat.beq r.off o then
        let w := b3 ++ b2 ++ b1 ++ b0
        let rel := relaxHead ly o r w rs' cs
        bytesOfWordLE (siteOut L ly o r w rel prev) == [s0, s1, s2, s3] &&
          siteRangeOk L ly o r prev && walk L ly (o + 4) rel rs' cs ss
      else
        b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 && walk L ly (o + 4) false rs cs ss
    | [] => b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 && walk L ly (o + 4) false [] cs ss
  | _, _, _, _ :: _, _ => false

/-! ## Soundness -/

theorem bytesOfWordLE_append4 (b0 b1 b2 b3 : BitVec 8) :
    bytesOfWordLE (b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3] := by
  simp only [bytesOfWordLE, bytesLE, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_bits

theorem relaxableId_eq_relaxHead {L : Lib} {pre rs' : List Reloc} {r : Reloc} {o : Nat}
    {cs : List (BitVec 8)} {b0 b1 b2 b3 : BitVec 8} (ly : Layout)
    (hrel : L.relocs = pre ++ r :: rs') (hpre : ∀ x ∈ pre, x.off < o) (hro : r.off = o)
    (ho : o % 4 = 0) (hwf : relocsWf L.code.length (r.off + 1) rs' = true)
    (hcs : L.code.drop o = b0 :: b1 :: b2 :: b3 :: cs) :
    relaxedId L ly o = relaxHead ly o r (b3 ++ b2 ++ b1 ++ b0) rs' cs := by
  have hw1 : wordOfBytesLE L.code o = b3 ++ b2 ++ b1 ++ b0 := by
    rw [← Nat.add_zero o, getD_eq_drop_getD_word, hcs, wordOfBytesLE_cons4_zero]
  have hw2 : wordOfBytesLE L.code (o + 4) = wordOfBytesLE cs 0 := by
    rw [← Nat.add_zero (o + 4), getD_eq_drop_getD_word, ← List.drop_drop, hcs]
    rfl
  have h1 : relocAtId? L.relocs o = some r := by
    rw [hrel, relocAtId?_append_of_lt hpre, relocAtId?_cons_eq hro]
  have h2 : relocAtId? L.relocs (o + 4) = relocAtId? rs' (o + 4) := by
    rw [hrel, relocAtId?_append_of_lt (fun x hx => by have := hpre x hx; omega),
      relocAtId?_cons_ne (by omega)]
  have hne : L.relocs.isEmpty = false := by
    rw [hrel]; cases pre <;> rfl
  unfold relaxedId relaxableId relaxHead
  rw [hne, h1, h2]
  cases rs' with
  | nil => simp [relocAtId?]
  | cons r2 rs'' =>
    rw [relocsWf_cons] at hwf
    by_cases h4 : r2.off = o + 4
    · rw [relocAtId?_cons_eq h4]
      simp only [pairOk_eq_pairOkW, hw1, hw2, h4, Nat.beq_refl, Bool.not_false, Bool.and_true]
    · rw [relocAtId?_cons_ne h4, relocAtId?_of_lt]
      · simp [nat_beq_false_of_ne h4]
      · intro x hx
        have := relocsWf_mem hwf.2.2.2 x hx
        have : o + 4 ≤ r2.off := by omega
        omega

theorem relaxedId_of_none {L : Lib} {ly : Layout} {o : Nat} (h : relocAtId? L.relocs o = none) :
    relaxedId L ly o = false := by
  simp [relaxedId, relaxableId, h]

theorem prefix_of_take_drop {l s : List (BitVec 8)} {k : Nat} {t : List (BitVec 8)}
    (ht : l.take k = t) (hd : (l.drop k).IsPrefix (s.drop k))
    (hs : s.take k = t) : l.IsPrefix s := by
  rw [← List.take_append_drop k l, ← List.take_append_drop k s, ht, hs]
  exact (List.prefix_append_right_inj t).2 hd

theorem relocsWf_align {len o : Nat} {rs : List Reloc} (ho : o % 4 = 0)
    (h : relocsWf len (o + 1) rs = true) : relocsWf len (o + 4) rs = true := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    rw [relocsWf_cons] at h ⊢
    exact ⟨by omega, h.2⟩

theorem sitePatched_eq_siteOut (L : Lib) (ly : Layout) (o : Nat) (r : Reloc) :
    sitePatched L ly o r = siteOut L ly o r (wordOfBytesLE L.code o) (relaxedId L ly o)
      (4 ≤ o && relaxedId L ly (o - 4)) := rfl

/-- The conclusion of `walk_sound` at offset `o`. -/
def WalkOk (L : Lib) (ly : Layout) (o : Nat) (rs : List Reloc) (seg : List (BitVec 8)) : Prop :=
  ((L.block.patched (ly.toPlacement L.names)).drop o).IsPrefix seg ∧
  (∀ r ∈ rs, relocInRangeB L ly r.kind r.off (ly.base + BitVec.ofNat 64 r.off)
      (relocTargetId L ly r.off r) = true) ∧
  (∀ off r, o ≤ off + 4 → relaxedId L ly off = true → relocAtId? L.relocs (off + 4) = some r →
      AdrInRange (ly.base + BitVec.ofNat 64 (off + 4)) (targetId L ly r))

/-- Soundness of `walk` at offset `o`: the patched code from `o` on is a prefix of `seg`, and
    every relocation at or after `o` satisfies its range conditions. -/
theorem walk_sound {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk) :
    ∀ (cs seg : List (BitVec 8)) (o : Nat) (prev : Bool) (pre rs : List Reloc),
      L.code.drop o = cs → o % 4 = 0 → L.relocs = pre ++ rs → (∀ x ∈ pre, x.off < o) →
      relocsWf L.code.length o rs = true →
      prev = (4 ≤ o && relaxedId L ly (o - 4)) →
      walk L ly o prev rs cs seg = true → WalkOk L ly o rs seg
  | [], seg, o, prev, pre, rs, hcs, _, hrel, hpre, hwf, _, _ => by
    have hlen : L.code.length ≤ o := by
      have := congrArg List.length hcs; simp at this; omega
    have hrs : rs = [] := by
      cases rs with
      | nil => rfl
      | cons r _ => rw [relocsWf_cons] at hwf; omega
    subst hrs
    refine ⟨?_, by simp, ?_⟩
    · rw [List.drop_eq_nil_of_le]
      · exact List.nil_prefix
      · rw [CodeBlock.length_patched]; simp; omega
    · intro off r hle _ hr
      have := relocAtId?_mem hr
      rw [hrel, List.append_nil] at this
      have h1 := hpre r this
      have h2 := relocAtId?_off hr
      omega
  | b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss, o, prev, pre, rs, hcs, ho, hrel,
      hpre, hwf, hprev, hw => by
    have hlen : o + 4 ≤ L.code.length := by
      have := congrArg List.length hcs; simp at this; omega
    have hcs' : L.code.drop (o + 4) = cs := by
      rw [← List.drop_drop, hcs]; rfl
    have htake := CodeBlock.take4_drop_patched (blk := L.block) (pl := ly.toPlacement L.names)
      ho (by simpa using hlen)
    have hdrop : ((L.block.patched (ly.toPlacement L.names)).drop o).drop 4 =
        (L.block.patched (ly.toPlacement L.names)).drop (o + 4) := by
      rw [List.drop_drop, Nat.add_comm]
    have hw1 : wordOfBytesLE L.code o = b3 ++ b2 ++ b1 ++ b0 := by
      rw [← Nat.add_zero o, getD_eq_drop_getD_word, hcs, wordOfBytesLE_cons4_zero]
    have hal : ∀ x ∈ L.relocs, o ≤ x.off → x.off % 4 = 0 := by
      intro x hx hle; rw [hrel] at hx
      rcases List.mem_append.1 hx with hx | hx
      · have := hpre x hx; omega
      · exact (relocsWf_mem hwf x hx).2.1
    have adr_later : (∀ off r, o + 4 ≤ off + 4 → relaxedId L ly off = true →
          relocAtId? L.relocs (off + 4) = some r →
          AdrInRange (ly.base + BitVec.ofNat 64 (off + 4)) (targetId L ly r)) →
        ∀ off r, o ≤ off + 4 → off + 4 ≠ o → relaxedId L ly off = true →
          relocAtId? L.relocs (off + 4) = some r →
          AdrInRange (ly.base + BitVec.ofNat 64 (off + 4)) (targetId L ly r) := by
      intro h off r hle hne hrx hr
      have h1 := relocAtId?_off hr
      have h2 := hal r (relocAtId?_mem hr) (by omega)
      exact h off r (by omega) hrx hr
    have prefix_of : ∀ w : BitVec 32, L.block.patchedWord (ly.toPlacement L.names) o = w →
        bytesOfWordLE w = [s0, s1, s2, s3] →
        ((L.block.patched (ly.toPlacement L.names)).drop (o + 4)).IsPrefix ss →
        ((L.block.patched (ly.toPlacement L.names)).drop o).IsPrefix (s0 :: s1 :: s2 :: s3 :: ss) := by
      intro w hpw hb hpre'
      refine prefix_of_take_drop (k := 4) (htake.trans (by rw [hpw, hb])) ?_ (by simp)
      rw [hdrop]; exact hpre'
    have nonsite : ∀ rs0, relocAtId? L.relocs o = none → relocsWf L.code.length (o + 4) rs0 = true →
        L.relocs = pre ++ rs0 → (∀ r ∈ rs, r ∈ rs0) →
        (b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 && walk L ly (o + 4) false rs0 cs ss) = true →
        WalkOk L ly o rs (s0 :: s1 :: s2 :: s3 :: ss) := by
      intro rs0 hnone hwf' hrel' hsub h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hw'⟩ := h
      have hrel0 := relaxedId_of_none (ly := ly) hnone
      have ih := walk_sound hnd hok cs ss (o + 4) false pre rs0 hcs' (by omega) hrel'
        (fun x hx => by have := hpre x hx; omega) hwf'
        (by simp only [show 4 ≤ o + 4 from by omega, decide_true, Bool.true_and,
              show o + 4 - 4 = o from by omega, hrel0]) hw'
      refine ⟨prefix_of _ (patchedWord_block_none hnone) (by rw [hw1, bytesOfWordLE_append4])
        ih.1, fun r hr => ih.2.1 r (hsub r hr), ?_⟩
      intro off r hle hrx hr
      by_cases hoff : off + 4 = o
      · rw [hoff, hnone] at hr; cases hr
      · exact adr_later ih.2.2 off r hle hoff hrx hr
    match rs, hw with
    | [], hw =>
      refine nonsite [] ?_ rfl hrel (fun _ h => h) hw
      rw [hrel, relocAtId?_append_of_lt hpre]; rfl
    | r :: rs', hw =>
      simp only [walk] at hw
      have hwf0 := hwf
      rw [relocsWf_cons] at hwf0
      obtain ⟨hlo, hral, hrlen, hwf'⟩ := hwf0
      by_cases hro : r.off = o
      · simp only [hro, Nat.beq_refl, ↓reduceIte] at hw
        simp only [Bool.and_eq_true, beq_iff_eq] at hw
        obtain ⟨⟨hb, hrange⟩, hw'⟩ := hw
        have hrelax := relaxableId_eq_relaxHead ly hrel hpre hro ho hwf' hcs
        rw [← hrelax] at hw' hb
        have hat : relocAtId? L.relocs o = some r := by
          rw [hrel, relocAtId?_append_of_lt hpre, relocAtId?_cons_eq hro]
        have ih := walk_sound hnd hok cs ss (o + 4) (relaxedId L ly o) (pre ++ [r]) rs' hcs'
          (by omega) (by rw [hrel]; simp)
          (fun x hx => by
            rcases List.mem_append.1 hx with hx | hx
            · have := hpre x hx; omega
            · rw [List.mem_singleton] at hx; subst hx; omega)
          (relocsWf_align ho (hro ▸ hwf'))
          (by simp only [show 4 ≤ o + 4 from by omega, decide_true, Bool.true_and,
                show o + 4 - 4 = o from by omega]) hw'
        simp only [siteRangeOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hrange
        refine ⟨prefix_of _ ((patchedWord_block_some hnd hok hat).trans
            (by rw [sitePatched_eq_siteOut, hw1, ← hprev])) hb ih.1, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · rw [hro]; exact hrange.1
          · exact ih.2.1 x hx
        · intro off r' hle hrx hr
          by_cases hoff : off + 4 = o
          · rw [hoff, hat] at hr
            cases hr
            have hp : prev = true := by
              rw [hprev, show o - 4 = off by omega]; simp [hrx]; omega
            rcases hrange.2 with h | h
            · rw [hp] at h; exact Bool.noConfusion h
            · rw [hoff]; exact adrInRange_of h
          · exact adr_later ih.2.2 off r' hle hoff hrx hr
      · rw [nat_beq_false_of_ne hro] at hw
        simp only [Bool.false_eq_true, ↓reduceIte] at hw
        have hgt : o + 4 ≤ r.off := by
          have := hal r (by rw [hrel]; simp) hlo; omega
        refine nonsite (r :: rs') ?_ ?_ hrel (fun _ h => h) hw
        · rw [hrel, relocAtId?_append_of_lt hpre]
          exact relocAtId?_of_lt (fun x hx => by
            rcases List.mem_cons.1 hx with rfl | hx
            · omega
            · have := relocsWf_mem hwf' x hx; omega)
        · rw [relocsWf_cons]; exact ⟨hgt, hral, hrlen, hwf'⟩
  | [_], _, _, _, _, _, _, _, _, _, _, _, hw => by simp [walk] at hw
  | [_, _], _, _, _, _, _, _, _, _, _, _, _, hw => by simp [walk] at hw
  | [_, _, _], _, _, _, _, _, _, _, _, _, _, _, hw => by simp [walk] at hw
  | _ :: _ :: _ :: _ :: _, [], _, _, _, _, _, _, _, _, _, _, hw => by simp [walk] at hw
  | _ :: _ :: _ :: _ :: _, [_], _, _, _, _, _, _, _, _, _, _, hw => by simp [walk] at hw
  | _ :: _ :: _ :: _ :: _, [_, _], _, _, _, _, _, _, _, _, _, _, hw => by simp [walk] at hw
  | _ :: _ :: _ :: _ :: _, [_, _, _], _, _, _, _, _, _, _, _, _, _, hw => by simp [walk] at hw

end Arm64.Obj.Interned
