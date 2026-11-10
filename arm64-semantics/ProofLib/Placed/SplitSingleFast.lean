/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.SplitSingle

/-!
# Symbol-Tree Text Walk for Chunked Single-Block Checks

Accelerates `ProofLib.Placed.SplitSingle` relocation-target resolution over large symbol tables by
walking text chunks (`walkT`, `walkToT`, `textOkChunksT`) against a pre-resolved `VecTree SymSlot`
validated once by index range (`SymTreeOk`, `symTreeOkChunks`), discharging `Placeable`, `InElf`,
and `DataDisjoint` via `checkDisjoint_spec_chunksT`.
-/

@[expose] public section

set_option autoImplicit false

namespace Arm64.Obj.Interned
open Arm64 Arm64.Process ProofLib.ProgramReflection ProofLib.ObjectLoad ProofLib.Placed.Split

/-! ## `List.rec`-Based Lookups -/

/-- `lookupId`, `List.rec`-based (cheap kernel reduction over long symbol tables). -/
noncomputable def rLookupId {α : Type} (i : Nat) (l : List (Nat × α)) : Option α :=
  @List.rec (Nat × α) (fun _ => Option α) none
    (fun p _ ih => Bool.casesOn (motive := fun _ => Option α) (Nat.beq p.1 i) ih (some p.2)) l

theorem rLookupId_eq {α : Type} (i : Nat) : ∀ l : List (Nat × α), rLookupId i l = lookupId i l
  | [] => rfl
  | (k, v) :: rest => by
    show Bool.casesOn (motive := fun _ => Option α) (Nat.beq k i) (rLookupId i rest) (some v) = _
    rw [rLookupId_eq i rest]
    simp only [lookupId]
    cases Nat.beq k i <;> rfl

/-- `memNat`, `List.rec`-based. -/
noncomputable def rMemNat (n : Nat) (l : List Nat) : Bool :=
  @List.rec Nat (fun _ => Bool) false
    (fun m _ ih => Bool.casesOn (motive := fun _ => Bool) (Nat.beq n m) ih true) l

theorem rMemNat_eq (n : Nat) : ∀ l : List Nat, rMemNat n l = memNat n l
  | [] => rfl
  | m :: ms => by
    show Bool.casesOn (motive := fun _ => Bool) (Nat.beq n m) (rMemNat n ms) true = _
    rw [rMemNat_eq n ms]
    simp only [memNat]
    cases Nat.beq n m <;> rfl

/-- `mkSymSlot` with `rLookupId`. -/
noncomputable def mkSymSlotR (L : Lib) (ly : Layout) (i : Nat) (a : BitVec 64) : SymSlot :=
  match rLookupId i L.symbols with
  | some off =>
    withNat (ly.base + BitVec.ofNat 64 off).toNat fun r =>
      ⟨false, a, BitVec.ofNat 64 r⟩
  | none =>
    withNat a.toNat fun na =>
      let a' := BitVec.ofNat 64 na
      ⟨true, a', a'⟩

theorem mkSymSlotR_eq (L : Lib) (ly : Layout) (i : Nat) (a : BitVec 64) :
    mkSymSlotR L ly i a = mkSymSlot L ly i a := by
  unfold mkSymSlotR mkSymSlot
  rw [rLookupId_eq]
  cases lookupId i L.symbols <;> rfl

/-- `relaxHead`, testing the next relocation's offset before `ly.relax` membership. -/
noncomputable def relaxHeadR (ly : Layout) (o : Nat) (r : Reloc) (w : BitVec 32) (rs : List Reloc)
    (rest : List (BitVec 8)) : Bool :=
  match rs with
  | r2 :: _ => Nat.beq r2.off (o + 4) && rMemNat o ly.relax && pairOkW r r2 w (wordOfBytesLE rest 0)
  | [] => false

theorem relaxHeadR_eq (ly : Layout) (o : Nat) (r : Reloc) (w : BitVec 32) (rs : List Reloc)
    (rest : List (BitVec 8)) : relaxHeadR ly o r w rs rest = relaxHead ly o r w rs rest := by
  cases rs with
  | nil => rfl
  | cons r2 _ =>
    simp only [relaxHeadR, relaxHead, rMemNat_eq]
    cases memNat o ly.relax <;> cases Nat.beq r2.off (o + 4) <;> rfl

/-! ## Checking a Symbol Tree -/

/-- `t` holds the pre-resolved slot `mkSymSlot L ly i (ly.addrs.getD i 0#64)` at every name index
    `i` of `L` (the hypothesis of `targetTree_eq` / `relocTargetTree_eq`). -/
def SymTreeOk (L : Lib) (ly : Layout) (t : VecTree SymSlot) : Prop :=
  ∀ i < L.names.length, t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64)

/-- Kernel-fast equality of symbol slots (`Bool` and `Nat` comparisons only). -/
def slotEqB (a b : SymSlot) : Bool :=
  a.notSym == b.notSym && Nat.beq a.addr.toNat b.addr.toNat &&
    Nat.beq a.resolved.toNat b.resolved.toNat

theorem slotEqB_spec {a b : SymSlot} (h : slotEqB a b = true) : a = b := by
  obtain ⟨n1, a1, r1⟩ := a
  obtain ⟨n2, a2, r2⟩ := b
  simp only [slotEqB, Bool.and_eq_true, beq_iff_eq, Nat.beq_eq] at h
  obtain ⟨⟨hn, ha⟩, hr⟩ := h
  rw [hn, BitVec.eq_of_toNat_eq ha, BitVec.eq_of_toNat_eq hr]

/-- `t` holds `mkSymSlot L ly (i + j) (as.getD j 0#64)` at index `i + j` for every `j < n`; `as`
    is consumed one entry per index, so the address table is walked once. -/
noncomputable def symTreeOkFrom (L : Lib) (ly : Layout) (t : VecTree SymSlot) :
    Nat → Nat → List (BitVec 64) → Bool
  | 0, _, _ => true
  | n + 1, i, as =>
    slotEqB (t.getD defaultSymSlot i) (mkSymSlotR L ly i (as.headD 0#64)) &&
      symTreeOkFrom L ly t n (i + 1) as.tail

theorem symTreeOkFrom_spec (L : Lib) (ly : Layout) (t : VecTree SymSlot) :
    ∀ (n i : Nat) (as : List (BitVec 64)), symTreeOkFrom L ly t n i as = true →
      ∀ j < n, t.getD defaultSymSlot (i + j) = mkSymSlot L ly (i + j) (as.getD j 0#64)
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, i, as, h, j, hj => by
    simp only [symTreeOkFrom, Bool.and_eq_true] at h
    obtain ⟨h0, hrest⟩ := h
    cases j with
    | zero =>
      rw [Nat.add_zero, slotEqB_spec h0, mkSymSlotR_eq]
      cases as <;> rfl
    | succ j =>
      have ih := symTreeOkFrom_spec L ly t n (i + 1) as.tail hrest j (by omega)
      rw [show i + 1 + j = i + (j + 1) by omega] at ih
      rw [ih]
      cases as <;> simp

/-- Slots `[i, j)` of `t` (one chunk of `symTreeOkChunks`). -/
noncomputable def symTreeOkChunk (L : Lib) (ly : Layout) (t : VecTree SymSlot) (i j : Nat) : Bool :=
  symTreeOkFrom L ly t (j - i) i (rDrop i ly.addrs)

/-- Slots `[i, L.names.length)` of `t` (the last chunk). -/
noncomputable def symTreeOkTail (L : Lib) (ly : Layout) (t : VecTree SymSlot) (i : Nat) : Bool :=
  symTreeOkFrom L ly t (rLen L.names - i) i (rDrop i ly.addrs)

/-- The slot chunks `[i, j₁), [j₁, j₂), ..., [jₖ, L.names.length)` of `t` all check. -/
noncomputable def symTreeOkChunks (L : Lib) (ly : Layout) (t : VecTree SymSlot) :
    Nat → List Nat → Prop
  | i, [] => symTreeOkTail L ly t i = true
  | i, j :: js => symTreeOkChunk L ly t i j = true ∧ symTreeOkChunks L ly t j js

theorem symTreeOkChunks_nil {L : Lib} {ly : Layout} {t : VecTree SymSlot} {i : Nat}
    (h : symTreeOkTail L ly t i = true) : symTreeOkChunks L ly t i [] := h

theorem symTreeOkChunks_cons {L : Lib} {ly : Layout} {t : VecTree SymSlot} {i j : Nat}
    {js : List Nat} (h : symTreeOkChunk L ly t i j = true) (hr : symTreeOkChunks L ly t j js) :
    symTreeOkChunks L ly t i (j :: js) := ⟨h, hr⟩

theorem symTreeOk_of_chunks_from {L : Lib} {ly : Layout} {t : VecTree SymSlot} :
    ∀ (i : Nat) (js : List Nat), symTreeOkChunks L ly t i js →
      ∀ x, i ≤ x → x < L.names.length →
        t.getD defaultSymSlot x = mkSymSlot L ly x (ly.addrs.getD x 0#64)
  | i, [], h, x, hix, hx => by
    simp only [symTreeOkChunks, symTreeOkTail, rLen_eq, rDrop_eq] at h
    have := symTreeOkFrom_spec L ly t _ i _ h (x - i) (by omega)
    rwa [show i + (x - i) = x by omega, getD_drop, show i + (x - i) = x by omega] at this
  | i, j :: js, h, x, hix, hx => by
    obtain ⟨h1, h2⟩ := h
    by_cases hxj : x < j
    · simp only [symTreeOkChunk, rDrop_eq] at h1
      have := symTreeOkFrom_spec L ly t _ i _ h1 (x - i) (by omega)
      rwa [show i + (x - i) = x by omega, getD_drop, show i + (x - i) = x by omega] at this
    · exact symTreeOk_of_chunks_from j js h2 x (by omega) hx

/-- Slot chunks from index `0` prove `SymTreeOk`. -/
theorem symTreeOk_of_chunks {L : Lib} {ly : Layout} {t : VecTree SymSlot} {js : List Nat}
    (h : symTreeOkChunks L ly t 0 js) : SymTreeOk L ly t :=
  fun x hx => symTreeOk_of_chunks_from 0 js h x (Nat.zero_le x) hx

/-! ## Text Walk over a Symbol Tree -/

/-- `siteOut` with targets resolved through `t`. -/
def siteOutT (L : Lib) (ly : Layout) (t : VecTree SymSlot) (o : Nat) (r : Reloc) (w : BitVec 32)
    (rel prev : Bool) : BitVec 32 :=
  let place := ly.base + BitVec.ofNat 64 o
  if rel then nopWord
  else if prev then adrWord (adrTemplate w) place (targetTree t r)
  else if r.kind.isGotOrTlsIe && 4 ≤ o &&
      (memNat (o - 4) ly.relax && gotPairId L (o - 4)) then
    adrWord (adrTemplate w) place (targetTree t r)
  else if r.kind.isGotOrTlsIe && memNat o ly.relax &&
      (gotPairId L o || tlsieRelaxableId L o ||
        (4 ≤ o && gotPairId L (o - 4))) then
    CodeBlock.patchGotOrTlsIeRelaxed w place (targetTree t r) r.kind
  else patchRelocWord r.kind w place
    (if undefWeakId L ly r then place + 4 else relocTargetTree L ly t o r)

/-- `siteRangeOk` with targets resolved through `t`. -/
def siteRangeOkT (L : Lib) (ly : Layout) (t : VecTree SymSlot) (o : Nat) (r : Reloc)
    (prev : Bool) : Bool :=
  let place := ly.base + BitVec.ofNat 64 o
  relocInRangeB L ly r.kind o place (relocTargetTree L ly t o r) &&
    (!prev || sInRange (-1048576) 1048576 (targetTree t r - place))

/-- `walk` with targets resolved through `t`. -/
noncomputable def walkT (L : Lib) (ly : Layout) (t : VecTree SymSlot) :
    Nat → Bool → List Reloc → List (BitVec 8) → List (BitVec 8) → Bool
  | _, _, _, [], _ => true
  | o, prev, rs, b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss =>
    match rs with
    | r :: rs' =>
      if Nat.beq r.off o then
        let w := b3 ++ b2 ++ b1 ++ b0
        let rel := relaxHeadR ly o r w rs' cs
        bytesOfWordLE (siteOutT L ly t o r w rel prev) == [s0, s1, s2, s3] &&
          siteRangeOkT L ly t o r prev && walkT L ly t (o + 4) rel rs' cs ss
      else
        b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 && walkT L ly t (o + 4) false rs cs ss
    | [] => b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 && walkT L ly t (o + 4) false [] cs ss
  | _, _, _, _ :: _, _ => false

/-- `walkTo` with targets resolved through `t`. -/
noncomputable def walkToT (L : Lib) (ly : Layout) (t : VecTree SymSlot) (stop : Nat) :
    Nat → Bool → List Reloc → List (BitVec 8) → List (BitVec 8) → Option (Bool × List Reloc)
  | o, prev, rs, b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss =>
    if Nat.beq o stop then some (prev, rs) else
    match rs with
    | r :: rs' =>
      if Nat.beq r.off o then
        let w := b3 ++ b2 ++ b1 ++ b0
        let rel := relaxHeadR ly o r w rs' cs
        if bytesOfWordLE (siteOutT L ly t o r w rel prev) == [s0, s1, s2, s3] &&
            siteRangeOkT L ly t o r prev then walkToT L ly t stop (o + 4) rel rs' cs ss
        else none
      else if b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 then
        walkToT L ly t stop (o + 4) false rs cs ss
      else none
    | [] =>
      if b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 then
        walkToT L ly t stop (o + 4) false [] cs ss
      else none
  | o, prev, rs, _, _ => if Nat.beq o stop then some (prev, rs) else none

/-! ## Agreement with the Linear Walk -/

theorem siteOutT_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : SymTreeOk L ly t) {r : Reloc} (hr : r ∈ L.relocs) (o : Nat) (w : BitVec 32)
    (rel prev : Bool) : siteOutT L ly t o r w rel prev = siteOut L ly o r w rel prev := by
  simp only [siteOutT, siteOut, targetTree_eq ht (hok.relocs r hr), relocTargetTree_eq hok ht hr]

theorem siteRangeOkT_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : SymTreeOk L ly t) {r : Reloc} (hr : r ∈ L.relocs) (o : Nat) (prev : Bool) :
    siteRangeOkT L ly t o r prev = siteRangeOk L ly o r prev := by
  simp only [siteRangeOkT, siteRangeOk, targetTree_eq ht (hok.relocs r hr),
    relocTargetTree_eq hok ht hr]

/-- `walkT` agrees with `walk` on a suffix of `L.relocs` when `t` holds the symbol slots. -/
theorem walkT_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : SymTreeOk L ly t) :
    ∀ {o : Nat} {prev : Bool} {rs : List Reloc} {cs ss : List (BitVec 8)}, rs <:+ L.relocs →
      walkT L ly t o prev rs cs ss = walk L ly o prev rs cs ss := by
  intro o prev rs cs ss hsuf
  fun_induction walk L ly o prev rs cs ss with
  | case1 => simp only [walkT]
  | case2 o prev b0 b1 b2 b3 cs s0 s1 s2 s3 ss r rs' hro w rel ih =>
    have hr : r ∈ L.relocs := hsuf.subset List.mem_cons_self
    simp only [walkT, hro, ↓reduceIte, relaxHeadR_eq, siteOutT_eq hok ht hr,
      siteRangeOkT_eq hok ht hr, ih ((List.suffix_cons r rs').trans hsuf), w, rel]
  | case3 o prev b0 b1 b2 b3 cs s0 s1 s2 s3 ss r rs' hro ih =>
    simp only [Bool.not_eq_true] at hro
    simp only [walkT, hro, Bool.false_eq_true, ↓reduceIte, ih hsuf]
  | case4 o prev b0 b1 b2 b3 cs s0 s1 s2 s3 ss ih =>
    simp only [walkT, ih hsuf]
  | case5 _ _ _ _ tl seg hne =>
    rcases tl with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, cs⟩⟩⟩ <;>
      rcases seg with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, ss⟩⟩⟩⟩ <;>
      first
        | exact (hne _ _ _ _ _ _ _ _ _ rfl rfl).elim
        | rfl
        | simp [walkT]

/-- `walkToT` agrees with `walkTo` on a suffix of `L.relocs` when `t` holds the symbol slots. -/
theorem walkToT_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : SymTreeOk L ly t) {stop : Nat} :
    ∀ {o : Nat} {prev : Bool} {rs : List Reloc} {cs ss : List (BitVec 8)}, rs <:+ L.relocs →
      walkToT L ly t stop o prev rs cs ss = walkTo L ly stop o prev rs cs ss := by
  intro o prev rs cs ss hsuf
  fun_induction walkTo L ly stop o prev rs cs ss with
  | case1 _ _ _ _ _ _ _ _ _ _ _ _ _ hst =>
    simp only [walkToT, hst, ↓reduceIte]
  | case2 o prev b0 b1 b2 b3 cs s0 s1 s2 s3 ss hst r rs' hro w rel hc ih =>
    have hr : r ∈ L.relocs := hsuf.subset List.mem_cons_self
    simp only [Bool.not_eq_true] at hst
    simp only [w, rel] at hc ih
    simp only [walkToT, hst, hro, Bool.false_eq_true, ↓reduceIte, relaxHeadR_eq,
      siteOutT_eq hok ht hr, siteRangeOkT_eq hok ht hr, hc]
    exact ih ((List.suffix_cons r rs').trans hsuf)
  | case3 o prev b0 b1 b2 b3 cs s0 s1 s2 s3 ss hst r rs' hro w rel hc =>
    have hr : r ∈ L.relocs := hsuf.subset List.mem_cons_self
    simp only [Bool.not_eq_true] at hst hc
    simp only [w, rel] at hc
    simp only [walkToT, hst, hro, Bool.false_eq_true, ↓reduceIte, relaxHeadR_eq,
      siteOutT_eq hok ht hr, siteRangeOkT_eq hok ht hr, hc]
  | case4 o prev b0 b1 b2 b3 cs s0 s1 s2 s3 ss hst r rs' hro hc ih =>
    simp only [Bool.not_eq_true] at hst hro
    simp only [walkToT, hst, hro, hc, Bool.false_eq_true, ↓reduceIte]
    exact ih hsuf
  | case5 o prev b0 b1 b2 b3 cs s0 s1 s2 s3 ss hst r rs' hro hc =>
    simp only [Bool.not_eq_true] at hst hro hc
    simp only [walkToT, hst, hro, hc, Bool.false_eq_true, ↓reduceIte]
  | case6 o prev b0 b1 b2 b3 cs s0 s1 s2 s3 ss hst hc ih =>
    simp only [Bool.not_eq_true] at hst
    simp only [walkToT, hst, hc, Bool.false_eq_true, ↓reduceIte]
    exact ih hsuf
  | case7 o prev b0 b1 b2 b3 cs s0 s1 s2 s3 ss hst hc =>
    simp only [Bool.not_eq_true] at hst hc
    simp only [walkToT, hst, hc, Bool.false_eq_true, ↓reduceIte]
  | case8 _ _ _ cs ss h1 h2 =>
    rcases cs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, cs⟩⟩⟩⟩ <;>
      rcases ss with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, ss⟩⟩⟩⟩ <;>
      first
        | exact (h1 _ _ _ _ _ _ _ _ _ _ rfl rfl).elim
        | exact (h2 _ _ _ _ _ _ _ _ _ _ rfl rfl).elim
        | simp_all [walkToT]
  | case9 _ _ _ cs ss h1 h2 =>
    rcases cs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, cs⟩⟩⟩⟩ <;>
      rcases ss with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, ss⟩⟩⟩⟩ <;>
      first
        | exact (h1 _ _ _ _ _ _ _ _ _ _ rfl rfl).elim
        | exact (h2 _ _ _ _ _ _ _ _ _ _ rfl rfl).elim
        | simp_all [walkToT]

/-! ## Chunked Text Check over a Symbol Tree -/

theorem rDrop_suffix {α : Type} (k : Nat) (l : List α) : rDrop k l <:+ l := by
  rw [rDrop_eq]; exact List.drop_suffix k l

/-- `textOkChunk` with targets resolved through `t` (one chunk of `textOkChunksT`). -/
noncomputable def textOkChunkT (L : Lib) (ly : Layout) (t : VecTree SymSlot)
    (rl : List (Snapshot.Region × Nat)) (o : Nat) (prev : Bool) (k o' : Nat) (prev' : Bool)
    (k' : Nat) : Bool :=
  match lRegionView ly.base rl with
  | some (p, bs, _) =>
    p == Perm.rx &&
      match walkToT L ly t o' o prev (rDrop k L.relocs) (rDrop o L.code) (rDrop o bs) with
      | some (q, rs) => q == prev' && Nat.beq (rLen rs + k') (rLen L.relocs)
      | none => false
  | none => false

/-- `textOkTail` with targets resolved through `t` (the last chunk of `textOkChunksT`). -/
noncomputable def textOkTailT (L : Lib) (ly : Layout) (t : VecTree SymSlot)
    (rl : List (Snapshot.Region × Nat)) (o : Nat) (prev : Bool) (k : Nat) : Bool :=
  match lRegionView ly.base rl with
  | some (p, bs, _) =>
    p == Perm.rx && walkT L ly t o prev (rDrop k L.relocs) (rDrop o L.code) (rDrop o bs)
  | none => false

/-- `textOkChunks` with targets resolved through `t`. -/
noncomputable def textOkChunksT (L : Lib) (ly : Layout) (t : VecTree SymSlot)
    (rl : List (Snapshot.Region × Nat)) : Nat → Bool → Nat → List (Nat × Bool × Nat) → Prop
  | o, prev, k, [] => textOkTailT L ly t rl o prev k = true
  | o, prev, k, (o', prev', k') :: bs =>
    textOkChunkT L ly t rl o prev k o' prev' k' = true ∧ textOkChunksT L ly t rl o' prev' k' bs

theorem textOkChunksT_nil {L : Lib} {ly : Layout} {t : VecTree SymSlot}
    {rl : List (Snapshot.Region × Nat)} {o : Nat} {prev : Bool} {k : Nat}
    (h : textOkTailT L ly t rl o prev k = true) : textOkChunksT L ly t rl o prev k [] := h

theorem textOkChunksT_cons {L : Lib} {ly : Layout} {t : VecTree SymSlot}
    {rl : List (Snapshot.Region × Nat)} {o : Nat} {prev : Bool} {k o' : Nat} {prev' : Bool}
    {k' : Nat} {bs : List (Nat × Bool × Nat)}
    (h : textOkChunkT L ly t rl o prev k o' prev' k' = true)
    (hr : textOkChunksT L ly t rl o' prev' k' bs) :
    textOkChunksT L ly t rl o prev k ((o', prev', k') :: bs) := ⟨h, hr⟩

theorem textOkChunkT_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : SymTreeOk L ly t) (rl : List (Snapshot.Region × Nat)) (o : Nat) (prev : Bool)
    (k o' : Nat) (prev' : Bool) (k' : Nat) :
    textOkChunkT L ly t rl o prev k o' prev' k' = textOkChunk L ly rl o prev k o' prev' k' := by
  unfold textOkChunkT textOkChunk
  rcases lRegionView ly.base rl with _ | ⟨p, bs, m⟩
  · rfl
  · simp only [walkToT_eq hok ht (rDrop_suffix k L.relocs)]
    rcases walkTo L ly o' o prev (rDrop k L.relocs) (rDrop o L.code) (rDrop o bs) with _ | ⟨q, rs⟩ <;>
      rfl

theorem textOkTailT_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : SymTreeOk L ly t) (rl : List (Snapshot.Region × Nat)) (o : Nat) (prev : Bool)
    (k : Nat) : textOkTailT L ly t rl o prev k = textOkTail L ly rl o prev k := by
  unfold textOkTailT textOkTail
  rcases lRegionView ly.base rl with _ | ⟨p, bs, m⟩
  · rfl
  · simp only [walkT_eq hok ht (rDrop_suffix k L.relocs)]

/-- Tree-backed text chunks are text chunks when `t` holds the symbol slots. -/
theorem textOkChunks_of_T {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : SymTreeOk L ly t) {rl : List (Snapshot.Region × Nat)} :
    ∀ (o : Nat) (prev : Bool) (k : Nat) (bds : List (Nat × Bool × Nat)),
      textOkChunksT L ly t rl o prev k bds → textOkChunks L ly rl o prev k bds
  | o, prev, k, [], h => by
    simp only [textOkChunksT, textOkTailT_eq hok ht] at h
    exact h
  | o, prev, k, (o', prev', k') :: bds, h => by
    obtain ⟨h1, h2⟩ := h
    rw [textOkChunkT_eq hok ht] at h1
    exact ⟨h1, textOkChunks_of_T hok ht o' prev' k' bds h2⟩

/-- `checkDisjoint_spec_chunks` with tree-backed text chunks: `hst` checks the symbol tree `t` by
    index chunks and `htext` walks the text through `t`. -/
theorem checkDisjoint_spec_chunksT {L : Lib} {ly : Layout} {nameChars : List (List Char)}
    {img : ElfImage} {symChars : List (List Char × BitVec 64)} {lens : List Nat}
    {t : VecTree SymSlot} {sb : List Nat} {tb : List (Nat × Bool × Nat)} {db : List Nat}
    (hnames : L.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hlens : img.segments.map (fun r => rLen r.bytes) = lens)
    (hnn : namesNodup nameChars = true) (hids : L.idsOk = true)
    (htp : textPlaceableR L ly = true) (hdp : dataPlaceableR L ly = true)
    (hst : symTreeOkChunks L ly t 0 sb)
    (htext : textOkChunksT L ly t (img.segments.zip lens) 0 false 0 tb)
    (hdata : dataOkChunks L ly (img.segments.zip lens) 0 db)
    (hexp : exportsOk L ly nameChars (prepareCharAssocVal symChars) = true)
    (hdd : dataDisjointROB L ly = true) :
    L.toLib.Placeable (ly.toPlacement L.names) ∧ L.toLib.InElf img (ly.toPlacement L.names) ∧
      L.toLib.DataDisjoint (ly.toPlacement L.names) :=
  checkDisjoint_spec_chunks hnames hsyms hlens hnn hids htp hdp
    (textOkChunks_of_T (Lib.idsOk_spec hids) (symTreeOk_of_chunks hst) 0 false 0 tb htext)
    hdata hexp hdd

end Arm64.Obj.Interned

end
