/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Split

/-!
# Chunked Placement Verification for Single-Block Libraries

Splits `Obj.Interned.checkDisjoint_spec` for a large single-block library into bounded-size facts
checkable separately by `decide +kernel`: resumable text-walk chunks (`walkTo`, `textOkChunks`),
data-walk chunks (`dataOkChunks`), a read-only-aware data-disjointness check (`dataDisjointROB`),
and `List.rec`-based placeability checks (`textPlaceableR`, `dataPlaceableR`), composed by
`checkDisjoint_spec_chunks`.
-/

@[expose] public section

set_option autoImplicit false

namespace Arm64.Obj.Interned
open Arm64 Arm64.Process ProofLib.ProgramReflection ProofLib.ObjectLoad ProofLib.Placed.Split


/-! ## Composing the text walk -/

/-- `walk` from offset `o` up to offset `stop`: `some (prev', rs')` if every word in `[o, stop)`
    passes the per-word test of `walk`, where `prev'` is the `prev` flag at `stop` and `rs'` the
    relocations not yet consumed. `none` if a word fails or the bytes run out before `stop`. -/
def walkTo (L : Lib) (ly : Layout) (stop : Nat) :
    Nat → Bool → List Reloc → List (BitVec 8) → List (BitVec 8) → Option (Bool × List Reloc)
  | o, prev, rs, b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss =>
    if Nat.beq o stop then some (prev, rs) else
    match rs with
    | r :: rs' =>
      if Nat.beq r.off o then
        let w := b3 ++ b2 ++ b1 ++ b0
        let rel := relaxHead ly o r w rs' cs
        if bytesOfWordLE (siteOut L ly o r w rel prev) == [s0, s1, s2, s3] &&
            siteRangeOk L ly o r prev then walkTo L ly stop (o + 4) rel rs' cs ss
        else none
      else if b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 then
        walkTo L ly stop (o + 4) false rs cs ss
      else none
    | [] =>
      if b0 == s0 && b1 == s1 && b2 == s2 && b3 == s3 then
        walkTo L ly stop (o + 4) false [] cs ss
      else none
  | o, prev, rs, _, _ => if Nat.beq o stop then some (prev, rs) else none

/-- Soundness of `walkTo`: it stops at or before `stop`, leaves a suffix of the relocations, and
    a `walk` resumed where it stopped gives the `walk` from where it started. -/
theorem walkTo_spec {L : Lib} {ly : Layout} {stop : Nat} :
    ∀ {o : Nat} {prev : Bool} {rs : List Reloc} {cs ss : List (BitVec 8)} {prev' : Bool}
      {rs' : List Reloc}, walkTo L ly stop o prev rs cs ss = some (prev', rs') →
      o ≤ stop ∧ rs' <:+ rs ∧
        (walk L ly stop prev' rs' (cs.drop (stop - o)) (ss.drop (stop - o)) = true →
          walk L ly o prev rs cs ss = true) := by
  intro o prev rs cs ss prev' rs' h
  fun_induction walkTo L ly stop o prev rs cs ss generalizing prev' rs'
  case case1 =>
    rename_i hst
    cases h
    rw [Nat.beq_eq] at hst
    subst hst
    exact ⟨Nat.le_refl _, List.suffix_refl _, by simp⟩
  case case8 =>
    rename_i hst _
    cases h
    rw [Nat.beq_eq] at hst
    subst hst
    exact ⟨Nat.le_refl _, List.suffix_refl _, by simp⟩
  case case3 => cases h
  case case5 => cases h
  case case7 => cases h
  case case9 => cases h
  case case2 =>
    rename_i hst _ _ hr _ _ ht ih
    obtain ⟨hle, hsuf, hw⟩ := ih h
    have e : ∀ {n m : Nat}, n + 4 ≤ m → m - n = m - (n + 4) + 1 + 1 + 1 + 1 := by omega
    refine ⟨by omega, hsuf.trans (List.suffix_cons _ _), fun hrest => ?_⟩
    rw [e hle] at hrest
    simp only [List.drop_succ_cons] at hrest
    rw [Nat.beq_eq] at hr
    simp only [walk, hr, Nat.beq_refl, ↓reduceIte, Bool.and_eq_true] at ht ⊢
    exact ⟨ht, hw hrest⟩
  case case4 =>
    rename_i hst _ _ hr ht ih
    obtain ⟨hle, hsuf, hw⟩ := ih h
    have e : ∀ {n m : Nat}, n + 4 ≤ m → m - n = m - (n + 4) + 1 + 1 + 1 + 1 := by omega
    refine ⟨by omega, hsuf, fun hrest => ?_⟩
    rw [e hle] at hrest
    simp only [List.drop_succ_cons] at hrest
    simp only [Bool.not_eq_true] at hr
    simp only [walk, hr, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ht ⊢
    exact ⟨ht, hw hrest⟩
  case case6 =>
    rename_i hst ht ih
    obtain ⟨hle, hsuf, hw⟩ := ih h
    have e : ∀ {n m : Nat}, n + 4 ≤ m → m - n = m - (n + 4) + 1 + 1 + 1 + 1 := by omega
    refine ⟨by omega, hsuf, fun hrest => ?_⟩
    rw [e hle] at hrest
    simp only [List.drop_succ_cons] at hrest
    simp only [walk, Bool.and_eq_true] at ht ⊢
    exact ⟨ht, hw hrest⟩


/-- The text walk over `a ++ b` from offset `o`: a `walkTo` over `a` that stops at its end,
    followed by a `walk` over `b` from there. -/
theorem walk_append {L : Lib} {ly : Layout} {o : Nat} {prev prev' : Bool}
    {rs rs' : List Reloc} {a b ss : List (BitVec 8)}
    (h1 : walkTo L ly (o + a.length) o prev rs (a ++ b) ss = some (prev', rs'))
    (h2 : walk L ly (o + a.length) prev' rs' b (ss.drop a.length) = true) :
    walk L ly o prev rs (a ++ b) ss = true := by
  have ⟨_, _, hw⟩ := walkTo_spec h1
  rw [Nat.add_sub_cancel_left, List.drop_left] at hw
  exact hw h2

/-! ## Chunked text check -/

/-- The text walk over words `[o, o')`, from flag `prev` with `k` relocations consumed, ends with
    flag `prev'` and `k'` relocations consumed. -/
noncomputable def textOkChunk (L : Lib) (ly : Layout) (rl : List (Snapshot.Region × Nat))
    (o : Nat) (prev : Bool) (k o' : Nat) (prev' : Bool) (k' : Nat) : Bool :=
  match lRegionView ly.base rl with
  | some (p, bs, _) =>
    p == Perm.rx &&
      match walkTo L ly o' o prev (rDrop k L.relocs) (rDrop o L.code) (rDrop o bs) with
      | some (q, rs) => q == prev' && Nat.beq (rLen rs + k') (rLen L.relocs)
      | none => false
  | none => false

/-- The text walk from word `o` to the end. -/
noncomputable def textOkTail (L : Lib) (ly : Layout) (rl : List (Snapshot.Region × Nat))
    (o : Nat) (prev : Bool) (k : Nat) : Bool :=
  match lRegionView ly.base rl with
  | some (p, bs, _) =>
    p == Perm.rx && walk L ly o prev (rDrop k L.relocs) (rDrop o L.code) (rDrop o bs)
  | none => false

/-- The text walk chunks `[o, o₁), [o₁, o₂), ..., [oₙ, end)` all succeed; chunk `i` ends at the
    boundary `(oᵢ, prevᵢ, kᵢ)` (word offset, `prev` flag, relocations consumed). -/
noncomputable def textOkChunks (L : Lib) (ly : Layout) (rl : List (Snapshot.Region × Nat)) :
    Nat → Bool → Nat → List (Nat × Bool × Nat) → Prop
  | o, prev, k, [] => textOkTail L ly rl o prev k = true
  | o, prev, k, (o', prev', k') :: bs =>
    textOkChunk L ly rl o prev k o' prev' k' = true ∧ textOkChunks L ly rl o' prev' k' bs

theorem textOkChunks_nil {L : Lib} {ly : Layout} {rl : List (Snapshot.Region × Nat)} {o : Nat}
    {prev : Bool} {k : Nat} (h : textOkTail L ly rl o prev k = true) :
    textOkChunks L ly rl o prev k [] := h

theorem textOkChunks_cons {L : Lib} {ly : Layout} {rl : List (Snapshot.Region × Nat)}
    {o : Nat} {prev : Bool} {k o' : Nat} {prev' : Bool} {k' : Nat}
    {bs : List (Nat × Bool × Nat)} (h : textOkChunk L ly rl o prev k o' prev' k' = true)
    (hr : textOkChunks L ly rl o' prev' k' bs) : textOkChunks L ly rl o prev k ((o', prev', k') :: bs) :=
  ⟨h, hr⟩

/-- A suffix of `l.drop k` of length `l.length - k'` is `l.drop k'`. -/
theorem suffix_drop_eq {α : Type} {l s : List α} {k k' : Nat} (hs : s <:+ l.drop k)
    (hlen : s.length + k' = l.length) : s = l.drop k' := by
  obtain ⟨t, ht⟩ := List.suffix_iff_exists_eq_append.1 hs
  have hl : l = (l.take k ++ t) ++ s := by rw [List.append_assoc, ← ht, List.take_append_drop]
  have hn := congrArg List.length hl
  simp only [List.length_append, List.length_take] at hn
  calc s = ((l.take k ++ t) ++ s).drop (l.take k ++ t).length := (List.drop_left ..).symm
    _ = l.drop k' := by
      rw [← hl]; congr 1; simp only [List.length_append, List.length_take]; omega

/-- Chunked text walks from `(o, prev, k)` give the region view at `ly.base` and the text walk
    from `(o, prev, k)` to the end. -/
theorem walk_of_textOkChunks {L : Lib} {ly : Layout} {regions : List Snapshot.Region} :
    ∀ (o : Nat) (prev : Bool) (k : Nat) (bds : List (Nat × Bool × Nat)),
      textOkChunks L ly (regions.map fun r => (r, r.bytes.length)) o prev k bds →
      ∃ bs m, regionView ly.base regions = some (Perm.rx, bs, m) ∧
        walk L ly o prev (L.relocs.drop k) (L.code.drop o) (bs.drop o) = true
  | o, prev, k, [], h => by
    simp only [textOkChunks, textOkTail, lRegionView_eq, rDrop_eq] at h
    split at h
    · rename_i p bs m hv
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨bs, m, by rw [hv, h.1], h.2⟩
    · cases h
  | o, prev, k, (o', prev', k') :: bds, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨bs, m, hv, hw⟩ := walk_of_textOkChunks o' prev' k' bds h2
    refine ⟨bs, m, hv, ?_⟩
    simp only [textOkChunk, lRegionView_eq, rDrop_eq, rLen_eq, hv] at h1
    simp only [beq_self_eq_true, Bool.true_and] at h1
    split at h1
    · rename_i q rs hwt
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq] at h1
      obtain ⟨hq, hlen⟩ := h1
      subst hq
      have ⟨hle, hsuf, hw'⟩ := walkTo_spec hwt
      have hrs := suffix_drop_eq hsuf hlen
      subst hrs
      apply hw'
      have e : o + (o' - o) = o' := by omega
      simp only [List.drop_drop, e]
      exact hw
    · cases h1


/-- Chunked text walks from word `0` prove `textOk`. -/
theorem textOk_of_chunks {L : Lib} {ly : Layout} {regions : List Snapshot.Region}
    {bds : List (Nat × Bool × Nat)}
    (h : textOkChunks L ly (regions.map fun r => (r, r.bytes.length)) 0 false 0 bds) :
    textOk L ly regions = true := by
  obtain ⟨bs, m, hv, hw⟩ := walk_of_textOkChunks 0 false 0 bds h
  simp only [List.drop_zero] at hw
  simp only [textOk, hv, beq_self_eq_true, Bool.true_and]
  exact hw

/-! ## Chunked data check -/

/-- The data walk over objects `[s, t)` of `L` from a fresh view. -/
noncomputable def dataOkChunk (L : Lib) (ly : Layout) (rl : List (Snapshot.Region × Nat))
    (s t : Nat) : Bool :=
  lDataWalk L ly rl none (rTake (t - s) (rDrop s L.data))

/-- The data walk over objects `[s, end)` of `L` from a fresh view. -/
noncomputable def dataOkTail (L : Lib) (ly : Layout) (rl : List (Snapshot.Region × Nat))
    (s : Nat) : Bool :=
  lDataWalk L ly rl none (rDrop s L.data)

/-- The data walk chunks `[s, t₁), [t₁, t₂), ..., [tₖ, end)` all succeed. -/
noncomputable def dataOkChunks (L : Lib) (ly : Layout) (rl : List (Snapshot.Region × Nat)) :
    Nat → List Nat → Prop
  | s, [] => dataOkTail L ly rl s = true
  | s, t :: ts => dataOkChunk L ly rl s t = true ∧ dataOkChunks L ly rl t ts

theorem dataOkChunks_nil {L : Lib} {ly : Layout} {rl : List (Snapshot.Region × Nat)} {s : Nat}
    (h : dataOkTail L ly rl s = true) : dataOkChunks L ly rl s [] := h

theorem dataOkChunks_cons {L : Lib} {ly : Layout} {rl : List (Snapshot.Region × Nat)}
    {s t : Nat} {ts : List Nat} (h : dataOkChunk L ly rl s t = true)
    (hr : dataOkChunks L ly rl t ts) : dataOkChunks L ly rl s (t :: ts) := ⟨h, hr⟩

/-- Chunked data walks from object `s` map every later object at its address with the permission
    `PlacedLib.InElf` asks for (what `dataWalk_sound` gives for the whole walk). -/
theorem dataObj_of_chunks {L : Lib} {ly : Layout} {regions : List Snapshot.Region} :
    ∀ (s : Nat) (ts : List Nat), dataOkChunks L ly (regions.map fun r => (r, r.bytes.length)) s ts →
      ∀ d ∈ L.data.drop s, ∃ p, View regions (ly.addrs.getD d.sym 0#64) p (patchedDataId L ly d) ∧
        dataPermOk d.readOnly p = true
  | s, [], h, d, hd => by
    simp only [dataOkChunks, dataOkTail, lDataWalk_eq, rDrop_eq] at h
    exact dataWalk_sound none _ (fun _ _ _ hc => nomatch hc) h d hd
  | s, t :: ts, h, d, hd => by
    simp only [dataOkChunks, dataOkChunk, lDataWalk_eq, rDrop_eq, rTake_eq] at h
    rw [← List.take_append_drop (t - s) (L.data.drop s), List.mem_append] at hd
    rcases hd with hd | hd
    · exact dataWalk_sound none _ (fun _ _ _ hc => nomatch hc) h.1 d hd
    · refine dataObj_of_chunks t ts h.2 d (mem_drop_of_le (k := s + (t - s)) (by omega) ?_)
      rwa [List.drop_drop] at hd

/-! ## Read-only-aware data disjointness -/

/-- `(readOnly, addr, len)` entries of the data objects of `L` under `ly`, with template lengths
    (`bytes.length + zeroTail`) and `List.rec` lookups. -/
noncomputable def dataEntriesRO (L : Lib) (ly : Layout) : List (Bool × BitVec 64 × Nat) :=
  L.data.map fun d => (d.readOnly, rGetD ly.addrs d.sym 0#64, rLen d.bytes + d.zeroTail)

/-- Read-only-aware `DataDisjoint` check (read-only objects may share tail-merged bytes). Tries
    the linear scan `dataScanB` for address-ordered objects, falling back to pairwise comparison
    `dataEntriesDisjointB`. -/
noncomputable def dataDisjointROB (L : Lib) (ly : Layout) : Bool :=
  dataScanB 0 0 (dataEntriesRO L ly) || dataEntriesDisjointB (dataEntriesRO L ly)

theorem dataDisjoint_of_dataDisjointROB {L : Lib} {ly : Layout} (hnd : L.names.Nodup)
    (hok : L.IdsOk) (hpl : L.toLib.Placeable (ly.toPlacement L.names))
    (h : dataDisjointROB L ly = true) : L.toLib.DataDisjoint (ly.toPlacement L.names) := by
  have hpd : dataEntriesDisjointB (dataEntriesRO L ly) = true := by
    simp only [dataDisjointROB, Bool.or_eq_true] at h
    exact h.elim dataEntriesDisjointB_of_scan id
  have ⟨_, hpw⟩ := dataEntriesDisjointB_pairwise hpd
  have heq : (L.toLib.data.map fun d => (d.readOnly, (ly.toPlacement L.names).ρ d.sym,
      (L.toLib.patchedData (ly.toPlacement L.names) d).length)) = dataEntriesRO L ly := by
    simp only [Lib.toLib, dataEntriesRO, List.map_map, rGetD_eq, rLen_eq]
    refine List.map_congr_left fun d hd => ?_
    have hdi : d.toInfo L.names ∈ L.toLib.data := List.mem_map_of_mem hd
    simp only [Function.comp_apply, Prod.mk.injEq]
    refine ⟨rfl, toPlacement_ρ hnd (hok.data d hd).1, ?_⟩
    rw [PlacedLib.length_patchedData fun r hr => (hpl.data_relocs_ok _ hdi r hr).2.1]
    rfl
  rw [← heq, List.pairwise_map] at hpw
  exact hpw

/-! ## Segment-free checks with `List.rec` lookups -/

/-- `textPlaceableB` with `rLen` / `rGetD` for linear-time kernel reduction. -/
noncomputable def textPlaceableR (L : Lib) (ly : Layout) : Bool :=
  let len := rLen L.code
  Nat.blt 0 L.align && Nat.beq (L.align % 4) 0 && Nat.beq (ly.base.toNat % L.align) 0 &&
    Nat.ble (ly.base.toNat + len) 18446744073709551616 && Nat.beq (len % 4) 0 &&
    relocsWf len 0 L.relocs &&
    L.symbols.all (fun s => Nat.beq (s.2 % 4) 0 && Nat.ble s.2 len) &&
    L.externs.all fun e =>
      (lookupId e L.symbols).isNone && Nat.ble len (rGetD ly.addrs e 0#64 - ly.base).toNat

theorem textPlaceableR_eq (L : Lib) (ly : Layout) : textPlaceableR L ly = textPlaceableB L ly := by
  simp only [textPlaceableR, textPlaceableB, rLen_eq, rGetD_eq]

/-- `dataPlaceableB` with `rLen` / `rGetD`. -/
noncomputable def dataPlaceableR (L : Lib) (ly : Layout) : Bool :=
  natNodupFast (L.data.map (·.sym)) &&
    L.data.all fun d =>
      let a := rGetD ly.addrs d.sym 0#64
      (lookupId d.sym L.symbols).isNone && Nat.blt 0 d.align && Nat.beq (a.toNat % d.align) 0 &&
        Nat.ble (a.toNat + rLen d.bytes + d.zeroTail) 18446744073709551616 &&
        d.relocs.all (dataRelocOkB L ly a (rLen d.bytes))

theorem dataPlaceableR_eq (L : Lib) (ly : Layout) : dataPlaceableR L ly = dataPlaceableB L ly := by
  simp only [dataPlaceableR, dataPlaceableB, rLen_eq, rGetD_eq]


/-! ## Composed check -/

/-- `checkDisjoint_spec` from chunked facts: each `textOkChunk` / `textOkTail` / `dataOkChunk` /
    `dataOkTail` and each segment-free check is a separate kernel check of bounded size.
    `hlens` fixes the segment lengths so the chunks do not recompute them. -/
theorem checkDisjoint_spec_chunks {L : Lib} {ly : Layout} {nameChars : List (List Char)}
    {img : ElfImage} {symChars : List (List Char × BitVec 64)} {lens : List Nat}
    {tb : List (Nat × Bool × Nat)} {db : List Nat}
    (hnames : L.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hlens : img.segments.map (fun r => rLen r.bytes) = lens)
    (hnn : namesNodup nameChars = true) (hids : L.idsOk = true)
    (htp : textPlaceableR L ly = true) (hdp : dataPlaceableR L ly = true)
    (htext : textOkChunks L ly (img.segments.zip lens) 0 false 0 tb)
    (hdata : dataOkChunks L ly (img.segments.zip lens) 0 db)
    (hexp : exportsOk L ly nameChars (prepareCharAssocVal symChars) = true)
    (hdd : dataDisjointROB L ly = true) :
    L.toLib.Placeable (ly.toPlacement L.names) ∧ L.toLib.InElf img (ly.toPlacement L.names) ∧
      L.toLib.DataDisjoint (ly.toPlacement L.names) := by
  subst hlens
  simp only [rLen_eq, zip_map_self] at htext hdata
  rw [textPlaceableR_eq] at htp
  rw [dataPlaceableR_eq] at hdp
  have hnd := nodup_of_namesNodup hnames hnn
  have hok := Lib.idsOk_spec hids
  have hwf : relocsWf L.code.length 0 L.relocs = true := by
    simp only [textPlaceableB, Bool.and_eq_true] at htp
    exact htp.1.1.2
  have ⟨⟨p, bs, hv, hp, hpre⟩, hw⟩ := textOk_sound (ly := ly) hnd hok hwf (textOk_of_chunks htext)
  have hpl := placeable_of hnd hok htp hdp hw
  refine ⟨hpl, ⟨?_, ?_, exports_of hnd hok hnames hsyms hexp⟩,
    dataDisjoint_of_dataDisjointROB hnd hok hpl hdd⟩
  · simp only [Lib.toLib_text, toPlacement_base]
    exact elfMaps_of_view (hv.of_prefix hpre) (by simp [hp])
  · intro d hd
    simp only [Lib.toLib, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    obtain ⟨p, hv, hp⟩ := dataObj_of_chunks 0 db hdata d' (by rw [List.drop_zero]; exact hd')
    have hi := (hok.data d' hd').1
    rw [show (Data.toInfo L.names d').readOnly = d'.readOnly from rfl,
      show (ly.toPlacement L.names).ρ (Data.toInfo L.names d').sym = ly.addrs.getD d'.sym 0#64
        from toPlacement_ρ hnd hi]
    rw [show L.toLib.patchedData (ly.toPlacement L.names) (Data.toInfo L.names d') =
        patchedDataId L ly d' from patchedData_toLib hnd hok hd']
    exact elfMaps_of_view hv hp

end Arm64.Obj.Interned

end
