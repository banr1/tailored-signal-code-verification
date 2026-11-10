/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.CheckText
public import ProofLib.ObjectLoad

/-!
# Placed Library Checkers

Defines kernel-reducible boolean checkers for `Obj.PlacedLib.Placeable`, extern-address
distinctness `(lib.text.externs.map pl.ρ).Nodup`, and `Obj.PlacedLib.LinkedIn`. Includes both
ELF-backed segment walks (`check`) and ELF-free `VecTree`-accelerated checks (`checkPlaceable`,
`checkPlaceableExt`, and the split checkers `checkTextPlaceable`, `checkDataPlaceable`,
`checkTextRelocsOk`, `checkExternsDisjoint`).
-/

@[expose] public section

namespace Arm64.Obj.Interned

open Arm64.Process ProofLib.ObjectLoad ProofLib.ProgramReflection

set_option linter.literalFetch false

/-! ## Views of mapped bytes -/

/-- `bs` are the bytes at `[addr, addr + bs.length)` in `regions`, all with permission `p`, each
    address resolved as `Snapshot.cellAt` resolves it. -/
def View (regions : List Snapshot.Region) (addr : BitVec 64) (p : Perm) (bs : List (BitVec 8)) :
    Prop :=
  ∀ (i : Nat) (hi : i < bs.length),
    Snapshot.cellAt regions (addr + BitVec.ofNat 64 i) = some (some p, bs[i])

theorem View.drop {regions : List Snapshot.Region} {addr : BitVec 64} {p : Perm}
    {bs : List (BitVec 8)} (h : View regions addr p bs) (k : Nat) :
    View regions (addr + BitVec.ofNat 64 k) p (bs.drop k) := by
  intro i hi
  rw [List.getElem_drop]
  have := h (k + i) (by simp at hi; omega)
  rw [← this, BitVec.add_assoc, BitVec.ofNat_add]

theorem View.of_prefix {regions : List Snapshot.Region} {addr : BitVec 64} {p : Perm}
    {bs xs : List (BitVec 8)} (h : View regions addr p bs) (hp : xs <+: bs) :
    View regions addr p xs := by
  intro i hi
  rw [hp.getElem]
  exact h i _

theorem elfMaps_of_view {img : ElfImage} {addr : BitVec 64} {p : Perm} {bs : List (BitVec 8)}
    {ok : Perm → Bool} (h : View img.segments addr p bs) (hok : ok p = true) :
    ElfMaps img addr bs ok :=
  fun i hi => ⟨p, h i hi, hok⟩

/-- The first region of `regions` holding `addr`, as `Snapshot.cellAt` finds it: its permission,
    its bytes from `addr` on, and their number. Fails unless no earlier region holds any address
    of that range. -/
def regionView (addr : BitVec 64) : List Snapshot.Region → Option (Perm × List (BitVec 8) × Nat)
  | [] => none
  | r :: rs =>
    let d := (addr - r.start).toNat
    let len := r.bytes.length
    if Nat.blt d len then
      if Nat.ble len 18446744073709551616 then some (r.perm, r.bytes.drop d, len - d) else none
    else
      match regionView addr rs with
      | some (p, bs, m) =>
        if Nat.ble len d && Nat.ble (d + m) 18446744073709551616 then some (p, bs, m) else none
      | none => none

theorem cellAt_cons_miss {r : Snapshot.Region} {rs : List Snapshot.Region} {a : BitVec 64}
    (h : r.bytes.length ≤ (a - r.start).toNat) :
    Snapshot.cellAt (r :: rs) a = Snapshot.cellAt rs a := by
  have h' : ¬ (a - r.start).toNat < r.bytes.length := by omega
  simp only [Snapshot.cellAt, List.findSome?_cons, h', ↓reduceDIte]

theorem cellAt_cons_hit {r : Snapshot.Region} {rs : List Snapshot.Region} {a : BitVec 64}
    (h : (a - r.start).toNat < r.bytes.length) :
    Snapshot.cellAt (r :: rs) a = some (some r.perm, r.bytes[(a - r.start).toNat]) := by
  simp only [Snapshot.cellAt, List.findSome?_cons, h, ↓reduceDIte]

theorem view_of_regionView : ∀ {regions : List Snapshot.Region} {addr : BitVec 64} {p : Perm}
    {bs : List (BitVec 8)} {m : Nat}, regionView addr regions = some (p, bs, m) →
    m = bs.length ∧ View regions addr p bs
  | [], _, _, _, _, h => nomatch h
  | r :: rs, addr, p, bs, m, h => by
    simp only [regionView] at h
    by_cases hd : (addr - r.start).toNat < r.bytes.length
    · rw [show Nat.blt (addr - r.start).toNat r.bytes.length = true by rw [Nat.blt_eq]; exact hd] at h
      simp only [↓reduceIte] at h
      split at h
      · rename_i hlen
        rw [Nat.ble_eq] at hlen
        cases h
        refine ⟨by simp, fun i hi => ?_⟩
        simp only [List.length_drop] at hi
        have hidx : (addr + BitVec.ofNat 64 i - r.start).toNat = (addr - r.start).toNat + i := by
          rw [show addr + BitVec.ofNat 64 i - r.start = (addr - r.start) + BitVec.ofNat 64 i by
            bv_omega]
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]
          have := (addr - r.start).isLt
          rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [cellAt_cons_hit (by omega), List.getElem_drop]
        simp only [hidx]
      · cases h
    · rw [show Nat.blt (addr - r.start).toNat r.bytes.length = false by
        rw [Bool.eq_false_iff]; intro h'; rw [Nat.blt_eq] at h'; omega] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i p' bs' m' hrec
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, Nat.ble_eq] at hc
          cases h
          have ⟨hm, hv⟩ := view_of_regionView hrec
          refine ⟨hm, fun i hi => ?_⟩
          rw [cellAt_cons_miss]
          · exact hv i hi
          · have hidx : (addr + BitVec.ofNat 64 i - r.start).toNat = (addr - r.start).toNat + i := by
              rw [show addr + BitVec.ofNat 64 i - r.start = (addr - r.start) + BitVec.ofNat 64 i by
                bv_omega]
              rw [BitVec.toNat_add, BitVec.toNat_ofNat]
              rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
        · cases h
      · cases h

/-! ## Text in the image -/

/-- The patched text of `L` under `ly` is mapped `r-x` at `ly.base` in `regions`, and every
    relocation site is in range (`walk`). -/
def textOk (L : Lib) (ly : Layout) (regions : List Snapshot.Region) : Bool :=
  match regionView ly.base regions with
  | some (p, bs, _) => p == Perm.rx && walk L ly 0 false L.relocs L.code bs
  | none => false

theorem walk_sound_zero {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    {seg : List (BitVec 8)} (hwf : relocsWf L.code.length 0 L.relocs = true)
    (hw : walk L ly 0 false L.relocs L.code seg = true) : WalkOk L ly 0 L.relocs seg :=
  walk_sound hnd hok L.code seg 0 false [] L.relocs (List.drop_zero) rfl rfl (by simp) hwf
    (by simp) hw

theorem textOk_sound {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    {regions : List Snapshot.Region} (hwf : relocsWf L.code.length 0 L.relocs = true)
    (h : textOk L ly regions = true) :
    (∃ p bs, View regions ly.base p bs ∧ p = Perm.rx ∧
      (L.block.patched (ly.toPlacement L.names)).IsPrefix bs) ∧
    WalkOk L ly 0 L.relocs (L.block.patched (ly.toPlacement L.names) ++ []) := by
  unfold textOk at h
  split at h
  · rename_i p bs m hv
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hw := walk_sound_zero (ly := ly) hnd hok hwf h.2
    refine ⟨⟨p, bs, (view_of_regionView hv).2, h.1, by simpa using hw.1⟩, ?_⟩
    exact ⟨by simp, hw.2.1, hw.2.2⟩
  · cases h

/-! ## Data objects in the image -/

def dropN? {α : Type} : Nat → List α → Option (List α)
  | 0, l => some l
  | _ + 1, [] => none
  | n + 1, _ :: l => dropN? n l

theorem dropN?_eq {α : Type} {k : Nat} {l l' : List α} (h : dropN? k l = some l') :
    l' = l.drop k := by
  induction k generalizing l with
  | zero => cases h; rfl
  | succ n ih =>
    cases l with
    | nil => cases h
    | cons _ l => exact ih h

/-- The permission `PlacedLib.InElf` asks for a data object. -/
def dataPermOk (readOnly : Bool) (p : Perm) : Bool := if readOnly then p.r else p == Perm.rw

/-- A view at the address of the next data object: from the current view `cur` if the object
    lies in it, else from `regionView`. -/
def nextView (regions : List Snapshot.Region) (a : BitVec 64) :
    Option (BitVec 64 × Perm × List (BitVec 8)) → Option (Perm × List (BitVec 8))
  | some (c, p, bs) =>
    if Nat.ble c.toNat a.toNat then
      match dropN? (a - c).toNat bs with
      | some bs' => some (p, bs')
      | none => (regionView a regions).map fun v => (v.1, v.2.1)
    else (regionView a regions).map fun v => (v.1, v.2.1)
  | none => (regionView a regions).map fun v => (v.1, v.2.1)

theorem nextView_sound {regions : List Snapshot.Region} {a : BitVec 64}
    {cur : Option (BitVec 64 × Perm × List (BitVec 8))}
    (hcur : ∀ c p bs, cur = some (c, p, bs) → View regions c p bs) {p : Perm}
    {bs : List (BitVec 8)} (h : nextView regions a cur = some (p, bs)) : View regions a p bs := by
  have fresh : (regionView a regions).map (fun v => (v.1, v.2.1)) = some (p, bs) →
      View regions a p bs := by
    intro h'
    cases hv : regionView a regions with
    | none => rw [hv] at h'; cases h'
    | some v =>
      rw [hv] at h'
      obtain ⟨p', bs', m'⟩ := v
      cases h'
      exact (view_of_regionView hv).2
  match cur, hcur, h with
  | none, _, h => exact fresh h
  | some (c, p0, bs0), hcur, h =>
    simp only [nextView] at h
    by_cases hc : c.toNat ≤ a.toNat
    · rw [show Nat.ble c.toNat a.toNat = true by rw [Nat.ble_eq]; exact hc] at h
      simp only [↓reduceIte] at h
      cases hd : dropN? (a - c).toNat bs0 with
      | none => rw [hd] at h; exact fresh h
      | some bs' =>
        rw [hd] at h
        cases h
        have := (hcur c _ bs0 rfl).drop (a - c).toNat
        rw [← dropN?_eq hd, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          show c + (a - c) = a by bv_omega] at this
        exact this
    · rw [show Nat.ble c.toNat a.toNat = false by
        rw [Bool.eq_false_iff]; intro h'; rw [Nat.ble_eq] at h'; omega] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact fresh h

/-- Every data object's patched bytes are mapped at its address with the permission
    `PlacedLib.InElf` asks for. `cur` is a view reused for objects that lie inside it. -/
def dataWalk (L : Lib) (ly : Layout) (regions : List Snapshot.Region) :
    Option (BitVec 64 × Perm × List (BitVec 8)) → List Data → Bool
  | _, [] => true
  | cur, d :: ds =>
    let a := ly.addrs.getD d.sym 0#64
    match nextView regions a cur with
    | some (p, bs) =>
      dataPermOk d.readOnly p && (patchedDataId L ly d).isPrefixOf bs &&
        dataWalk L ly regions (some (a, p, bs)) ds
    | none => false

theorem dataWalk_sound {L : Lib} {ly : Layout} {regions : List Snapshot.Region} :
    ∀ (cur : Option (BitVec 64 × Perm × List (BitVec 8))) (ds : List Data),
      (∀ c p bs, cur = some (c, p, bs) → View regions c p bs) →
      dataWalk L ly regions cur ds = true →
      ∀ d ∈ ds, ∃ p, View regions (ly.addrs.getD d.sym 0#64) p (patchedDataId L ly d) ∧
        dataPermOk d.readOnly p = true
  | _, [], _, _, _, hd => nomatch hd
  | cur, d :: ds, hcur, h, d', hd' => by
    simp only [dataWalk] at h
    split at h
    · rename_i p bs hnv
      simp only [Bool.and_eq_true, List.isPrefixOf_iff_prefix] at h
      obtain ⟨⟨hp, hpre⟩, hrest⟩ := h
      have hv := nextView_sound hcur hnv
      rcases List.mem_cons.1 hd' with rfl | hm
      · exact ⟨p, hv.of_prefix hpre, hp⟩
      · exact dataWalk_sound _ ds (fun c p' bs' he => by cases he; exact hv) hrest d' hm
    · cases h

/-! ## `Placeable` -/

/-- `Nat` list without duplicates (quadratic; for short lists). -/
def natNodup : List Nat → Bool
  | [] => true
  | n :: ns => !memNat n ns && natNodup ns

theorem natNodup_spec : ∀ {l : List Nat}, natNodup l = true → l.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [natNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hm => ?_, natNodup_spec h.2⟩
    rw [← memNat_iff, h.1] at hm
    exact Bool.noConfusion hm

/-- `Nat` list without duplicates: linear `strictChain` fast path when strictly increasing or
    strictly decreasing, falling back to `natNodup`. -/
def natNodupFast (l : List Nat) : Bool :=
  strictChain Nat.blt l || strictChain (fun a b => Nat.blt b a) l || natNodup l

theorem natNodupFast_spec {l : List Nat} (h : natNodupFast l = true) : l.Nodup := by
  simp only [natNodupFast, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · have hp := strictChain_pairwise Nat.blt
      (fun {a b c} h₁ h₂ => by rw [Nat.blt_eq] at h₁ h₂ ⊢; omega) l h
    rw [List.nodup_iff_pairwise_ne]
    exact hp.imp fun {a b} hab => by rw [Nat.blt_eq] at hab; omega
  · have hp := strictChain_pairwise (fun a b => Nat.blt b a)
      (fun {a b c} h₁ h₂ => by rw [Nat.blt_eq] at h₁ h₂ ⊢; omega) l h
    rw [List.nodup_iff_pairwise_ne]
    exact hp.imp fun {a b} hab => by rw [Nat.blt_eq] at hab; omega
  · exact natNodup_spec h

/-- The text-block fields of `CodeBlock.Placeable` not covered by `walk`. -/
def textPlaceableB (L : Lib) (ly : Layout) : Bool :=
  let len := L.code.length
  Nat.blt 0 L.align && Nat.beq (L.align % 4) 0 && Nat.beq (ly.base.toNat % L.align) 0 &&
    Nat.ble (ly.base.toNat + len) 18446744073709551616 && Nat.beq (len % 4) 0 &&
    relocsWf len 0 L.relocs &&
    L.symbols.all (fun s => Nat.beq (s.2 % 4) 0 && Nat.ble s.2 len) &&
    L.externs.all fun e =>
      (lookupId e L.symbols).isNone && Nat.ble len (ly.addrs.getD e 0#64 - ly.base).toNat

/-- The range conditions of `PlacedLib.Placeable` on data relocation `r` of an object of `n`
    bytes at `addr`. -/
def dataRelocOkB (L : Lib) (ly : Layout) (addr : BitVec 64) (n : Nat) (r : Reloc) : Bool :=
  Nat.blt 0 (dataRelocWidth r.kind) && Nat.ble (r.off + dataRelocWidth r.kind) n &&
    match r.kind with
    | .abs32 => sInRange (-2147483648) 4294967296 (targetId L ly r)
    | .prel32 => sInRange (-2147483648) 2147483648 (targetId L ly r - (addr + BitVec.ofNat 64 r.off))
    | _ => true

/-- The data fields of `PlacedLib.Placeable`. -/
def dataPlaceableB (L : Lib) (ly : Layout) : Bool :=
  natNodupFast (L.data.map (·.sym)) &&
    L.data.all fun d =>
      let a := ly.addrs.getD d.sym 0#64
      (lookupId d.sym L.symbols).isNone && Nat.blt 0 d.align && Nat.beq (a.toNat % d.align) 0 &&
        Nat.ble (a.toNat + d.bytes.length + d.zeroTail) 18446744073709551616 &&
        d.relocs.all (dataRelocOkB L ly a d.bytes.length)

theorem lookupId_map_none {α : Type} {names : List String} (hnd : names.Nodup) {i : Nat}
    (hi : i < names.length) {syms : List (Nat × α)} (hok : ∀ s ∈ syms, s.1 < names.length)
    (h : (lookupId i syms).isNone = true) :
    lookup (names.getD i "") (syms.map fun s => (names.getD s.1 "", s.2)) = none := by
  rw [lookup_map_getD hnd hi syms hok]
  exact Option.isNone_iff_eq_none.1 h

theorem textPlaceable_of {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    (hp : textPlaceableB L ly = true) {seg : List (BitVec 8)}
    (hw : WalkOk L ly 0 L.relocs seg) : L.block.Placeable (ly.toPlacement L.names) := by
  simp only [textPlaceableB, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq,
    List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hwf⟩, hsyms⟩, hext⟩ := hp
  refine ⟨⟨h1, h2⟩, h3, by simpa using h4, by simpa using h5, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Lib.block_relocs, List.map_map]
    exact relocsWf_nodup hwf
  · intro r hr
    simp only [Lib.block_relocs, List.mem_map] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    have hm := relocsWf_mem hwf r' hr'
    refine ⟨hm.2.1, by simpa using hm.2.2, ?_⟩
    simp only [Reloc.toEntry_off, Reloc.toEntry_kind, toPlacement_base,
      relocTarget_block hnd hok (hok.relocs r' hr')]
    exact relocInRange_of hnd hok (hw.2.1 r' hr')
  · intro off r hrx hr
    rw [relaxedAt_block hnd hok] at hrx
    rw [relocAt?_block] at hr
    cases hr' : relocAtId? L.relocs (off + 4) with
    | none => rw [hr'] at hr; cases hr
    | some r' =>
      rw [hr'] at hr
      cases hr
      rw [toPlacement_base, target_block hnd hok (hok.relocs r' (relocAtId?_mem hr'))]
      exact hw.2.2 off r' (by omega) hrx hr'
  · intro s hs
    simp only [Lib.block, List.mem_map] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hsyms s' hs'
    exact ⟨this.1, by simpa using this.2⟩
  · intro e he
    simp only [Lib.block, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    have := hext e' he'
    have hi := hok.externs e' he'
    refine ⟨lookupId_map_none hnd hi hok.symbols this.1, ?_⟩
    rw [toPlacement_ρ hnd hi, toPlacement_base]
    simpa using this.2

theorem placeable_of {L : Lib} {ly : Layout} (hnd : L.names.Nodup) (hok : L.IdsOk)
    (htp : textPlaceableB L ly = true) (hdp : dataPlaceableB L ly = true)
    {seg : List (BitVec 8)} (hw : WalkOk L ly 0 L.relocs seg) :
    L.toLib.Placeable (ly.toPlacement L.names) := by
  simp only [dataPlaceableB, Bool.and_eq_true, List.all_eq_true] at hdp
  obtain ⟨hnodup, hds⟩ := hdp
  refine ⟨textPlaceable_of hnd hok htp hw, ?_, ?_, ?_⟩
  · simp only [Lib.toLib, List.map_map]
    have : ((·.sym) ∘ Data.toInfo L.names) = (fun i => L.names.getD i "") ∘ (·.sym) := rfl
    rw [this, ← List.map_map]
    have hn := natNodupFast_spec hnodup
    rw [List.nodup_iff_pairwise_ne] at hn ⊢
    rw [List.pairwise_map]
    refine hn.imp_of_mem (fun {x y} hx hy hxy heq => hxy ?_)
    simp only [List.mem_map] at hx hy
    obtain ⟨dx, hdx, rfl⟩ := hx
    obtain ⟨dy, hdy, rfl⟩ := hy
    exact getD_inj hnd (hok.data dx hdx).1 (hok.data dy hdy).1 heq
  · intro d hd
    simp only [Lib.toLib, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    have := hds d' hd'
    simp only [Nat.blt_eq, Nat.beq_eq, Nat.ble_eq] at this
    obtain ⟨⟨⟨⟨hl, ha⟩, hal⟩, hnw⟩, _⟩ := this
    have hi := (hok.data d' hd').1
    simp only [Data.toInfo, Lib.toLib_text, toPlacement_ρ hnd hi]
    exact ⟨lookupId_map_none hnd hi hok.symbols hl, ha, hal, hnw⟩
  · intro d hd r hr
    simp only [Lib.toLib, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    simp only [Data.toInfo, List.mem_map] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    have := hds d' hd'
    have hro := this.2 r' hr'
    simp only [dataRelocOkB, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hro
    obtain ⟨⟨hw0, hlen⟩, hk⟩ := hro
    have hsi := (hok.data d' hd').2 r' hr'
    have hi := (hok.data d' hd').1
    simp only [Reloc.toEntry_kind, Reloc.toEntry_off, Reloc.toEntry_sym, Reloc.toEntry_addend,
      Lib.toLib_text, resolve_block hnd hok hsi]
    rw [show (Data.toInfo L.names d').sym = L.names.getD d'.sym "" from rfl, toPlacement_ρ hnd hi]
    refine ⟨hw0, hlen, fun hk' => ?_, fun hk' => ?_⟩
    · rw [hk'] at hk
      have := sInRange_iff.1 hk
      unfold Abs32InRange
      exact ⟨by unfold targetId at this; omega, by unfold targetId at this; omega⟩
    · rw [hk'] at hk
      have := sInRange_iff.1 hk
      unfold Prel32InRange
      exact ⟨by unfold targetId at this; omega, by unfold targetId at this; omega⟩

/-! ## Exports -/

/-- Each export of `L` is a block symbol with exactly one entry in the ELF's encoded `.symtab`
    `enc`, at its placed address. -/
def exportsOk (L : Lib) (ly : Layout) (nameChars : List (List Char))
    (enc : EncSymTable (BitVec 64)) : Bool :=
  L.exports.all fun e =>
    match lookupId e L.symbols with
    | some off =>
      match lookupUniqueEnc (encodeCharKey (nameChars.getD e [])) enc with
      | some a => a == ly.base + BitVec.ofNat 64 off
      | none => false
    | none => false

theorem names_getD {L : Lib} {nameChars : List (List Char)}
    (hnames : L.names = nameChars.map String.ofList) (i : Nat) :
    L.names.getD i "" = String.ofList (nameChars.getD i []) := by
  rw [hnames]
  clear hnames
  induction nameChars generalizing i with
  | nil => rfl
  | cons c cs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem exports_of {L : Lib} {ly : Layout} {nameChars : List (List Char)} {img : ElfImage}
    {symChars : List (List Char × BitVec 64)} (hnd : L.names.Nodup) (hok : L.IdsOk)
    (hnames : L.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (h : exportsOk L ly nameChars (prepareCharAssocVal symChars) = true) :
    ∀ e ∈ L.toLib.exports, ∃ off, lookup e L.toLib.text.symbols = some off ∧
      lookupUnique e img.symbols = some ((ly.toPlacement L.names).base + BitVec.ofNat 64 off) := by
  intro e he
  simp only [Lib.toLib, List.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  have hi := hok.exports e' he'
  have := List.all_eq_true.1 h e' he'
  split at this
  · rename_i off hoff
    split at this
    · rename_i a ha
      refine ⟨off, ?_, ?_⟩
      · simp only [Lib.toLib_text, Lib.block]
        rw [lookup_map_getD hnd hi L.symbols hok.symbols, hoff]
      · rw [lookupUnique_eq_lookupUniqueEnc hsyms rfl (names_getD hnames e'), ha,
          toPlacement_base]
        simpa using this
    · cases this
  · cases this

/-! ## ELF-backed checker -/

/-- Kernel-fast check that the stock-linked image `img` contains `L` placed by `ly`. `nameChars`
    is the names table as `List Char`s and `enc` the image's encoded `.symtab`. -/
def check (L : Lib) (ly : Layout) (nameChars : List (List Char)) (img : ElfImage)
    (enc : EncSymTable (BitVec 64)) : Bool :=
  namesNodup nameChars && L.idsOk && textPlaceableB L ly && dataPlaceableB L ly &&
    textOk L ly img.segments && dataWalk L ly img.segments none L.data &&
    exportsOk L ly nameChars enc

theorem check_spec {L : Lib} {ly : Layout} {nameChars : List (List Char)} {img : ElfImage}
    {symChars : List (List Char × BitVec 64)} (hnames : L.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (h : check L ly nameChars img (prepareCharAssocVal symChars) = true) :
    L.toLib.Placeable (ly.toPlacement L.names) ∧ L.toLib.InElf img (ly.toPlacement L.names) := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hnn, hids⟩, htp⟩, hdp⟩, htext⟩, hdata⟩, hexp⟩ := h
  have hnd := nodup_of_namesNodup hnames hnn
  have hok := Lib.idsOk_spec hids
  have hwf : relocsWf L.code.length 0 L.relocs = true := by
    simp only [textPlaceableB, Bool.and_eq_true] at htp
    exact htp.1.1.2
  have ⟨⟨p, bs, hv, hp, hpre⟩, hw⟩ := textOk_sound (ly := ly) hnd hok hwf htext
  refine ⟨placeable_of hnd hok htp hdp hw, ?_, ?_, exports_of hnd hok hnames hsyms hexp⟩
  · simp only [Lib.toLib_text, toPlacement_base]
    exact elfMaps_of_view (hv.of_prefix hpre) (by simp [hp])
  · intro d hd
    simp only [Lib.toLib, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    obtain ⟨p, hv, hp⟩ := dataWalk_sound none L.data (fun _ _ _ h => nomatch h) hdata d' hd'
    have hi := (hok.data d' hd').1
    rw [show (Data.toInfo L.names d').readOnly = d'.readOnly from rfl,
      show (ly.toPlacement L.names).ρ (Data.toInfo L.names d').sym = ly.addrs.getD d'.sym 0#64
        from toPlacement_ρ hnd hi]
    rw [show L.toLib.patchedData (ly.toPlacement L.names) (Data.toInfo L.names d') =
        patchedDataId L ly d' from patchedData_toLib hnd hok hd']
    exact elfMaps_of_view hv hp

theorem linkedAt_of_check {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} {bytes : List (BitVec 8)} {img : ElfImage}
    {symChars : List (List Char × BitVec 64)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList) (hparse : ElfImage.parse bytes = .ok img)
    (hsyms : img.symbols = toStringAssoc symChars)
    (h : check L ly nameChars img (prepareCharAssocVal symChars) = true) :
    lib.LinkedAt bytes (ly.toPlacement L.names) := by
  subst hlib
  have ⟨hpl, hin⟩ := check_spec hnames hsyms h
  exact ⟨img, hparse, hpl, hin⟩

theorem linkedIn_of_check {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} {bytes : List (BitVec 8)} {img : ElfImage}
    {symChars : List (List Char × BitVec 64)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList) (hparse : ElfImage.parse bytes = .ok img)
    (hsyms : img.symbols = toStringAssoc symChars)
    (h : check L ly nameChars img (prepareCharAssocVal symChars) = true) : lib.LinkedIn bytes :=
  ⟨_, linkedAt_of_check hlib hnames hparse hsyms h⟩

/-! ## ELF-free `Placeable` and extern-distinctness checker -/

/-- Text relocation range validity and relaxed `ADRP`+`ADD` pair `AdrInRange` validity across
    `L.relocs` and `ly.relax`, without requiring an ELF segment image. -/
def textRelocsOkB (L : Lib) (ly : Layout) : Bool :=
  L.relocs.all (fun r =>
    relocInRangeB L ly r.kind r.off (ly.base + BitVec.ofNat 64 r.off)
      (relocTargetId L ly r.off r)) &&
  ly.relax.all fun off =>
    match relocAtId? L.relocs (off + 4) with
    | some r =>
      !relaxableId L off ||
        sInRange (-1048576) 1048576 (targetId L ly r - (ly.base + BitVec.ofNat 64 (off + 4)))
    | none => true

theorem walkOk_of_textRelocsOkB {L : Lib} {ly : Layout} (h : textRelocsOkB L ly = true) :
    WalkOk L ly 0 L.relocs (L.block.patched (ly.toPlacement L.names)) := by
  simp only [textRelocsOkB, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨List.prefix_rfl, h.1, fun off r _ hrx hr => ?_⟩
  simp only [relaxedId, Bool.and_eq_true, memNat_iff] at hrx
  have hrel := h.2 off hrx.1.1
  rw [hr] at hrel
  simp only [hrx.2, Bool.not_true, Bool.false_or] at hrel
  exact adrInRange_of hrel

/-- Extern symbols in `L.externs` are mapped by `ly` to pairwise-distinct addresses. -/
def externsDisjointB (L : Lib) (ly : Layout) : Bool :=
  natNodupFast (L.externs.map fun e => (ly.addrs.getD e 0#64).toNat)

theorem externsDisjoint_of_externsDisjointB {L : Lib} {ly : Layout} {lib : PlacedLib}
    {pl : Placement} (hlib : lib = L.toLib) (hpl : pl = ly.toPlacement L.names)
    (hnd : L.names.Nodup) (hok : L.IdsOk) (h : externsDisjointB L ly = true) :
    (lib.text.externs.map pl.ρ).Nodup := by
  subst hlib hpl
  have hnodup := natNodupFast_spec h
  simp only [Lib.toLib_text, Lib.block, List.map_map]
  rw [List.map_congr_left (g := fun e => ly.addrs.getD e 0#64) fun e he => by
    simp only [Function.comp_apply, toPlacement_ρ hnd (hok.externs e he)]]
  rw [List.nodup_iff_pairwise_ne] at hnodup ⊢
  rw [List.pairwise_map] at hnodup ⊢
  exact hnodup.imp fun {a b} hab heq => hab (congrArg BitVec.toNat heq)

/-- Distinct extern addresses imply distinct extern offsets from `pl.base` (as required by
    `PlacedLib.externAt?_program`). -/
theorem externsOffsetNodup_of_externsNodup {externs : List String} {pl : Placement}
    (h : (externs.map pl.ρ).Nodup) :
    (externs.map fun e => (pl.ρ e - pl.base).toNat).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at h ⊢
  rw [List.pairwise_map] at h ⊢
  refine h.imp fun {a b} hab heq => hab ?_
  have h1 : pl.ρ a - pl.base = pl.ρ b - pl.base := BitVec.eq_of_toNat_eq heq
  have h2 := congrArg (· + pl.base) h1
  simpa [BitVec.sub_add_cancel] using h2

/-! ### Balanced index tree for `O(log N)` symbol resolution in the kernel -/

/-- Balanced binary tree indexing a 0-based sequence in `O(log n)` kernel steps. -/
inductive VecTree (α : Type) where
  | leaf
  | node (half : Nat) (left : VecTree α) (val : α) (right : VecTree α)

/-- Look up 0-based index `i` in `VecTree`, returning `d` if out of bounds. -/
def VecTree.getD {α : Type} (d : α) : VecTree α → Nat → α
  | .leaf, _ => d
  | .node half l v r, i =>
    match Nat.blt i half with
    | true => l.getD d i
    | false =>
      match Nat.beq i half with
      | true => v
      | false => r.getD d (i - (half + 1))

/-- Pre-resolved symbol slot at name index `i`: whether `i` is not a block symbol, its `ly.addrs[i]`
    entry, and its resolved target address `resolveId L ly i`. -/
structure SymSlot where
  notSym : Bool
  addr : BitVec 64
  resolved : BitVec 64

def defaultSymSlot : SymSlot := ⟨true, 0#64, 0#64⟩

/-- Force `n : Nat` to `Literal.natVal` in the kernel via primitive `Nat.casesOn` before passing it
    to `k`, avoiding call-by-name (`zeta`) re-evaluation and equation-compiler `Bool.decEq`. -/
def withNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn n (k 0) (fun m => k m.succ)

@[simp] theorem withNat_eq {α : Type} (n : Nat) (k : Nat → α) : withNat n k = k n := by
  cases n <;> rfl

def mkSymSlot (L : Lib) (ly : Layout) (i : Nat) (a : BitVec 64) : SymSlot :=
  match lookupId i L.symbols with
  | some off =>
    withNat (ly.base + BitVec.ofNat 64 off).toNat fun r =>
      ⟨false, a, BitVec.ofNat 64 r⟩
  | none =>
    withNat a.toNat fun na =>
      let a' := BitVec.ofNat 64 na
      ⟨true, a', a'⟩

@[simp] theorem mkSymSlot_notSym (L : Lib) (ly : Layout) (i : Nat) (a : BitVec 64) :
    (mkSymSlot L ly i a).notSym = (lookupId i L.symbols).isNone := by
  unfold mkSymSlot; cases lookupId i L.symbols <;> simp

@[simp] theorem mkSymSlot_addr (L : Lib) (ly : Layout) (i : Nat) (a : BitVec 64) :
    (mkSymSlot L ly i a).addr = a := by
  unfold mkSymSlot; cases lookupId i L.symbols <;> simp

@[simp] theorem mkSymSlot_resolved (L : Lib) (ly : Layout) (i : Nat) :
    (mkSymSlot L ly i (ly.addrs.getD i 0#64)).resolved = resolveId L ly i := by
  unfold mkSymSlot resolveId
  cases lookupId i L.symbols <;> simp only [withNat_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

def withSlot {α : Type} (s : SymSlot) (k : Bool → BitVec 64 → BitVec 64 → α) : α :=
  match s with
  | ⟨ns, a, r⟩ => k ns a r

@[simp] theorem withSlot_eq {α : Type} (s : SymSlot) (k : Bool → BitVec 64 → BitVec 64 → α) :
    withSlot s k = k s.notSym s.addr s.resolved := by
  cases s; rfl

def headTailD (as : List (BitVec 64)) : BitVec 64 × List (BitVec 64) :=
  match as with
  | [] => (0#64, [])
  | a :: as' => (a, as')

@[simp] theorem headTailD_fst (as : List (BitVec 64)) :
    (headTailD as).1 = as.getD 0 0#64 := by
  cases as <;> rfl

@[simp] theorem headTailD_snd (as : List (BitVec 64)) :
    (headTailD as).2 = as.drop 1 := by
  cases as <;> rfl

theorem getD_drop {α : Type} (xs : List α) (d : α) (k i : Nat) :
    (xs.drop k).getD i d = xs.getD (k + i) d := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [List.drop_succ_cons, ih, Nat.succ_add]
      rfl

/-- Build a balanced `VecTree SymSlot` in CPS over `n` symbol indices starting at `off`, consuming
    `as` (`ly.addrs.drop off`) in one linear pass and forcing every slot to literal WHNF once. -/
def buildSymTree (L : Lib) (ly : Layout) :
    Nat → Nat → Nat → List (BitVec 64) → (VecTree SymSlot → List (BitVec 64) → Bool) → Bool
  | 0, _, _, as, k => k .leaf as
  | fuel + 1, off, n, as, k =>
    Nat.casesOn n (k .leaf as) fun n =>
      withNat (n / 2) fun half =>
        buildSymTree L ly fuel off half as fun l rest =>
          withNat (off + half) fun mid =>
            match headTailD rest with
            | (a, rest') =>
              withNat (mid + 1) fun rOff =>
                withNat (n - half) fun rlen =>
                  buildSymTree L ly fuel rOff rlen rest' fun r rest'' =>
                    k (.node half l (mkSymSlot L ly mid a) r) rest''

theorem buildSymTree_spec (L : Lib) (ly : Layout) :
    ∀ (fuel off n : Nat) (as : List (BitVec 64))
      (k : VecTree SymSlot → List (BitVec 64) → Bool),
      n < 2 ^ fuel →
      buildSymTree L ly fuel off n as k = true →
      ∃ t, k t (as.drop n) = true ∧
        ∀ i < n, t.getD defaultSymSlot i = mkSymSlot L ly (off + i) (as.getD i 0#64)
  | 0, off, n, as, k, hn, h => by
    have hn0 : n = 0 := by simp [Nat.pow_zero] at hn; omega
    subst hn0
    exact ⟨.leaf, by simpa [buildSymTree] using h, fun i hi => by omega⟩
  | fuel + 1, off, 0, as, k, _, h =>
    ⟨.leaf, h, fun i hi => by omega⟩
  | fuel + 1, off, n + 1, as, k, hn, h => by
    simp only [buildSymTree, withNat_eq] at h
    rw [Nat.pow_succ] at hn
    have h1 : n / 2 < 2 ^ fuel := by omega
    have h2 : n - n / 2 < 2 ^ fuel := by omega
    obtain ⟨l, hl_k, hl_get⟩ := buildSymTree_spec L ly fuel off (n / 2) as _ h1 h
    have hht : headTailD (as.drop (n / 2)) = (as.getD (n / 2) 0#64, (as.drop (n / 2)).drop 1) := by
      ext
      · rw [headTailD_fst, getD_drop, Nat.add_zero]
      · rw [headTailD_snd]
    rw [hht] at hl_k
    dsimp only at hl_k
    obtain ⟨r, hr_k, hr_get⟩ := buildSymTree_spec L ly fuel (off + n / 2 + 1) (n - n / 2)
      ((as.drop (n / 2)).drop 1) _ h2 hl_k
    rw [List.drop_drop, List.drop_drop,
      show n / 2 + (1 + (n - n / 2)) = n + 1 by omega] at hr_k
    refine ⟨.node (n / 2) l (mkSymSlot L ly (off + n / 2) (as.getD (n / 2) 0#64)) r, hr_k,
      fun i hi => ?_⟩
    simp only [VecTree.getD]
    by_cases hlt : i < n / 2
    · rw [show Nat.blt i (n / 2) = true by rw [Nat.blt_eq]; exact hlt]
      exact hl_get i hlt
    · rw [show Nat.blt i (n / 2) = false by rw [Bool.eq_false_iff, Ne, Nat.blt_eq]; omega]
      by_cases heq : i = n / 2
      · subst heq; simp [Nat.beq_refl]
      · rw [nat_beq_false_of_ne heq]
        have hr := hr_get (i - (n / 2 + 1)) (by omega)
        rw [getD_drop, getD_drop,
          show n / 2 + (1 + (i - (n / 2 + 1))) = i by omega,
          show off + n / 2 + 1 + (i - (n / 2 + 1)) = off + i by omega] at hr
        exact hr

def idsOkWith (n : Nat) (L : Lib) : Bool :=
  L.symbols.all (fun s => Nat.blt s.1 n) && L.relocs.all (fun r => Nat.blt r.sym n) &&
  L.externs.all (fun e => Nat.blt e n) && L.exports.all (fun e => Nat.blt e n) &&
  L.data.all fun d => Nat.blt d.sym n && d.relocs.all fun r => Nat.blt r.sym n

@[simp] theorem idsOkWith_names_length (L : Lib) : idsOkWith L.names.length L = L.idsOk := rfl

def targetTree (t : VecTree SymSlot) (r : Reloc) : BitVec 64 :=
  withSlot (t.getD defaultSymSlot r.sym) fun _ _ res =>
    addSignedAddr res r.addend

def relocTargetTree (L : Lib) (ly : Layout) (t : VecTree SymSlot) (off : Nat) (r : Reloc) :
    BitVec 64 :=
  match (if memNat off ly.b2b then b2bNextId L r else none) with
  | some r2 => targetTree t r2
  | none => targetTree t r

def textPlaceableTree (L : Lib) (ly : Layout) (t : VecTree SymSlot) : Bool :=
  withNat L.code.length fun len =>
    Nat.blt 0 L.align && Nat.beq (L.align % 4) 0 && Nat.beq (ly.base.toNat % L.align) 0 &&
      Nat.ble (ly.base.toNat + len) 18446744073709551616 && Nat.beq (len % 4) 0 &&
      relocsWf len 0 L.relocs &&
      L.symbols.all (fun s => Nat.beq (s.2 % 4) 0 && Nat.ble s.2 len) &&
      L.externs.all fun e =>
        withSlot (t.getD defaultSymSlot e) fun ns a _ =>
          ns && Nat.ble len (a - ly.base).toNat

def dataRelocOkTree (t : VecTree SymSlot) (addr : BitVec 64) (n : Nat) (r : Reloc) : Bool :=
  Nat.blt 0 (dataRelocWidth r.kind) && Nat.ble (r.off + dataRelocWidth r.kind) n &&
    match r.kind with
    | .abs32 => sInRange (-2147483648) 4294967296 (targetTree t r)
    | .prel32 =>
      sInRange (-2147483648) 2147483648 (targetTree t r - (addr + BitVec.ofNat 64 r.off))
    | _ => true

def dataPlaceableTree (L : Lib) (t : VecTree SymSlot) : Bool :=
  natNodupFast (L.data.map (·.sym)) &&
    L.data.all fun d =>
      withSlot (t.getD defaultSymSlot d.sym) fun ns a _ =>
        withNat d.bytes.length fun dlen =>
          ns && Nat.blt 0 d.align && Nat.beq (a.toNat % d.align) 0 &&
            Nat.ble (a.toNat + dlen + d.zeroTail) 18446744073709551616 &&
            d.relocs.all (dataRelocOkTree t a dlen)

def textRelocsOkTree (L : Lib) (ly : Layout) (t : VecTree SymSlot) : Bool :=
  L.relocs.all (fun r =>
    relocInRangeB L ly r.kind r.off (ly.base + BitVec.ofNat 64 r.off)
      (relocTargetTree L ly t r.off r)) &&
  ly.relax.all fun off =>
    match relocAtId? L.relocs (off + 4) with
    | some r =>
      !relaxableId L off ||
        sInRange (-1048576) 1048576 (targetTree t r - (ly.base + BitVec.ofNat 64 (off + 4)))
    | none => true

def externsDisjointTree (L : Lib) (t : VecTree SymSlot) : Bool :=
  natNodupFast (L.externs.map fun e => withSlot (t.getD defaultSymSlot e) fun _ a _ => a.toNat)

theorem targetTree_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot}
    (ht : ∀ i < L.names.length, t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64))
    {r : Reloc} (hr : r.sym < L.names.length) :
    targetTree t r = targetId L ly r := by
  simp only [targetTree, targetId, withSlot_eq, ht r.sym hr, mkSymSlot_resolved]

theorem relocTargetTree_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : ∀ i < L.names.length, t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64))
    {r : Reloc} (hr : r ∈ L.relocs) (off : Nat) :
    relocTargetTree L ly t off r = relocTargetId L ly off r := by
  unfold relocTargetTree relocTargetId
  cases hb : (if memNat off ly.b2b then b2bNextId L r else none) with
  | none => exact targetTree_eq ht (hok.relocs r hr)
  | some r2 =>
    have hm : b2bNextId L r = some r2 := by
      split at hb
      · exact hb
      · cases hb
    exact targetTree_eq ht (hok.relocs r2 (b2bNextId_mem hm))

theorem all_congr_left {α : Type} {xs : List α} {f g : α → Bool} (h : ∀ x ∈ xs, f x = g x) :
    xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem textPlaceableTree_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : ∀ i < L.names.length, t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64)) :
    textPlaceableTree L ly t = textPlaceableB L ly := by
  simp only [textPlaceableTree, textPlaceableB, withNat_eq, withSlot_eq]
  congr 1
  refine all_congr_left fun e he => ?_
  rw [ht e (hok.externs e he), mkSymSlot_notSym, mkSymSlot_addr]

theorem dataPlaceableTree_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : ∀ i < L.names.length, t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64)) :
    dataPlaceableTree L t = dataPlaceableB L ly := by
  simp only [dataPlaceableTree, dataPlaceableB, withNat_eq, withSlot_eq]
  congr 1
  refine all_congr_left fun d hd => ?_
  have ⟨hds, hdr⟩ := hok.data d hd
  rw [ht d.sym hds, mkSymSlot_notSym, mkSymSlot_addr]
  congr 1
  refine all_congr_left fun r hr => ?_
  simp only [dataRelocOkTree, dataRelocOkB, targetTree_eq ht (hdr r hr)]

theorem textRelocsOkTree_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : ∀ i < L.names.length, t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64)) :
    textRelocsOkTree L ly t = textRelocsOkB L ly := by
  simp only [textRelocsOkTree, textRelocsOkB]
  congr 1
  · refine all_congr_left fun r hr => ?_
    rw [relocTargetTree_eq hok ht hr]
  · refine all_congr_left fun off _ => ?_
    cases hr : relocAtId? L.relocs (off + 4) with
    | none => rfl
    | some r =>
      simp only [targetTree_eq ht (hok.relocs r (relocAtId?_mem hr))]

theorem externsDisjointTree_eq {L : Lib} {ly : Layout} {t : VecTree SymSlot} (hok : L.IdsOk)
    (ht : ∀ i < L.names.length, t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64)) :
    externsDisjointTree L t = externsDisjointB L ly := by
  simp only [externsDisjointTree, externsDisjointB, withSlot_eq]
  congr 1
  refine List.map_congr_left fun e he => ?_
  rw [ht e (hok.externs e he), mkSymSlot_addr]

/-- Kernel-fast ELF-free check that `L` is `Placeable` at `ly`. -/
def checkPlaceable (L : Lib) (ly : Layout) (nameChars : List (List Char)) : Bool :=
  withNat L.names.length fun n =>
    namesNodup nameChars && idsOkWith n L && Nat.blt n 1048576 &&
      buildSymTree L ly 20 0 n ly.addrs fun t _ =>
        textPlaceableTree L ly t && dataPlaceableTree L t && textRelocsOkTree L ly t

theorem checkPlaceable_spec {L : Lib} {ly : Layout} {nameChars : List (List Char)}
    (hnames : L.names = nameChars.map String.ofList)
    (h : checkPlaceable L ly nameChars = true) :
    L.toLib.Placeable (ly.toPlacement L.names) := by
  simp only [checkPlaceable, withNat_eq, idsOkWith_names_length, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨hnn, hids⟩, hn⟩, htree⟩ := h
  have hok := Lib.idsOk_spec hids
  obtain ⟨t, hk, ht⟩ := buildSymTree_spec L ly 20 0 L.names.length ly.addrs _ hn htree
  have ht0 : ∀ i < L.names.length,
      t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64) := by
    intro i hi; simpa using ht i hi
  simp only [Bool.and_eq_true, textPlaceableTree_eq hok ht0, dataPlaceableTree_eq hok ht0,
    textRelocsOkTree_eq hok ht0] at hk
  exact placeable_of (nodup_of_namesNodup hnames hnn) hok hk.1.1 hk.1.2
    (walkOk_of_textRelocsOkB hk.2)

theorem placeable_of_checkPlaceable {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList)
    (h : checkPlaceable L ly nameChars = true) :
    lib.Placeable (ly.toPlacement L.names) := by
  subst hlib
  exact checkPlaceable_spec hnames h

theorem exists_placeable_of_checkPlaceable {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList)
    (h : checkPlaceable L ly nameChars = true) :
    ∃ pl, lib.Placeable pl :=
  ⟨ly.toPlacement L.names, placeable_of_checkPlaceable hlib hnames h⟩

/-- Kernel-fast ELF-free check that `L` is `Placeable` at `ly` and maps `L.externs` to
    pairwise-distinct addresses. -/
def checkPlaceableExt (L : Lib) (ly : Layout) (nameChars : List (List Char)) : Bool :=
  withNat L.names.length fun n =>
    namesNodup nameChars && idsOkWith n L && Nat.blt n 1048576 &&
      buildSymTree L ly 20 0 n ly.addrs fun t _ =>
        textPlaceableTree L ly t && dataPlaceableTree L t && textRelocsOkTree L ly t &&
          externsDisjointTree L t

theorem checkPlaceableExt_spec {L : Lib} {ly : Layout} {nameChars : List (List Char)}
    (hnames : L.names = nameChars.map String.ofList)
    (h : checkPlaceableExt L ly nameChars = true) :
    L.toLib.Placeable (ly.toPlacement L.names) ∧
      (L.toLib.text.externs.map (ly.toPlacement L.names).ρ).Nodup := by
  simp only [checkPlaceableExt, withNat_eq, idsOkWith_names_length, Bool.and_eq_true,
    Nat.blt_eq] at h
  obtain ⟨⟨⟨hnn, hids⟩, hn⟩, htree⟩ := h
  have hnd := nodup_of_namesNodup hnames hnn
  have hok := Lib.idsOk_spec hids
  obtain ⟨t, hk, ht⟩ := buildSymTree_spec L ly 20 0 L.names.length ly.addrs _ hn htree
  have ht0 : ∀ i < L.names.length,
      t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64) := by
    intro i hi; simpa using ht i hi
  simp only [Bool.and_eq_true, textPlaceableTree_eq hok ht0, dataPlaceableTree_eq hok ht0,
    textRelocsOkTree_eq hok ht0, externsDisjointTree_eq hok ht0] at hk
  exact ⟨placeable_of hnd hok hk.1.1.1 hk.1.1.2 (walkOk_of_textRelocsOkB hk.1.2),
    externsDisjoint_of_externsDisjointB rfl rfl hnd hok hk.2⟩

theorem placeable_and_externs_of_checkPlaceable {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList)
    (h : checkPlaceableExt L ly nameChars = true) :
    lib.Placeable (ly.toPlacement L.names) ∧
      (lib.text.externs.map (ly.toPlacement L.names).ρ).Nodup := by
  subst hlib
  exact checkPlaceableExt_spec hnames h

theorem exists_placeable_and_externs_of_checkPlaceable {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList)
    (h : checkPlaceableExt L ly nameChars = true) :
    ∃ pl, lib.Placeable pl ∧ (lib.text.externs.map pl.ρ).Nodup :=
  ⟨ly.toPlacement L.names, placeable_and_externs_of_checkPlaceable hlib hnames h⟩

/-- Run a symbol-tree predicate `k` on the balanced `VecTree SymSlot` built for `(L, ly)`. -/
abbrev withSymTree (L : Lib) (ly : Layout) (k : VecTree SymSlot → Bool) : Bool :=
  withNat L.names.length fun n =>
    buildSymTree L ly 20 0 n ly.addrs fun t _ => k t

theorem withSymTree_spec {L : Lib} {ly : Layout} {k : VecTree SymSlot → Bool}
    (hn : Nat.blt L.names.length 1048576 = true)
    (h : withSymTree L ly k = true) :
    ∃ t, k t = true ∧ ∀ i < L.names.length,
      t.getD defaultSymSlot i = mkSymSlot L ly i (ly.addrs.getD i 0#64) := by
  rw [withSymTree, withNat_eq] at h
  obtain ⟨t, hk, ht⟩ := buildSymTree_spec L ly 20 0 L.names.length ly.addrs _
    (by rw [Nat.blt_eq] at hn; exact hn) h
  exact ⟨t, hk, fun i hi => by simpa using ht i hi⟩

/-- Standalone tree-backed check for text alignment, bounds, symbol offsets, and extern bounds. -/
abbrev checkTextPlaceable (L : Lib) (ly : Layout) : Bool :=
  withSymTree L ly (textPlaceableTree L ly)

/-- Standalone tree-backed check for data symbol uniqueness, bounds, and data relocations. -/
abbrev checkDataPlaceable (L : Lib) (ly : Layout) : Bool :=
  withSymTree L ly (dataPlaceableTree L)

/-- Standalone tree-backed check for text relocation ranges and relaxed `ADRP`+`ADD` pairs. -/
abbrev checkTextRelocsOk (L : Lib) (ly : Layout) : Bool :=
  withSymTree L ly (textRelocsOkTree L ly)

/-- Standalone tree-backed check that `L.externs` map to pairwise-distinct addresses under `ly`. -/
abbrev checkExternsDisjoint (L : Lib) (ly : Layout) : Bool :=
  withSymTree L ly (externsDisjointTree L)

/-- Combine individually kernel-checked sub-goals into `L.toLib.Placeable (ly.toPlacement L.names)`
    without elaborating a single monolithic `checkPlaceable` term. -/
theorem checkPlaceable_spec_split {L : Lib} {ly : Layout} {nameChars : List (List Char)}
    (hnames : L.names = nameChars.map String.ofList)
    (hnn : namesNodup nameChars = true)
    (hids : L.idsOk = true)
    (hsize : Nat.blt L.names.length 1048576 = true)
    (htext : checkTextPlaceable L ly = true)
    (hdata : checkDataPlaceable L ly = true)
    (hrelocs : checkTextRelocsOk L ly = true) :
    L.toLib.Placeable (ly.toPlacement L.names) := by
  have hnd := nodup_of_namesNodup hnames hnn
  have hok := Lib.idsOk_spec hids
  obtain ⟨t1, h1, ht1⟩ := withSymTree_spec hsize htext
  obtain ⟨t2, h2, ht2⟩ := withSymTree_spec hsize hdata
  obtain ⟨t3, h3, ht3⟩ := withSymTree_spec hsize hrelocs
  rw [textPlaceableTree_eq hok ht1] at h1
  rw [dataPlaceableTree_eq hok ht2] at h2
  rw [textRelocsOkTree_eq hok ht3] at h3
  exact placeable_of hnd hok h1 h2 (walkOk_of_textRelocsOkB h3)

theorem placeable_of_split_checks {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList)
    (hnn : namesNodup nameChars = true)
    (hids : L.idsOk = true)
    (hsize : Nat.blt L.names.length 1048576 = true)
    (htext : checkTextPlaceable L ly = true)
    (hdata : checkDataPlaceable L ly = true)
    (hrelocs : checkTextRelocsOk L ly = true) :
    lib.Placeable (ly.toPlacement L.names) := by
  subst hlib
  exact checkPlaceable_spec_split hnames hnn hids hsize htext hdata hrelocs

theorem exists_placeable_of_split_checks {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList)
    (hnn : namesNodup nameChars = true)
    (hids : L.idsOk = true)
    (hsize : Nat.blt L.names.length 1048576 = true)
    (htext : checkTextPlaceable L ly = true)
    (hdata : checkDataPlaceable L ly = true)
    (hrelocs : checkTextRelocsOk L ly = true) :
    ∃ pl, lib.Placeable pl :=
  ⟨ly.toPlacement L.names,
    placeable_of_split_checks hlib hnames hnn hids hsize htext hdata hrelocs⟩

/-- Combine individually kernel-checked sub-goals into `Placeable` and extern-address `Nodup`
    without elaborating a single monolithic `checkPlaceableExt` term. -/
theorem checkPlaceableExt_spec_split {L : Lib} {ly : Layout} {nameChars : List (List Char)}
    (hnames : L.names = nameChars.map String.ofList)
    (hnn : namesNodup nameChars = true)
    (hids : L.idsOk = true)
    (hsize : Nat.blt L.names.length 1048576 = true)
    (htext : checkTextPlaceable L ly = true)
    (hdata : checkDataPlaceable L ly = true)
    (hrelocs : checkTextRelocsOk L ly = true)
    (hexterns : checkExternsDisjoint L ly = true) :
    L.toLib.Placeable (ly.toPlacement L.names) ∧
      (L.toLib.text.externs.map (ly.toPlacement L.names).ρ).Nodup := by
  have hnd := nodup_of_namesNodup hnames hnn
  have hok := Lib.idsOk_spec hids
  obtain ⟨t4, h4, ht4⟩ := withSymTree_spec hsize hexterns
  rw [externsDisjointTree_eq hok ht4] at h4
  exact ⟨checkPlaceable_spec_split hnames hnn hids hsize htext hdata hrelocs,
    externsDisjoint_of_externsDisjointB rfl rfl hnd hok h4⟩

theorem placeable_and_externs_of_split_checks {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList)
    (hnn : namesNodup nameChars = true)
    (hids : L.idsOk = true)
    (hsize : Nat.blt L.names.length 1048576 = true)
    (htext : checkTextPlaceable L ly = true)
    (hdata : checkDataPlaceable L ly = true)
    (hrelocs : checkTextRelocsOk L ly = true)
    (hexterns : checkExternsDisjoint L ly = true) :
    lib.Placeable (ly.toPlacement L.names) ∧
      (lib.text.externs.map (ly.toPlacement L.names).ρ).Nodup := by
  subst hlib
  exact checkPlaceableExt_spec_split hnames hnn hids hsize htext hdata hrelocs hexterns

theorem exists_placeable_and_externs_of_split_checks {lib : PlacedLib} {L : Lib} {ly : Layout}
    {nameChars : List (List Char)} (hlib : lib = L.toLib)
    (hnames : L.names = nameChars.map String.ofList)
    (hnn : namesNodup nameChars = true)
    (hids : L.idsOk = true)
    (hsize : Nat.blt L.names.length 1048576 = true)
    (htext : checkTextPlaceable L ly = true)
    (hdata : checkDataPlaceable L ly = true)
    (hrelocs : checkTextRelocsOk L ly = true)
    (hexterns : checkExternsDisjoint L ly = true) :
    ∃ pl, lib.Placeable pl ∧ (lib.text.externs.map pl.ρ).Nodup :=
  ⟨ly.toPlacement L.names,
    placeable_and_externs_of_split_checks hlib hnames hnn hids hsize htext hdata hrelocs hexterns⟩

end Arm64.Obj.Interned
