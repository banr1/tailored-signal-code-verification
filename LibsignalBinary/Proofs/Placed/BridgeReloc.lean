/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.Bridge
public import ProofLib.SepLogic.Bytes
import ProofLib.BV.WidthNorm

/-!
# Slices and Relocated Words of Read-Only Data

Sub-slice extraction (`holdsBytes_slice`), $O(\log N)$ bounds checks via `lsroFind`, plain byte/word
slice introduction lemmas (`lsro_slice_intro`, `lsro64_intro`, `lsro32_intro`, `lsro16_intro`,
`lsro8_intro`), and relocated `abs64` word lemmas (`lsro_reloc64_intro`) under `LibsignalRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Placed.BridgeReloc

open _root_.Arm64 _root_.Arm64.Obj ProofLib
open CryptoVerification (libsignalSessionLib)
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalRoLoaded checkBlockCharSymAt fastLookupBlockSym getElem?_patchDataReloc_of_disjoint getElem?_patchedData_of_notReloc lookupBlockSym_none_of_chars lookupBlockSym_none_of_tree lookupBlockSym_of_fast_some lookupBlockSym_some_of_chars lsNotBlockCharSym lsNotBlockSym lsroFind lsroFind_spec)

/-! ## 1. Sub-slices of `HoldsBytes` -/

theorem holdsBytes_slice {m : Memory} {addr : BitVec 64} {L bs : List (BitVec 8)}
    {p : BitVec 64 → Perm} {off : Nat} (h : HoldsBytes m addr L p)
    (hbs : (L.drop off).take bs.length = bs) (hlen : off + bs.length ≤ L.length) :
    HoldsBytes m (addr + BitVec.ofNat 64 off) bs p := by
  intro i hi
  have hij : off + i < L.length := by omega
  obtain ⟨hrd, hperm⟩ := h (off + i) hij
  have hadd : addr + BitVec.ofNat 64 off + BitVec.ofNat 64 i =
      addr + BitVec.ofNat 64 (off + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hbi : bs[i] = L[off + i] := by
    have h1 : ((L.drop off).take bs.length)[i]? = bs[i]? := congrArg (·[i]?) hbs
    rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_eq_getElem hij,
      List.getElem?_eq_getElem hi] at h1
    exact (Option.some.inj h1).symm
  rw [hadd, hbi]
  exact ⟨hrd, hperm⟩

/-! ## 2. Checks (`$O(\log N)$` via `lsroFind`) -/

def relocsInBounds (d : SymDataInfo) : Bool :=
  d.relocs.all fun r => decide (r.off + dataRelocWidth r.kind ≤ d.bytes.length)

def relocsDisjoint (d : SymDataInfo) (off n : Nat) : Bool :=
  d.relocs.all fun r => decide (off + n ≤ r.off ∨ r.off + dataRelocWidth r.kind ≤ off)

def lsroSliceCheck (sym : String) (off : Nat) (bs : List (BitVec 8)) : Bool :=
  match lsroFind sym with
  | some d =>
    d.readOnly && relocsInBounds d && relocsDisjoint d off bs.length &&
      decide (off + bs.length ≤ d.bytes.length + d.zeroTail) &&
      decide (d.bytes.length + d.zeroTail ≤ 2 ^ 64) &&
      ((d.bytes ++ List.replicate d.zeroTail 0#8).drop off).take bs.length == bs
  | none => false

theorem relocsInBounds_spec {d : SymDataInfo} (h : relocsInBounds d = true) :
    ∀ r ∈ d.relocs, r.off + dataRelocWidth r.kind ≤ d.bytes.length := by
  simpa [relocsInBounds] using h

theorem relocsDisjoint_spec {d : SymDataInfo} {off n : Nat} (h : relocsDisjoint d off n = true) :
    ∀ r ∈ d.relocs, off + n ≤ r.off ∨ r.off + dataRelocWidth r.kind ≤ off := by
  simpa [relocsDisjoint] using h

/-! ## 3. Plain Slices -/

theorem lsro_slice_holds {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {off : Nat} {bs : List (BitVec 8)} (h : lsroSliceCheck sym off bs = true) :
    HoldsBytes m (pl.ρ sym + BitVec.ofNat 64 off) bs (fun _ => Perm.ro) := by
  unfold lsroSliceCheck at h
  cases hf : lsroFind sym with
  | none => simp [hf] at h
  | some d =>
    simp only [hf, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hrd, hinb⟩, hdis⟩, hbnd⟩, _⟩, hbs⟩ := h
    obtain ⟨hmem, hsym⟩ := lsroFind_spec hf
    have hd := hro d hmem hrd
    rw [hsym] at hd
    have hin := relocsInBounds_spec hinb
    have hdis' := relocsDisjoint_spec hdis
    intro i hi
    have hlenPatched : off + i < (libsignalSessionLib.patchedData pl d).length := by
      have hfl :
          (d.relocs.foldl (libsignalSessionLib.patchDataReloc pl (pl.ρ d.sym)) d.bytes).length =
            d.bytes.length := by
        have haux : ∀ (rs : List RelocEntry) (acc : List (BitVec 8)),
            (∀ r ∈ rs, r.off + dataRelocWidth r.kind ≤ acc.length) →
            (rs.foldl (libsignalSessionLib.patchDataReloc pl (pl.ρ d.sym)) acc).length =
              acc.length := by
          intro rs
          induction rs with
          | nil => intro _ _; rfl
          | cons r rs ih =>
            intro acc hacc
            have hr1 :
                (libsignalSessionLib.patchDataReloc pl (pl.ρ d.sym) acc r).length = acc.length := by
              have h0 := hacc r (.head _)
              unfold MultiPlacedLib.patchDataReloc
              cases hk : r.kind <;> simp only []
              · simp [hk, dataRelocWidth] at h0; simp [bytesLE]; omega
              · simp [hk, dataRelocWidth] at h0; simp [bytesLE]; omega
              · simp [hk, dataRelocWidth] at h0; simp [bytesLE]; omega
              all_goals rfl
            rw [List.foldl_cons, ih _ (fun r' hr' => by rw [hr1]; exact hacc r' (.tail _ hr')), hr1]
        exact haux d.relocs d.bytes hin
      simp only [MultiPlacedLib.patchedData, List.length_append, hfl, List.length_replicate]
      omega
    obtain ⟨hrd_i, hperm_i⟩ := hd (off + i) hlenPatched
    have hadd : pl.ρ sym + BitVec.ofNat 64 off + BitVec.ofNat 64 i =
        pl.ρ sym + BitVec.ofNat 64 (off + i) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have hget := getElem?_patchedData_of_notReloc (lib := libsignalSessionLib)
      (pl := pl) (d := d) (i := off + i) hin
      (fun r hr => by rcases hdis' r hr with h1 | h2 <;> omega)
    have hraw : (d.bytes ++ List.replicate d.zeroTail 0#8)[off + i]? = some bs[i] := by
      have h1 : (((d.bytes ++ List.replicate d.zeroTail 0#8).drop off).take bs.length)[i]? =
          bs[i]? := congrArg (·[i]?) hbs
      rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_eq_getElem hi] at h1
      exact h1
    rw [List.getElem?_eq_getElem hlenPatched, hraw] at hget
    have heq : (libsignalSessionLib.patchedData pl d)[off + i] = bs[i] := Option.some.inj hget
    rw [hadd, ← heq]
    exact ⟨hrd_i, hperm_i⟩

theorem lsroSliceCheck_len {sym : String} {off : Nat} {bs : List (BitVec 8)}
    (h : lsroSliceCheck sym off bs = true) : bs.length ≤ 2 ^ 64 := by
  unfold lsroSliceCheck at h
  cases hf : lsroFind sym with
  | none => simp [hf] at h
  | some d =>
    simp only [hf, Bool.and_eq_true, decide_eq_true_eq] at h
    omega

theorem lsro_slice_read {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {off : Nat} {bs : List (BitVec 8)} (h : lsroSliceCheck sym off bs = true) :
    m.RO (pl.ρ sym + BitVec.ofNat 64 off) bs.length ∧
      m.readBytes (pl.ρ sym + BitVec.ofNat 64 off) bs.length = bs :=
  ProofLib.ObjectLoad.holdsBytes_ro (lsro_slice_holds hro h)

theorem lsro_slice_intro {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {off : Nat} {addr : BitVec 64} {bs : List (BitVec 8)}
    (haddr : addr = pl.ρ sym + BitVec.ofNat 64 off) (h : lsroSliceCheck sym off bs = true)
    {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (addr ↦ᵣ bs) ∗ P := by
  subst haddr
  obtain ⟨hro', hrd⟩ := lsro_slice_read hro h
  exact IsBlockRO.intro_of_ro (IsBlockRO.pointsToBytesRO _ _ (lsroSliceCheck_len h)) hro' hrd hP

theorem lsro64_intro {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {off : Nat} {addr : BitVec 64} {v : BitVec 64}
    (haddr : addr = pl.ρ sym + BitVec.ofNat 64 off) (h : lsroSliceCheck sym off (unpack64 v) = true)
    {P : SepProp} (hP : m ⊨ P) : m ⊨ (addr ↦₆₄ᵣ v) ∗ P := by
  rw [pointsTo64RO_eq_pointsToBytesRO]
  exact lsro_slice_intro hro haddr h hP

theorem lsro32_intro {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {off : Nat} {addr : BitVec 64} {v : BitVec 32}
    (haddr : addr = pl.ρ sym + BitVec.ofNat 64 off) (h : lsroSliceCheck sym off (unpack32 v) = true)
    {P : SepProp} (hP : m ⊨ P) : m ⊨ (addr ↦₃₂ᵣ v) ∗ P := by
  rw [pointsTo32RO_eq_pointsToBytesRO]
  exact lsro_slice_intro hro haddr h hP

theorem lsro16_intro {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {off : Nat} {addr : BitVec 64} {v : BitVec 16}
    (haddr : addr = pl.ρ sym + BitVec.ofNat 64 off) (h : lsroSliceCheck sym off (unpack16 v) = true)
    {P : SepProp} (hP : m ⊨ P) : m ⊨ (addr ↦₁₆ᵣ v) ∗ P := by
  rw [pointsTo16RO_eq_pointsToBytesRO]
  exact lsro_slice_intro hro haddr h hP

theorem lsro8_intro {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {off : Nat} {addr : BitVec 64} {v : BitVec 8}
    (haddr : addr = pl.ρ sym + BitVec.ofNat 64 off) (h : lsroSliceCheck sym off [v] = true)
    {P : SepProp} (hP : m ⊨ P) : m ⊨ (addr ↦₈ᵣ v) ∗ P := by
  rw [← pointsToBytesRO_singleton]
  exact lsro_slice_intro hro haddr h hP

/-! ## 4. Relocated `abs64` Words -/

def isReloc64To (off : Nat) (tgt : String) (r : RelocEntry) : Bool :=
  decide (r.off = off) && decide (r.kind = .abs64) && decide (r.sym = tgt) && decide (r.addend = 0)

def lsroReloc64Check (sym : String) (off : Nat) (tgt : String) : Bool :=
  match lsroFind sym with
  | some d =>
    d.readOnly && relocsInBounds d && d.relocs.any (isReloc64To off tgt) &&
      d.relocs.all fun r =>
        isReloc64To off tgt r || decide (off + 8 ≤ r.off ∨ r.off + dataRelocWidth r.kind ≤ off)
  | none => false

theorem isReloc64To_spec {off : Nat} {tgt : String} {r : RelocEntry}
    (h : isReloc64To off tgt r = true) :
    r.off = off ∧ r.kind = .abs64 ∧ r.sym = tgt ∧ r.addend = 0 := by
  unfold isReloc64To at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem splice_drop_take_eq {d bs : List (BitVec 8)} {off n : Nat} (hn : bs.length = n)
    (hb : off + n ≤ d.length) :
    ((d.take off ++ bs ++ d.drop (off + n)).drop off).take n = bs := by
  have htake : (d.take off).length = off := by simp; omega
  have hdrop : (d.take off).drop off = [] := by simp
  rw [List.append_assoc, List.drop_append_of_le_length (by omega), hdrop, List.nil_append,
    List.take_append_of_le_length (by omega), ← hn, List.take_length]

theorem patchDataReloc_slot_of_disjoint {lib : MultiPlacedLib} {pl : MultiPlacement}
    {addr : BitVec 64} {bytes : List (BitVec 8)} {r : RelocEntry} {off : Nat}
    (hdis : off + 8 ≤ r.off ∨ r.off + dataRelocWidth r.kind ≤ off)
    (hin : r.off + dataRelocWidth r.kind ≤ bytes.length) :
    ((lib.patchDataReloc pl addr bytes r).drop off).take 8 =
      (bytes.drop off).take 8 := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 8
  · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi,
      List.getElem?_drop, List.getElem?_drop]
    exact getElem?_patchDataReloc_of_disjoint (by rcases hdis with h1 | h2 <;> omega) hin
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem length_foldl_patchDataReloc {lib : MultiPlacedLib} {pl : MultiPlacement}
    {addr : BitVec 64} :
    ∀ (rs : List RelocEntry) (bs : List (BitVec 8)),
      (∀ r ∈ rs, r.off + dataRelocWidth r.kind ≤ bs.length) →
      (rs.foldl (lib.patchDataReloc pl addr) bs).length = bs.length
  | [], bs, _ => rfl
  | r :: rs, bs, hin => by
    have h1 : (lib.patchDataReloc pl addr bs r).length = bs.length := by
      have h0 := hin r (.head _)
      unfold MultiPlacedLib.patchDataReloc
      cases hk : r.kind <;> simp only []
      · simp [hk, dataRelocWidth] at h0; simp [bytesLE]; omega
      · simp [hk, dataRelocWidth] at h0; simp [bytesLE]; omega
      · simp [hk, dataRelocWidth] at h0; simp [bytesLE]; omega
      all_goals rfl
    rw [List.foldl_cons, length_foldl_patchDataReloc rs _ (fun r' hr' => by
      rw [h1]; exact hin r' (.tail _ hr')), h1]

private theorem addSignedAddr_zero (x : BitVec 64) : addSignedAddr x 0 = x := by
  simp [addSignedAddr]

theorem foldl_patchDataReloc_slot {lib : MultiPlacedLib} {pl : MultiPlacement}
    {addr : BitVec 64} {off : Nat} {tgt : String} :
    ∀ (rs : List RelocEntry) (bs : List (BitVec 8)),
      (∀ r ∈ rs, r.off + dataRelocWidth r.kind ≤ bs.length) →
      (∀ r ∈ rs, isReloc64To off tgt r = true ∨
        (off + 8 ≤ r.off ∨ r.off + dataRelocWidth r.kind ≤ off)) →
      (rs.any (isReloc64To off tgt) = true ∨
        (bs.drop off).take 8 = bytesLE 8 (lib.resolve pl tgt)) →
      ((rs.foldl (lib.patchDataReloc pl addr) bs).drop off).take 8 =
        bytesLE 8 (lib.resolve pl tgt)
  | [], bs, _, _, hany => by
    rcases hany with h | h
    · simp at h
    · exact h
  | r :: rs, bs, hin, hcases, hany => by
    have hr_in := hin r (.head _)
    have hlen1 : (lib.patchDataReloc pl addr bs r).length = bs.length :=
      length_foldl_patchDataReloc [r] bs (fun r' hr' => by simp at hr'; subst hr'; exact hr_in)
    have hin' : ∀ r' ∈ rs, r'.off + dataRelocWidth r'.kind ≤
        (lib.patchDataReloc pl addr bs r).length := fun r' hr' => by
      rw [hlen1]; exact hin r' (.tail _ hr')
    have hcases' : ∀ r' ∈ rs, isReloc64To off tgt r' = true ∨
        (off + 8 ≤ r'.off ∨ r'.off + dataRelocWidth r'.kind ≤ off) :=
      fun r' hr' => hcases r' (.tail _ hr')
    rcases hcases r (.head _) with hrel | hdis
    · obtain ⟨hoff, hkind, hsym, hadd⟩ := isReloc64To_spec hrel
      have hslot : ((lib.patchDataReloc pl addr bs r).drop off).take 8 =
          bytesLE 8 (lib.resolve pl tgt) := by
        have hb : off + 8 ≤ bs.length := by simpa [hoff, hkind, dataRelocWidth] using hr_in
        unfold MultiPlacedLib.patchDataReloc
        have hadd0 := addSignedAddr_zero (lib.resolve pl tgt)
        simp only [hoff, hkind, hsym, hadd, hadd0]
        exact splice_drop_take_eq (by simp [bytesLE]) hb
      exact foldl_patchDataReloc_slot rs _ hin' hcases' (Or.inr hslot)
    · have hslot := patchDataReloc_slot_of_disjoint (lib := lib) (pl := pl) (addr := addr) hdis hr_in
      have hany' : rs.any (isReloc64To off tgt) = true ∨
          ((lib.patchDataReloc pl addr bs r).drop off).take 8 =
            bytesLE 8 (lib.resolve pl tgt) := by
        rcases hany with ha | hb
        · simp only [List.any_cons, Bool.or_eq_true] at ha
          rcases ha with hr0 | hrs
          · obtain ⟨hoff, hkind, _, _⟩ := isReloc64To_spec hr0
            have : dataRelocWidth r.kind = 8 := by simp [hkind, dataRelocWidth]
            omega
          · exact Or.inl hrs
        · exact Or.inr (hslot.trans hb)
      exact foldl_patchDataReloc_slot rs _ hin' hcases' hany'

theorem lsro_reloc64_holds {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {off : Nat} {tgt : String} {v : BitVec 64}
    (hv : v = libsignalSessionLib.resolve pl tgt)
    (h : lsroReloc64Check sym off tgt = true) :
    HoldsBytes m (pl.ρ sym + BitVec.ofNat 64 off) (unpack64 v) (fun _ => Perm.ro) := by
  unfold lsroReloc64Check at h
  cases hf : lsroFind sym with
  | none => simp [hf] at h
  | some d =>
    simp only [hf, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hrd, hinb⟩, hany⟩, hall⟩ := h
    obtain ⟨hmem, hsym⟩ := lsroFind_spec hf
    have hin := relocsInBounds_spec hinb
    obtain ⟨r0, hr0_mem, hr0_is⟩ := List.any_eq_true.mp hany
    obtain ⟨hr0_off, hr0_kind, _, _⟩ := isReloc64To_spec hr0_is
    have hoff8 : off + 8 ≤ d.bytes.length := by
      simpa [hr0_off, hr0_kind, dataRelocWidth] using hin r0 hr0_mem
    have hd := hro d hmem hrd
    rw [hsym] at hd
    have hfl := length_foldl_patchDataReloc (lib := libsignalSessionLib)
      (pl := pl) (addr := pl.ρ d.sym) d.relocs d.bytes hin
    have hslot := foldl_patchDataReloc_slot (lib := libsignalSessionLib)
      (pl := pl) (addr := pl.ρ d.sym) (off := off)
      (tgt := tgt) d.relocs d.bytes hin hall (Or.inl hany)
    rw [← hv, bytesLE_eight_eq_unpack64] at hslot
    have hpatched_slice : ((libsignalSessionLib.patchedData pl d).drop off).take 8 =
        unpack64 v := by
      unfold MultiPlacedLib.patchedData
      rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by simp [hfl]; omega)]
      exact hslot
    exact holdsBytes_slice hd (by simpa using hpatched_slice)
      (by simp [MultiPlacedLib.patchedData, hfl]; omega)

theorem lsro_reloc64_intro {pl : MultiPlacement} {m : Memory} (hro : LibsignalRoLoaded pl m)
    {sym : String} {off : Nat} {tgt : String} {addr v : BitVec 64}
    (haddr : addr = pl.ρ sym + BitVec.ofNat 64 off) (hv : v = libsignalSessionLib.resolve pl tgt)
    (h : lsroReloc64Check sym off tgt = true) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ (addr ↦₆₄ᵣ v) ∗ P := by
  subst haddr
  obtain ⟨hro', hrd⟩ := ProofLib.ObjectLoad.holdsBytes_ro (lsro_reloc64_holds hro hv h)
  rw [pointsTo64RO_eq_pointsToBytesRO]
  exact IsBlockRO.intro_of_ro (IsBlockRO.pointsToBytesRO _ _ (by simp [unpack64_length]))
    hro' hrd hP

/-! ## 5. $O(\log N)$ Symbol Resolution Lemmas -/

theorem ls_resolve_data_chars {pl : MultiPlacement} {tgt : String} {cs : List Char}
    (hname : tgt = String.ofList cs) (h : lsNotBlockCharSym cs = true) :
    libsignalSessionLib.resolve pl tgt = pl.ρ tgt := by
  simp [MultiPlacedLib.resolve, lookupBlockSym_none_of_chars hname h]

theorem ls_resolve_text_chars {pl : MultiPlacement} {tgt : String} {cs : List Char} {i : Nat}
    (hname : tgt = String.ofList cs) (h : checkBlockCharSymAt cs = some (i, 0)) :
    libsignalSessionLib.resolve pl tgt = pl.base i := by
  simp [MultiPlacedLib.resolve, lookupBlockSym_some_of_chars hname h]

theorem ls_fnAddr_text_chars {pl : MultiPlacement} {tgt : String} {cs : List Char} {i : Nat}
    (hname : tgt = String.ofList cs) (h : checkBlockCharSymAt cs = some (i, 0)) :
    libsignalSessionLib.fnAddr pl tgt = pl.base i := by
  simp [MultiPlacedLib.fnAddr, lookupBlockSym_some_of_chars hname h]

theorem ls_resolve_data {pl : MultiPlacement} {tgt : String}
    (h : lsNotBlockSym tgt = true) : libsignalSessionLib.resolve pl tgt = pl.ρ tgt := by
  simp [MultiPlacedLib.resolve, lookupBlockSym_none_of_tree h]

theorem ls_resolve_text {pl : MultiPlacement} {tgt : String} {i : Nat}
    (h : fastLookupBlockSym tgt = some (i, 0)) :
    libsignalSessionLib.resolve pl tgt = pl.base i := by
  simp [MultiPlacedLib.resolve, lookupBlockSym_of_fast_some h]

theorem ls_fnAddr_text {pl : MultiPlacement} {tgt : String} {i : Nat}
    (h : fastLookupBlockSym tgt = some (i, 0)) :
    libsignalSessionLib.fnAddr pl tgt = pl.base i := by
  simp [MultiPlacedLib.fnAddr, lookupBlockSym_of_fast_some h]

/-- Close `addr = pl.ρ sym + BitVec.ofNat 64 off` side goals of the `lsro*_intro` lemmas. -/
macro "lsro_addr" : tactic => `(tactic| first
  | rfl
  | exact (BitVec.add_zero _).symm
  | (simp only [BitVec.add_assoc, BitVec.ofNat_add]; done)
  | (simp only [BitVec.add_assoc, BitVec.ofNat_add]; rfl)
  | bv_omega)

/-- Close `v = libsignalSessionLib.resolve pl tgt` side goals of `lsro_reloc64_intro` in
    $O(\log N)$ time. -/
macro "lsro_tgt" : tactic => `(tactic| first
  | exact (ls_resolve_data (by decide +kernel)).symm
  | exact (ls_resolve_text (by decide +kernel)).symm)

end LibsignalBinary.Proofs.Placed.BridgeReloc

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification
export LibsignalBinary.Proofs.Placed.BridgeReloc (holdsBytes_slice relocsInBounds relocsDisjoint lsroSliceCheck relocsInBounds_spec)
export LibsignalBinary.Proofs.Placed.BridgeReloc (relocsDisjoint_spec lsro_slice_holds lsroSliceCheck_len lsro_slice_read lsro_slice_intro)
export LibsignalBinary.Proofs.Placed.BridgeReloc (lsro64_intro lsro32_intro lsro16_intro lsro8_intro isReloc64To lsroReloc64Check)
export LibsignalBinary.Proofs.Placed.BridgeReloc (isReloc64To_spec splice_drop_take_eq patchDataReloc_slot_of_disjoint)
export LibsignalBinary.Proofs.Placed.BridgeReloc (length_foldl_patchDataReloc foldl_patchDataReloc_slot lsro_reloc64_holds)
export LibsignalBinary.Proofs.Placed.BridgeReloc (lsro_reloc64_intro ls_resolve_data_chars ls_resolve_text_chars ls_fnAddr_text_chars)
export LibsignalBinary.Proofs.Placed.BridgeReloc (ls_resolve_data ls_resolve_text ls_fnAddr_text)
end CryptoVerification
-- AUTO-BRIDGE END
