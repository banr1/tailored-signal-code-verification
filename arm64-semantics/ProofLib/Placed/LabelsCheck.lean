/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Object.Labels
public import ProofLib.Placed.Multi

/-!
# Object-Level Label Provenance Checker

Proves symbol and relocation provenance bridge lemmas from `Arm64.Obj.LabelsFromObjects` and
defines the decidable checker `checkLabelsFromObjectsB` with its soundness theorem
`labelsFromObjects_of_check`.
-/

@[expose] public section

namespace Arm64.Obj

/-! ## Provenance Bridge Theorems -/

theorem LabelsFromObjects.lookupBlockSym_data_none
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO) {d : SymDataInfo} (hd : d ∈ lib.data) :
    lookupBlockSym d.sym lib.blocks = none :=
  hlbl.names_nodup.2.2 d hd

theorem LabelsFromObjects.resolve_data_eq_rho
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO) (mpl : MultiPlacement)
    {d : SymDataInfo} (hd : d ∈ lib.data) :
    lib.resolve mpl d.sym = mpl.ρ d.sym := by
  simp [MultiPlacedLib.resolve, hlbl.lookupBlockSym_data_none hd]

theorem LabelsFromObjects.lookupBlockSym_extern_none
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO) {b : CodeBlock} (hb : b ∈ lib.blocks)
    {x : String} (hx : x ∈ b.externs) :
    lookupBlockSym x lib.blocks = none :=
  ((hlbl.externs_valid b hb).2.1 x hx).1

theorem LabelsFromObjects.resolve_extern_eq_rho
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO) (mpl : MultiPlacement)
    {b : CodeBlock} (hb : b ∈ lib.blocks) {x : String} (hx : x ∈ b.externs) :
    lib.resolve mpl x = mpl.ρ x := by
  simp [MultiPlacedLib.resolve, hlbl.lookupBlockSym_extern_none hb hx]

private theorem sub_toNat_beq_iff (a b base : BitVec 64) :
    ((a - base).toNat == (b - base).toNat) = (a == b) := by
  cases h : a == b with
  | true =>
    have hab : a = b := eq_of_beq h
    subst hab
    simp
  | false =>
    have hne : a ≠ b := ne_of_beq_false h
    rw [beq_eq_false_iff_ne]
    intro heq
    have hsub : a - base = b - base := BitVec.eq_of_toNat_eq heq
    have hadd := congrArg (· + base) hsub
    simp only [BitVec.sub_add_cancel] at hadd
    exact hne hadd

private theorem findSome_none {α β : Type} :
    ∀ (xs : List α), xs.findSome? (fun _ => (none : Option β)) = none
  | [] => rfl
  | _ :: xs => findSome_none xs

/-- Under `LabelsFromObjects`, `(lib.blockProgram mpl i externs (fun _ => none) svc).externAt? pc`
    reduces at every `pc : BitVec 64` directly to scanning `lib.blocks[i].externs` against `mpl.ρ`. -/
theorem LabelsFromObjects.externAt?_blockProgram
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO) (mpl : MultiPlacement)
    {i : Nat} (hi : i < lib.blocks.length)
    (externs : String → Option (State → State))
    (svc : State → State := Syscall.standard) (pc : BitVec 64) :
    (lib.blockProgram mpl i externs (fun _ => none) svc).externAt? pc =
      lib.blocks[i].externs.findSome? fun e =>
        if mpl.ρ e == pc then externs e else none := by
  have hb : lib.blocks[i] ∈ lib.blocks := List.getElem_mem hi
  have hblk : lib.blockLib i =
      { name := lib.name, text := lib.blocks[i], data := lib.data, exports := lib.exports } := by
    simp [MultiPlacedLib.blockLib, hi]
  rw [MultiPlacedLib.blockProgram, hblk]
  dsimp only [Program.externAt?, Program.hookAtOff?, PlacedLib.program,
    MultiPlacedLib.blockPlacement]
  simp only [ite_self]
  rw [findSome_none, Option.or_none, List.findSome?_map]
  suffices h : ∀ (es : List String),
      (∀ e ∈ es, e ∈ lib.blocks[i].externs) →
      es.findSome? ((fun (n, o) => if o == (pc - mpl.base i).toNat then externs n else none) ∘
        fun e => (e, (lib.resolve mpl e - mpl.base i).toNat)) =
      es.findSome? (fun e => if mpl.ρ e == pc then externs e else none) from
    h lib.blocks[i].externs (fun _ hmem => hmem)
  intro es hes
  induction es with
  | nil => rfl
  | cons e rest ih =>
    have he : e ∈ lib.blocks[i].externs := hes e List.mem_cons_self
    have hres : lib.resolve mpl e = mpl.ρ e := hlbl.resolve_extern_eq_rho mpl hb he
    simp only [List.findSome?_cons, Function.comp_apply, hres, sub_toNat_beq_iff]
    cases hpc : mpl.ρ e == pc
    · exact ih (fun x hx => hes x (List.mem_cons_of_mem _ hx))
    · simp only [↓reduceIte]
      cases externs e
      · exact ih (fun x hx => hes x (List.mem_cons_of_mem _ hx))
      · rfl

/-- Every raw relocation inside kept text slice `bO bi` appears as a matching `RelocEntry` in
    `lib.blocks[bi].relocs`. -/
theorem LabelsFromObjects.exists_reloc_of_rawReloc
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO) (bi : Fin lib.blocks.length)
    {bObj : ExtractedObj} {bSec : RawSec} {rr : RawReloc}
    (hbobj : objs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len) :
    ∃ r ∈ lib.blocks[bi].relocs,
      RelocMatches objs lib bO dO (bO bi).oi (bO bi).start rr r := by
  obtain ⟨obj, sec, hobj, hsec, perm, hplen, _, _, hmatch⟩ := hlbl.block_relocs bi
  rw [hbobj] at hobj; cases hobj
  rw [hbsec] at hsec; cases hsec
  let raw := bSec.relocs.filter fun r0 =>
    decide ((bO bi).start ≤ r0.off ∧ r0.off < (bO bi).start + (bO bi).len)
  have hmem : rr ∈ raw := List.mem_filter.2 ⟨hrr, decide_eq_true ⟨hlo, hhi⟩⟩
  obtain ⟨k, hk, hk_eq⟩ := List.getElem_of_mem hmem
  have hkp : k < perm.length := hplen.symm ▸ hk
  obtain ⟨hr, hrel⟩ := hmatch k hk hkp
  refine ⟨lib.blocks[bi].relocs[perm[k]]'hr, List.getElem_mem hr, ?_⟩
  exact hk_eq ▸ hrel

/-- `Resolves` is functional: a name has at most one `lld` winner. -/
theorem Resolves.unique {objs : List ExtractedObj} {raw : String}
    {oi k si oi' k' si' : Nat} {sy sy' : RawSym}
    (h : Resolves objs raw oi k si sy) (h' : Resolves objs raw oi' k' si' sy') :
    oi = oi' ∧ k = k' ∧ si = si' ∧ sy = sy' := by
  obtain ⟨_, ⟨o, ho, hsy⟩, hraw, hbind, hsec, _, hall⟩ := h
  obtain ⟨_, ⟨o', ho', hsy'⟩, hraw', hbind', hsec', _, hall'⟩ := h'
  by_cases hsame : oi' = oi ∧ k' = k
  · obtain ⟨rfl, rfl⟩ := hsame
    rw [ho] at ho'; cases ho'
    rw [hsy] at hsy'; cases hsy'
    rw [hsec] at hsec'; cases hsec'
    exact ⟨rfl, rfl, rfl, rfl⟩
  · exfalso
    have hne : oi' ≠ oi ∨ k' ≠ k := by
      by_cases h1 : oi' = oi
      · exact Or.inr fun h2 => hsame ⟨h1, h2⟩
      · exact Or.inl h1
    have hne' : oi ≠ oi' ∨ k ≠ k' := by
      rcases hne with h1 | h1
      · exact Or.inl (Ne.symm h1)
      · exact Or.inr (Ne.symm h1)
    have hnl : ∀ s : RawSym, (s.bind = .global ∨ s.bind = .weak) → s.bind ≠ .local := by
      intro s hs hl; rcases hs with hs | hs <;> rw [hs] at hl <;> exact nomatch hl
    have hnu : ∀ s : RawSym, ∀ n, s.sec = .sec n → s.sec ≠ .undef := by
      intro s n hs hu; rw [hs] at hu; exact nomatch hu
    obtain ⟨hw', _, hord⟩ := hall oi' k' o' sy' ho' hsy' hraw' (hnl sy' hbind')
      (hnu sy' si' hsec') hne
    obtain ⟨hw, _, hord'⟩ := hall' oi k o sy ho hsy hraw (hnl sy hbind) (hnu sy si hsec) hne'
    rw [hw] at hord; rw [hw'] at hord'
    rcases hord with hg | hlt | ⟨heq, hlt⟩
    · exact nomatch hg
    · rcases hord' with hg | hlt' | ⟨heq', hlt'⟩
      · exact nomatch hg
      · omega
      · omega
    · rcases hord' with hg | hlt' | ⟨heq', hlt'⟩
      · exact nomatch hg
      · omega
      · omega

/-- Two distinct `STB_GLOBAL` definitions of `raw` (a duplicate strong symbol) leave `raw` with no
    `lld` winner. -/
theorem Resolves.not_of_two_global {objs : List ExtractedObj} {raw : String}
    {o1 o2 : ExtractedObj} {oi1 k1 oi2 k2 : Nat} {s1 s2 : RawSym}
    (ho1 : objs[oi1]? = some o1) (hs1 : o1.symbols[k1]? = some s1)
    (ho2 : objs[oi2]? = some o2) (hs2 : o2.symbols[k2]? = some s2)
    (hr1 : s1.rawName = raw) (hr2 : s2.rawName = raw)
    (hg1 : s1.bind = .global) (hg2 : s2.bind = .global)
    (hd1 : s1.sec ≠ .undef) (hd2 : s2.sec ≠ .undef) (hne : oi1 ≠ oi2 ∨ k1 ≠ k2)
    {oi k si : Nat} {sy : RawSym} : ¬Resolves objs raw oi k si sy := by
  rintro ⟨_, _, _, _, _, _, hall⟩
  have hnl : ∀ s : RawSym, s.bind = .global → s.bind ≠ .local := by
    intro s hs hl; rw [hs] at hl; exact nomatch hl
  by_cases h1 : oi1 = oi ∧ k1 = k
  · obtain ⟨rfl, rfl⟩ := h1
    have hne2 : oi2 ≠ oi1 ∨ k2 ≠ k1 := by
      rcases hne with h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Ne.symm h)
    obtain ⟨hw, _⟩ := hall oi2 k2 o2 s2 ho2 hs2 hr2 (hnl s2 hg2) hd2 hne2
    rw [hg2] at hw; exact nomatch hw
  · have hne1 : oi1 ≠ oi ∨ k1 ≠ k := by
      by_cases h : oi1 = oi
      · exact Or.inr fun h' => h1 ⟨h, h'⟩
      · exact Or.inl h
    obtain ⟨hw, _⟩ := hall oi1 k1 o1 s1 ho1 hs1 hr1 (hnl s1 hg1) hd1 hne1
    rw [hg1] at hw; exact nomatch hw

/-- If `RelocMatches` links `rr` to `r` and `rr` resolves to offset `t` in non-exec, non-TLS data
    section `(dO di).oi, (dO di).si` where `dO di` is the unique data slice covering `t`, then
    `r.sym = lib.data[di].sym` and `(dO di).start + r.addend = t`. -/
theorem LabelsFromObjects.relocMatches_data_slice
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO) (di : Fin lib.data.length)
    {dObj : ExtractedObj} {dSec : RawSec}
    (hdobj : objs[(dO di).oi]? = some dObj)
    (hdsec : dObj.sections[(dO di).si]? = some dSec)
    {oi sliceStart : Nat} {rr : RawReloc} {r : RelocEntry}
    (hrel : RelocMatches objs lib bO dO oi sliceStart rr r)
    {bObj : ExtractedObj} {sy : RawSym}
    (hbobj : objs[oi]? = some bObj) (hsy : bObj.symbols[rr.symIdx]? = some sy)
    {t : Int}
    (htarget :
      (oi = (dO di).oi ∧ sy.bind = .local ∧ sy.sec = .sec (dO di).si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Resolves objs sy.rawName (dO di).oi k (dO di).si tSym ∧
        t = (tSym.value : Int) + rr.addend))
    (huniq : ∀ dj : Fin lib.data.length, dj ≠ di →
      (dO dj).oi = (dO di).oi → (dO dj).si = (dO di).si →
      t < ((dO dj).start : Int) ∨ (((dO dj).start + (dO dj).len : Nat) : Int) < t) :
    r.off + sliceStart = rr.off ∧ rr.kind = some r.kind ∧
      r.sym = lib.data[di].sym ∧ ((dO di).start : Int) + r.addend = t := by
  obtain ⟨dObj0, dSec0, hdobj0, hdsec0, _, hnoExec, hnoTls, _⟩ := hlbl.data_valid di
  rw [hdobj] at hdobj0; cases hdobj0
  rw [hdsec] at hdsec0; cases hdsec0
  obtain ⟨hoff, hkind, o0, sy0, ho0, hsy0, hcases⟩ := hrel
  rw [hbobj] at ho0; cases ho0
  rw [hsy] at hsy0; cases hsy0
  cases hcases with
  | inr hundef =>
    obtain ⟨hsec_u, hraw_eq, _, _, _, _, hall_u⟩ := hundef
    cases htarget with
    | inl hloc =>
      rw [hloc.2.2.1] at hsec_u
      exact nomatch hsec_u
    | inr hglob =>
      obtain ⟨_, k, tSym, hgdef, _⟩ := hglob
      obtain ⟨_, ⟨oDef, hoDef, hsymDef⟩, hrawDef, hbindDef, hsecDef, _⟩ := hgdef
      have hnl : tSym.bind ≠ .local := by
        intro hl; rcases hbindDef with hb | hb <;> rw [hb] at hl <;> exact nomatch hl
      have hu := hall_u oDef (List.mem_of_getElem? hoDef) tSym (List.mem_of_getElem? hsymDef)
        (hrawDef.trans hraw_eq) hnl
      rw [hsecDef] at hu
      exact nomatch hu
  | inl hint =>
    obtain ⟨oj, sj, ojObj, secT, tSym', t', hsrc, hoj, hsecT, hkind3⟩ := hint
    have heq_target : oj = (dO di).oi ∧ sj = (dO di).si ∧ t' = t := by
      cases htarget with
      | inl hloc =>
        obtain ⟨hoi, hbl, hsec_s, ht⟩ := hloc
        cases hsrc with
        | inl hsrcL =>
          obtain ⟨_, rfl, hsec_s', _, rfl, rfl⟩ := hsrcL
          rw [hsec_s] at hsec_s'
          cases hsec_s'
          exact ⟨hoi, rfl, ht.symm⟩
        | inr hsrcG => exact absurd hbl hsrcG.1
      | inr hglob =>
        obtain ⟨hnl, k, tSym, hgdef, ht⟩ := hglob
        cases hsrc with
        | inl hsrcL => exact absurd hsrcL.1 hnl
        | inr hsrcG =>
          obtain ⟨_, k', hgdef', rfl⟩ := hsrcG
          obtain ⟨rfl, rfl, rfl, rfl⟩ := Resolves.unique hgdef' hgdef
          exact ⟨rfl, rfl, ht.symm⟩
    obtain ⟨rfl, rfl, rfl⟩ := heq_target
    rw [hdobj] at hoj; cases hoj
    rw [hdsec] at hsecT; cases hsecT
    rcases hkind3 with hexec | hdata | htls
    · rw [hnoExec] at hexec; exact nomatch hexec.1
    · obtain ⟨_, _, _, dj, hdsym, hdoi, hdsi, hadd_lo, hadd_hi, hadd_eq⟩ := hdata
      by_cases hdj : dj = di
      · subst hdj
        exact ⟨hoff, hkind, hdsym.symm, hadd_eq⟩
      · exfalso
        have hu := huniq dj hdj hdoi hdsi
        omega
    · rw [hnoTls] at htls; exact nomatch htls.2.1

/-- Combined provenance theorem for raw code relocations targeting a covered data slice `dO di`. -/
theorem LabelsFromObjects.data_reloc_sym_eq
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO)
    (bi : Fin lib.blocks.length) (di : Fin lib.data.length)
    {bObj dObj : ExtractedObj} {bSec dSec : RawSec} {rr : RawReloc} {sy : RawSym}
    (hbobj : objs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hdobj : objs[(dO di).oi]? = some dObj)
    (hdsec : dObj.sections[(dO di).si]? = some dSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    {t : Int}
    (htarget :
      ((bO bi).oi = (dO di).oi ∧ sy.bind = .local ∧ sy.sec = .sec (dO di).si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Resolves objs sy.rawName (dO di).oi k (dO di).si tSym ∧
        t = (tSym.value : Int) + rr.addend))
    (huniq : ∀ dj : Fin lib.data.length, dj ≠ di →
      (dO dj).oi = (dO di).oi → (dO dj).si = (dO di).si →
      t < ((dO dj).start : Int) ∨ (((dO dj).start + (dO dj).len : Nat) : Int) < t) :
    ∃ r ∈ lib.blocks[bi].relocs,
      r.off + (bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = lib.data[di].sym ∧ ((dO di).start : Int) + r.addend = t := by
  obtain ⟨r, hr_mem, hrel⟩ := hlbl.exists_reloc_of_rawReloc bi hbobj hbsec hrr hlo hhi
  exact ⟨r, hr_mem, hlbl.relocMatches_data_slice di hdobj hdsec hrel hbobj hsy htarget huniq⟩

/-- Specialization of `data_reloc_sym_eq` when `dO di` is the sole data slice in section
    `((dO di).oi, (dO di).si)` (standard under `-fdata-sections` / Rust per-static sections). -/
theorem LabelsFromObjects.sole_data_reloc_sym_eq
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO : Fin lib.blocks.length → SliceOrigin} {dO : Fin lib.data.length → SliceOrigin}
    (hlbl : LabelsFromObjects objs lib bO dO)
    (bi : Fin lib.blocks.length) (di : Fin lib.data.length)
    {bObj dObj : ExtractedObj} {bSec dSec : RawSec} {rr : RawReloc} {sy : RawSym}
    (hbobj : objs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hdobj : objs[(dO di).oi]? = some dObj)
    (hdsec : dObj.sections[(dO di).si]? = some dSec)
    (hsole : ∀ dj : Fin lib.data.length, (dO dj).oi = (dO di).oi → (dO dj).si = (dO di).si → dj = di)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    {t : Int}
    (htarget :
      ((bO bi).oi = (dO di).oi ∧ sy.bind = .local ∧ sy.sec = .sec (dO di).si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Resolves objs sy.rawName (dO di).oi k (dO di).si tSym ∧
        t = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ lib.blocks[bi].relocs,
      r.off + (bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = lib.data[di].sym ∧ ((dO di).start : Int) + r.addend = t :=
  hlbl.data_reloc_sym_eq bi di hbobj hbsec hdobj hdsec hrr hlo hhi hsy htarget
    (fun dj hne hoi hsi => False.elim (hne (hsole dj hoi hsi)))

/-! ## Decidable Checker -/

def checkSymNameDerivedB (sym base objName : String) : Bool :=
  (sym == base) || (sym == base ++ " [" ++ objName ++ "]")

theorem symNameDerived_of_check {sym base objName : String}
    (h : checkSymNameDerivedB sym base objName = true) :
    SymNameDerived sym base objName := by
  unfold checkSymNameDerivedB at h
  rw [Bool.or_eq_true] at h
  rcases h with h1 | h2
  · exact Or.inl (eq_of_beq h1)
  · exact Or.inr (eq_of_beq h2)

def checkUnclaimedSymNameB (objs : List ExtractedObj) (sym : String) : Bool :=
  objs.all fun o =>
    o.symbols.all fun sy =>
      if sy.rawName == "" then true
      else (sym != sy.rawName) && !checkSymNameDerivedB sym sy.name o.name

theorem unclaimedSymName_of_check {objs : List ExtractedObj} {sym : String}
    (h : checkUnclaimedSymNameB objs sym = true) :
    UnclaimedSymName objs sym := by
  intro o ho sy hsy hraw
  unfold checkUnclaimedSymNameB at h
  rw [List.all_eq_true] at h
  have ho' := h o ho
  rw [List.all_eq_true] at ho'
  have hsy' := ho' sy hsy
  have hrawF : (sy.rawName == "") = false := beq_eq_false_iff_ne.2 hraw
  simp only [hrawF, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, bne_iff_ne,
    Bool.not_eq_true'] at hsy'
  refine ⟨hsy'.1, ?_⟩
  intro hder
  have hcb : checkSymNameDerivedB sym sy.name o.name = true := by
    unfold checkSymNameDerivedB
    rcases hder with rfl | rfl <;> simp
  rw [hsy'.2] at hcb
  exact nomatch hcb

def checkCoversDataSliceB (o : SliceOrigin) (sy : RawSym) : Bool :=
  (sy.kind == .object) && (sy.sec == .sec o.si) &&
    (sy.value == o.start) && (sy.size == o.len) && (sy.rawName != "")

theorem coversDataSlice_iff_check (o : SliceOrigin) (sy : RawSym) :
    checkCoversDataSliceB o sy = true ↔ CoversDataSlice o sy := by
  unfold checkCoversDataSliceB CoversDataSlice
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, and_assoc]

/-- Some COMDAT group earlier than group `gi` of `objs[oi]` (in an earlier object, or earlier in
    the same object) has signature `sig`. -/
def claimedEarlierB (objs : List ExtractedObj) (oi gi : Nat) (sig : String) : Bool :=
  (List.range objs.length).any fun oj =>
    match objs[oj]? with
    | none => false
    | some o' =>
      (List.range o'.groups.length).any fun gj =>
        match o'.groups[gj]? with
        | none => false
        | some g' => (g'.signature == sig) && decide (oj < oi ∨ (oj = oi ∧ gj < gi))

theorem claimedEarlierB_iff {objs : List ExtractedObj} {oi gi : Nat} {sig : String} :
    claimedEarlierB objs oi gi sig = true ↔
      ∃ (oj : Nat) (o' : ExtractedObj) (g' : RawGroup) (gj : Nat),
        objs[oj]? = some o' ∧ o'.groups[gj]? = some g' ∧
        g'.signature = sig ∧ (oj < oi ∨ (oj = oi ∧ gj < gi)) := by
  unfold claimedEarlierB
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨oj, _, h⟩ := h
    cases ho : objs[oj]? with
    | none => rw [ho] at h; exact nomatch h
    | some o' =>
      rw [ho] at h; dsimp only at h
      rw [List.any_eq_true] at h
      obtain ⟨gj, _, h⟩ := h
      cases hg : o'.groups[gj]? with
      | none => rw [hg] at h; exact nomatch h
      | some g' =>
        rw [hg] at h; dsimp only at h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        exact ⟨oj, o', g', gj, ho, hg, h.1, h.2⟩
  · rintro ⟨oj, o', g', gj, ho, hg, hsig, hlt⟩
    rw [List.any_eq_true]
    refine ⟨oj, List.mem_range.2 (List.getElem?_eq_some_iff.1 ho).1, ?_⟩
    rw [ho]; dsimp only
    rw [List.any_eq_true]
    refine ⟨gj, List.mem_range.2 (List.getElem?_eq_some_iff.1 hg).1, ?_⟩
    rw [hg]; dsimp only
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨hsig, hlt⟩

def checkDiscardedB (objs : List ExtractedObj) (oi si : Nat) : Bool :=
  match objs[oi]? with
  | none => false
  | some o =>
    (List.range o.groups.length).any fun gi =>
      match o.groups[gi]? with
      | none => false
      | some g => g.members.contains si && claimedEarlierB objs oi gi g.signature

theorem discarded_iff_check {objs : List ExtractedObj} {oi si : Nat} :
    checkDiscardedB objs oi si = true ↔ Discarded objs oi si := by
  unfold checkDiscardedB Discarded
  constructor
  · intro h
    cases ho : objs[oi]? with
    | none => rw [ho] at h; exact nomatch h
    | some o =>
      rw [ho] at h; dsimp only at h
      rw [List.any_eq_true] at h
      obtain ⟨gi, _, h⟩ := h
      cases hg : o.groups[gi]? with
      | none => rw [hg] at h; exact nomatch h
      | some g =>
        rw [hg] at h; dsimp only at h
        rw [Bool.and_eq_true, List.contains_iff_mem, claimedEarlierB_iff] at h
        exact ⟨o, g, gi, rfl, hg, h.1, h.2⟩
  · rintro ⟨o, g, gi, ho, hg, hmem, hclaim⟩
    rw [ho]; dsimp only
    rw [List.any_eq_true]
    refine ⟨gi, List.mem_range.2 (List.getElem?_eq_some_iff.1 hg).1, ?_⟩
    rw [hg]; dsimp only
    rw [Bool.and_eq_true, List.contains_iff_mem, claimedEarlierB_iff]
    exact ⟨hmem, hclaim⟩

theorem not_discarded_of_check {objs : List ExtractedObj} {oi si : Nat}
    (h : checkDiscardedB objs oi si = false) : ¬Discarded objs oi si := by
  intro hd
  rw [← discarded_iff_check, h] at hd
  exact nomatch hd

instance instDecidableDiscarded (objs : List ExtractedObj) (oi si : Nat) :
    Decidable (Discarded objs oi si) :=
  decidable_of_iff _ discarded_iff_check

/-- No COMDAT group signature of `objs` repeats (within or across objects), so nothing is
    `Discarded`. -/
def checkNoDiscardedB (objs : List ExtractedObj) : Bool :=
  (List.range objs.length).all fun oi =>
    match objs[oi]? with
    | none => true
    | some o =>
      (List.range o.groups.length).all fun gi =>
        match o.groups[gi]? with
        | none => true
        | some g => !claimedEarlierB objs oi gi g.signature

theorem not_discarded_of_checkNoDiscarded {objs : List ExtractedObj}
    (h : checkNoDiscardedB objs = true) (oi si : Nat) : ¬Discarded objs oi si := by
  rintro ⟨o, g, gi, ho, hg, _, hclaim⟩
  unfold checkNoDiscardedB at h
  rw [List.all_eq_true] at h
  have h1 := h oi (List.mem_range.2 (List.getElem?_eq_some_iff.1 ho).1)
  rw [ho] at h1; dsimp only at h1
  rw [List.all_eq_true] at h1
  have h2 := h1 gi (List.mem_range.2 (List.getElem?_eq_some_iff.1 hg).1)
  rw [hg] at h2; dsimp only at h2
  rw [← claimedEarlierB_iff] at hclaim
  rw [hclaim] at h2
  exact nomatch h2

/-- `sy'` is a non-local definition (not `SHN_UNDEF`) of name `raw`. -/
def nonLocalDefB (raw : String) (sy' : RawSym) : Bool :=
  (sy'.rawName == raw) && (sy'.bind != .local) && (sy'.sec != .undef)

/-- `sy` is defined in an allocated section. -/
def secDefinedB (sy : RawSym) : Bool :=
  match sy.sec with
  | .sec _ => true
  | _ => false

theorem secDefinedB_iff {sy : RawSym} : secDefinedB sy = true ↔ ∃ sj, sy.sec = .sec sj := by
  cases hs : sy.sec <;> simp [secDefinedB, hs]

/-- Competitor `sy'` at `(oj, k')` loses to `sy` at `(oi, k)` under `lld` precedence: `sy'` is an
    `STB_WEAK` definition in an allocated section, and `sy` is `STB_GLOBAL` or comes first. -/
def losesToB (sy : RawSym) (oi k : Nat) (sy' : RawSym) (oj k' : Nat) : Bool :=
  (sy'.bind == .weak) && secDefinedB sy' &&
    ((sy.bind == .global) || decide (oi < oj) || ((oi == oj) && decide (k < k')))

def checkResolvesB (objs : List ExtractedObj) (raw : String) (oi k si : Nat) (sy : RawSym) :
    Bool :=
  (raw != "") &&
  (match objs[oi]? with
   | some o => o.symbols[k]? == some sy
   | none => false) &&
  (sy.rawName == raw) && ((sy.bind == .global) || (sy.bind == .weak)) && (sy.sec == .sec si) &&
  !checkDiscardedB objs oi si &&
  (List.range objs.length).all fun oj =>
    match objs[oj]? with
    | none => true
    | some o' =>
      (List.range o'.symbols.length).all fun k' =>
        match o'.symbols[k']? with
        | none => true
        | some sy' =>
          if nonLocalDefB raw sy' && ((oj != oi) || (k' != k)) then losesToB sy oi k sy' oj k'
          else true

theorem resolves_of_check {objs : List ExtractedObj} {raw : String} {oi k si : Nat}
    {sy : RawSym} (h : checkResolvesB objs raw oi k si sy = true) :
    Resolves objs raw oi k si sy := by
  unfold checkResolvesB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hraw, hex⟩, hsr⟩, hbind⟩, hsec⟩, hdisc⟩, hall⟩ := h
  have hex' : ∃ o, objs[oi]? = some o ∧ o.symbols[k]? = some sy := by
    cases ho : objs[oi]? with
    | none => rw [ho] at hex; exact nomatch hex
    | some o => rw [ho, beq_iff_eq] at hex; exact ⟨o, rfl, hex⟩
  refine ⟨bne_iff_ne.1 hraw, hex', beq_iff_eq.1 hsr, ?_, beq_iff_eq.1 hsec,
    not_discarded_of_check hdisc, ?_⟩
  · simpa only [Bool.or_eq_true, beq_iff_eq] using hbind
  intro oj k' o' sy' hoj hk' hsr' hbind' hsec' hne
  rw [List.all_eq_true] at hall
  have h1 := hall oj (List.mem_range.2 (List.getElem?_eq_some_iff.1 hoj).1)
  rw [hoj] at h1; dsimp only at h1
  rw [List.all_eq_true] at h1
  have h2 := h1 k' (List.mem_range.2 (List.getElem?_eq_some_iff.1 hk').1)
  rw [hk'] at h2; dsimp only at h2
  have hcond : nonLocalDefB raw sy' = true ∧ ((oj != oi) || (k' != k)) = true := by
    unfold nonLocalDefB
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
    exact ⟨⟨⟨hsr', hbind'⟩, hsec'⟩, hne⟩
  rw [ite_eq_left hcond] at h2
  unfold losesToB at h2
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
  obtain ⟨⟨hw, hdef⟩, hord⟩ := h2
  refine ⟨hw, secDefinedB_iff.1 hdef, ?_⟩
  rcases hord with (hg | hlt) | ⟨heq, hk⟩
  · exact Or.inl hg
  · exact Or.inr (Or.inl hlt)
  · exact Or.inr (Or.inr ⟨heq, hk⟩)

/-- Candidate `Resolves` winner of `raw`: the first `STB_GLOBAL` non-local definition in
    `(oi, k)` order, else the first `STB_WEAK` one (validated by `checkResolvesB`). -/
def findResolves? (objs : List ExtractedObj) (raw : String) :
    Option (Nat × Nat × Nat × RawSym) :=
  if raw == "" then none
  else
    let hits := (List.range objs.length).flatMap fun oj =>
      match objs[oj]? with
      | none => []
      | some o =>
        (List.range o.symbols.length).filterMap fun k =>
          match o.symbols[k]? with
          | none => none
          | some sy => if nonLocalDefB raw sy then some (oj, k, sy) else none
    let pick := (hits.find? fun (_, _, sy) => sy.bind == .global).or
      (hits.find? fun (_, _, sy) => sy.bind == .weak)
    match pick with
    | some (oi, k, sy) =>
      match sy.sec with
      | .sec si => some (oi, k, si, sy)
      | _ => none
    | none => none

def checkValidTextSliceB (objs : List ExtractedObj) (b : CodeBlock) (o : SliceOrigin) : Bool :=
  match objs[o.oi]? with
  | none => false
  | some obj =>
    match obj.sections[o.si]? with
    | none => false
    | some sec =>
      !checkDiscardedB objs o.oi o.si &&
      sec.isExec && sec.readOnly && (!sec.isNobits) && (!sec.isTls) &&
      decide (0 < o.len) && decide (o.start % 4 = 0) && decide (o.len % 4 = 0) &&
      decide (o.start + o.len ≤ sec.size) &&
      decide (sec.bytes.length = sec.size) &&
      (b.code == (sec.bytes.drop o.start).take o.len) &&
      decide (0 < sec.align) && decide (b.align % Nat.gcd sec.align o.start = 0) &&
      b.symbols.all fun (sym, off) =>
        decide (off < o.len) && decide (off % 4 = 0) &&
        ((obj.symbols.any fun sy =>
            (sy.kind == .func) && (sy.sec == .sec o.si) && (sy.rawName != "") &&
            (sy.value == o.start + off) && checkSymNameDerivedB sym sy.name obj.name) ||
          checkUnclaimedSymNameB objs sym)

theorem validTextSlice_of_check {objs : List ExtractedObj} {b : CodeBlock} {o : SliceOrigin}
    (h : checkValidTextSliceB objs b o = true) :
    ValidTextSlice objs b o := by
  unfold checkValidTextSliceB at h
  cases hobj : objs[o.oi]? with
  | none => rw [hobj] at h; exact nomatch h
  | some obj =>
    rw [hobj] at h; dsimp only at h
    cases hsec : obj.sections[o.si]? with
    | none => rw [hsec] at h; exact nomatch h
    | some sec =>
      rw [hsec] at h; dsimp only at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdisc, hexec⟩, hro⟩, hnob⟩, htls⟩, hpos⟩, hs4⟩, hl4⟩, hle⟩, hblen⟩,
        hcode⟩, halign0⟩, halign⟩, hsyms⟩ := h
      refine ⟨obj, sec, hobj, hsec, not_discarded_of_check hdisc, hexec, hro, hnob, htls, hpos,
        hs4, hl4, hle, hblen, hcode, halign0, halign, ?_⟩
      intro sym off hmem
      rw [List.all_eq_true] at hsyms
      have hs := hsyms (sym, off) hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hs
      refine ⟨hs.1.1, hs.1.2, ?_⟩
      rcases hs.2 with hany | huncl
      · rw [List.any_eq_true] at hany
        obtain ⟨sy, hsy_mem, hsy_ok⟩ := hany
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hsy_ok
        exact Or.inl ⟨sy, hsy_mem, hsy_ok.1.1.1.1, hsy_ok.1.1.1.2, hsy_ok.1.1.2, hsy_ok.1.2,
          symNameDerived_of_check hsy_ok.2⟩
      · exact Or.inr (unclaimedSymName_of_check huncl)

def checkValidDataSliceB (objs : List ExtractedObj) (d : SymDataInfo) (o : SliceOrigin) : Bool :=
  match objs[o.oi]? with
  | none => false
  | some obj =>
    match obj.sections[o.si]? with
    | none => false
    | some sec =>
      !checkDiscardedB objs o.oi o.si &&
      (!sec.isExec) && (!sec.isTls) && decide (o.start + o.len ≤ sec.size) &&
      (d.readOnly == sec.readOnly) &&
      (if sec.isNobits then (d.bytes == []) && (d.zeroTail == o.len)
       else decide (sec.bytes.length = sec.size) &&
            (d.bytes == (sec.bytes.drop o.start).take o.len) && (d.zeroTail == 0)) &&
      decide (0 < sec.align) && decide (d.align % Nat.gcd sec.align o.start = 0) &&
      ((obj.symbols.any fun sy =>
          checkCoversDataSliceB o sy && checkSymNameDerivedB d.sym sy.name obj.name) ||
       ((!obj.symbols.any fun sy => checkCoversDataSliceB o sy) &&
        checkUnclaimedSymNameB objs d.sym))

theorem validDataSlice_of_check {objs : List ExtractedObj} {d : SymDataInfo} {o : SliceOrigin}
    (h : checkValidDataSliceB objs d o = true) :
    ValidDataSlice objs d o := by
  unfold checkValidDataSliceB at h
  cases hobj : objs[o.oi]? with
  | none => rw [hobj] at h; exact nomatch h
  | some obj =>
    rw [hobj] at h; dsimp only at h
    cases hsec : obj.sections[o.si]? with
    | none => rw [hsec] at h; exact nomatch h
    | some sec =>
      rw [hsec] at h; dsimp only at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hdisc, hexec⟩, htls⟩, hle⟩, hro⟩, hbytes⟩, halign0⟩, halign⟩, hsym⟩ := h
      refine ⟨obj, sec, hobj, hsec, not_discarded_of_check hdisc, hexec, htls, hle, hro, ?_,
        halign0, halign, ?_⟩
      · cases hnb : sec.isNobits with
        | true =>
          rw [hnb] at hbytes
          simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hbytes
          exact hbytes
        | false =>
          rw [hnb] at hbytes
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
            beq_iff_eq] at hbytes
          exact ⟨hbytes.1.1, hbytes.1.2, hbytes.2⟩
      · rw [Bool.or_eq_true] at hsym
        rcases hsym with hcov | huncov
        · rw [List.any_eq_true] at hcov
          obtain ⟨sy, hsy_mem, hsy_ok⟩ := hcov
          rw [Bool.and_eq_true] at hsy_ok
          exact Or.inl ⟨sy, hsy_mem, (coversDataSlice_iff_check o sy).1 hsy_ok.1,
            symNameDerived_of_check hsy_ok.2⟩
        · rw [Bool.and_eq_true, Bool.not_eq_true'] at huncov
          refine Or.inr ⟨?_, unclaimedSymName_of_check huncov.2⟩
          rintro ⟨sy, hsy_mem, hcov⟩
          have hany : (obj.symbols.any fun sy => checkCoversDataSliceB o sy) = true :=
            List.any_eq_true.2 ⟨sy, hsy_mem, (coversDataSlice_iff_check o sy).2 hcov⟩
          rw [huncov.1] at hany
          exact nomatch hany

instance instDecidableRangesDisjoint (s1 n1 s2 n2 : Nat) :
    Decidable (RangesDisjoint s1 n1 s2 n2) :=
  inferInstanceAs (Decidable (_ ∨ _))

def checkOriginsDisjointB (origins : List SliceOrigin) : Bool :=
  (List.range origins.length).all fun i =>
    (List.range origins.length).all fun j =>
      if i == j then true
      else
        match origins[i]?, origins[j]? with
        | some oi, some oj =>
          (oi.oi != oj.oi) || (oi.si != oj.si) ||
            decide (RangesDisjoint oi.start oi.len oj.start oj.len)
        | _, _ => false

theorem originsDisjoint_of_check {origins : List SliceOrigin} {n : Nat}
    (hlen : origins.length = n) (h : checkOriginsDisjointB origins = true) :
    ∀ i j : Fin n, i ≠ j →
      (origins[i.1]'(by omega)).oi = (origins[j.1]'(by omega)).oi →
      (origins[i.1]'(by omega)).si = (origins[j.1]'(by omega)).si →
      RangesDisjoint (origins[i.1]'(by omega)).start (origins[i.1]'(by omega)).len
        (origins[j.1]'(by omega)).start (origins[j.1]'(by omega)).len := by
  intro i j hne hoi hsi
  unfold checkOriginsDisjointB at h
  rw [List.all_eq_true] at h
  have hi := h i.1 (List.mem_range.2 (by omega))
  rw [List.all_eq_true] at hi
  have hj := hi j.1 (List.mem_range.2 (by omega))
  have hij : (i.1 == j.1) = false := beq_eq_false_iff_ne.2 (fun heq => hne (Fin.ext heq))
  rw [hij] at hj
  simp only [Bool.false_eq_true, ↓reduceIte, List.getElem?_eq_getElem (by omega : i.1 < origins.length),
    List.getElem?_eq_getElem (by omega : j.1 < origins.length), Bool.or_eq_true, bne_iff_ne,
    decide_eq_true_eq] at hj
  rcases hj with (h1 | h2) | hdisj
  · exact False.elim (h1 hoi)
  · exact False.elim (h2 hsi)
  · exact hdisj

def checkRelocMatchesB (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (bO dO : List SliceOrigin) (oi sliceStart : Nat) (rr : RawReloc) (r : RelocEntry) : Bool :=
  decide (r.off + sliceStart = rr.off) && (rr.kind == some r.kind) &&
  match objs[oi]? with
  | none => false
  | some o =>
    match o.symbols[rr.symIdx]? with
    | none => false
    | some sy =>
      let resolvedTarget? : Option (Nat × Nat × RawSym × Int) :=
        if sy.bind == .local then
          match sy.sec with
          | .sec sj =>
            if !checkDiscardedB objs oi sj then some (oi, sj, sy, (sy.value : Int) + rr.addend)
            else none
          | _ => none
        else
          match findResolves? objs sy.rawName with
          | some (oj, k, sj, tSym) =>
            if checkResolvesB objs sy.rawName oj k sj tSym then
              some (oj, sj, tSym, (tSym.value : Int) + rr.addend)
            else none
          | none => none
      let internalOk : Bool :=
        match resolvedTarget? with
        | none => false
        | some (oj, sj, _, t) =>
          match objs[oj]? with
          | none => false
          | some ojObj =>
            match ojObj.sections[sj]? with
            | none => false
            | some secT =>
              if secT.isExec then
                match lookupBlockSym r.sym lib.blocks with
                | some (bj, off) =>
                  match bO[bj]? with
                  | some bo =>
                    decide (bj < lib.blocks.length) && (bo.oi == oj) && (bo.si == sj) &&
                    decide (0 ≤ (off : Int) + r.addend) &&
                    decide ((off : Int) + r.addend ≤ (bo.len : Int)) &&
                    decide ((bo.start + off : Int) + r.addend = t)
                  | none => false
                | none => false
              else if !secT.isTls then
                (lookupBlockSym r.sym lib.blocks).isNone &&
                (List.range lib.data.length).any fun dj =>
                  match lib.data[dj]?, dO[dj]? with
                  | some d, some do_ =>
                    (d.sym == r.sym) && (do_.oi == oj) && (do_.si == sj) &&
                    decide (0 ≤ r.addend) && decide (r.addend ≤ (do_.len : Int)) &&
                    decide ((do_.start : Int) + r.addend = t)
                  | _, _ => false
              else
                (lookupBlockSym r.sym lib.blocks).isNone &&
                (lib.data.all fun d => d.sym != r.sym) &&
                ojObj.symbols.any fun ts =>
                  (ts.sec == .sec sj) && (ts.kind == .tls) && (ts.rawName != "") &&
                  (r.sym == ts.rawName) && decide ((ts.value : Int) + r.addend = t)
      let undefOk : Bool :=
        (sy.sec == .undef) && (sy.rawName == r.sym) && (r.sym != "") &&
        decide (r.addend = rr.addend) &&
        (lookupBlockSym r.sym lib.blocks).isNone &&
        (lib.data.all fun d => d.sym != r.sym) &&
        objs.all fun o' =>
          o'.symbols.all fun sy' =>
            if (sy'.rawName == r.sym) && (sy'.bind != .local) then sy'.sec == .undef
            else true
      internalOk || undefOk

theorem relocMatches_of_check {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO dO : List SliceOrigin}
    (hbLen : bO.length = lib.blocks.length) (hdLen : dO.length = lib.data.length)
    {oi sliceStart : Nat} {rr : RawReloc} {r : RelocEntry}
    (h : checkRelocMatchesB objs lib bO dO oi sliceStart rr r = true) :
    RelocMatches objs lib (fun i => bO[i.1]'(by omega)) (fun i => dO[i.1]'(by omega))
      oi sliceStart rr r := by
  unfold checkRelocMatchesB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hoff, hkind⟩, hbody⟩ := h
  refine ⟨hoff, hkind, ?_⟩
  cases ho : objs[oi]? with
  | none => rw [ho] at hbody; exact nomatch hbody
  | some o =>
    rw [ho] at hbody; dsimp only at hbody
    cases hsy : o.symbols[rr.symIdx]? with
    | none => rw [hsy] at hbody; exact nomatch hbody
    | some sy =>
      rw [hsy] at hbody; dsimp only at hbody
      rw [Bool.or_eq_true] at hbody
      refine ⟨o, sy, rfl, hsy, ?_⟩
      rcases hbody with hint | hundef
      · left
        have hres : ∃ oj sj tSym t,
            ((sy.bind = .local ∧ oj = oi ∧ sy.sec = .sec sj ∧ ¬Discarded objs oi sj ∧
                tSym = sy ∧ t = (sy.value : Int) + rr.addend) ∨
             (sy.bind ≠ .local ∧ ∃ k, Resolves objs sy.rawName oj k sj tSym ∧
               t = (tSym.value : Int) + rr.addend)) ∧
            (match objs[oj]? with
             | none => false
             | some ojObj =>
               match ojObj.sections[sj]? with
               | none => false
               | some secT =>
                 if secT.isExec then
                   match lookupBlockSym r.sym lib.blocks with
                   | some (bj, off) =>
                     match bO[bj]? with
                     | some bo =>
                       decide (bj < lib.blocks.length) && (bo.oi == oj) && (bo.si == sj) &&
                       decide (0 ≤ (off : Int) + r.addend) &&
                       decide ((off : Int) + r.addend ≤ (bo.len : Int)) &&
                       decide ((bo.start + off : Int) + r.addend = t)
                     | none => false
                   | none => false
                 else if !secT.isTls then
                   (lookupBlockSym r.sym lib.blocks).isNone &&
                   (List.range lib.data.length).any fun dj =>
                     match lib.data[dj]?, dO[dj]? with
                     | some d, some do_ =>
                       (d.sym == r.sym) && (do_.oi == oj) && (do_.si == sj) &&
                       decide (0 ≤ r.addend) && decide (r.addend ≤ (do_.len : Int)) &&
                       decide ((do_.start : Int) + r.addend = t)
                     | _, _ => false
                 else
                   (lookupBlockSym r.sym lib.blocks).isNone &&
                   (lib.data.all fun d => d.sym != r.sym) &&
                   ojObj.symbols.any fun ts =>
                     (ts.sec == .sec sj) && (ts.kind == .tls) && (ts.rawName != "") &&
                     (r.sym == ts.rawName) && decide ((ts.value : Int) + r.addend = t)) = true := by
          by_cases hloc' : sy.bind = .local
          · rw [ite_eq_left hloc'] at hint
            cases hsec : sy.sec with
            | sec sj =>
              rw [hsec] at hint; dsimp only at hint
              cases hdisc : checkDiscardedB objs oi sj with
              | true => rw [hdisc] at hint; exact nomatch hint
              | false =>
                rw [hdisc] at hint; simp only [Bool.not_false, ↓reduceIte] at hint
                exact ⟨oi, sj, sy, (sy.value : Int) + rr.addend,
                  Or.inl ⟨hloc', rfl, rfl, not_discarded_of_check hdisc, rfl, rfl⟩, hint⟩
            | undef => rw [hsec] at hint; exact nomatch hint
            | other => rw [hsec] at hint; exact nomatch hint
          · rw [ite_eq_right hloc'] at hint
            cases hf : findResolves? objs sy.rawName with
            | none => rw [hf] at hint; exact nomatch hint
            | some q =>
              obtain ⟨oj, k, sj, tSym⟩ := q
              rw [hf] at hint; dsimp only at hint
              cases hchk : checkResolvesB objs sy.rawName oj k sj tSym with
              | false => rw [hchk] at hint; exact nomatch hint
              | true =>
                rw [hchk] at hint; simp only [↓reduceIte] at hint
                exact ⟨oj, sj, tSym, (tSym.value : Int) + rr.addend,
                  Or.inr ⟨hloc', k, resolves_of_check hchk, rfl⟩, hint⟩
        obtain ⟨oj, sj, tSym, t, hsrc, hint'⟩ := hres
        cases hoj : objs[oj]? with
        | none => rw [hoj] at hint'; exact nomatch hint'
        | some ojObj =>
          rw [hoj] at hint'; dsimp only at hint'
          cases hsecT : ojObj.sections[sj]? with
          | none => rw [hsecT] at hint'; exact nomatch hint'
          | some secT =>
            rw [hsecT] at hint'; dsimp only at hint'
            refine ⟨oj, sj, ojObj, secT, tSym, t, hsrc, hoj, hsecT, ?_⟩
            cases hexec : secT.isExec with
            | true =>
              rw [hexec] at hint'
              simp only [↓reduceIte] at hint'
              cases hlk : lookupBlockSym r.sym lib.blocks with
              | none => rw [hlk] at hint'; exact nomatch hint'
              | some pair =>
                obtain ⟨bj, off⟩ := pair
                rw [hlk] at hint'; dsimp only at hint'
                cases hbo : bO[bj]? with
                | none => rw [hbo] at hint'; exact nomatch hint'
                | some bo =>
                  rw [hbo] at hint'; dsimp only at hint'
                  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hint'
                  obtain ⟨⟨⟨⟨⟨hbj, hboi⟩, hbsi⟩, hlo⟩, hhi⟩, hteq⟩ := hint'
                  have hbo_eq : bO[bj]'(by omega) = bo := by
                    rw [List.getElem?_eq_getElem (by omega)] at hbo
                    exact Option.some.inj hbo
                  exact Or.inl ⟨rfl, bj, off, rfl, hbj, by simpa [hbo_eq] using hboi,
                    by simpa [hbo_eq] using hbsi, hlo, by simpa [hbo_eq] using hhi,
                    by simpa [hbo_eq] using hteq⟩
            | false =>
              rw [hexec] at hint'
              cases htls : secT.isTls with
              | false =>
                rw [htls] at hint'
                simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_eq_true,
                  Option.isNone_iff_eq_none, List.any_eq_true] at hint'
                obtain ⟨hlk, dj, hdj_mem, hdj_ok⟩ := hint'
                have hdj_lt : dj < lib.data.length := List.mem_range.1 hdj_mem
                rw [List.getElem?_eq_getElem hdj_lt,
                  List.getElem?_eq_getElem (by omega : dj < dO.length)] at hdj_ok
                simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hdj_ok
                exact Or.inr (Or.inl ⟨rfl, rfl, hlk, ⟨dj, hdj_lt⟩, hdj_ok.1.1.1.1.1,
                  hdj_ok.1.1.1.1.2, hdj_ok.1.1.1.2, hdj_ok.1.1.2, hdj_ok.1.2, hdj_ok.2⟩)
              | true =>
                rw [htls] at hint'
                simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.and_eq_true,
                  Option.isNone_iff_eq_none, List.all_eq_true, bne_iff_ne,
                  List.any_eq_true] at hint'
                obtain ⟨⟨hlk, hnodata⟩, ts, hts_mem, hts_ok⟩ := hint'
                simp only [beq_iff_eq, decide_eq_true_eq] at hts_ok
                exact Or.inr (Or.inr ⟨rfl, rfl, hlk, hnodata, ts, hts_mem, hts_ok.1.1.1.1,
                  hts_ok.1.1.1.2, hts_ok.1.1.2, hts_ok.1.2, hts_ok.2⟩)
      · right
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
          Option.isNone_iff_eq_none, List.all_eq_true] at hundef
        obtain ⟨⟨⟨⟨⟨⟨hsec, hraw⟩, hnonempty⟩, hadd⟩, hlk⟩, hnodata⟩, hall⟩ := hundef
        refine ⟨hsec, hraw, hnonempty, hadd, hlk, hnodata, ?_⟩
        intro o' ho' sy' hsy' hraw' hbind'
        have h1 := hall o' ho' sy' hsy'
        split at h1
        · simpa only [beq_iff_eq] using h1
        · rename_i hneg; exact False.elim (hneg ⟨hraw', hbind'⟩)

/-- Greedily match each raw relocation in `raw` to a distinct index in `0 .. rs.length - 1`. -/
def findRelocPermAux (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (bO dO : List SliceOrigin) (oi sliceStart : Nat) (rs : List RelocEntry) :
    List RawReloc → List Nat → Option (List Nat)
  | [], _ => some []
  | rr :: rest, used =>
    match (List.range rs.length).find? fun j =>
        (!used.contains j) &&
        match rs[j]? with
        | some r => checkRelocMatchesB objs lib bO dO oi sliceStart rr r
        | none => false with
    | none => none
    | some j => (findRelocPermAux objs lib bO dO oi sliceStart rs rest (j :: used)).map (j :: ·)

def checkSliceRelocsMatchB (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (bO dO : List SliceOrigin) (o : SliceOrigin) (rs : List RelocEntry) : Bool :=
  match objs[o.oi]? with
  | none => false
  | some obj =>
    match obj.sections[o.si]? with
    | none => false
    | some sec =>
      let raw := sec.relocs.filter fun rr => decide (o.start ≤ rr.off ∧ rr.off < o.start + o.len)
      match findRelocPermAux objs lib bO dO o.oi o.start rs raw [] with
      | none => false
      | some perm =>
        decide (perm.length = raw.length) && decide perm.Nodup && decide (rs.length = raw.length) &&
        (List.range raw.length).all fun k =>
          match raw[k]?, perm[k]? with
          | some rr, some j =>
            match rs[j]? with
            | some r => checkRelocMatchesB objs lib bO dO o.oi o.start rr r
            | none => false
          | _, _ => false

theorem sliceRelocsMatch_of_check {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO dO : List SliceOrigin}
    (hbLen : bO.length = lib.blocks.length) (hdLen : dO.length = lib.data.length)
    {o : SliceOrigin} {rs : List RelocEntry}
    (h : checkSliceRelocsMatchB objs lib bO dO o rs = true) :
    SliceRelocsMatch objs lib (fun i => bO[i.1]'(by omega)) (fun i => dO[i.1]'(by omega)) o rs := by
  unfold checkSliceRelocsMatchB at h
  cases hobj : objs[o.oi]? with
  | none => rw [hobj] at h; exact nomatch h
  | some obj =>
    rw [hobj] at h; dsimp only at h
    cases hsec : obj.sections[o.si]? with
    | none => rw [hsec] at h; exact nomatch h
    | some sec =>
      rw [hsec] at h; dsimp only at h
      let raw := sec.relocs.filter fun rr => decide (o.start ≤ rr.off ∧ rr.off < o.start + o.len)
      cases hp : findRelocPermAux objs lib bO dO o.oi o.start rs raw [] with
      | none => rw [hp] at h; exact nomatch h
      | some perm =>
        rw [hp] at h; dsimp only at h
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
        obtain ⟨⟨⟨hplen, hpnd⟩, hrlen⟩, hall⟩ := h
        refine ⟨obj, sec, hobj, hsec, perm, hplen, hpnd, hrlen, ?_⟩
        intro k hk hp_lt
        have hk_ok := hall k (List.mem_range.2 hk)
        rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hp_lt] at hk_ok
        dsimp only at hk_ok
        cases hrj : rs[perm[k]]? with
        | none => rw [hrj] at hk_ok; exact nomatch hk_ok
        | some r =>
          rw [hrj] at hk_ok; dsimp only at hk_ok
          have hj_lt : perm[k] < rs.length := (List.getElem?_eq_some_iff.1 hrj).1
          have hr_eq : rs[perm[k]]'hj_lt = r := by
            rw [List.getElem?_eq_getElem hj_lt] at hrj
            exact Option.some.inj hrj
          exact ⟨hj_lt, hr_eq ▸ relocMatches_of_check hbLen hdLen hk_ok⟩

def checkWeakOnlyUndefB (objs : List ExtractedObj) (x : String) : Bool :=
  (objs.any fun o =>
    o.symbols.any fun sy =>
      (sy.sec == .undef) && (sy.rawName == x) && (sy.bind == .weak)) &&
  objs.all fun o =>
    o.symbols.all fun sy =>
      if sy.rawName == x then
        (if sy.sec == .undef then sy.bind == .weak else true) &&
        (if sy.bind != .local then sy.sec == .undef else true) &&
        match sy.sec with
        | .sec _ => false
        | _ => true
      else true

theorem weakOnlyUndef_of_check {objs : List ExtractedObj} {x : String}
    (h : checkWeakOnlyUndefB objs x = true) :
    WeakOnlyUndef objs x := by
  unfold checkWeakOnlyUndefB at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨o0, ho0, sy0, hsy0, h0⟩, hall⟩ := h
  simp only [beq_iff_eq] at h0
  refine ⟨⟨o0, ho0, sy0, hsy0, h0.1.1, h0.1.2, h0.2⟩, ?_⟩
  intro o ho sy hsy hraw
  have hs := hall o ho sy hsy
  simp only [hraw, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at hs
  refine ⟨?_, ?_, ?_⟩
  · intro hu
    have h1 := hs.1.1
    rw [hu] at h1
    simpa using h1
  · intro hb
    have h2 := hs.1.2
    have hbf : (sy.bind != .local) = true := bne_iff_ne.2 hb
    rw [hbf] at h2
    simpa using h2
  · intro si hsec
    have h3 := hs.2
    rw [hsec] at h3
    exact nomatch h3

def checkExportsValidB (objs : List ExtractedObj) (lib : MultiPlacedLib) (bO : List SliceOrigin) :
    Bool :=
  lib.exports.all fun e =>
    match lookupBlockSym e lib.blocks with
    | none => false
    | some (bi, off) =>
      decide (bi < lib.blocks.length) &&
      match bO[bi]? with
      | none => false
      | some bo =>
        match objs[bo.oi]? with
        | none => false
        | some o =>
          (List.range o.symbols.length).any fun k =>
            match o.symbols[k]? with
            | none => false
            | some sy =>
              checkResolvesB objs (lib.elfSym e) bo.oi k bo.si sy &&
              (sy.kind == .func) && (sy.name == e) && (sy.value == bo.start + off)

def checkExternsValidB (objs : List ExtractedObj) (lib : MultiPlacedLib) : Bool :=
  lib.blocks.all fun b =>
    (b.relocs.all fun r =>
      if (r.kind == .call26) || (r.kind == .jump26) then
        if (lookupBlockSym r.sym lib.blocks).isNone then b.externs.contains r.sym
        else true
      else true) &&
    (b.externs.all fun x =>
      (lookupBlockSym x lib.blocks).isNone &&
      (lib.data.all fun d => d.sym != x) &&
      (lib.blocks.any fun b' =>
        b'.relocs.any fun r =>
          ((r.kind == .call26) || (r.kind == .jump26)) && (r.sym == x))) &&
    (b.weakRefs.all fun w =>
      b.externs.contains w && checkWeakOnlyUndefB objs w)

/-- Direct decidable check for `LabelsFromObjects objs lib bO dO`. -/
def checkLabelsFromObjectsB (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (bO dO : List SliceOrigin) : Bool :=
  decide (bO.length = lib.blocks.length) &&
  decide (dO.length = lib.data.length) &&
  ((List.range lib.blocks.length).all fun i =>
    match lib.blocks[i]?, bO[i]? with
    | some b, some o => checkValidTextSliceB objs b o
    | _, _ => false) &&
  ((List.range lib.data.length).all fun i =>
    match lib.data[i]?, dO[i]? with
    | some d, some o => checkValidDataSliceB objs d o
    | _, _ => false) &&
  checkOriginsDisjointB bO &&
  checkOriginsDisjointB dO &&
  decide (((lib.blocks.flatMap (·.symbols)).map (·.1)).Nodup) &&
  decide ((lib.data.map (·.sym)).Nodup) &&
  (lib.data.all fun d => (lookupBlockSym d.sym lib.blocks).isNone) &&
  ((List.range lib.blocks.length).all fun i =>
    match lib.blocks[i]?, bO[i]? with
    | some b, some o => checkSliceRelocsMatchB objs lib bO dO o b.relocs
    | _, _ => false) &&
  ((List.range lib.data.length).all fun i =>
    match lib.data[i]?, dO[i]? with
    | some d, some o => checkSliceRelocsMatchB objs lib bO dO o d.relocs
    | _, _ => false) &&
  checkExportsValidB objs lib bO &&
  checkExternsValidB objs lib

theorem checkLabelsFromObjectsB_bO_len {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO dO : List SliceOrigin}
    (h : checkLabelsFromObjectsB objs lib bO dO = true) :
    bO.length = lib.blocks.length := by
  unfold checkLabelsFromObjectsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1

theorem checkLabelsFromObjectsB_dO_len {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO dO : List SliceOrigin}
    (h : checkLabelsFromObjectsB objs lib bO dO = true) :
    dO.length = lib.data.length := by
  unfold checkLabelsFromObjectsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.2

/-- Soundness of `checkLabelsFromObjectsB`: a `true` check certifies `LabelsFromObjects`. -/
theorem labelsFromObjects_of_check {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO dO : List SliceOrigin}
    (h : checkLabelsFromObjectsB objs lib bO dO = true) :
    LabelsFromObjects objs lib
      (fun i => bO[i.1]'(Nat.lt_of_lt_of_eq i.2 (checkLabelsFromObjectsB_bO_len h).symm))
      (fun i => dO[i.1]'(Nat.lt_of_lt_of_eq i.2 (checkLabelsFromObjectsB_dO_len h).symm)) := by
  have hbLen := checkLabelsFromObjectsB_bO_len h
  have hdLen := checkLabelsFromObjectsB_dO_len h
  unfold checkLabelsFromObjectsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hbVal⟩, hdVal⟩, hbDisj⟩, hdDisj⟩, hsymNd⟩, hdatNd⟩, hdatNone⟩,
    hbRel⟩, hdRel⟩, hexp⟩, hext⟩ := h
  refine
    { blocks_valid := ?_
      data_valid := ?_
      blocks_disjoint := originsDisjoint_of_check hbLen hbDisj
      data_disjoint := originsDisjoint_of_check hdLen hdDisj
      names_nodup := ⟨hsymNd, hdatNd, ?_⟩
      block_relocs := ?_
      data_relocs := ?_
      exports_valid := ?_
      externs_valid := ?_ }
  · intro i
    rw [List.all_eq_true] at hbVal
    have hi := hbVal i.1 (List.mem_range.2 i.2)
    rw [List.getElem?_eq_getElem i.2, List.getElem?_eq_getElem (by omega : i.1 < bO.length)] at hi
    exact validTextSlice_of_check hi
  · intro i
    rw [List.all_eq_true] at hdVal
    have hi := hdVal i.1 (List.mem_range.2 i.2)
    rw [List.getElem?_eq_getElem i.2, List.getElem?_eq_getElem (by omega : i.1 < dO.length)] at hi
    exact validDataSlice_of_check hi
  · intro d hd
    rw [List.all_eq_true] at hdatNone
    exact Option.isNone_iff_eq_none.1 (hdatNone d hd)
  · intro i
    rw [List.all_eq_true] at hbRel
    have hi := hbRel i.1 (List.mem_range.2 i.2)
    rw [List.getElem?_eq_getElem i.2, List.getElem?_eq_getElem (by omega : i.1 < bO.length)] at hi
    exact sliceRelocsMatch_of_check hbLen hdLen hi
  · intro i
    rw [List.all_eq_true] at hdRel
    have hi := hdRel i.1 (List.mem_range.2 i.2)
    rw [List.getElem?_eq_getElem i.2, List.getElem?_eq_getElem (by omega : i.1 < dO.length)] at hi
    exact sliceRelocsMatch_of_check hbLen hdLen hi
  · intro e he
    unfold checkExportsValidB at hexp
    rw [List.all_eq_true] at hexp
    have he_ok := hexp e he
    cases hlk : lookupBlockSym e lib.blocks with
    | none => rw [hlk] at he_ok; exact nomatch he_ok
    | some pair =>
      obtain ⟨bi, off⟩ := pair
      rw [hlk] at he_ok; dsimp only at he_ok
      rw [Bool.and_eq_true, decide_eq_true_eq] at he_ok
      obtain ⟨hbi, he_rest⟩ := he_ok
      rw [List.getElem?_eq_getElem (by omega : bi < bO.length)] at he_rest
      dsimp only at he_rest
      cases hbo : objs[(bO[bi]'(by omega)).oi]? with
      | none => rw [hbo] at he_rest; exact nomatch he_rest
      | some o =>
        rw [hbo] at he_rest; dsimp only at he_rest
        rw [List.any_eq_true] at he_rest
        obtain ⟨k, hk_mem, hk_ok⟩ := he_rest
        have hk_lt : k < o.symbols.length := List.mem_range.1 hk_mem
        rw [List.getElem?_eq_getElem hk_lt] at hk_ok
        dsimp only at hk_ok
        simp only [Bool.and_eq_true, beq_iff_eq] at hk_ok
        exact ⟨bi, off, rfl, hbi, k, o.symbols[k], resolves_of_check hk_ok.1.1.1,
          hk_ok.1.1.2, hk_ok.1.2, hk_ok.2⟩
  · intro b hb
    unfold checkExternsValidB at hext
    rw [List.all_eq_true] at hext
    have hb_ok := hext b hb
    simp only [Bool.and_eq_true, List.all_eq_true] at hb_ok
    obtain ⟨⟨hrel_ext, hext_mem⟩, hweak⟩ := hb_ok
    refine ⟨?_, ?_, ?_⟩
    · intro r hr hkind hnone
      have h1 := hrel_ext r hr
      have hk : ((r.kind == .call26) || (r.kind == .jump26)) = true := by
        rcases hkind with h | h <;> simp [h]
      have hn : (lookupBlockSym r.sym lib.blocks).isNone = true :=
        Option.isNone_iff_eq_none.2 hnone
      simp only [hk, hn, ↓reduceIte] at h1
      exact List.contains_iff_mem.1 h1
    · intro x hx
      have h2 := hext_mem x hx
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne,
        List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨hlk, hnod⟩, b', hb', r, hr, hkind, hsym⟩ := h2
      exact ⟨hlk, hnod, b', hb', r, hr, hkind, hsym⟩
    · intro w hw
      have h3 := hweak w hw
      exact ⟨List.contains_iff_mem.1 h3.1, weakOnlyUndef_of_check h3.2⟩

theorem exists_labelsFromObjects_of_check {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {bO dO : List SliceOrigin}
    (h : checkLabelsFromObjectsB objs lib bO dO = true) :
    ∃ bO' dO', LabelsFromObjects objs lib bO' dO' :=
  ⟨_, _, labelsFromObjects_of_check h⟩

end Arm64.Obj
