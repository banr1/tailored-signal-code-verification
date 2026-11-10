/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliLabels
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfo
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage

@[expose] public section

set_option autoImplicit false

/-!
# SPQR CPU-Probe Data Label Anchoring (`CliProbeLabelsAnchored`)

**Checked by Lean.** Certifies `CliProbeLabelsAnchored` via `CoveredDataSpec` witnesses
(`tokenStorageSpec`, `tokenSpec`) for SPQR's `STORAGE.0` and `TOKEN` statics, and derives the
symbol-resolution (`libsignalSessionLib.resolve = mpl.ρ`) and relocation-provenance lemmas consumed
by `cliTokenPatchPlaced`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProbeLabels

open Arm64
open CryptoVerification.LibsignalSpqrV1 (tokenStorageName tokenName)
open CryptoVerification.SignalSession (
  cliLinkObjs libsignalSessionLib CliProbeLabelsAnchored
)
open CryptoVerification.SignalSession.Placed (cliTokenPatchPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfo (
  cliLabelsLfo_dOTree cliLabelsLfo_bO cliLabelsLfo_dO cliLabelsLfo_spec
)

/-- `CoveredDataSpec` for `spqr::encoding::gf::check_accelerated::use_accelerated::STORAGE.0`
(1-byte `AtomicU8` at `libsignalSessionLib.data[818]`, sharing section `(oi := 6, si := 650)` with
`TOKEN`). -/
def tokenStorageSpec : Obj.CoveredDataSpec :=
  { di := 818
    sym := tokenStorageName
    origin := { oi := 6, si := 650, start := 0, len := 1 }
    rawName :=
      "_RNvNtNtNtNtCs8JFVmrO4JRH_4spqr8encoding2gf17check_accelerated15use_accelerated7STORAGE.0"
    demangledName := tokenStorageName
    expectedReadOnly := some false
    expectedZeroTail := some 0
    soleInSection := false }

/-- `CoveredDataSpec` for `spqr::encoding::gf::check_accelerated::TOKEN` (16-byte
`LazyLock<InitToken>` at `libsignalSessionLib.data[819]`, sharing section `(oi := 6, si := 650)`
with `STORAGE.0`). -/
def tokenSpec : Obj.CoveredDataSpec :=
  { di := 819
    sym := tokenName
    origin := { oi := 6, si := 650, start := 8, len := 16 }
    rawName :=
      "_RNvNtNtNtCs8JFVmrO4JRH_4spqr8encoding2gf17check_accelerated5TOKEN"
    demangledName := tokenName
    expectedReadOnly := some false
    expectedZeroTail := some 0
    soleInSection := false }

/-- Boolean checker anchoring both SPQR CPU-probe statics (`tokenStorageName`, `tokenName`) against
`cliLinkObjs` and `libsignalSessionLib` at slice-origin map `dO`. -/
def checkCliProbeLabelsB (dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin) : Bool :=
  Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib dO tokenStorageSpec &&
    Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib dO tokenSpec

/-- Projects `Obj.DataLabelAnchored` to the `.o` `STT_OBJECT` witness required by
`CliProbeLabelsAnchored` when `spec.sym = n` and `spec.demangledName = n`. -/
theorem dataLabelAnchored_probe_witness
    {objs : List Obj.ExtractedObj} {lib : Obj.MultiPlacedLib}
    {dO : Fin lib.data.length → Obj.SliceOrigin} {spec : Obj.CoveredDataSpec} {n : String}
    (hd : Obj.DataLabelAnchored objs lib dO spec)
    (hsym : spec.sym = n)
    (hdem : spec.demangledName = n) :
    ∃ dj : Fin lib.data.length, lib.data[dj].sym = n ∧
      ∃ obj, objs[(dO dj).oi]? = some obj ∧ ∃ sy ∈ obj.symbols,
        Obj.CoversDataSlice (dO dj) sy ∧ sy.name = n := by
  refine ⟨⟨spec.di, hd.in_bounds⟩, by simpa using hd.sym_eq.trans hsym, ?_⟩
  obtain ⟨obj, _sec, sy, hobj, _hsec, hsy_mem, hcov, _hraw, hsy_name, _hder, _hro⟩ :=
    hd.obj_witness
  have horig : dO ⟨spec.di, hd.in_bounds⟩ = spec.origin := hd.origin_eq
  rw [horig]
  exact ⟨obj, hobj, sy, hsy_mem, hcov, hsy_name.trans hdem⟩

/-- Any slice-origin map `dO` satisfying `checkCliProbeLabelsB dO = true` satisfies
`CliProbeLabelsAnchored dO`. -/
theorem cliProbeLabelsAnchored_of_check
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (h : checkCliProbeLabelsB dO = true) :
    CliProbeLabelsAnchored dO := by
  unfold checkCliProbeLabelsB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hs, ht⟩ := h
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact dataLabelAnchored_probe_witness (Obj.dataLabelAnchored_of_check hs) rfl rfl
  · exact dataLabelAnchored_probe_witness (Obj.dataLabelAnchored_of_check ht) rfl rfl

/-- When `spec.soleInSection = false`, `Obj.checkCoveredDataSpecB` depends on `dO` only at
`spec.di`. -/
theorem checkCoveredDataSpecB_congr_of_sole_false
    {objs : List Obj.ExtractedObj} {lib : Obj.MultiPlacedLib}
    {dO₁ dO₂ : Fin lib.data.length → Obj.SliceOrigin} {spec : Obj.CoveredDataSpec}
    (hsole : spec.soleInSection = false)
    (heq : ∀ hdi : spec.di < lib.data.length, dO₁ ⟨spec.di, hdi⟩ = dO₂ ⟨spec.di, hdi⟩) :
    Obj.checkCoveredDataSpecB objs lib dO₁ spec =
      Obj.checkCoveredDataSpecB objs lib dO₂ spec := by
  unfold Obj.checkCoveredDataSpecB
  split
  case isFalse => rfl
  case isTrue hdi =>
    simp only [hsole, Bool.false_eq_true, ↓reduceIte, heq hdi]

/-- Standalone slice-origin map matching `tokenStorageSpec.origin` at `818` and `tokenSpec.origin`
at `819`. -/
def probePreviewDO (dj : Fin libsignalSessionLib.data.length) : Obj.SliceOrigin :=
  if dj.val == 818 then tokenStorageSpec.origin else tokenSpec.origin

theorem checkCliProbeLabelsB_preview : checkCliProbeLabelsB probePreviewDO = true := by
  decide +kernel

/-- Transfers `checkCliProbeLabelsB` from `probePreviewDO` to any `dO` agreeing at indices `818`
and `819` without re-evaluating `cliLinkObjs`. -/
theorem checkCliProbeLabelsB_of_origins
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hs : ∀ hdi : 818 < libsignalSessionLib.data.length,
      dO ⟨818, hdi⟩ = tokenStorageSpec.origin)
    (ht : ∀ hdi : 819 < libsignalSessionLib.data.length,
      dO ⟨819, hdi⟩ = tokenSpec.origin) :
    checkCliProbeLabelsB dO = true := by
  have h1 : Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib dO tokenStorageSpec =
      Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib probePreviewDO tokenStorageSpec :=
    checkCoveredDataSpecB_congr_of_sole_false rfl fun hdi => hs hdi
  have h2 : Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib dO tokenSpec =
      Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib probePreviewDO tokenSpec :=
    checkCoveredDataSpecB_congr_of_sole_false rfl fun hdi => ht hdi
  unfold checkCliProbeLabelsB
  rw [h1, h2]
  exact checkCliProbeLabelsB_preview

theorem cliProbeLabelsAnchored_of_origins
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hs : ∀ hdi : 818 < libsignalSessionLib.data.length,
      dO ⟨818, hdi⟩ = tokenStorageSpec.origin)
    (ht : ∀ hdi : 819 < libsignalSessionLib.data.length,
      dO ⟨819, hdi⟩ = tokenSpec.origin) :
    CliProbeLabelsAnchored dO :=
  cliProbeLabelsAnchored_of_check (checkCliProbeLabelsB_of_origins hs ht)

theorem resolve_tokenStorage_eq_rho_of_check
    {bO : Fin libsignalSessionLib.blocks.length → Obj.SliceOrigin}
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO)
    (hchk : checkCliProbeLabelsB dO = true)
    (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl tokenStorageName = mpl.ρ tokenStorageName := by
  unfold checkCliProbeLabelsB at hchk
  rw [Bool.and_eq_true] at hchk
  exact (Obj.dataLabelAnchored_of_check hchk.1).resolve_eq_rho hlfo mpl

theorem resolve_token_eq_rho_of_check
    {bO : Fin libsignalSessionLib.blocks.length → Obj.SliceOrigin}
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO)
    (hchk : checkCliProbeLabelsB dO = true)
    (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl tokenName = mpl.ρ tokenName := by
  unfold checkCliProbeLabelsB at hchk
  rw [Bool.and_eq_true] at hchk
  exact (Obj.dataLabelAnchored_of_check hchk.2).resolve_eq_rho hlfo mpl

/-- Rewrites `Placed.cliTokenPatchPlaced` write addresses from `mpl.ρ` to
`libsignalSessionLib.resolve` under `Obj.LabelsFromObjects` and `checkCliProbeLabelsB`. -/
theorem cliTokenPatchPlaced_eq_resolve_of_check
    {bO : Fin libsignalSessionLib.blocks.length → Obj.SliceOrigin}
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO)
    (hchk : checkCliProbeLabelsB dO = true)
    (mpl : Obj.MultiPlacement) (s : State) :
    cliTokenPatchPlaced mpl s =
      s.setMem
        ((s.mem.writeBytes (libsignalSessionLib.resolve mpl tokenStorageName) [0#8]).writeBytes
          (libsignalSessionLib.resolve mpl tokenName + 8#64) [0#8, 0#8, 0#8, 0#8]) := by
  unfold cliTokenPatchPlaced
  rw [resolve_tokenStorage_eq_rho_of_check hlfo hchk mpl,
      resolve_token_eq_rho_of_check hlfo hchk mpl]

theorem resolve_tokenStorage_eq_rho_of_anchored
    {bO : Fin libsignalSessionLib.blocks.length → Obj.SliceOrigin}
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO)
    (hprobe : CliProbeLabelsAnchored dO)
    (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl tokenStorageName = mpl.ρ tokenStorageName := by
  obtain ⟨djs, hdjs_sym, _⟩ := hprobe tokenStorageName (by simp)
  rw [← hdjs_sym]
  exact hlfo.resolve_data_eq_rho mpl (List.getElem_mem djs.isLt)

theorem resolve_token_eq_rho_of_anchored
    {bO : Fin libsignalSessionLib.blocks.length → Obj.SliceOrigin}
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO)
    (hprobe : CliProbeLabelsAnchored dO)
    (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl tokenName = mpl.ρ tokenName := by
  obtain ⟨djt, hdjt_sym, _⟩ := hprobe tokenName (by simp)
  rw [← hdjt_sym]
  exact hlfo.resolve_data_eq_rho mpl (List.getElem_mem djt.isLt)

/-- Rewrites `Placed.cliTokenPatchPlaced` write addresses from `mpl.ρ` to
`libsignalSessionLib.resolve` under `Obj.LabelsFromObjects` and `CliProbeLabelsAnchored`. -/
theorem cliTokenPatchPlaced_eq_resolve_of_anchored
    {bO : Fin libsignalSessionLib.blocks.length → Obj.SliceOrigin}
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO)
    (hprobe : CliProbeLabelsAnchored dO)
    (mpl : Obj.MultiPlacement) (s : State) :
    cliTokenPatchPlaced mpl s =
      s.setMem
        ((s.mem.writeBytes (libsignalSessionLib.resolve mpl tokenStorageName) [0#8]).writeBytes
          (libsignalSessionLib.resolve mpl tokenName + 8#64) [0#8, 0#8, 0#8, 0#8]) := by
  unfold cliTokenPatchPlaced
  rw [resolve_tokenStorage_eq_rho_of_anchored hlfo hprobe mpl,
      resolve_token_eq_rho_of_anchored hlfo hprobe mpl]

theorem validDataSlice_len_eq
    {objs : List Obj.ExtractedObj} {d : Obj.SymDataInfo} {o : Obj.SliceOrigin}
    (hv : Obj.ValidDataSlice objs d o) :
    o.len = d.bytes.length + d.zeroTail := by
  obtain ⟨_obj, sec, _hobj, _hsec, _hnd, _hnoExec, _hnoTls, hbound, _hro, hbytes, _⟩ := hv
  split at hbytes
  · obtain ⟨hb, hz⟩ := hbytes
    simp [hb, hz]
  · obtain ⟨hlen, hb, hz⟩ := hbytes
    rw [hb, hz, List.length_take, List.length_drop, hlen]
    omega

/-- Under `Obj.LabelsFromObjects`, a raw code relocation targeting a strictly interior offset
`(dO di).start < t < (dO di).start + (dO di).len` resolves uniquely to a `RelocEntry` in
`lib.blocks[bi].relocs` with `.sym = lib.data[di].sym` and `(dO di).start + r.addend = t`. -/
theorem interior_data_reloc_sym_eq
    {objs : List Obj.ExtractedObj} {lib : Obj.MultiPlacedLib}
    {bO : Fin lib.blocks.length → Obj.SliceOrigin}
    {dO : Fin lib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects objs lib bO dO)
    (bi : Fin lib.blocks.length) (di : Fin lib.data.length)
    {bObj dObj : Obj.ExtractedObj} {bSec dSec : Obj.RawSec}
    {rr : Obj.RawReloc} {sy : Obj.RawSym}
    (hbobj : objs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hdobj : objs[(dO di).oi]? = some dObj)
    (hdsec : dObj.sections[(dO di).si]? = some dSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    {t : Int}
    (ht_lo : ((dO di).start : Int) < t)
    (ht_hi : t < (((dO di).start + (dO di).len : Nat) : Int))
    (htarget :
      ((bO bi).oi = (dO di).oi ∧ sy.bind = .local ∧ sy.sec = .sec (dO di).si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves objs sy.rawName (dO di).oi k (dO di).si tSym ∧
        t = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ lib.blocks[bi].relocs,
      r.off + (bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = lib.data[di].sym ∧ ((dO di).start : Int) + r.addend = t := by
  refine hlfo.data_reloc_sym_eq bi di hbobj hbsec hdobj hdsec hrr hlo hhi hsy htarget ?_
  intro dj hdj hdoi hdsi
  have hdisj := hlfo.data_disjoint dj di hdj hdoi hdsi
  unfold Obj.RangesDisjoint at hdisj
  omega

/-- Relocation provenance at section offset `0` (`(dO di).start = 0`, `0 ≤ t < (dO di).len`) when
no other slice in `(oi, si)` has zero length at offset `0`. -/
theorem zero_start_data_reloc_sym_eq
    {objs : List Obj.ExtractedObj} {lib : Obj.MultiPlacedLib}
    {bO : Fin lib.blocks.length → Obj.SliceOrigin}
    {dO : Fin lib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects objs lib bO dO)
    (bi : Fin lib.blocks.length) (di : Fin lib.data.length)
    {bObj dObj : Obj.ExtractedObj} {bSec dSec : Obj.RawSec}
    {rr : Obj.RawReloc} {sy : Obj.RawSym}
    (hbobj : objs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hdobj : objs[(dO di).oi]? = some dObj)
    (hdsec : dObj.sections[(dO di).si]? = some dSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    (hstart0 : (dO di).start = 0)
    {t : Int}
    (ht_hi : t < ((dO di).len : Int))
    (hlen : ∀ dj : Fin lib.data.length, dj ≠ di →
      (dO dj).oi = (dO di).oi → (dO dj).si = (dO di).si → (dO dj).start = 0 → 0 < (dO dj).len)
    (htarget :
      ((bO bi).oi = (dO di).oi ∧ sy.bind = .local ∧ sy.sec = .sec (dO di).si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves objs sy.rawName (dO di).oi k (dO di).si tSym ∧
        t = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ lib.blocks[bi].relocs,
      r.off + (bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = lib.data[di].sym ∧ ((dO di).start : Int) + r.addend = t := by
  refine hlfo.data_reloc_sym_eq bi di hbobj hbsec hdobj hdsec hrr hlo hhi hsy htarget ?_
  intro dj hdj hdoi hdsi
  have hdisj := hlfo.data_disjoint dj di hdj hdoi hdsi
  unfold Obj.RangesDisjoint at hdisj
  rcases hdisj with hle | hge
  · exfalso
    have hdj0 : (dO dj).start = 0 := by omega
    have hpos := hlen dj hdj hdoi hdsi hdj0
    omega
  · left
    omega

/-- Relocation provenance for an `Obj.DataLabelAnchored` slice at a strictly interior offset
`spec.origin.start < t < spec.origin.start + spec.origin.len`. -/
theorem anchored_interior_reloc_sym_eq
    {objs : List Obj.ExtractedObj} {lib : Obj.MultiPlacedLib}
    {bO : Fin lib.blocks.length → Obj.SliceOrigin}
    {dO : Fin lib.data.length → Obj.SliceOrigin}
    {spec : Obj.CoveredDataSpec}
    (hlfo : Obj.LabelsFromObjects objs lib bO dO)
    (hd : Obj.DataLabelAnchored objs lib dO spec)
    (bi : Fin lib.blocks.length)
    {bObj : Obj.ExtractedObj} {bSec : Obj.RawSec} {rr : Obj.RawReloc} {sy : Obj.RawSym}
    (hbobj : objs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    {t add : Int}
    (ht_lo : (spec.origin.start : Int) < t)
    (ht_hi : t < ((spec.origin.start + spec.origin.len : Nat) : Int))
    (hadd_spec : (spec.origin.start : Int) + add = t)
    (htarget :
      ((bO bi).oi = spec.origin.oi ∧ sy.bind = .local ∧ sy.sec = .sec spec.origin.si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves objs sy.rawName spec.origin.oi k spec.origin.si tSym ∧
        t = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ lib.blocks[bi].relocs,
      r.off + (bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = spec.sym ∧ r.addend = add := by
  let di : Fin lib.data.length := ⟨spec.di, hd.in_bounds⟩
  have horig : dO di = spec.origin := hd.origin_eq
  obtain ⟨dObj, dSec, _syT, hdobj0, hdsec0, _⟩ := hd.obj_witness
  have hdobj : objs[(dO di).oi]? = some dObj := by rw [horig]; exact hdobj0
  have hdsec : dObj.sections[(dO di).si]? = some dSec := by rw [horig]; exact hdsec0
  have ht_lo' : ((dO di).start : Int) < t := by rw [horig]; exact ht_lo
  have ht_hi' : t < (((dO di).start + (dO di).len : Nat) : Int) := by rw [horig]; exact ht_hi
  have htarget' :
      ((bO bi).oi = (dO di).oi ∧ sy.bind = .local ∧ sy.sec = .sec (dO di).si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves objs sy.rawName (dO di).oi k (dO di).si tSym ∧
        t = (tSym.value : Int) + rr.addend) := by
    rw [horig]; exact htarget
  obtain ⟨r, hr_mem, hoff, hkind, hsym, hadd⟩ :=
    interior_data_reloc_sym_eq hlfo bi di hbobj hbsec hdobj hdsec hrr hlo hhi hsy ht_lo' ht_hi' htarget'
  have hdsym : lib.data[di].sym = spec.sym := hd.sym_eq
  have hadd_eq : r.addend = add := by
    rw [horig] at hadd
    omega
  exact ⟨r, hr_mem, hoff, hkind, hsym.trans hdsym, hadd_eq⟩

/-- Relocation provenance for an `Obj.DataLabelAnchored` slice starting at section offset `0`. -/
theorem anchored_zero_start_reloc_sym_eq
    {objs : List Obj.ExtractedObj} {lib : Obj.MultiPlacedLib}
    {bO : Fin lib.blocks.length → Obj.SliceOrigin}
    {dO : Fin lib.data.length → Obj.SliceOrigin}
    {spec : Obj.CoveredDataSpec}
    (hlfo : Obj.LabelsFromObjects objs lib bO dO)
    (hd : Obj.DataLabelAnchored objs lib dO spec)
    (bi : Fin lib.blocks.length)
    {bObj : Obj.ExtractedObj} {bSec : Obj.RawSec} {rr : Obj.RawReloc} {sy : Obj.RawSym}
    (hbobj : objs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    (hlen : ∀ dj : Fin lib.data.length,
      (dO dj).oi = spec.origin.oi → (dO dj).si = spec.origin.si → (dO dj).start = 0 →
        0 < (dO dj).len)
    (hstart0 : spec.origin.start = 0)
    {t : Int}
    (ht_hi : t < (spec.origin.len : Int))
    (htarget :
      ((bO bi).oi = spec.origin.oi ∧ sy.bind = .local ∧ sy.sec = .sec spec.origin.si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves objs sy.rawName spec.origin.oi k spec.origin.si tSym ∧
        t = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ lib.blocks[bi].relocs,
      r.off + (bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = spec.sym ∧ r.addend = t := by
  let di : Fin lib.data.length := ⟨spec.di, hd.in_bounds⟩
  have horig : dO di = spec.origin := hd.origin_eq
  obtain ⟨dObj, dSec, _syT, hdobj0, hdsec0, _⟩ := hd.obj_witness
  have hdobj : objs[(dO di).oi]? = some dObj := by rw [horig]; exact hdobj0
  have hdsec : dObj.sections[(dO di).si]? = some dSec := by rw [horig]; exact hdsec0
  have hstart0' : (dO di).start = 0 := by rw [horig]; exact hstart0
  have ht_hi' : t < ((dO di).len : Int) := by rw [horig]; exact ht_hi
  have hlen' : ∀ dj : Fin lib.data.length, dj ≠ di →
      (dO dj).oi = (dO di).oi → (dO dj).si = (dO di).si → (dO dj).start = 0 → 0 < (dO dj).len := by
    intro dj _ hdoi hdsi hdj0
    rw [horig] at hdoi hdsi
    exact hlen dj hdoi hdsi hdj0
  have htarget' :
      ((bO bi).oi = (dO di).oi ∧ sy.bind = .local ∧ sy.sec = .sec (dO di).si ∧
        t = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves objs sy.rawName (dO di).oi k (dO di).si tSym ∧
        t = (tSym.value : Int) + rr.addend) := by
    rw [horig]; exact htarget
  obtain ⟨r, hr_mem, hoff, hkind, hsym, hadd⟩ :=
    zero_start_data_reloc_sym_eq hlfo bi di hbobj hbsec hdobj hdsec hrr hlo hhi hsy
      hstart0' ht_hi' hlen' htarget'
  have hdsym : lib.data[di].sym = spec.sym := hd.sym_eq
  have hadd_eq : r.addend = t := by
    rw [hstart0'] at hadd
    omega
  exact ⟨r, hr_mem, hoff, hkind, hsym.trans hdsym, hadd_eq⟩

private theorem token_off16_lo : (tokenSpec.origin.start : Int) < 16 := by decide
private theorem token_off16_hi :
    (16 : Int) < ((tokenSpec.origin.start + tokenSpec.origin.len : Nat) : Int) := by decide

/-- Specialization of `anchored_interior_reloc_sym_eq` to SPQR's `TOKEN` `futex::Once` state word
(`offset 16 = start 8 + addend 8` in `(oi := 6, si := 650)`). -/
theorem tokenOnce_reloc_sym_eq_of_check
    {bO : Fin libsignalSessionLib.blocks.length → Obj.SliceOrigin}
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO)
    (hchk : checkCliProbeLabelsB dO = true)
    (bi : Fin libsignalSessionLib.blocks.length)
    {bObj : Obj.ExtractedObj} {bSec : Obj.RawSec} {rr : Obj.RawReloc} {sy : Obj.RawSym}
    (hbobj : cliLinkObjs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    (htarget :
      ((bO bi).oi = 6 ∧ sy.bind = .local ∧ sy.sec = .sec 650 ∧
        (16 : Int) = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves cliLinkObjs sy.rawName 6 k 650 tSym ∧
        (16 : Int) = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ libsignalSessionLib.blocks[bi].relocs,
      r.off + (bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = tokenName ∧ r.addend = 8 :=
  anchored_interior_reloc_sym_eq hlfo
    (Obj.dataLabelAnchored_of_check (Eq.mp (Bool.and_eq_true _ _) hchk).2)
    bi hbobj hbsec hrr hlo hhi hsy token_off16_lo token_off16_hi rfl htarget

private theorem tokenStorage_len_pos : (0 : Int) < (tokenStorageSpec.origin.len : Int) := by decide

/-- Specialization of `anchored_zero_start_reloc_sym_eq` to SPQR's `STORAGE.0` byte at offset `0`
in `(oi := 6, si := 650)`. -/
theorem tokenStorage_reloc_sym_eq_of_check
    {bO : Fin libsignalSessionLib.blocks.length → Obj.SliceOrigin}
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hlfo : Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO)
    (hchk : checkCliProbeLabelsB dO = true)
    (bi : Fin libsignalSessionLib.blocks.length)
    {bObj : Obj.ExtractedObj} {bSec : Obj.RawSec} {rr : Obj.RawReloc} {sy : Obj.RawSym}
    (hbobj : cliLinkObjs[(bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(bO bi).si]? = some bSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (bO bi).start ≤ rr.off) (hhi : rr.off < (bO bi).start + (bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    (hlen : ∀ dj : Fin libsignalSessionLib.data.length,
      (dO dj).oi = 6 → (dO dj).si = 650 → (dO dj).start = 0 → 0 < (dO dj).len)
    (htarget :
      ((bO bi).oi = 6 ∧ sy.bind = .local ∧ sy.sec = .sec 650 ∧
        (0 : Int) = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves cliLinkObjs sy.rawName 6 k 650 tSym ∧
        (0 : Int) = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ libsignalSessionLib.blocks[bi].relocs,
      r.off + (bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = tokenStorageName ∧ r.addend = 0 :=
  anchored_zero_start_reloc_sym_eq hlfo
    (Obj.dataLabelAnchored_of_check (Eq.mp (Bool.and_eq_true _ _) hchk).1)
    bi hbobj hbsec hrr hlo hhi hsy hlen rfl tokenStorage_len_pos htarget

/-! ## Instantiation at `cliLabelsLfo_dO` -/

private theorem cliLabelsLfo_dOTree_818 :
    (cliLabelsLfo_dOTree.get? 818).getD { oi := 0, si := 0, start := 0, len := 0 } =
      tokenStorageSpec.origin :=
  rfl

private theorem cliLabelsLfo_dOTree_819 :
    (cliLabelsLfo_dOTree.get? 819).getD { oi := 0, si := 0, start := 0, len := 0 } =
      tokenSpec.origin :=
  rfl

theorem cliLabelsLfo_dO_818 (hdi : 818 < libsignalSessionLib.data.length) :
    cliLabelsLfo_dO ⟨818, hdi⟩ = tokenStorageSpec.origin :=
  cliLabelsLfo_dOTree_818

theorem cliLabelsLfo_dO_819 (hdi : 819 < libsignalSessionLib.data.length) :
    cliLabelsLfo_dO ⟨819, hdi⟩ = tokenSpec.origin :=
  cliLabelsLfo_dOTree_819

theorem checkCliProbeLabelsB_lfo : checkCliProbeLabelsB cliLabelsLfo_dO = true :=
  checkCliProbeLabelsB_of_origins cliLabelsLfo_dO_818 cliLabelsLfo_dO_819

/-- Concrete SPQR CPU-probe data label anchoring at `cliLabelsLfo_dO`. -/
theorem cliProbeLabelsAnchored : CliProbeLabelsAnchored cliLabelsLfo_dO :=
  cliProbeLabelsAnchored_of_check checkCliProbeLabelsB_lfo

theorem resolve_tokenStorage_eq_rho (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl tokenStorageName = mpl.ρ tokenStorageName :=
  resolve_tokenStorage_eq_rho_of_anchored cliLabelsLfo_spec cliProbeLabelsAnchored mpl

theorem resolve_token_eq_rho (mpl : Obj.MultiPlacement) :
    libsignalSessionLib.resolve mpl tokenName = mpl.ρ tokenName :=
  resolve_token_eq_rho_of_anchored cliLabelsLfo_spec cliProbeLabelsAnchored mpl

/-- Rewrites `Placed.cliTokenPatchPlaced` via `libsignalSessionLib.resolve` using
`cliLabelsLfo_spec` and `cliProbeLabelsAnchored`. -/
theorem cliTokenPatchPlaced_eq_resolve (mpl : Obj.MultiPlacement) (s : State) :
    cliTokenPatchPlaced mpl s =
      s.setMem
        ((s.mem.writeBytes (libsignalSessionLib.resolve mpl tokenStorageName) [0#8]).writeBytes
          (libsignalSessionLib.resolve mpl tokenName + 8#64) [0#8, 0#8, 0#8, 0#8]) :=
  cliTokenPatchPlaced_eq_resolve_of_anchored cliLabelsLfo_spec cliProbeLabelsAnchored mpl s

/-- Concrete relocation provenance for SPQR's `TOKEN` `futex::Once` state word. -/
theorem tokenOnce_reloc_sym_eq
    (bi : Fin libsignalSessionLib.blocks.length)
    {bObj : Obj.ExtractedObj} {bSec : Obj.RawSec} {rr : Obj.RawReloc} {sy : Obj.RawSym}
    (hbobj : cliLinkObjs[(cliLabelsLfo_bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(cliLabelsLfo_bO bi).si]? = some bSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (cliLabelsLfo_bO bi).start ≤ rr.off)
    (hhi : rr.off < (cliLabelsLfo_bO bi).start + (cliLabelsLfo_bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    (htarget :
      ((cliLabelsLfo_bO bi).oi = 6 ∧ sy.bind = .local ∧ sy.sec = .sec 650 ∧
        (16 : Int) = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves cliLinkObjs sy.rawName 6 k 650 tSym ∧
        (16 : Int) = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ libsignalSessionLib.blocks[bi].relocs,
      r.off + (cliLabelsLfo_bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = tokenName ∧ r.addend = 8 :=
  tokenOnce_reloc_sym_eq_of_check cliLabelsLfo_spec checkCliProbeLabelsB_lfo
    bi hbobj hbsec hrr hlo hhi hsy htarget

/-- Concrete relocation provenance for SPQR's `STORAGE.0` byte. -/
theorem tokenStorage_reloc_sym_eq
    (bi : Fin libsignalSessionLib.blocks.length)
    {bObj : Obj.ExtractedObj} {bSec : Obj.RawSec} {rr : Obj.RawReloc} {sy : Obj.RawSym}
    (hbobj : cliLinkObjs[(cliLabelsLfo_bO bi).oi]? = some bObj)
    (hbsec : bObj.sections[(cliLabelsLfo_bO bi).si]? = some bSec)
    (hrr : rr ∈ bSec.relocs)
    (hlo : (cliLabelsLfo_bO bi).start ≤ rr.off)
    (hhi : rr.off < (cliLabelsLfo_bO bi).start + (cliLabelsLfo_bO bi).len)
    (hsy : bObj.symbols[rr.symIdx]? = some sy)
    (hlen : ∀ dj : Fin libsignalSessionLib.data.length,
      (cliLabelsLfo_dO dj).oi = 6 → (cliLabelsLfo_dO dj).si = 650 →
        (cliLabelsLfo_dO dj).start = 0 → 0 < (cliLabelsLfo_dO dj).len)
    (htarget :
      ((cliLabelsLfo_bO bi).oi = 6 ∧ sy.bind = .local ∧ sy.sec = .sec 650 ∧
        (0 : Int) = (sy.value : Int) + rr.addend) ∨
      (sy.bind ≠ .local ∧ ∃ k tSym,
        Obj.Resolves cliLinkObjs sy.rawName 6 k 650 tSym ∧
        (0 : Int) = (tSym.value : Int) + rr.addend)) :
    ∃ r ∈ libsignalSessionLib.blocks[bi].relocs,
      r.off + (cliLabelsLfo_bO bi).start = rr.off ∧ rr.kind = some r.kind ∧
        r.sym = tokenStorageName ∧ r.addend = 0 :=
  tokenStorage_reloc_sym_eq_of_check cliLabelsLfo_spec checkCliProbeLabelsB_lfo
    bi hbobj hbsec hrr hlo hhi hsy hlen htarget

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProbeLabels
