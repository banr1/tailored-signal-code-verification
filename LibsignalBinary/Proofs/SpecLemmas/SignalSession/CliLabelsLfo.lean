/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliLabels
public import ProofLib.Placed.LabelsInterned
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoObjsEq
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoText
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoData
meta import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
meta import Lean

@[expose] public section

set_option autoImplicit false

/-!
# `Obj.LabelsFromObjects` Certificate Join

**Checked by Lean.** Assembles the four privately imported `rfl_kernel` sub-certificates
(`CliLabelsLfoCert`, `CliLabelsLfoObjsEq`, `CliLabelsLfoText`, `CliLabelsLfoData`) via
`Arm64.Obj.LabelsInterned.labelsFromObjects_of_split_checks`, exposing compact `IdxTree SliceOrigin`
witnesses `cliLabelsLfo_bO` and `cliLabelsLfo_dO` without re-exporting shard `.olean` payloads.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfo

open Arm64 Arm64.Obj Arm64.Obj.LabelsInterned
open ProofLib.ProgramReflection
open Lean Elab Command
open CryptoVerification.SignalSession (cliLinkObjs libsignalSessionLib)

local syntax (name := copyCliLabelsLfoOriginTrees) "copy_cli_labels_lfo_origin_trees" : command

@[local command_elab copyCliLabelsLfoOriginTrees]
private meta def elabCopyCliLabelsLfoOriginTrees : CommandElab := fun _ => do
  let currNs ← getCurrNamespace
  liftTermElabM do
    let env ← getEnv
    let privEnv := env.setExporting false
    for (srcName, dstBase) in [
      (`LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert.cliLabelsLfo_bOTree,
        `cliLabelsLfo_bOTree),
      (`LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert.cliLabelsLfo_dOTree,
        `cliLabelsLfo_dOTree)
    ] do
      let some cinfo := privEnv.find? srcName
        | throwError "copy_cli_labels_lfo_origin_trees: missing {srcName}"
      let some val := cinfo.value?
        | throwError "copy_cli_labels_lfo_origin_trees: missing value for {srcName}"
      addDecl (.defnDecl {
        name := currNs ++ dstBase
        levelParams := []
        type := cinfo.type
        value := val
        hints := .regular (getMaxHeight privEnv val + 1)
        safety := .safe
      }) (forceExpose := true)
      modifyEnv (addNoncomputable · (currNs ++ dstBase))

copy_cli_labels_lfo_origin_trees

noncomputable def cliLabelsLfo_bO
    (i : Fin libsignalSessionLib.blocks.length) : Arm64.Obj.SliceOrigin :=
  Arm64.Obj.LabelsInterned.originAt cliLabelsLfo_bOTree i

noncomputable def cliLabelsLfo_dO
    (i : Fin libsignalSessionLib.data.length) : Arm64.Obj.SliceOrigin :=
  Arm64.Obj.LabelsInterned.originAt cliLabelsLfo_dOTree i

private theorem allIdx_toList_getElem {α : Type} {p : Nat → α → Bool} {t : IdxTree α}
    {sz : Nat} (hsz : t.size? = some sz)
    (h : IdxTree.allIdx p 0 t = true) {i : Nat} (hi : i < t.toList.length) :
    p i t.toList[i] = true := by
  rw [IdxTree.allIdx_eq_checkListIdx p hsz 0] at h
  have h1 := (checkListIdx_eq_true_iff p 0 t.toList).1 h i hi
  simpa using h1

private theorem not_discarded_of_groups_empty
    (namesTree : IdxTree String) {objsTree : IdxTree IObj}
    (hgroups : CliLabelsLfoCert.checkIObjsGroupsEmptyB objsTree = true)
    (oi si : Nat) :
    ¬Discarded (objsTree.toList.map (IObj.toExtractedObj namesTree)) oi si := by
  rintro ⟨o, g, gi, ho, hg, hmem, _⟩
  simp only [List.getElem?_map] at ho
  cases ho0 : objsTree.toList[oi]? with
  | none => rw [ho0] at ho; exact nomatch ho
  | some io =>
    rw [ho0] at ho; cases ho
    dsimp only [IObj.toExtractedObj] at hg
    obtain ⟨hoi_lt, hio_eq⟩ := List.getElem?_eq_some_iff.1 ho0
    have hio_mem : io ∈ objsTree.toList := hio_eq ▸ List.getElem_mem hoi_lt
    obtain ⟨hgi_lt, hg_eq⟩ := List.getElem?_eq_some_iff.1 hg
    have hg_mem : g ∈ io.groups := hg_eq ▸ List.getElem_mem hgi_lt
    unfold CliLabelsLfoCert.checkIObjsGroupsEmptyB at hgroups
    rw [IdxTree.all_eq_toList_all, List.all_eq_true] at hgroups
    have hio_ok := hgroups io hio_mem
    rw [List.all_eq_true] at hio_ok
    have hg_empty : g.members.isEmpty = true := hio_ok g hg_mem
    cases hgm : g.members with
    | nil => rw [hgm] at hmem; cases hmem
    | cons _ _ => rw [hgm] at hg_empty; exact nomatch hg_empty

private theorem labelsFromObjects_of_split_checks_nd
    {objs : List ExtractedObj} {lib : MultiPlacedLib}
    {N B D : Nat}
    {namesTree : IdxTree String} {charsTree : IdxTree (List Char)}
    {objsTree : IdxTree IObj} {L : IMultiLib}
    {bOTree dOTree : IdxTree SliceOrigin}
    {symRole : IdxTree SymRole}
    {rawSummary : IdxTree RawIdStatus} {rawClaimed : IdxTree Bool}
    {textGroups dataGroups : IdxTree SliceGroup}
    {textToGroup dataToGroup : IdxTree (Nat × Nat)}
    {branchCalled : IdxTree (Option (Nat × Nat))} {commonExtSet : IdxTree Bool}
    (hobjs_eq : objs = objsTree.toList.map (IObj.toExtractedObj namesTree))
    (hlib_eq : lib = L.toMultiPlacedLib namesTree)
    (hsz : namesTree.size? = some N)
    (hcsz : charsTree.size? = some N)
    (hnames_eq : namesTree.toList = charsTree.toList.map String.ofList)
    (hnn : Arm64.Obj.Interned.namesNodup charsTree.toList = true)
    (h0 : namesTree.get? 0 = some "")
    (hB : L.blocks.size? = some B)
    (hD : L.data.size? = some D)
    (hroles : checkSymRolesB N L symRole = true)
    (hobjs : checkObjSymsB N charsTree objsTree rawSummary rawClaimed = true)
    (hgroups : CliLabelsLfoCert.checkIObjsGroupsEmptyB objsTree = true)
    (hbdisj : checkGroupsDisjointB B bOTree textGroups textToGroup = true)
    (hddisj : checkGroupsDisjointB D dOTree dataGroups dataToGroup = true)
    (htbytes : checkTextGroupsBytesB objsTree L.blocks bOTree textGroups = true)
    (htmeta : checkTextSlicesMetaB N objsTree L.blocks bOTree rawClaimed = true)
    (hdbytes : checkDataGroupsBytesB objsTree L.data dOTree dataGroups = true)
    (hdmeta : checkDataSlicesMetaB N objsTree L.data dOTree rawClaimed = true)
    (hbrelocs : checkAllBlockRelocsB N objsTree L bOTree dOTree symRole rawSummary = true)
    (hdrelocs : checkAllDataRelocsB N objsTree L bOTree dOTree symRole rawSummary = true)
    (hexports : checkIExportsB N objsTree L bOTree symRole rawSummary = true)
    (hexterns : checkIExternsB N L symRole rawSummary branchCalled commonExtSet = true) :
    LabelsFromObjects objs lib (originAt bOTree) (originAt dOTree) := by
  subst hobjs_eq; subst hlib_eq
  have hnd_disc := not_discarded_of_groups_empty namesTree hgroups
  have hnd : namesTree.toList.Nodup := Arm64.Obj.Interned.nodup_of_namesNodup hnames_eq hnn
  have hbO_sz : bOTree.size? = some B := by
    unfold checkGroupsDisjointB at hbdisj
    simp only [Bool.and_eq_true, beq_iff_eq] at hbdisj
    exact hbdisj.1.1.1.1.1
  have hdO_sz : dOTree.size? = some D := by
    unfold checkGroupsDisjointB at hddisj
    simp only [Bool.and_eq_true, beq_iff_eq] at hddisj
    exact hddisj.1.1.1.1.1
  have hlenB : (L.toMultiPlacedLib namesTree).blocks.length = B := by
    simp [IMultiLib.toMultiPlacedLib, IdxTree.length_toList_of_size? hB]
  have hlenD : (L.toMultiPlacedLib namesTree).data.length = D := by
    simp [IMultiLib.toMultiPlacedLib, IdxTree.length_toList_of_size? hD]
  refine
    { blocks_valid := validTextSlices_of_check hsz hcsz hnames_eq hnd h0 hB hobjs hnd_disc hbdisj htbytes htmeta
      data_valid := validDataSlices_of_check hsz hcsz hnames_eq hnd h0 hD hobjs hnd_disc hddisj hdbytes hdmeta
      blocks_disjoint := ?_
      data_disjoint := ?_
      names_nodup := ⟨blockSymbols_nodup_of_roles hsz hnd hroles,
        dataSyms_nodup_of_roles hsz hnd hroles,
        fun _ hd => data_lookup_none_of_roles hsz hnd hroles hd⟩
      block_relocs := ?_
      data_relocs := ?_
      exports_valid := exportsValid_of_checkI hsz hnd h0 hB hbO_sz hroles hobjs hnd_disc hexports
      externs_valid := externsValid_of_checkI hsz hnd hroles hobjs hexterns }
  · intro i j hij hoi hsi
    have hdisj := groups_disjoint_of_check hbdisj ⟨i.1, hlenB ▸ i.2⟩ ⟨j.1, hlenB ▸ j.2⟩
      (fun heq => hij (Fin.ext (Fin.mk.inj heq))) hoi hsi
    exact hdisj
  · intro i j hij hoi hsi
    have hdisj := groups_disjoint_of_check hddisj ⟨i.1, hlenD ▸ i.2⟩ ⟨j.1, hlenD ▸ j.2⟩
      (fun heq => hij (Fin.ext (Fin.mk.inj heq))) hoi hsi
    exact hdisj
  · intro i
    have hiL : i.1 < L.blocks.toList.length := by simpa [IMultiLib.toMultiPlacedLib] using i.2
    have hbr := allIdx_toList_getElem hB hbrelocs hiL
    have ho_elem : bOTree.get? i.1 = some (originAt bOTree i) := by
      have hiB : i.1 < B := hlenB ▸ i.2
      have hlenbO : bOTree.toList.length = B := IdxTree.length_toList_of_size? hbO_sz
      unfold originAt
      rw [IdxTree.get?_eq_getElem? hbO_sz i.1, List.getElem?_eq_getElem (hlenbO ▸ hiB)]
      rfl
    rw [ho_elem] at hbr; dsimp only at hbr
    have hrel_eq : (L.toMultiPlacedLib namesTree).blocks[i].relocs =
        L.blocks.toList[i.1].relocs.toList.map (IReloc.toEntry namesTree) := by
      change ((L.toMultiPlacedLib namesTree).blocks[i.1]'i.2).relocs = _
      simp [IMultiLib.toMultiPlacedLib, IBlock.toCodeBlock]
    rw [hrel_eq]
    exact sliceRelocsMatch_of_checkI hsz hnd h0 hB hD hbO_sz hdO_sz hroles hobjs hnd_disc hbr
  · intro i
    have hiL : i.1 < L.data.toList.length := by simpa [IMultiLib.toMultiPlacedLib] using i.2
    have hdr := allIdx_toList_getElem hD hdrelocs hiL
    have ho_elem : dOTree.get? i.1 = some (originAt dOTree i) := by
      have hiD : i.1 < D := hlenD ▸ i.2
      have hlendO : dOTree.toList.length = D := IdxTree.length_toList_of_size? hdO_sz
      unfold originAt
      rw [IdxTree.get?_eq_getElem? hdO_sz i.1, List.getElem?_eq_getElem (hlendO ▸ hiD)]
      rfl
    rw [ho_elem] at hdr; dsimp only at hdr
    have hrel_eq : (L.toMultiPlacedLib namesTree).data[i].relocs =
        L.data.toList[i.1].relocs.toList.map (IReloc.toEntry namesTree) := by
      change ((L.toMultiPlacedLib namesTree).data[i.1]'i.2).relocs = _
      simp [IMultiLib.toMultiPlacedLib, IData.toSymDataInfo]
    rw [hrel_eq]
    exact sliceRelocsMatch_of_checkI hsz hnd h0 hB hD hbO_sz hdO_sz hroles hobjs hnd_disc hdr

theorem cliLabelsLfo_spec :
    Arm64.Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib
      cliLabelsLfo_bO cliLabelsLfo_dO :=
  labelsFromObjects_of_split_checks_nd
    CliLabelsLfoObjsEq.cliLabelsLfo_objs_eq
    CliLabelsLfoText.cliLabelsLfo_lib_eq
    CliLabelsLfoCert.cliLabelsLfo_names_sz
    CliLabelsLfoCert.cliLabelsLfo_chars_sz
    CliLabelsLfoCert.cliLabelsLfo_names_eq
    CliLabelsLfoCert.cliLabelsLfo_names_nodup
    CliLabelsLfoCert.cliLabelsLfo_names_zero
    CliLabelsLfoCert.cliLabelsLfo_blocks_sz
    CliLabelsLfoCert.cliLabelsLfo_data_sz
    CliLabelsLfoCert.cliLabelsLfo_roles_ok
    CliLabelsLfoObjsEq.cliLabelsLfo_objs_ok
    CliLabelsLfoCert.cliLabelsLfo_groups_ok
    CliLabelsLfoCert.cliLabelsLfo_bdisj_ok
    CliLabelsLfoCert.cliLabelsLfo_ddisj_ok
    CliLabelsLfoText.cliLabelsLfo_tbytes_ok
    CliLabelsLfoText.cliLabelsLfo_tmeta_ok
    CliLabelsLfoData.cliLabelsLfo_dbytes_ok
    CliLabelsLfoData.cliLabelsLfo_dmeta_ok
    CliLabelsLfoText.cliLabelsLfo_brelocs_ok
    CliLabelsLfoData.cliLabelsLfo_drelocs_ok
    CliLabelsLfoCert.cliLabelsLfo_exports_ok
    CliLabelsLfoCert.cliLabelsLfo_externs_ok

theorem cliLabelsLfo :
    ∃ bO dO, Arm64.Obj.LabelsFromObjects cliLinkObjs libsignalSessionLib bO dO :=
  ⟨cliLabelsLfo_bO, cliLabelsLfo_dO, cliLabelsLfo_spec⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfo
