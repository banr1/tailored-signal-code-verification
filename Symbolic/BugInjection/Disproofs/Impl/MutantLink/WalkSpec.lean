/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection

/-!
# Variable-Width Text-Slice Combiner for `LinkedAt` Proofs

Defines `SlicesTextVarOk`, which accumulates contiguous `checkMultiTextSliceB` boolean slice checks,
and proves `checkMultiVarSliced_spec` to establish `Placeable`, `InElf`, and `DataDisjoint` for an
interned `MultiLib` of arbitrary block count bounded by `bound`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec

open Arm64 Arm64.Obj Arm64.Obj.Interned Arm64.Process
open ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection

/-- Witnesses that `checkMultiTextSliceB` holds on contiguous slices covering `[0, n)`. -/
inductive SlicesTextVarOk (ML : MultiLib) (mly : MultiLayout) (img : ElfImage) :
    Nat → Prop
  | zero : SlicesTextVarOk ML mly img 0
  | step {endIdx count : Nat} :
      SlicesTextVarOk ML mly img endIdx →
      checkMultiTextSliceB ML mly img endIdx count = true →
      SlicesTextVarOk ML mly img (endIdx + count)

theorem slicesTextVarOk_sound {ML : MultiLib} {mly : MultiLayout} {img : ElfImage}
    {bound : Nat}
    (hnd : ML.names.Nodup) (hids : ML.idsOk = true)
    (hwf : ∀ b ∈ ML.blocks, relocsWf b.code.length 0 b.relocs = true)
    (hb : mly.bases.length < 2 ^ 20) (ha : mly.addrs.length < 2 ^ 20)
    (hrx : mly.relax.length < 2 ^ 20) (hb2b : mly.b2b.length < 2 ^ 20)
    (hs : SlicesTextVarOk ML mly img bound) :
    ∀ (i : Nat) (hi : i < ML.blocks.length), i < bound →
      BlockTextWalkOk ML mly img.segments i hi := by
  induction hs with
  | zero => intro _ _ hlt; nomatch hlt
  | @step endIdx count _ hslice ih =>
    intro i hi hlt
    by_cases hlt' : i < endIdx
    · exact ih i hi hlt'
    · exact checkMultiTextSliceB_sound hnd hids hwf hb ha hrx hb2b hslice
        (by omega) hlt hi

/-- Combines fast metadata, data-walk, and sliced text-walk checks into `Placeable`, `InElf`, and `DataDisjoint`. -/
theorem checkMultiVarSliced_spec {lib : MultiPlacedLib} {ML : MultiLib} {mly : MultiLayout}
    {nameChars : List (List Char)} {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    {bound : Nat}
    (hlib : lib = ML.toMultiPlacedLib)
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hmeta : checkMultiMetaFastB ML mly nameChars symChars = true)
    (hdwalk : checkMultiDataWalkFastB ML mly img = true)
    (hbound : Nat.ble ML.blocks.length bound = true)
    (hslices : SlicesTextVarOk ML mly img bound) :
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  subst hlib
  unfold checkMultiMetaFastB at hmeta
  unfold checkMultiDataWalkFastB at hdwalk
  simp only [withVecTree_eq, withRegionsWithLen_eq, buildEncSymTable_eq, withNat_eq,
    multiIdsOkFast_eq, Bool.and_eq_true, Nat.blt_eq] at hmeta hdwalk
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, ha⟩, hrx⟩, hb2b⟩, hnc⟩, hnn⟩, hids⟩, hrest⟩ := hmeta
  cases hsym : insertAllBlocks 0 ML.blocks (mkNoneTree 20 ML.names.length) with
  | none => rw [hsym] at hrest; nomatch hrest
  | some tSym =>
    rw [hsym] at hrest
    dsimp only at hrest
    cases hdsym : insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => rw [hdsym] at hrest; nomatch hrest
    | some tSymData =>
      rw [hdsym] at hrest
      dsimp only at hrest
      simp only [Bool.and_eq_true] at hrest
      obtain ⟨⟨⟨⟨⟨hmatch, htp⟩, hdisj⟩, hdp⟩, hexp⟩, hddisj⟩ := hrest
      obtain ⟨hnd_syms, _, hget_sym⟩ := insertAllBlocks_spec 0 ML.blocks _ tSym hsym
      obtain ⟨hnd_data_raw, hnone_data_raw, _⟩ :=
        insertBlockSyms_spec 0 (ML.data.map fun d => (d.sym, 0)) tSym tSymData hdsym
      have hmap_data : ((ML.data.map fun d => (d.sym, 0)).map (·.1)) = ML.data.map (·.sym) := by
        simp [List.map_map, Function.comp_def]
      rw [hmap_data] at hnd_data_raw hnone_data_raw
      have hlookup : ∀ q, tSym.getD none q = lookupBlockSymId q ML.blocks := by
        intro q
        rw [hget_sym q, getD_mkNoneTree]
        rfl
      rw [blockSymsMatchTree_eq ML mly hb ha] at hmatch
      rw [textPlaceableTreeMulti_eq ML mly hb ha] at htp
      have hdisj' := blocksDisjoint_of_rangesSorted hb hdisj
      have hnd_b : natNodupFast ((ML.blocks.flatMap (·.symbols)).map (·.1)) = true := by
        simp [natNodupFast, natNodup_of_nodup hnd_syms]
      have hdp' := dataPlaceableTreeMulti_imp ML mly ha hnd_data_raw hdp
      have hd_none : ∀ d ∈ ML.data, (lookupBlockSymId d.sym ML.blocks).isNone = true := by
        intro d hd
        have hnone := hnone_data_raw d.sym (List.mem_map_of_mem hd)
        rw [hlookup d.sym] at hnone
        simp [hnone]
      rw [dataWalkTreeMulti_eq ML mly ha] at hdwalk
      rw [multiExportsOkTree_eq ML mly nameChars _ tSym hb hnc hlookup] at hexp
      have hddisj' := multiDataDisjointTree_imp ha hddisj
      have hnd := nodup_of_namesNodup hnames hnn
      have hok0 := ML.emptyBlock_idsOk hids
      have hwf : ∀ b ∈ ML.blocks, relocsWf b.code.length 0 b.relocs = true := by
        intro b hbm
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hbm
        have hti := allIdx_spec htp i hi
        rw [Nat.zero_add] at hti
        simp only [textPlaceableB, Bool.and_eq_true] at hti
        exact hti.1.1.2
      have hlen_le : ML.blocks.length ≤ bound := by rwa [Nat.ble_eq] at hbound
      have hwalk : ∀ (i : Nat) (hi : i < ML.blocks.length),
          BlockTextWalkOk ML mly img.segments i hi :=
        fun i hi => slicesTextVarOk_sound hnd hids hwf hb ha hrx hb2b hslices i hi
          (Nat.lt_of_lt_of_le hi hlen_le)
      have htp0 : textPlaceableB (ML.blockLib { code := [] }) mly.dataLayout = true := by
        dsimp only [textPlaceableB, MultiLib.blockLib, MultiLayout.dataLayout, relocsWf, List.all]
        decide
      have hwalk0 : WalkOk (ML.blockLib { code := [] }) mly.dataLayout 0 [] [] := by
        refine ⟨?_, ?_, ?_⟩
        · simp [MultiLib.blockLib, CodeBlock.patched]
        · intro _ hr; nomatch hr
        · intro _ _ _ _ hr; nomatch hr
      have hpl0 := placeable_of hnd hok0 htp0 hdp' hwalk0
      have hbp_eq : ∀ i, ML.toMultiPlacedLib.blockPlacement (mly.toMultiPlacement ML.names) i =
          (mly.blockLayout i).toPlacement ML.names :=
        toMultiPlacement_blockPlacement_eq hnd hids hmatch
      have hres_eq : ∀ s, ML.toMultiPlacedLib.resolve (mly.toMultiPlacement ML.names) s =
          (mly.dataLayout.toPlacement ML.names).ρ s :=
        toMultiPlacement_resolve_eq hnd hids hmatch
      have hpl : ML.toMultiPlacedLib.Placeable (mly.toMultiPlacement ML.names) := by
        refine ⟨?_, ?_, ?_, hpl0.data_nodup, ?_, ?_⟩
        · intro i hi
          simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map, List.getElem_map] at hi ⊢
          rw [hbp_eq i, ← MultiLib.blockLib_block]
          have hti := allIdx_spec htp i hi
          rw [Nat.zero_add] at hti
          have ⟨_, hw⟩ := hwalk i hi
          exact textPlaceable_of hnd (ML.blockLib_idsOk hids (List.getElem_mem hi)) hti hw
        · intro i j hi hj hij
          simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map, List.getElem_map] at hi hj ⊢
          have h1 := allIdx_spec hdisj' i hi
          rw [Nat.zero_add] at h1
          have h2 := allIdx_spec h1 j hj
          rw [Nat.zero_add] at h2
          simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Nat.blt_eq] at h2
          rcases h2 with hnot | hok
          · exact absurd hij hnot
          · exact rangesDisjoint_of_check hok
        · rw [MultiLib.toMultiPlacedLib_blocks, flatMap_toCodeBlock_symbols_fst]
          have hn := natNodupFast_spec hnd_b
          rw [List.nodup_iff_pairwise_ne] at hn ⊢
          rw [List.pairwise_map]
          refine hn.imp_of_mem fun {x y} hx hy hxy heq => hxy ?_
          exact getD_inj hnd (mem_flatMap_symbols_lt hids hx) (mem_flatMap_symbols_lt hids hy) heq
        · intro d hd
          have hdo := hpl0.data_ok d hd
          simp only [MultiLib.toMultiPlacedLib, List.mem_map] at hd
          obtain ⟨d', hd', rfl⟩ := hd
          have hdi := (hok0.data d' hd').1
          have hln : lookupBlockSym (Data.toInfo ML.names d').sym ML.toMultiPlacedLib.blocks = none := by
            show lookupBlockSym (ML.names.getD d'.sym "") ML.toMultiPlacedLib.blocks = none
            rw [lookupBlockSym_toMultiPlacedLib hnd hids hdi]
            exact Option.isNone_iff_eq_none.1 (hd_none d' hd')
          exact ⟨hln, hdo.2⟩
        · intro d hd r hr
          have hdro := hpl0.data_relocs_ok d hd r hr
          have hres0 : (Block.toCodeBlock ML.names { code := [] }).resolve
              (mly.dataLayout.toPlacement ML.names) r.sym =
              ML.toMultiPlacedLib.resolve (mly.toMultiPlacement ML.names) r.sym := by
            rw [hres_eq r.sym]
            rfl
          have hρ0 : (mly.dataLayout.toPlacement ML.names).ρ d.sym =
              (mly.toMultiPlacement ML.names).ρ d.sym := rfl
          simpa only [Lib.toLib_text, MultiLib.blockLib_block, MultiLib.blockLib_names, hres0, hρ0]
            using hdro
      have hin : ML.toMultiPlacedLib.InElf img (mly.toMultiPlacement ML.names) := by
        refine ⟨?_, ?_, ?_⟩
        · intro i hi
          simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map, List.getElem_map] at hi ⊢
          rw [hbp_eq i, ← MultiLib.blockLib_block]
          have ⟨⟨p, bs, hv, hp, hpre⟩, _⟩ := hwalk i hi
          exact elfMaps_of_view (hv.of_prefix hpre) (by simp [hp])
        · intro d hd
          simp only [MultiLib.toMultiPlacedLib, List.mem_map] at hd
          obtain ⟨d', hd', rfl⟩ := hd
          obtain ⟨p, hv, hp⟩ := dataWalk_sound none ML.data (fun _ _ _ hc => nomatch hc) hdwalk d' hd'
          have hi := (hok0.data d' hd').1
          have hρ : (mly.toMultiPlacement ML.names).ρ (Data.toInfo ML.names d').sym =
              mly.dataLayout.addrs.getD d'.sym 0#64 :=
            toPlacement_ρ (ly := mly.dataLayout) hnd hi
          have hpd : ML.toMultiPlacedLib.patchedData (mly.toMultiPlacement ML.names)
              (Data.toInfo ML.names d') =
              patchedDataId (ML.blockLib { code := [] }) mly.dataLayout d' := by
            rw [← patchedData_toLib (L := ML.blockLib { code := [] }) (ly := mly.dataLayout)
              hnd hok0 hd']
            have hpr : ML.toMultiPlacedLib.patchDataReloc (mly.toMultiPlacement ML.names) =
                (ML.blockLib { code := [] }).toLib.patchDataReloc
                  (mly.dataLayout.toPlacement ML.names) := by
              funext addr bytes r
              simp only [MultiPlacedLib.patchDataReloc, PlacedLib.patchDataReloc, hres_eq]
              rfl
            simp only [MultiPlacedLib.patchedData, PlacedLib.patchedData, hpr]
            rfl
          rw [show (Data.toInfo ML.names d').readOnly = d'.readOnly from rfl, hρ, hpd]
          exact elfMaps_of_view hv hp
        · intro e he
          simp only [MultiLib.toMultiPlacedLib, List.mem_map] at he
          obtain ⟨e', he', rfl⟩ := he
          have he_lt : e' < ML.names.length := by
            simp only [MultiLib.idsOk, Bool.and_eq_true, List.all_eq_true, blt_iff] at hids
            exact hids.1.2 e' he'
          simp only [multiExportsOk, Bool.and_eq_true] at hexp
          obtain ⟨hesb, hexp⟩ := hexp
          have hes : ∀ p ∈ ML.exportSyms, p.1 < ML.names.length := fun p hp =>
            blt_iff.1 (List.all_eq_true.1 hesb p hp)
          have helf : ML.toMultiPlacedLib.elfSym (ML.names.getD e' "") =
              ML.names.getD ((lookupId e' ML.exportSyms).getD e') "" := by
            have hmap : ∀ xs : List (Nat × Nat),
                lookupId e' (xs.map fun p => (p.1, ML.names.getD p.2 "")) =
                  (lookupId e' xs).map fun j => ML.names.getD j "" := by
              intro xs
              induction xs with
              | nil => rfl
              | cons p rest ih =>
                simp only [List.map_cons, lookupId]
                cases Nat.beq p.1 e'
                · simpa using ih
                · rfl
            have hl := lookup_map_getD hnd he_lt
              (ML.exportSyms.map fun p => (p.1, ML.names.getD p.2 ""))
              (fun p hp => by
                obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
                exact hes q hq)
            rw [List.map_map] at hl
            show (lookup (ML.names.getD e' "")
                (ML.exportSyms.map fun p => (ML.names.getD p.1 "", ML.names.getD p.2 ""))).getD
                  (ML.names.getD e' "") = _
            rw [show (fun p : Nat × Nat => (ML.names.getD p.1 "", ML.names.getD p.2 "")) =
                ((fun s : Nat × String => (ML.names.getD s.1 "", s.2)) ∘
                  fun p => (p.1, ML.names.getD p.2 "")) from rfl, hl, hmap]
            cases lookupId e' ML.exportSyms <;> rfl
          have hex := List.all_eq_true.1 hexp e' he'
          split at hex
          · rename_i i off hblk
            split at hex
            · rename_i a ha_enc
              rw [beq_iff_eq] at hex
              subst hex
              refine ⟨i, off, ?_, ?_⟩
              · rw [lookupBlockSym_toMultiPlacedLib hnd hids he_lt, hblk]
              · have hng : ML.names.getD ((lookupId e' ML.exportSyms).getD e') "" =
                    String.ofList (nameChars.getD ((lookupId e' ML.exportSyms).getD e') []) :=
                  names_getD (L := ML.blockLib { code := [] }) hnames _
                rw [helf, lookupUnique_eq_lookupUniqueEnc hsyms rfl hng, ha_enc]
                rfl
            · cases hex
          · cases hex
      refine ⟨hpl, hin, ?_⟩
      have ⟨_, hpw⟩ := dataEntriesDisjointB_pairwise hddisj'
      have heq : (ML.toMultiPlacedLib.data.map fun d =>
          (d.readOnly, (mly.toMultiPlacement ML.names).ρ d.sym,
            (ML.toMultiPlacedLib.patchedData (mly.toMultiPlacement ML.names) d).length)) =
          ML.data.map fun d =>
            (d.readOnly, mly.addrs.getD d.sym 0#64, d.bytes.length + d.zeroTail) := by
        simp only [MultiLib.toMultiPlacedLib_data, List.map_map]
        refine List.map_congr_left fun d hd => ?_
        have hdi : d.toInfo ML.names ∈ ML.toMultiPlacedLib.data := by
          simp only [MultiLib.toMultiPlacedLib_data]; exact List.mem_map_of_mem hd
        simp only [Function.comp_apply, Prod.mk.injEq]
        refine ⟨rfl, toPlacement_ρ (ly := mly.dataLayout) hnd (hok0.data d hd).1, ?_⟩
        have hpr : ML.toMultiPlacedLib.patchDataReloc (mly.toMultiPlacement ML.names) =
            (ML.blockLib { code := [] }).toLib.patchDataReloc
              (mly.dataLayout.toPlacement ML.names) := by
          funext addr bytes r
          simp only [MultiPlacedLib.patchDataReloc, PlacedLib.patchDataReloc, hres_eq]
          rfl
        have hpd : ML.toMultiPlacedLib.patchedData (mly.toMultiPlacement ML.names)
            (d.toInfo ML.names) =
            (ML.blockLib { code := [] }).toLib.patchedData
              (mly.dataLayout.toPlacement ML.names) (d.toInfo ML.names) := by
          simp only [MultiPlacedLib.patchedData, PlacedLib.patchedData, hpr]
          rfl
        rw [hpd, PlacedLib.length_patchedData fun r hr => (hpl.data_relocs_ok _ hdi r hr).2.1]
        rfl
      rw [← heq, List.pairwise_map] at hpw
      exact hpw

end Symbolic.BugInjection.Disproofs.Impl.MutantLink.WalkSpec
