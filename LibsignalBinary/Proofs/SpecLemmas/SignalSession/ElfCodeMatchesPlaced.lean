/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionPlacedObj
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMallocngPlaced
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import ProofLib.Placed.Multi
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned

/-!
# Two-Placement `CliElfCodeMatchesPlaced` and `LinkedAt` Uniqueness

Proves concrete and universal two-placement `(mpl, mmpl)` containment, relocation-DAG uniqueness,
cross-library code and data disjointness, and `CliElfCodeMatchesPlaced` witnesses for
`libsignalSessionLib` and `VerifiedLibraries.mallocngLib` in `f3TrialElf` / `f3TrialElfBytes`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced

open Arm64 Arm64.Obj Arm64.Obj.Interned Arm64.Process
open ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1 (tokenName tokenStorageName)
open CryptoVerification.SignalSession
  (CliHooks CliReachesOOMPlaced OutcomeMatchesProcess abortOnPanic cliDehookedSymsPlaced
   cliExternsPlaced cliExternsPlacedSig cliHookTablePlaced cliPanicSymbolsPlaced cliProcessInputs
   isCliPanicSymbolPlaced libsignalSessionLib lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Placed
  (CliElfCodeMatchesPlaced CliRunsToPlaced DirectOrBranchStub cliProgPlacedSig cliRunPlacedSig
   cliTokenPatchPlaced)
open LibsignalBinary.Heap.Fine
  (f3MallocngMly f3MallocngMpl f3StdLayout f3StubNoShimAddr)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage cliElf_parse)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars
  (cliElfSymChars cliElf_symbols_eq)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMallocngPlaced
  (cliElf_mallocng_placed)
open VerifiedLibraries.Mallocng.Proofs
  (mallocngMultiL mallocngMultiL_names mallocngMultiL_toMultiPlacedLib mallocngNameChars)

open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
  (checkLsDataBoundsB checkLsDataBounds_ok checkMallocngCodeBoundsB checkMallocngCodeBounds_ok
   checkMallocngDataBoundsB checkMallocngDataBounds_ok checkMallocngLibcPin_ok
   cliDehookedSymsPlaced_eq_entries f3CoinsLeftIdx f3CoinsNextIdx f3DehookedEntries
   f3HandleErrorIdx f3HandleError_pin_ok f3LogFilterIdx f3LsBlockBases f3LsBlockBases_len
   f3LsBlockBases_lt_codeHi f3LsBlockBases_pos f3LsBlocksLen f3LsBlocksLen_ge_600 f3LsCodeHi
   f3LsCodeHi_lt_2pow64 f3LsDataHi f3LsMpl_relax_false f3LsNamesLen f3LsRoHi f3LsRw1Hi
   f3LsRw1Lo f3LsRw2Hi f3LsRw2Lo f3LsSymAddrs f3Ls_metaCore_ok
   f3Ls_metaData_ok f3Ls_mng_base0_lt f3MallocngMpl_relax_false f3MngCodeHi f3MngCodeLo
   f3MngDataHi f3MngDataLo f3MngRoHi f3MngRoLo f3MngRwHi f3MngRwLo f3NoShimIdx f3NoShim_pin_ok
   f3StaticsPins_ok f3TokenIdx f3TokenPins_ok f3TokenStorageIdx libsignalBlocks_len
   lsDataInStockBandsB lsHookNamesPlaced
   lsInternedMultiLib lsNameChars lsNames lsPlacedCompactLit lsPlacedCompactLit_lt_mngCodeLo
   lsPlacedStubPairs lsPlacedStubPairs_eq lsPlacedTagTableLit lsRelocInvSteps lsSharedExterns
   ls_block617_externs_eq ls_blockSymsMatch_ok ls_ext_ok ls_fast_eq ls_idsOk ls_ids_ok
   ls_namesNodup_ok ls_names_eq ls_names_len ls_names_nodup ls_relocInv_ok ls_sharedExterns_lt
   ls_toMultiPlacedLib_eq mallocngRelocInvSteps mallocngRelocInv_ok)

noncomputable section

abbrev f3TrialElfBytes : List (BitVec 8) := cliElfBytes
abbrev f3TrialElf : ElfImage := cliElfImage
abbrev f3TrialElfSymChars : List (List Char × BitVec 64) := cliElfSymChars
theorem f3TrialElf_parse : ElfImage.parse f3TrialElfBytes = .ok f3TrialElf := cliElf_parse
theorem f3TrialElfSyms_eq :
    f3TrialElf.symbols = ProofLib.ProgramReflection.toStringAssoc f3TrialElfSymChars :=
  cliElf_symbols_eq
theorem mallocngLib_in_f3TrialElf :
    VerifiedLibraries.mallocngLib.Placeable f3MallocngMpl ∧
    VerifiedLibraries.mallocngLib.InElf f3TrialElf f3MallocngMpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint f3MallocngMpl :=
  cliElf_mallocng_placed

/-- Interned `MultiLayout` for `lsInternedMultiLib` matching `f3TrialElf`. -/
abbrev f3LsLayout : Obj.Interned.MultiLayout :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsLayout

/-- Concrete `MultiPlacement` witness for `libsignalSessionLib` in `f3TrialElf`. -/
noncomputable abbrev f3LsMpl : Obj.MultiPlacement :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsMpl

/-- Mangled `alloc::raw_vec::handle_error` symbol name. -/
abbrev f3HandleErrorSym : String :=
  LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3HandleErrorSym

/-! ## Variable-Width Slice Combiner -/

private inductive SlicesTextVarOk (ML : MultiLib) (mly : MultiLayout) (img : ElfImage) :
    Nat → Prop
  | zero : SlicesTextVarOk ML mly img 0
  | step {endIdx count : Nat} :
      SlicesTextVarOk ML mly img endIdx →
      checkMultiTextSliceB ML mly img endIdx count = true →
      SlicesTextVarOk ML mly img (endIdx + count)

private theorem slicesTextVarOk_sound {ML : MultiLib} {mly : MultiLayout} {img : ElfImage}
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

private theorem checkMultiVarSliced_spec {lib : MultiPlacedLib} {ML : MultiLib} {mly : MultiLayout}
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

/-! ## `libsignalSessionLib` Placement, `LinkedAt`, and Uniqueness -/

theorem f3Ls_metaExports_ok :
    Obj.Interned.checkMultiMetaExportsFastB lsInternedMultiLib f3LsLayout
      lsNameChars f3TrialElfSymChars = true := by
  rfl_kernel

theorem f3Ls_meta_ok :
    Obj.Interned.checkMultiMetaFastB lsInternedMultiLib f3LsLayout
      lsNameChars f3TrialElfSymChars = true :=
  Obj.Interned.checkMultiMetaFastB_of_parts
    f3Ls_metaCore_ok f3Ls_metaData_ok f3Ls_metaExports_ok

theorem f3Ls_dataWalk_ok :
    Obj.Interned.checkMultiDataWalkFastB lsInternedMultiLib f3LsLayout f3TrialElf = true := by
  rfl_kernel

theorem f3Ls_blocks_bound :
    Nat.ble lsInternedMultiLib.blocks.length 624 = true := by
  rfl_kernel

theorem f3Ls_textWalk_00 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 0 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_01 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 40 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_02 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 80 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_03 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 120 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_04 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 160 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_05 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 200 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_06 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 240 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_07 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 280 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_08 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 320 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_09 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 360 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_10 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 400 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_11 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 440 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_12 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 480 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_13 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 520 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_14 :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 560 40 = true := by
  rfl_kernel

theorem f3Ls_textWalk_15a :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 600 17 = true := by
  rfl_kernel

theorem f3Ls_textWalk_15b :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 617 1 = true := by
  rfl_kernel

theorem f3Ls_textWalk_15c :
    Obj.Interned.checkMultiTextSliceB lsInternedMultiLib f3LsLayout f3TrialElf 618 6 = true := by
  rfl_kernel

private theorem f3Ls_slicesTextVarOk :
    SlicesTextVarOk lsInternedMultiLib f3LsLayout f3TrialElf 624 :=
  ((((((((((((((((((SlicesTextVarOk.zero.step
    f3Ls_textWalk_00).step
    f3Ls_textWalk_01).step
    f3Ls_textWalk_02).step
    f3Ls_textWalk_03).step
    f3Ls_textWalk_04).step
    f3Ls_textWalk_05).step
    f3Ls_textWalk_06).step
    f3Ls_textWalk_07).step
    f3Ls_textWalk_08).step
    f3Ls_textWalk_09).step
    f3Ls_textWalk_10).step
    f3Ls_textWalk_11).step
    f3Ls_textWalk_12).step
    f3Ls_textWalk_13).step
    f3Ls_textWalk_14).step
    f3Ls_textWalk_15a).step
    f3Ls_textWalk_15b).step
    f3Ls_textWalk_15c)

/-- `Placeable ∧ InElf f3TrialElf ∧ DataDisjoint` for `libsignalSessionLib` at `f3LsMpl`. -/
theorem f3CliElf_libsignal_placed :
    libsignalSessionLib.Placeable f3LsMpl ∧
    libsignalSessionLib.InElf f3TrialElf f3LsMpl ∧
    libsignalSessionLib.DataDisjoint f3LsMpl :=
  checkMultiVarSliced_spec ls_toMultiPlacedLib_eq ls_names_eq f3TrialElfSyms_eq
    f3Ls_meta_ok f3Ls_dataWalk_ok f3Ls_blocks_bound f3Ls_slicesTextVarOk

theorem f3CliElf_libsignal_linkedAt :
    libsignalSessionLib.LinkedAt f3TrialElfBytes f3LsMpl :=
  ⟨f3TrialElf, f3TrialElf_parse, f3CliElf_libsignal_placed.1, f3CliElf_libsignal_placed.2.1⟩

theorem f3CliElf_libsignal_linkedIn :
    libsignalSessionLib.LinkedIn f3TrialElfBytes :=
  ⟨f3LsMpl, f3CliElf_libsignal_linkedAt⟩

/-- Relocation-inversion uniqueness and `DataDisjoint` for any `mpl` with `Placeable mpl` and
`InElf f3TrialElf mpl`. -/
theorem f3CliElf_libsignal_inElf_unique {mpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl) :
    (∀ i < libsignalSessionLib.blocks.length, mpl.base i = f3LsMpl.base i) ∧
    (∀ s ∈ lsInternedMultiLib.names,
      libsignalSessionLib.resolve mpl s = libsignalSessionLib.resolve f3LsMpl s) ∧
    (∀ s ∈ lsInternedMultiLib.names,
      Obj.lookupBlockSym s libsignalSessionLib.blocks = none → mpl.ρ s = f3LsMpl.ρ s) ∧
    libsignalSessionLib.DataDisjoint mpl :=
  Obj.Interned.checkRelocInvStepsB_sound ls_toMultiPlacedLib_eq ls_names_eq
    ls_relocInv_ok f3LsMpl_relax_false f3CliElf_libsignal_placed ⟨hpl, hin⟩

/-- Relocation-inversion uniqueness and `DataDisjoint` for any `mpl` satisfying
`libsignalSessionLib.LinkedAt f3TrialElfBytes mpl`. -/
theorem f3CliElf_libsignal_linkedAt_unique {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl) :
    (∀ i < libsignalSessionLib.blocks.length, mpl.base i = f3LsMpl.base i) ∧
    (∀ s ∈ lsInternedMultiLib.names,
      libsignalSessionLib.resolve mpl s = libsignalSessionLib.resolve f3LsMpl s) ∧
    (∀ s ∈ lsInternedMultiLib.names,
      Obj.lookupBlockSym s libsignalSessionLib.blocks = none → mpl.ρ s = f3LsMpl.ρ s) ∧
    libsignalSessionLib.DataDisjoint mpl := by
  obtain ⟨img, hparse, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hparse
  exact f3CliElf_libsignal_inElf_unique hpl hin

private theorem toMultiPlacement_rho_eq (mly : Obj.Interned.MultiLayout) (names : List String)
    (s : String) :
    (mly.toMultiPlacement names).ρ s = mly.addrs.getD (names.idxOf s) 0#64 := by
  rfl

private theorem f3LsMpl_rho_of_idx {s : String} {idx : Nat}
    (hidx : lsInternedMultiLib.names.idxOf s = idx) :
    f3LsMpl.ρ s = f3LsSymAddrs.getD idx 0#64 := by
  unfold f3LsMpl LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData.f3LsMpl
  rw [toMultiPlacement_rho_eq, hidx]
  rfl

private theorem mem_lsNames_of_getD {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (heq : lsInternedMultiLib.names.getD idx "" = s) :
    s ∈ lsInternedMultiLib.names := by
  rw [← heq, Obj.Interned.getD_of_lt hlt]
  exact List.getElem_mem hlt

private theorem lookupBlockSym_none_of_idx {idx : Nat} {s : String}
    (hlt : idx < lsInternedMultiLib.names.length)
    (heq : lsInternedMultiLib.names.getD idx "" = s)
    (hid : Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks = none) :
    Obj.lookupBlockSym s libsignalSessionLib.blocks = none := by
  rw [← heq, ls_toMultiPlacedLib_eq,
    Obj.Interned.lookupBlockSym_toMultiPlacedLib ls_names_nodup ls_idsOk hlt]
  exact hid

/-- Every placed block base `mpl.base i` (`i < f3LsBlocksLen`) of `libsignalSessionLib` in
`f3TrialElf` is non-zero. -/
theorem f3CliElf_libsignal_base_ne_zero_of_inElf {mpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl)
    (i : Nat) (hi : i < libsignalSessionLib.blocks.length) :
    mpl.base i ≠ 0#64 := by
  have hbase := (f3CliElf_libsignal_inElf_unique hpl hin).1 i hi
  have hlen_ls : libsignalSessionLib.blocks.length = f3LsBlocksLen := Nat.beq_eq.mp libsignalBlocks_len
  have hlen_bs : f3LsBlockBases.length = f3LsBlocksLen := Nat.beq_eq.mp f3LsBlockBases_len
  have hi_bs : i < f3LsBlockBases.length := by omega
  have hbase0 : f3LsMpl.base i = f3LsBlockBases[i] :=
    Obj.Interned.getD_of_lt hi_bs
  have hpos := Nat.blt_eq.mp (List.all_eq_true.mp f3LsBlockBases_pos _ (List.getElem_mem hi_bs))
  rw [hbase, hbase0]
  intro hz
  rw [hz] at hpos
  exact Nat.lt_irrefl 0 hpos

theorem f3CliElf_libsignal_base_ne_zero_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (i : Nat) (hi : i < libsignalSessionLib.blocks.length) :
    mpl.base i ≠ 0#64 := by
  obtain ⟨img, hparse, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hparse
  exact f3CliElf_libsignal_base_ne_zero_of_inElf hpl hin i hi

/-- Block `547` has non-zero base `mpl.base 547 ≠ 0#64` for every `LinkedAt` placement `mpl`. -/
theorem f3CliElf_libsignal_base547_ne_zero_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl) :
    mpl.base 547 ≠ 0#64 := by
  have h547 : 547 < libsignalSessionLib.blocks.length := by
    have hlen : libsignalSessionLib.blocks.length = f3LsBlocksLen := Nat.beq_eq.mp libsignalBlocks_len
    have hge : 600 ≤ f3LsBlocksLen := Nat.ble_eq.mp f3LsBlocksLen_ge_600
    omega
  exact f3CliElf_libsignal_base_ne_zero_of_linkedAt hlink 547 h547

/-- Under `Placeable mpl` and `InElf f3TrialElf mpl`, `mpl.ρ lsRustNoAllocShimSymCli = f3StubNoShimAddr`. -/
theorem f3CliElf_rho_noAllocShim_of_inElf {mpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl) :
    mpl.ρ lsRustNoAllocShimSymCli = f3StubNoShimAddr := by
  have hc := f3NoShim_pin_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨hlt, hname⟩, hid⟩, haddr⟩ := hc
  have hmem := mem_lsNames_of_getD hlt hname
  have hnone := lookupBlockSym_none_of_idx hlt hname hid
  have hρ := (f3CliElf_libsignal_inElf_unique hpl hin).2.2.1 _ hmem hnone
  have hidx : lsInternedMultiLib.names.idxOf lsRustNoAllocShimSymCli = f3NoShimIdx := by
    rw [← hname]
    exact Obj.Interned.idxOf_getD ls_names_nodup hlt
  exact hρ.trans ((f3LsMpl_rho_of_idx hidx).trans haddr)

theorem f3CliElf_rho_noAllocShim_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl) :
    mpl.ρ lsRustNoAllocShimSymCli = f3StubNoShimAddr := by
  obtain ⟨img, hparse, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hparse
  exact f3CliElf_rho_noAllocShim_of_inElf hpl hin

/-- Under `Placeable mpl` and `InElf f3TrialElf mpl`, `mpl.ρ f3HandleErrorSym` agrees with
`f3LsMpl.ρ f3HandleErrorSym`. -/
theorem f3CliElf_rho_handleError_eq_of_inElf {mpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl) :
    mpl.ρ f3HandleErrorSym = f3LsMpl.ρ f3HandleErrorSym := by
  have hc := f3HandleError_pin_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  obtain ⟨⟨hlt, hname⟩, hid⟩ := hc
  exact (f3CliElf_libsignal_inElf_unique hpl hin).2.2.1 _
    (mem_lsNames_of_getD hlt hname) (lookupBlockSym_none_of_idx hlt hname hid)

theorem f3CliElf_rho_handleError_eq_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl) :
    mpl.ρ f3HandleErrorSym = f3LsMpl.ρ f3HandleErrorSym := by
  obtain ⟨img, hparse, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hparse
  exact f3CliElf_rho_handleError_eq_of_inElf hpl hin

/-! ## `VerifiedLibraries.mallocngLib` Placement and Uniqueness -/

/-- `Placeable ∧ InElf f3TrialElf ∧ DataDisjoint` for `VerifiedLibraries.mallocngLib` at
`f3MallocngMpl`. -/
theorem f3CliElf_mallocng_placed :
    VerifiedLibraries.mallocngLib.Placeable f3MallocngMpl ∧
    VerifiedLibraries.mallocngLib.InElf f3TrialElf f3MallocngMpl ∧
    VerifiedLibraries.mallocngLib.DataDisjoint f3MallocngMpl :=
  mallocngLib_in_f3TrialElf

theorem f3CliElf_mallocng_linkedAt :
    VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes f3MallocngMpl :=
  ⟨f3TrialElf, f3TrialElf_parse, f3CliElf_mallocng_placed.1, f3CliElf_mallocng_placed.2.1⟩

theorem f3CliElf_mallocng_linkedIn :
    VerifiedLibraries.mallocngLib.LinkedIn f3TrialElfBytes :=
  ⟨f3MallocngMpl, f3CliElf_mallocng_linkedAt⟩

/-- Relocation-inversion uniqueness and `DataDisjoint` for any `InElf f3TrialElf` placement of
`VerifiedLibraries.mallocngLib`. -/
theorem f3CliElf_mallocng_inElf_unique {mmpl : Obj.MultiPlacement}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin : VerifiedLibraries.mallocngLib.InElf f3TrialElf mmpl) :
    (∀ i < VerifiedLibraries.mallocngLib.blocks.length,
      mmpl.base i = f3MallocngMpl.base i) ∧
    (∀ s ∈ mallocngMultiL.names,
      VerifiedLibraries.mallocngLib.resolve mmpl s =
        VerifiedLibraries.mallocngLib.resolve f3MallocngMpl s) ∧
    (∀ s ∈ mallocngMultiL.names,
      Obj.lookupBlockSym s VerifiedLibraries.mallocngLib.blocks = none →
        mmpl.ρ s = f3MallocngMpl.ρ s) ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl :=
  Obj.Interned.checkRelocInvStepsB_sound mallocngMultiL_toMultiPlacedLib.symm mallocngMultiL_names
    mallocngRelocInv_ok f3MallocngMpl_relax_false f3CliElf_mallocng_placed ⟨hpl, hin⟩

theorem f3CliElf_mallocng_linkedAt_unique {mmpl : Obj.MultiPlacement}
    (hlink : VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes mmpl) :
    (∀ i < VerifiedLibraries.mallocngLib.blocks.length,
      mmpl.base i = f3MallocngMpl.base i) ∧
    (∀ s ∈ mallocngMultiL.names,
      VerifiedLibraries.mallocngLib.resolve mmpl s =
        VerifiedLibraries.mallocngLib.resolve f3MallocngMpl s) ∧
    (∀ s ∈ mallocngMultiL.names,
      Obj.lookupBlockSym s VerifiedLibraries.mallocngLib.blocks = none →
        mmpl.ρ s = f3MallocngMpl.ρ s) ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl := by
  obtain ⟨img, hparse, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hparse
  exact f3CliElf_mallocng_inElf_unique hpl hin

theorem f3CliElf_mallocng_dataDisjoint_of_linkedAt {mmpl : Obj.MultiPlacement}
    (hlink : VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes mmpl) :
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl :=
  (f3CliElf_mallocng_linkedAt_unique hlink).2.2.2

theorem f3CliElf_mallocng_dataInit_of_linkedAt {mmpl : Obj.MultiPlacement}
    {inputs : ProcessInputs} {s : State}
    (hlink : VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes mmpl)
    (hload : f3TrialElf.loadState inputs = .ok s) :
    s.mem ⊨ VerifiedLibraries.mallocngLib.dataInit mmpl := by
  obtain ⟨img, hparse, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hparse
  exact VerifiedLibraries.mallocngLib.satisfies_dataInit_of_inElf hpl hin hload
    (Nat.zero_lt_succ 23) (f3CliElf_mallocng_inElf_unique hpl hin).2.2.2

/-- Under `Placeable mmpl` and `InElf f3TrialElf mmpl`, `mmpl.ρ "__libc" = f3StdLayout.libcAddr`. -/
theorem f3CliElf_mallocng_libc_eq_of_inElf {mmpl : Obj.MultiPlacement}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin : VerifiedLibraries.mallocngLib.InElf f3TrialElf mmpl) :
    mmpl.ρ "__libc" = f3StdLayout.libcAddr := by
  have hc := checkMallocngLibcPin_ok
  simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hc
  obtain ⟨⟨hmem, hnone⟩, hρ0⟩ := hc
  exact ((f3CliElf_mallocng_inElf_unique hpl hin).2.2.1 "__libc" hmem hnone).trans hρ0

theorem f3CliElf_mallocng_libc_eq_of_linkedAt {mmpl : Obj.MultiPlacement}
    (hlink : VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes mmpl) :
    mmpl.ρ "__libc" = f3StdLayout.libcAddr := by
  obtain ⟨img, hparse, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hparse
  exact f3CliElf_mallocng_libc_eq_of_inElf hpl hin

/-! ## Cross-Library Code and Data Disjointness -/

private theorem toNat_add_ofNat_of_lt {b : BitVec 64} {k : Nat}
    (hlt : b.toNat + k < 18446744073709551616) :
    (b + BitVec.ofNat 64 k).toNat = b.toNat + k := by
  have hpow : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hk : k < 2 ^ 64 := by omega
  have hlt' : b.toNat + k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt']

private theorem not_inRegion_of_sep {b₁ b₂ a : BitVec 64} {n₁ n₂ : Nat}
    (hsep : b₁.toNat + n₁ ≤ b₂.toNat)
    (hbound₂ : b₂.toNat + n₂ ≤ 18446744073709551616)
    (h₁ : InRegion b₁ n₁ a) (h₂ : InRegion b₂ n₂ a) : False := by
  obtain ⟨hk₁, heq₁⟩ := inRegion_offset h₁
  obtain ⟨hk₂, heq₂⟩ := inRegion_offset h₂
  have ht₁ : (b₁ + BitVec.ofNat 64 (a - b₁).toNat).toNat = b₁.toNat + (a - b₁).toNat :=
    toNat_add_ofNat_of_lt (b := b₁) (k := (a - b₁).toNat) (by omega)
  rw [heq₁] at ht₁
  have ht₂ : (b₂ + BitVec.ofNat 64 (a - b₂).toNat).toNat = b₂.toNat + (a - b₂).toNat :=
    toNat_add_ofNat_of_lt (b := b₂) (k := (a - b₂).toNat) (by omega)
  rw [heq₂] at ht₂
  omega

private theorem length_patched_eq_div4 (blk : CodeBlock) (pl : Placement) :
    (blk.patched pl).length = 4 * (blk.code.length / 4) := by
  have h4 : ∀ w : BitVec 32, (bytesOfWordLE w).length = 4 := fun _ => rfl
  have hflat : ∀ (xs : List Nat),
      (xs.flatMap fun j => bytesOfWordLE (blk.patchedWord pl (4 * j))).length = 4 * xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons _ xs ih =>
      rw [List.flatMap_cons, List.length_append, h4, ih, List.length_cons]
      omega
  unfold CodeBlock.patched
  rw [hflat, List.length_range]

private theorem length_patched_of_mod4 (blk : CodeBlock) (pl : Placement)
    (h : blk.code.length % 4 = 0) :
    (blk.patched pl).length = blk.code.length := by
  rw [length_patched_eq_div4]
  omega

private theorem head?_drop_of_lt {α : Type} :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length), (xs.drop i).head? = some xs[i]
  | [], _, hi => nomatch hi
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, hi => head?_drop_of_lt xs i (Nat.lt_of_succ_lt_succ hi)

private def cellAtFastAux (rws : List (Snapshot.Region × Nat)) (a : BitVec 64) :
    Option (Option Perm × BitVec 8) :=
  rws.findSome? fun (r, len) =>
    let i := (a - r.start).toNat
    if Nat.blt i len then
      match (Arm64.Process.fastDrop i r.bytes).head? with
      | some b => some (some r.perm, b)
      | none => none
    else none

private theorem cellAtFastAux_eq (regions : List Snapshot.Region) (a : BitVec 64) :
    cellAtFastAux (regions.map fun r => (r, r.bytes.length)) a =
      Snapshot.cellAt regions a := by
  induction regions with
  | nil => rfl
  | cons r rs ih =>
    by_cases hi : (a - r.start).toNat < r.bytes.length
    · have hblt : Nat.blt (a - r.start).toNat r.bytes.length = true := by
        rw [Nat.blt_eq]; exact hi
      rw [Obj.Interned.cellAt_cons_hit hi]
      simp only [List.map_cons, cellAtFastAux, List.findSome?_cons, hblt, ↓reduceIte,
        Arm64.Process.fastDrop_eq_drop, head?_drop_of_lt r.bytes _ hi]
    · have hblt : Nat.blt (a - r.start).toNat r.bytes.length = false := by
        rw [Bool.eq_false_iff, Ne, Nat.blt_eq]; exact hi
      rw [Obj.Interned.cellAt_cons_miss (by omega), ← ih]
      simp only [List.map_cons, cellAtFastAux, List.findSome?_cons, hblt, Bool.false_eq_true,
        ↓reduceIte]

private def checkLsBlocksUpperB : List (BitVec 64) → List Obj.Interned.Block → Bool
  | [], [] => true
  | b :: bs, blk :: blks =>
    Nat.ble (b.toNat + Arm64.Process.fastLen512 512 blk.code) f3LsCodeHi &&
    checkLsBlocksUpperB bs blks
  | _, _ => false

private theorem checkLsBlocksUpper_ok :
    checkLsBlocksUpperB f3LsBlockBases lsInternedMultiLib.blocks = true := by
  rfl_kernel

private theorem checkLsBlocksUpperB_sound :
    ∀ (bs : List (BitVec 64)) (blks : List Obj.Interned.Block),
      checkLsBlocksUpperB bs blks = true →
      ∀ (i : Nat) (hi_b : i < bs.length) (hi_k : i < blks.length),
        bs[i].toNat + blks[i].code.length ≤ f3LsCodeHi
  | [], [], _, _, _, hi_k => nomatch hi_k
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h
  | _ :: _, _ :: _, h, 0, _, _ => by
    simp only [checkLsBlocksUpperB, Bool.and_eq_true, Nat.ble_eq,
      Arm64.Process.fastLen512_eq_length, List.getElem_cons_zero] at h ⊢
    exact h.1
  | _ :: bs, _ :: blks, h, i + 1, hi_b, hi_k => by
    simp only [checkLsBlocksUpperB, Bool.and_eq_true] at h
    simpa only [List.getElem_cons_succ] using
      checkLsBlocksUpperB_sound bs blks h.2 i
        (Nat.lt_of_succ_lt_succ hi_b) (Nat.lt_of_succ_lt_succ hi_k)

/-- Every block `i < f3LsBlocksLen` of `libsignalSessionLib` under `f3LsMpl` ends at or below
`f3LsCodeHi`. -/
theorem f3CliElf_libsignal_code_upper (i : Nat)
    (hi : i < libsignalSessionLib.blocks.length) :
    (f3LsMpl.base i).toNat + libsignalSessionLib.blocks[i].code.length ≤ f3LsCodeHi := by
  have hlen_ls : libsignalSessionLib.blocks.length = f3LsBlocksLen := Nat.beq_eq.mp libsignalBlocks_len
  have hlen_bs : f3LsBlockBases.length = f3LsBlocksLen := Nat.beq_eq.mp f3LsBlockBases_len
  have hlen_int : lsInternedMultiLib.blocks.length = libsignalSessionLib.blocks.length := by
    rw [ls_toMultiPlacedLib_eq, Obj.Interned.MultiLib.toMultiPlacedLib_blocks, List.length_map]
  have hi_bs : i < f3LsBlockBases.length := by omega
  have hi_int : i < lsInternedMultiLib.blocks.length := by omega
  have hbase_nat : (f3LsMpl.base i).toNat = (f3LsBlockBases[i]'hi_bs).toNat :=
    congrArg BitVec.toNat (Obj.Interned.getD_of_lt hi_bs)
  have hcode_eq : (libsignalSessionLib.blocks[i]'hi).code.length =
      (lsInternedMultiLib.blocks[i]'hi_int).code.length := by
    simp only [ls_toMultiPlacedLib_eq, Obj.Interned.MultiLib.toMultiPlacedLib_blocks,
      List.getElem_map, Obj.Interned.Block.toCodeBlock]
  calc (f3LsMpl.base i).toNat + (libsignalSessionLib.blocks[i]'hi).code.length
      = (f3LsBlockBases[i]'hi_bs).toNat + (lsInternedMultiLib.blocks[i]'hi_int).code.length :=
        congrArg₂ (· + ·) hbase_nat hcode_eq
    _ ≤ f3LsCodeHi :=
        checkLsBlocksUpperB_sound f3LsBlockBases lsInternedMultiLib.blocks
          checkLsBlocksUpper_ok i hi_bs hi_int

theorem f3CliElf_mallocng_code_bounds_of_inElf {mmpl : Obj.MultiPlacement}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin : VerifiedLibraries.mallocngLib.InElf f3TrialElf mmpl)
    (j : Nat) (hj : j < VerifiedLibraries.mallocngLib.blocks.length) :
    f3LsCodeHi ≤ f3MngCodeLo ∧
    f3MngCodeHi ≤ 18446744073709551616 ∧
    f3MngCodeLo ≤ (mmpl.base j).toNat ∧
    (mmpl.base j).toNat + VerifiedLibraries.mallocngLib.blocks[j].code.length ≤ f3MngCodeHi := by
  have hchk := checkMallocngCodeBounds_ok
  unfold checkMallocngCodeBoundsB at hchk
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hchk
  obtain ⟨⟨⟨hlen24, hsep⟩, hhi64⟩, hall⟩ := hchk
  have hj24 : j < 24 := by omega
  have hj_ok := List.all_eq_true.mp hall j (List.mem_range.mpr hj24)
  simp only [Bool.and_eq_true, Nat.ble_eq, Obj.Interned.getD_of_lt hj] at hj_ok
  have hbase := (f3CliElf_mallocng_inElf_unique hpl hin).1 j hj
  rw [hbase]
  exact ⟨hsep, hhi64, hj_ok.1, hj_ok.2⟩

/-- Distinctness `mpl ≠ mmpl` whenever `mpl` links `libsignalSessionLib` and `mmpl` links
`mallocngLib` in `f3TrialElfBytes`. -/
theorem f3CliElf_libsignal_mallocng_ne {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes mmpl) :
    mpl ≠ mmpl := by
  intro heq
  have h0_ls : 0 < libsignalSessionLib.blocks.length := by
    have h := Nat.beq_eq.mp libsignalBlocks_len
    have hge := Nat.ble_eq.mp f3LsBlocksLen_ge_600
    omega
  have h0_mng : 0 < VerifiedLibraries.mallocngLib.blocks.length := Nat.zero_lt_succ 23
  have hb_ls := (f3CliElf_libsignal_linkedAt_unique hls).1 0 h0_ls
  have hb_mng := (f3CliElf_mallocng_linkedAt_unique hmng).1 0 h0_mng
  have hlt := Nat.blt_eq.mp f3Ls_mng_base0_lt
  rw [← hb_ls, heq, hb_mng] at hlt
  exact Nat.lt_irrefl _ hlt

/-- Cross-library code-block disjointness for any `InElf` placements `(mpl, mmpl)` on
`f3TrialElf`. -/
theorem f3CliElf_libsignal_mallocng_code_disjoint_of_inElf {mpl mmpl : Obj.MultiPlacement}
    (hpl₁ : libsignalSessionLib.Placeable mpl)
    (hin₁ : libsignalSessionLib.InElf f3TrialElf mpl)
    (hpl₂ : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin₂ : VerifiedLibraries.mallocngLib.InElf f3TrialElf mmpl)
    (i : Nat) (hi : i < libsignalSessionLib.blocks.length)
    (j : Nat) (hj : j < VerifiedLibraries.mallocngLib.blocks.length)
    (a : BitVec 64)
    (ha₁ : InRegion (mpl.base i) libsignalSessionLib.blocks[i].code.length a) :
    ¬ InRegion (mmpl.base j) VerifiedLibraries.mallocngLib.blocks[j].code.length a := by
  intro ha₂
  have hb₁ := (f3CliElf_libsignal_inElf_unique hpl₁ hin₁).1 i hi
  rw [hb₁] at ha₁
  have hls := f3CliElf_libsignal_code_upper i hi
  obtain ⟨hsep, hhi64, hm_lo, hm_hi⟩ := f3CliElf_mallocng_code_bounds_of_inElf hpl₂ hin₂ j hj
  exact not_inRegion_of_sep (by omega) (by omega) ha₁ ha₂

theorem f3CliElf_libsignal_mallocng_code_disjoint_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes mmpl)
    (i : Nat) (hi : i < libsignalSessionLib.blocks.length)
    (j : Nat) (hj : j < VerifiedLibraries.mallocngLib.blocks.length)
    (a : BitVec 64)
    (ha₁ : InRegion (mpl.base i) libsignalSessionLib.blocks[i].code.length a) :
    ¬ InRegion (mmpl.base j) VerifiedLibraries.mallocngLib.blocks[j].code.length a := by
  obtain ⟨_, hp₁, hpl₁, hin₁⟩ := hls
  obtain ⟨_, hp₂, hpl₂, hin₂⟩ := hmng
  cases f3TrialElf_parse.symm.trans hp₁
  cases f3TrialElf_parse.symm.trans hp₂
  exact f3CliElf_libsignal_mallocng_code_disjoint_of_inElf hpl₁ hin₁ hpl₂ hin₂ i hi j hj a ha₁

/-- 5-band cross-library data disjointness across all `(d₁, d₂)` pairs (RO and RW, leaving trusted
`Arm64.Obj.MultiPlacedLib.DataDisjoint` completely untouched) for any `InElf` placements `(mpl, mmpl)`
on `f3TrialElf`: `d₁` lies in `[0, f3LsRoHi)` (`.rodata`), `[f3LsRw1Lo, f3LsRw1Hi)` (`.data`), or
`[f3LsRw2Lo, f3LsRw2Hi)` (`.bss`); `d₂` lies in `[f3MngRoLo, f3MngRoHi)` or `[f3MngRwLo, f3MngRwHi)`. -/
theorem f3CliElf_libsignal_mallocng_data_disjoint_of_inElf {mpl mmpl : Obj.MultiPlacement}
    (hpl₁ : libsignalSessionLib.Placeable mpl)
    (hin₁ : libsignalSessionLib.InElf f3TrialElf mpl)
    (hpl₂ : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin₂ : VerifiedLibraries.mallocngLib.InElf f3TrialElf mmpl)
    {d₁ : SymDataInfo} (hd₁ : d₁ ∈ libsignalSessionLib.data)
    {d₂ : SymDataInfo} (hd₂ : d₂ ∈ VerifiedLibraries.mallocngLib.data)
    (a : BitVec 64)
    (ha₁ : InRegion (mpl.ρ d₁.sym) (libsignalSessionLib.patchedData mpl d₁).length a) :
    ¬ InRegion (mmpl.ρ d₂.sym) (VerifiedLibraries.mallocngLib.patchedData mmpl d₂).length a := by
  intro ha₂
  have hd₁_int : d₁ ∈ lsInternedMultiLib.toMultiPlacedLib.data := ls_toMultiPlacedLib_eq ▸ hd₁
  rw [Obj.Interned.MultiLib.toMultiPlacedLib_data, List.mem_map] at hd₁_int
  obtain ⟨di, hdi_mem, hdi_eq⟩ := hd₁_int
  have hls_chk := List.all_eq_true.mp checkLsDataBounds_ok di hdi_mem
  unfold lsDataInStockBandsB at hls_chk
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at hls_chk
  obtain ⟨hdi_lt, hls_bands⟩ := hls_chk
  have hsym₁ : d₁.sym = lsInternedMultiLib.names.getD di.sym "" := by
    rw [← hdi_eq]; rfl
  have hbytes₁ : d₁.bytes.length + d₁.zeroTail = di.bytes.length + di.zeroTail := by
    rw [← hdi_eq]; rfl
  have hmem₁ := mem_lsNames_of_getD hdi_lt hsym₁.symm
  have hnone₁ := (hpl₁.data_ok d₁ hd₁).1
  have hρ₁ := (f3CliElf_libsignal_inElf_unique hpl₁ hin₁).2.2.1 d₁.sym hmem₁ hnone₁
  have hidx₁ : lsInternedMultiLib.names.idxOf d₁.sym = di.sym := by
    rw [hsym₁]
    exact Obj.Interned.idxOf_getD ls_names_nodup hdi_lt
  have hρ₁_val := hρ₁.trans (f3LsMpl_rho_of_idx hidx₁)
  have hplen₁ := Obj.Interned.length_patchedData_multi (lib := libsignalSessionLib) (mpl := mpl)
    (fun r hr => (hpl₁.data_relocs_ok d₁ hd₁ r hr).2.1)

  have hmng_chk := checkMallocngDataBounds_ok
  unfold checkMallocngDataBoundsB at hmng_chk
  simp only [Bool.and_eq_true, Nat.ble_eq] at hmng_chk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb01, hb12⟩, hb23⟩, hb34⟩, hb45⟩, hb5c⟩, hbc6⟩, hb56⟩, hb67⟩, hb78⟩, hb89⟩, hall_mng⟩ := hmng_chk
  have hd₂_chk := List.all_eq_true.mp hall_mng d₂ hd₂
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem, Nat.ble_eq] at hd₂_chk
  obtain ⟨hmem₂, hm_bands⟩ := hd₂_chk
  have hρ₂ := (f3CliElf_mallocng_inElf_unique hpl₂ hin₂).2.2.1 d₂.sym hmem₂ (hpl₂.data_ok d₂ hd₂).1
  have hplen₂ := Obj.Interned.length_patchedData_multi
    (lib := VerifiedLibraries.mallocngLib) (mpl := mmpl)
    (fun r hr => (hpl₂.data_relocs_ok d₂ hd₂ r hr).2.1)

  rw [hρ₁_val, hplen₁, hbytes₁] at ha₁
  rw [hρ₂, hplen₂] at ha₂
  rcases hls_bands with (hls_ro | ⟨hls_rw1_lo, hls_rw1_hi⟩) | ⟨hls_rw2_lo, hls_rw2_hi⟩ <;>
    rcases hm_bands with ⟨hm_ro_lo, hm_ro_hi⟩ | ⟨⟨_, hm_rw_lo⟩, hm_rw_hi⟩
  · exact not_inRegion_of_sep (by omega) (by omega) ha₁ ha₂
  · exact not_inRegion_of_sep (by omega) (by omega) ha₁ ha₂
  · exact not_inRegion_of_sep (by omega) (by omega) ha₂ ha₁
  · exact not_inRegion_of_sep (by omega) (by omega) ha₁ ha₂
  · exact not_inRegion_of_sep (by omega) (by omega) ha₂ ha₁
  · exact not_inRegion_of_sep (by omega) (by omega) ha₂ ha₁

theorem f3CliElf_libsignal_mallocng_data_disjoint_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes mmpl)
    {d₁ : SymDataInfo} (hd₁ : d₁ ∈ libsignalSessionLib.data)
    {d₂ : SymDataInfo} (hd₂ : d₂ ∈ VerifiedLibraries.mallocngLib.data)
    (a : BitVec 64)
    (ha₁ : InRegion (mpl.ρ d₁.sym) (libsignalSessionLib.patchedData mpl d₁).length a) :
    ¬ InRegion (mmpl.ρ d₂.sym) (VerifiedLibraries.mallocngLib.patchedData mmpl d₂).length a := by
  obtain ⟨_, hp₁, hpl₁, hin₁⟩ := hls
  obtain ⟨_, hp₂, hpl₂, hin₂⟩ := hmng
  cases f3TrialElf_parse.symm.trans hp₁
  cases f3TrialElf_parse.symm.trans hp₂
  exact f3CliElf_libsignal_mallocng_data_disjoint_of_inElf hpl₁ hin₁ hpl₂ hin₂ hd₁ hd₂ a ha₁

/-- Stock RW sub-band framing: on stock `ld.lld` (where `PT_LOAD[3]` is shared between `libsignal`
and `mallocng`/`musl` RW data), every `d₁ ∈ libsignalSessionLib.data` is byte-disjoint from both
every `mallocngLib` RW global AND the `104`-byte `"__libc"` struct `[mmpl.ρ "__libc", +104)`. -/
theorem stockCliElf_rw_mallocng_disjoint {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes mmpl)
    {d₁ : SymDataInfo} (hd₁ : d₁ ∈ libsignalSessionLib.data) :
    (∀ d₂ ∈ VerifiedLibraries.mallocngLib.data, d₂.readOnly = false →
      ∀ a, InRegion (mpl.ρ d₁.sym) (libsignalSessionLib.patchedData mpl d₁).length a →
        ¬ InRegion (mmpl.ρ d₂.sym)
            (VerifiedLibraries.mallocngLib.patchedData mmpl d₂).length a) ∧
    (∀ a, InRegion (mpl.ρ d₁.sym) (libsignalSessionLib.patchedData mpl d₁).length a →
      ¬ InRegion (mmpl.ρ "__libc") 104 a) := by
  refine ⟨fun d₂ hd₂ _ a ha₁ =>
    f3CliElf_libsignal_mallocng_data_disjoint_of_linkedAt hls hmng hd₁ hd₂ a ha₁, ?_⟩
  obtain ⟨_, hp₁, hpl₁, hin₁⟩ := hls
  obtain ⟨_, hp₂, hpl₂, hin₂⟩ := hmng
  cases f3TrialElf_parse.symm.trans hp₁
  cases f3TrialElf_parse.symm.trans hp₂
  intro a ha₁ ha₂
  have hd₁_int : d₁ ∈ lsInternedMultiLib.toMultiPlacedLib.data := ls_toMultiPlacedLib_eq ▸ hd₁
  rw [Obj.Interned.MultiLib.toMultiPlacedLib_data, List.mem_map] at hd₁_int
  obtain ⟨di, hdi_mem, hdi_eq⟩ := hd₁_int
  have hls_chk := List.all_eq_true.mp checkLsDataBounds_ok di hdi_mem
  unfold lsDataInStockBandsB at hls_chk
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at hls_chk
  obtain ⟨hdi_lt, hls_bands⟩ := hls_chk
  have hsym₁ : d₁.sym = lsInternedMultiLib.names.getD di.sym "" := by rw [← hdi_eq]; rfl
  have hbytes₁ : d₁.bytes.length + d₁.zeroTail = di.bytes.length + di.zeroTail := by rw [← hdi_eq]; rfl
  have hmem₁ := mem_lsNames_of_getD hdi_lt hsym₁.symm
  have hρ₁ := (f3CliElf_libsignal_inElf_unique hpl₁ hin₁).2.2.1 d₁.sym hmem₁ (hpl₁.data_ok d₁ hd₁).1
  have hidx₁ : lsInternedMultiLib.names.idxOf d₁.sym = di.sym := by
    rw [hsym₁]; exact Obj.Interned.idxOf_getD ls_names_nodup hdi_lt
  have hρ₁_val := hρ₁.trans (f3LsMpl_rho_of_idx hidx₁)
  have hplen₁ := Obj.Interned.length_patchedData_multi (lib := libsignalSessionLib) (mpl := mpl)
    (fun r hr => (hpl₁.data_relocs_ok d₁ hd₁ r hr).2.1)
  have hmng_chk := checkMallocngDataBounds_ok
  unfold checkMallocngDataBoundsB at hmng_chk
  simp only [Bool.and_eq_true, Nat.ble_eq] at hmng_chk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb01, hb12⟩, hb23⟩, hb34⟩, hb45⟩, hb5c⟩, hbc6⟩, hb56⟩, hb67⟩, hb78⟩, hb89⟩, _⟩ := hmng_chk
  have hlibc := f3CliElf_mallocng_libc_eq_of_inElf hpl₂ hin₂
  rw [hρ₁_val, hplen₁, hbytes₁] at ha₁
  rw [hlibc] at ha₂
  rcases hls_bands with (hls_ro | ⟨hls_rw1_lo, hls_rw1_hi⟩) | ⟨hls_rw2_lo, hls_rw2_hi⟩
  · exact not_inRegion_of_sep (by omega) (by omega) ha₁ ha₂
  · exact not_inRegion_of_sep (by omega) (by omega) ha₁ ha₂
  · exact not_inRegion_of_sep (by omega) (by omega) ha₂ ha₁

/-! ## Placement Independence of `externAt?`, `cliTokenPatchPlaced`, and `CliRunsToPlaced` -/

/-- `cliTokenPatchPlaced mpl = cliTokenPatchPlaced f3LsMpl` for any `InElf` placement `mpl`. -/
theorem cliTokenPatchPlaced_eq_of_inElf {mpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl) :
    cliTokenPatchPlaced mpl = cliTokenPatchPlaced f3LsMpl := by
  have hc := f3TokenPins_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hlt1, hn1⟩, hid1⟩, hlt2⟩, hn2⟩, hid2⟩ := hc
  have hρ := (f3CliElf_libsignal_inElf_unique hpl hin).2.2.1
  have h1 := hρ _ (mem_lsNames_of_getD hlt1 hn1) (lookupBlockSym_none_of_idx hlt1 hn1 hid1)
  have h2 := hρ _ (mem_lsNames_of_getD hlt2 hn2) (lookupBlockSym_none_of_idx hlt2 hn2 hid2)
  funext s
  unfold cliTokenPatchPlaced
  rw [h1, h2]

theorem cliTokenPatchPlaced_eq_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl) :
    cliTokenPatchPlaced mpl = cliTokenPatchPlaced f3LsMpl := by
  obtain ⟨_, hp, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hp
  exact cliTokenPatchPlaced_eq_of_inElf hpl hin

/-- Uniqueness of `mpl.ρ` on all five `cliStaticsPlacedAt` and `CliElfTokenCellsPlacedAt`
read-write statics across `InElf` placements on `f3TrialElf`. -/
theorem f3CliElf_statics_rho_eq_of_inElf {mpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl) :
    mpl.ρ CryptoVerification.lsLogFilterSym = f3LsMpl.ρ CryptoVerification.lsLogFilterSym ∧
    mpl.ρ "libsignal_cli::coins::NEXT.0" = f3LsMpl.ρ "libsignal_cli::coins::NEXT.0" ∧
    mpl.ρ "libsignal_cli::coins::LEFT.0" = f3LsMpl.ρ "libsignal_cli::coins::LEFT.0" ∧
    mpl.ρ tokenStorageName = f3LsMpl.ρ tokenStorageName ∧
    mpl.ρ tokenName = f3LsMpl.ρ tokenName := by
  have hcT := f3TokenPins_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hcT
  obtain ⟨⟨⟨⟨⟨hltT, hnT⟩, hidT⟩, hltS⟩, hnS⟩, hidS⟩ := hcT
  have hcS := f3StaticsPins_ok
  simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hcS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hltL, hnL⟩, hidL⟩, hltN⟩, hnN⟩, hidN⟩, hltC⟩, hnC⟩, hidC⟩ := hcS
  have hρ := (f3CliElf_libsignal_inElf_unique hpl hin).2.2.1
  exact ⟨hρ _ (mem_lsNames_of_getD hltL hnL) (lookupBlockSym_none_of_idx hltL hnL hidL),
    hρ _ (mem_lsNames_of_getD hltN hnN) (lookupBlockSym_none_of_idx hltN hnN hidN),
    hρ _ (mem_lsNames_of_getD hltC hnC) (lookupBlockSym_none_of_idx hltC hnC hidC),
    hρ _ (mem_lsNames_of_getD hltS hnS) (lookupBlockSym_none_of_idx hltS hnS hidS),
    hρ _ (mem_lsNames_of_getD hltT hnT) (lookupBlockSym_none_of_idx hltT hnT hidT)⟩

theorem f3CliElf_statics_rho_eq_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl) :
    mpl.ρ CryptoVerification.lsLogFilterSym = f3LsMpl.ρ CryptoVerification.lsLogFilterSym ∧
    mpl.ρ "libsignal_cli::coins::NEXT.0" = f3LsMpl.ρ "libsignal_cli::coins::NEXT.0" ∧
    mpl.ρ "libsignal_cli::coins::LEFT.0" = f3LsMpl.ρ "libsignal_cli::coins::LEFT.0" ∧
    mpl.ρ tokenStorageName = f3LsMpl.ρ tokenStorageName ∧
    mpl.ρ tokenName = f3LsMpl.ρ tokenName := by
  obtain ⟨_, hp, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hp
  exact f3CliElf_statics_rho_eq_of_inElf hpl hin

private theorem step_iff_of_externAt_pc {p₁ p₂ : Program} {s s' : State}
    (hpc : p₁.externAt? s.pc = p₂.externAt? s.pc) (hsvc : p₁.svc = p₂.svc) :
    Step p₁ s s' ↔ Step p₂ s s' := by
  have hfetch : p₁.fetchMem s.mem s.pc = p₂.fetchMem s.mem s.pc := by
    unfold Program.fetchMem; rw [hpc]
  have heval : ∀ inst, p₁.evalInst inst s = p₂.evalInst inst s := by
    intro inst; unfold Program.evalInst; rw [hsvc]
  constructor <;> intro h <;> cases h
  · rename_i inst hrun hf; rw [hfetch] at hf; rw [heval]; exact Step.exec hrun hf
  · rename_i hrun hf he; rw [hfetch] at hf; rw [hpc] at he; exact Step.halt_unmapped hrun hf he
  · rename_i f hrun he hk hs; rw [hpc] at he; exact Step.extern hrun he hk hs
  · rename_i f hrun he hnk; rw [hpc] at he; exact Step.extern_fault hrun he hnk
  · rename_i inst hrun hf; rw [← hfetch] at hf; rw [← heval]; exact Step.exec hrun hf
  · rename_i hrun hf he; rw [← hfetch] at hf; rw [← hpc] at he; exact Step.halt_unmapped hrun hf he
  · rename_i f hrun he hk hs; rw [← hpc] at he; exact Step.extern hrun he hk hs
  · rename_i f hrun he hnk; rw [← hpc] at he; exact Step.extern_fault hrun he hnk

private theorem steps_iff_of_externAt_eq {p₁ p₂ : Program}
    (hext : ∀ pc, p₁.externAt? pc = p₂.externAt? pc) (hsvc : p₁.svc = p₂.svc)
    (s s' : State) : Steps p₁ s s' ↔ Steps p₂ s s' := by
  constructor <;> intro h <;> induction h with
  | refl s => exact Steps.refl s
  | step h1 _ ih =>
    first
    | exact Steps.step ((step_iff_of_externAt_pc (hext _) hsvc).mp h1) ih
    | exact Steps.step ((step_iff_of_externAt_pc (hext _) hsvc).mpr h1) ih

private theorem processRunsTo_iff_of_externAt_eq {p₁ p₂ : Program}
    (hext : ∀ pc, p₁.externAt? pc = p₂.externAt? pc) (hsvc : p₁.svc = p₂.svc)
    (s0 : State) (post : Process.ProcessOutcome → Prop) (oom : State → Prop) :
    Process.ProcessRunsTo p₁ s0 post oom ↔ Process.ProcessRunsTo p₂ s0 post oom := by
  have hsteps : ∀ a b, Steps p₁ a b ↔ Steps p₂ a b := steps_iff_of_externAt_eq hext hsvc
  have hexits : ∀ out, Process.ProcessExitsWith p₁ s0 out ↔ Process.ProcessExitsWith p₂ s0 out := by
    intro out; unfold Process.ProcessExitsWith; simp only [hsteps]
  unfold Process.ProcessRunsTo Process.ProcessTerminates Process.ProcessPartialRunsTo
  simp only [hexits, hsteps, step_iff_of_externAt_pc (hext _) hsvc]

theorem externAt?_cliProgPlacedSig (mpl mmpl : Obj.MultiPlacement) (W : CliHooks)
    (pc : BitVec 64) :
    (cliProgPlacedSig mpl mmpl W).externAt? pc =
      (libsignalSessionLib.blockLib 617).text.externs.findSome? fun e =>
        if libsignalSessionLib.resolve mpl e == pc then cliExternsPlacedSig mmpl W e else none := by
  have key : ∀ (b : BitVec 64) (e : String),
      ((libsignalSessionLib.resolve mpl e - b).toNat == (pc - b).toNat) =
        (libsignalSessionLib.resolve mpl e == pc) := by
    intro b e
    cases h : libsignalSessionLib.resolve mpl e == pc with
    | true =>
      have heq := beq_iff_eq.mp h
      subst heq
      simp
    | false =>
      rw [beq_eq_false_iff_ne] at h ⊢
      intro hnat
      apply h
      have hbv := BitVec.eq_of_toNat_eq hnat
      have : (libsignalSessionLib.resolve mpl e - b) + b = (pc - b) + b := congrArg (· + b) hbv
      simpa [BitVec.sub_add_cancel] using this
  have h0 : ∀ L : List (String × Nat),
      L.findSome? (fun _ => (none : Option (State → State))) = none := by
    intro L; induction L <;> simp [*]
  dsimp only [cliProgPlacedSig, MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
    MultiPlacedLib.blockPlacement, Program.externAt?, Program.hookAtOff?]
  simp only [ite_self, h0, Option.or_none, List.findSome?_map, Function.comp_def, key]

private theorem list_findSome?_congr {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.findSome?_cons, h a List.mem_cons_self]
    cases g a with
    | none => exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    | some _ => rfl

/-- `(cliProgPlacedSig mpl mmpl W).externAt? pc` is independent of `mpl` across `InElf` placements
on `f3TrialElf`. -/
theorem cliProgPlacedSig_externAt_eq_of_inElf {mpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl)
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (pc : BitVec 64) :
    (cliProgPlacedSig mpl mmpl W).externAt? pc =
      (cliProgPlacedSig f3LsMpl mmpl W).externAt? pc := by
  have hres := (f3CliElf_libsignal_inElf_unique hpl hin).2.1
  rw [externAt?_cliProgPlacedSig, externAt?_cliProgPlacedSig, ls_block617_externs_eq]
  refine list_findSome?_congr (l := lsSharedExterns.map _) fun e he => ?_
  simp only [List.mem_map] at he
  obtain ⟨idx, hidx, rfl⟩ := he
  have hlt := Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
  rw [hres _ (mem_lsNames_of_getD hlt rfl)]

theorem cliProgPlacedSig_externAt_eq_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (pc : BitVec 64) :
    (cliProgPlacedSig mpl mmpl W).externAt? pc =
      (cliProgPlacedSig f3LsMpl mmpl W).externAt? pc := by
  obtain ⟨_, hp, hpl, hin⟩ := hlink
  cases f3TrialElf_parse.symm.trans hp
  exact cliProgPlacedSig_externAt_eq_of_inElf hpl hin mmpl W pc

/-- `CliRunsToPlaced mpl mmpl f3TrialElf W` is independent of `mpl` across `LinkedAt` placements. -/
theorem cliRunsToPlaced_eq_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    CliRunsToPlaced mpl mmpl f3TrialElf W =
      CliRunsToPlaced f3LsMpl mmpl f3TrialElf W := by
  funext i o
  unfold CliRunsToPlaced
  rw [cliTokenPatchPlaced_eq_of_linkedAt hlink]
  have hp := fun s0 => processRunsTo_iff_of_externAt_eq
    (cliProgPlacedSig_externAt_eq_of_linkedAt hlink mmpl W) rfl
    (cliTokenPatchPlaced f3LsMpl s0) (OutcomeMatchesProcess o) (fun _ => False)
  simp only [hp]

theorem cliRunPlacedSig_eq_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliRunPlacedSig mpl mmpl f3TrialElf W =
      cliRunPlacedSig f3LsMpl mmpl f3TrialElf W := by
  funext i
  unfold cliRunPlacedSig
  rw [cliRunsToPlaced_eq_of_linkedAt hlink mmpl W]

/-- `CliReachesOOMPlaced mpl mmpl f3TrialElf W i` is independent of `mpl` across `LinkedAt`
placements. -/
theorem cliReachesOOMPlaced_iff_of_linkedAt {mpl : Obj.MultiPlacement}
    (hlink : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (mmpl : Obj.MultiPlacement) (W : CliHooks) (i : CryptoVerification.SignalSession.Inputs) :
    CliReachesOOMPlaced mpl mmpl f3TrialElf W i ↔
      CliReachesOOMPlaced f3LsMpl mmpl f3TrialElf W i := by
  unfold CliReachesOOMPlaced
  rw [cliTokenPatchPlaced_eq_of_linkedAt hlink]
  have hsteps := fun s0 s => steps_iff_of_externAt_eq
    (cliProgPlacedSig_externAt_eq_of_linkedAt hlink mmpl W) rfl
    (cliTokenPatchPlaced f3LsMpl s0) s
  simp only [hsteps]

/-! ## Tag-Table Reduction and Dehooked Stub Witnesses -/

private def lookupKeyIdx : List String → String → Option Nat
  | [], _ => none
  | k :: ks, s => if k == s then some 0 else (lookupKeyIdx ks s).map Nat.succ

private theorem lookup_zip_eq_map {α : Type} (d : α) :
    ∀ (keys : List String) (vals : List α) (s : String),
      keys.length ≤ vals.length →
      (List.zip keys vals).lookup s = (lookupKeyIdx keys s).map (fun i => vals.getD i d)
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | k :: ks, v :: vs, s, h => by
    simp only [List.zip_cons_cons, List.lookup, lookupKeyIdx]
    have hcomm : (s == k) = (k == s) := BEq.comm
    rw [hcomm]
    cases hs : k == s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [lookup_zip_eq_map d ks vs s (Nat.le_of_succ_le_succ h)]
      cases lookupKeyIdx ks s <;> rfl
    · rfl

private noncomputable def cliHookVals (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    List (State → State) :=
  (cliHookTablePlaced mmpl W).map Prod.snd

private theorem cliHookTablePlaced_eq_zip (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliHookTablePlaced mmpl W = List.zip lsHookNamesPlaced (cliHookVals mmpl W) := by
  rfl_kernel

private theorem lsHookNamesPlaced_eq_fst (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    lsHookNamesPlaced = (cliHookTablePlaced mmpl W).map Prod.fst := by
  rfl_kernel

private theorem lsHookNamesPlaced_len (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    lsHookNamesPlaced.length ≤ (cliHookVals mmpl W).length := by
  rw [lsHookNamesPlaced_eq_fst mmpl W, cliHookVals, List.length_map, List.length_map]

private def placedExternTag (s : String) : Option Nat :=
  if isCliPanicSymbolPlaced s then some 0
  else (lookupKeyIdx lsHookNamesPlaced s).map Nat.succ

private noncomputable def evalCliTag (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    Nat → State → State
  | 0 => abortOnPanic Rust.panicked
  | k + 1 => abortOnPanic ((cliHookVals mmpl W).getD k Rust.panicked)

private theorem cliExternsPlacedSig_eq_tag (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (s : String) :
    cliExternsPlacedSig mmpl W s = (placedExternTag s).map (evalCliTag mmpl W) := by
  unfold cliExternsPlacedSig cliExternsPlaced placedExternTag
  cases isCliPanicSymbolPlaced s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [cliHookTablePlaced_eq_zip mmpl W,
      lookup_zip_eq_map Rust.panicked _ _ s (lsHookNamesPlaced_len mmpl W)]
    cases lookupKeyIdx lsHookNamesPlaced s <;> rfl
  · rfl

private theorem findSome_map_val {α β γ : Type} (f : β → γ) :
    ∀ (L : List α) (g : α → Option β),
      L.findSome? (fun x => (g x).map f) = (L.findSome? g).map f
  | [], _ => rfl
  | x :: xs, g => by
    simp only [List.findSome?_cons]
    cases g x <;> simp [findSome_map_val f xs g]

private def placedTagAt (pc : BitVec 64) : Option Nat :=
  lsPlacedStubPairs.findSome? fun (n, a) =>
    if a == pc then placedExternTag n else none

private theorem placedTagAt_eq_sharedExterns (pc : BitVec 64) :
    placedTagAt pc = lsSharedExterns.findSome? (fun idx =>
      if f3LsSymAddrs.getD idx 0#64 == pc then
        placedExternTag (lsInternedMultiLib.names.getD idx "")
      else none) := by
  unfold placedTagAt
  rw [lsPlacedStubPairs_eq, List.findSome?_map]
  rfl

private theorem cliProgPlacedSig_f3Ls_externAt_tag (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (pc : BitVec 64) :
    (cliProgPlacedSig f3LsMpl mmpl W).externAt? pc =
      (placedTagAt pc).map (evalCliTag mmpl W) := by
  rw [placedTagAt_eq_sharedExterns, externAt?_cliProgPlacedSig, ls_block617_externs_eq,
    List.findSome?_map]
  have hstep : (lsSharedExterns.findSome? (Function.comp
      (fun e => if libsignalSessionLib.resolve f3LsMpl e == pc then
        cliExternsPlacedSig mmpl W e else none)
      (fun idx => lsInternedMultiLib.names.getD idx ""))) =
      lsSharedExterns.findSome? (fun idx =>
        ((if f3LsSymAddrs.getD idx 0#64 == pc then
          placedExternTag (lsInternedMultiLib.names.getD idx "") else none)).map
          (evalCliTag mmpl W)) := by
    refine list_findSome?_congr (l := lsSharedExterns) fun idx hidx => ?_
    dsimp only [Function.comp_def]
    have hlt : idx < lsInternedMultiLib.names.length :=
      Nat.blt_eq.mp (List.all_eq_true.mp ls_sharedExterns_lt idx hidx)
    have hres : libsignalSessionLib.resolve f3LsMpl (lsInternedMultiLib.names.getD idx "") =
        f3LsSymAddrs.getD idx 0#64 := by
      rw [ls_toMultiPlacedLib_eq]
      change lsInternedMultiLib.toMultiPlacedLib.resolve
        (f3LsLayout.toMultiPlacement lsInternedMultiLib.names) _ = _
      rw [Obj.Interned.toMultiPlacement_resolve_eq ls_names_nodup ls_idsOk ls_blockSymsMatch_ok,
        Obj.Interned.idxOf_getD ls_names_nodup hlt]
      rfl
    rw [hres, cliExternsPlacedSig_eq_tag]
    cases f3LsSymAddrs.getD idx 0#64 == pc <;> rfl
  rw [hstep, findSome_map_val]

private theorem string_startsWith_eq_isPrefixOf (s pat : String) :
    s.startsWith pat = List.isPrefixOf pat.toList s.toList := by
  rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]

private def panicPrefixChars : List Char :=
  ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':']

private theorem core_panicking_toList_eq : "core::panicking::".toList = panicPrefixChars := by
  rfl_kernel

private def isPanicSymbolFast (name : String) : Bool :=
  List.isPrefixOf panicPrefixChars name.toList ||
  [ "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error" ].contains name

private theorem isPanicSymbol_eq_fast (name : String) :
    Rust.isPanicSymbol name = isPanicSymbolFast name := by
  unfold Rust.isPanicSymbol isPanicSymbolFast
  rw [string_startsWith_eq_isPrefixOf, core_panicking_toList_eq]

private def placedExternTagFast (s : String) : Option Nat :=
  if cliPanicSymbolsPlaced.contains s || isPanicSymbolFast s then some 0
  else (lookupKeyIdx lsHookNamesPlaced s).map Nat.succ

private theorem placedExternTag_eq_fast (s : String) :
    placedExternTag s = placedExternTagFast s := by
  unfold placedExternTag placedExternTagFast isCliPanicSymbolPlaced
  rw [isPanicSymbol_eq_fast]

private def lookupAddrTag (tbl : List (BitVec 64 × Option Nat)) (pc : BitVec 64) : Option Nat :=
  tbl.findSome? fun (a, t) => if a == pc then t else none

private def lsPlacedTagTable : List (BitVec 64 × Option Nat) :=
  lsPlacedStubPairs.map fun (n, a) => (a, placedExternTagFast n)

private theorem placedTagAt_eq_table (pc : BitVec 64) :
    placedTagAt pc = lookupAddrTag lsPlacedTagTable pc := by
  unfold placedTagAt lookupAddrTag lsPlacedTagTable
  rw [List.findSome?_map]
  refine list_findSome?_congr (l := lsPlacedStubPairs) fun ⟨n, a⟩ _ => ?_
  dsimp only [Function.comp_def]
  rw [placedExternTag_eq_fast]

private def compactTagTbl : List (BitVec 64 × Option Nat) → List (Nat × Nat)
  | [] => []
  | (_, none) :: xs => compactTagTbl xs
  | (a, some t) :: xs => (a.toNat, t) :: compactTagTbl xs

private def lookupAddrTagNat : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (a, t) :: xs, pc => if Nat.beq a pc then some t else lookupAddrTagNat xs pc

private theorem bv64_beq_eq_nat_beq (a b : BitVec 64) : (a == b) = Nat.beq a.toNat b.toNat := by
  cases h : a == b
  · symm
    rw [Bool.eq_false_iff]
    intro h'
    rw [Nat.beq_eq] at h'
    exact absurd (beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h')) (by simp [h])
  · rw [beq_iff_eq] at h
    subst h
    exact (Nat.beq_refl _).symm

private theorem lookupAddrTag_eq_compact :
    ∀ (tbl : List (BitVec 64 × Option Nat)) (pc : BitVec 64),
      lookupAddrTag tbl pc = lookupAddrTagNat (compactTagTbl tbl) pc.toNat
  | [], _ => rfl
  | (_, none) :: xs, pc => by
    simp only [lookupAddrTag, compactTagTbl, List.findSome?_cons, ite_self]
    exact lookupAddrTag_eq_compact xs pc
  | (a, some t) :: xs, pc => by
    simp only [lookupAddrTag, compactTagTbl, lookupAddrTagNat, List.findSome?_cons]
    rw [bv64_beq_eq_nat_beq a pc]
    cases Nat.beq a.toNat pc.toNat
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact lookupAddrTag_eq_compact xs pc
    · rfl

private theorem lsPlacedTagTable_eq_lit : lsPlacedTagTable = lsPlacedTagTableLit := by
  rfl_kernel

private theorem compactTagTbl_placed_eq_lit :
    compactTagTbl lsPlacedTagTableLit = lsPlacedCompactLit := by
  rfl_kernel

private theorem placedTagAt_eq_compact (pc : BitVec 64) :
    placedTagAt pc = lookupAddrTagNat lsPlacedCompactLit pc.toNat := by
  rw [placedTagAt_eq_table, lsPlacedTagTable_eq_lit, lookupAddrTag_eq_compact,
    compactTagTbl_placed_eq_lit]

private theorem externAt?_none_of_lookupCompact_none {mpl mmpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl)
    {pc : BitVec 64}
    (hnone : lookupAddrTagNat lsPlacedCompactLit pc.toNat = none) (W : CliHooks) :
    (cliProgPlacedSig mpl mmpl W).externAt? pc = none := by
  rw [cliProgPlacedSig_externAt_eq_of_inElf hpl hin mmpl W pc,
    cliProgPlacedSig_f3Ls_externAt_tag, placedTagAt_eq_compact, hnone]
  rfl

private theorem lookupAddrTagNat_none_of_all_lt :
    ∀ (xs : List (Nat × Nat)) (pc : Nat),
      (xs.all fun p => Nat.blt p.1 pc) = true →
      lookupAddrTagNat xs pc = none
  | [], _, _ => rfl
  | (a, t) :: xs, pc, hall => by
    simp only [List.all_cons, Bool.and_eq_true, Nat.blt_eq] at hall
    have hne : Nat.beq a pc = false := by
      rw [Bool.eq_false_iff, Ne, Nat.beq_eq]
      omega
    simp only [lookupAddrTagNat, hne, Bool.false_eq_true, ↓reduceIte]
    exact lookupAddrTagNat_none_of_all_lt xs pc hall.2

/-- Every `pc` with `f3MngCodeLo ≤ pc.toNat` satisfies `(cliProgPlacedSig mpl mmpl W).externAt? pc = none`
for any `InElf` placement `mpl`. -/
theorem f3CliElf_externAt_none_of_ge_mngCodeLo {mpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl)
    (mmpl : Obj.MultiPlacement) (W : CliHooks) {pc : BitVec 64}
    (hge : f3MngCodeLo ≤ pc.toNat) :
    (cliProgPlacedSig mpl mmpl W).externAt? pc = none := by
  have hall : (lsPlacedCompactLit.all fun p => Nat.blt p.1 pc.toNat) = true := by
    rw [List.all_eq_true]
    intro p hp
    have hlt := Nat.blt_eq.mp (List.all_eq_true.mp lsPlacedCompactLit_lt_mngCodeLo p hp)
    rw [Nat.blt_eq]
    omega
  exact externAt?_none_of_lookupCompact_none hpl hin
    (lookupAddrTagNat_none_of_all_lt lsPlacedCompactLit pc.toNat hall) W

/-- `(cliProgPlacedSig mpl mmpl W).externAt? = none` across all `mallocngLib` code bytes. -/
theorem f3CliElf_mallocng_code_externAt_none_of_inElf {mpl mmpl : Obj.MultiPlacement}
    (hpl₁ : libsignalSessionLib.Placeable mpl)
    (hin₁ : libsignalSessionLib.InElf f3TrialElf mpl)
    (hpl₂ : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin₂ : VerifiedLibraries.mallocngLib.InElf f3TrialElf mmpl)
    (j : Nat) (hj : j < VerifiedLibraries.mallocngLib.blocks.length)
    (W : CliHooks) (a : BitVec 64)
    (ha : InRegion (mmpl.base j) VerifiedLibraries.mallocngLib.blocks[j].code.length a) :
    (cliProgPlacedSig mpl mmpl W).externAt? a = none := by
  obtain ⟨_, hhi64, hm_lo, hm_hi⟩ := f3CliElf_mallocng_code_bounds_of_inElf hpl₂ hin₂ j hj
  obtain ⟨hk, heq⟩ := inRegion_offset ha
  have htonat : (mmpl.base j + BitVec.ofNat 64 (a - mmpl.base j).toNat).toNat =
      (mmpl.base j).toNat + (a - mmpl.base j).toNat :=
    toNat_add_ofNat_of_lt (by omega)
  rw [heq] at htonat
  exact f3CliElf_externAt_none_of_ge_mngCodeLo hpl₁ hin₁ mmpl W (by omega)

private def checkElfMaps4RxFastAux (rws : List (Snapshot.Region × Nat)) (addr : BitVec 64)
    (bs : List (BitVec 8)) : Bool :=
  match bs with
  | [b0, b1, b2, b3] =>
    (cellAtFastAux rws (addr + BitVec.ofNat 64 0) == some (some .rx, b0)) &&
    (cellAtFastAux rws (addr + BitVec.ofNat 64 1) == some (some .rx, b1)) &&
    (cellAtFastAux rws (addr + BitVec.ofNat 64 2) == some (some .rx, b2)) &&
    (cellAtFastAux rws (addr + BitVec.ofNat 64 3) == some (some .rx, b3))
  | _ => false

private theorem elfMaps4Rx_of_checkAux {elf : ElfImage} {addr : BitVec 64}
    {bs : List (BitVec 8)}
    (h : checkElfMaps4RxFastAux (elf.segments.map fun r => (r, r.bytes.length)) addr bs = true) :
    Obj.ElfMaps elf addr bs (· == Perm.rx) := by
  unfold checkElfMaps4RxFastAux at h
  match bs with
  | [b0, b1, b2, b3] =>
    simp only [Bool.and_eq_true, beq_iff_eq, cellAtFastAux_eq] at h
    obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
    intro i hi
    match i with
    | 0 => exact ⟨.rx, h0, rfl⟩
    | 1 => exact ⟨.rx, h1, rfl⟩
    | 2 => exact ⟨.rx, h2, rfl⟩
    | 3 => exact ⟨.rx, h3, rfl⟩
    | n + 4 => simp [List.length] at hi
  | [] => nomatch h
  | [_] => nomatch h
  | [_, _] => nomatch h
  | [_, _, _] => nomatch h
  | _ :: _ :: _ :: _ :: _ :: _ => nomatch h

private def checkDirectOrBranchStubFastAux (rws : List (Snapshot.Region × Nat))
    (stubVa targetVa : BitVec 64) : Bool :=
  (stubVa == targetVa) ||
    (Nat.beq (stubVa.toNat % 4) 0 &&
      Obj.Interned.codeRelocInRangeB .jump26 stubVa targetVa &&
      checkElfMaps4RxFastAux rws stubVa
        (Obj.bytesOfWordLE (Obj.branchWord 0x14000000#32 stubVa targetVa)))

private theorem directOrBranchStub_of_checkAux {elf : ElfImage} {stubVa targetVa : BitVec 64}
    (h : checkDirectOrBranchStubFastAux
      (elf.segments.map fun r => (r, r.bytes.length)) stubVa targetVa = true) :
    DirectOrBranchStub elf stubVa targetVa := by
  unfold checkDirectOrBranchStubFastAux at h
  rcases Bool.or_eq_true_iff.mp h with heq | hbr
  · exact Or.inl (beq_iff_eq.mp heq)
  · simp only [Bool.and_eq_true, Nat.beq_eq] at hbr
    obtain ⟨⟨hal, hrange⟩, hmaps0⟩ := hbr
    have hbrRange : Obj.BranchInRange stubVa targetVa :=
      Obj.Interned.codeRelocInRange_of (kind := .jump26) hrange
    have hmaps := elfMaps4Rx_of_checkAux (elf := elf) hmaps0
    exact Or.inr ⟨hal, hbrRange, fun i hi => hmaps i hi⟩

private def checkF3DehookedAllB : Bool :=
  Obj.Interned.buildEncSymTable f3TrialElfSymChars fun enc =>
  Obj.Interned.withRegionsWithLen f3TrialElf.segments fun rws =>
    f3DehookedEntries.all fun (idx, cs, stubVa, targetVa) =>
      Nat.blt idx lsInternedMultiLib.names.length &&
      (lsInternedMultiLib.names.getD idx "" == String.ofList cs) &&
      (Obj.Interned.lookupBlockSymId idx lsInternedMultiLib.blocks == none) &&
      (f3LsSymAddrs.getD idx 0#64 == stubVa) &&
      (lookupAddrTagNat lsPlacedCompactLit stubVa.toNat == none) &&
      (lookupAddrTagNat lsPlacedCompactLit targetVa.toNat == none) &&
      (Obj.Interned.withEncodeCharKey cs fun key =>
        lookupUniqueEnc key enc == some targetVa) &&
      checkDirectOrBranchStubFastAux rws stubVa targetVa

private theorem checkF3DehookedAll_ok : checkF3DehookedAllB = true := by
  rfl_kernel

/-- For every `sym ∈ cliDehookedSymsPlaced`, `externAt? (mpl.ρ sym) = none`, `.symtab` uniquely
resolves `sym` to `targetVa`, `DirectOrBranchStub f3TrialElf (mpl.ρ sym) targetVa` holds, and
`externAt? targetVa = none`. -/
theorem f3CliElf_dehooked_witness_of_inElf {mpl mmpl : Obj.MultiPlacement}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf f3TrialElf mpl)
    {sym : String} (hsym : sym ∈ cliDehookedSymsPlaced) :
    (∀ W : CliHooks, (cliProgPlacedSig mpl mmpl W).externAt? (mpl.ρ sym) = none) ∧
    ∃ targetVa : BitVec 64,
      Obj.lookupUnique sym f3TrialElf.symbols = some targetVa ∧
      DirectOrBranchStub f3TrialElf (mpl.ρ sym) targetVa ∧
      ∀ W : CliHooks, (cliProgPlacedSig mpl mmpl W).externAt? targetVa = none := by
  rw [cliDehookedSymsPlaced_eq_entries, List.mem_map] at hsym
  obtain ⟨⟨idx, cs, stubVa, targetVa⟩, hmem_e, rfl⟩ := hsym
  have hchk := checkF3DehookedAll_ok
  unfold checkF3DehookedAllB at hchk
  rw [Obj.Interned.buildEncSymTable_eq, Obj.Interned.withRegionsWithLen_eq] at hchk
  have he := List.all_eq_true.mp hchk (idx, cs, stubVa, targetVa) hmem_e
  simp only [Obj.Interned.withEncodeCharKey_eq, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨hlt, hname⟩, hid⟩, hstub_addr⟩, htag_stub⟩, htag_tgt⟩, hlu_enc⟩, hdir_chk⟩ := he
  have hmem_ls := mem_lsNames_of_getD hlt hname
  have hnone := lookupBlockSym_none_of_idx hlt hname hid
  have hρ_eq := (f3CliElf_libsignal_inElf_unique hpl hin).2.2.1 _ hmem_ls hnone
  have hidx : lsInternedMultiLib.names.idxOf (String.ofList cs) = idx := by
    rw [← hname]
    exact Obj.Interned.idxOf_getD ls_names_nodup hlt
  have hρ_stub : mpl.ρ (String.ofList cs) = stubVa :=
    hρ_eq.trans ((f3LsMpl_rho_of_idx hidx).trans hstub_addr)
  have hlu : Obj.lookupUnique (String.ofList cs) f3TrialElf.symbols = some targetVa := by
    rw [lookupUnique_eq_lookupUniqueEnc f3TrialElfSyms_eq rfl rfl]
    exact hlu_enc
  have hdir : DirectOrBranchStub f3TrialElf (mpl.ρ (String.ofList cs)) targetVa := by
    rw [hρ_stub]
    exact directOrBranchStub_of_checkAux hdir_chk
  refine ⟨fun W => ?_, targetVa, hlu, hdir, fun W => ?_⟩
  · rw [hρ_stub]
    exact externAt?_none_of_lookupCompact_none hpl hin htag_stub W
  · exact externAt?_none_of_lookupCompact_none hpl hin htag_tgt W

/-! ## `CliElfCodeMatchesPlaced` Witnesses -/

/-- Universal `InElf` witness for `CliElfCodeMatchesPlaced mpl mmpl f3TrialElf`. -/
theorem f3TrialElf_codeMatchesPlaced_of_inElf {mpl mmpl : Obj.MultiPlacement}
    (hpl₁ : libsignalSessionLib.Placeable mpl)
    (hin₁ : libsignalSessionLib.InElf f3TrialElf mpl)
    (hpl₂ : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin₂ : VerifiedLibraries.mallocngLib.InElf f3TrialElf mmpl) :
    CliElfCodeMatchesPlaced mpl mmpl f3TrialElf :=
  ⟨hpl₁,
   hin₁,
   (f3CliElf_libsignal_inElf_unique hpl₁ hin₁).2.2.2,
   hpl₂,
   hin₂,
   (f3CliElf_mallocng_inElf_unique hpl₂ hin₂).2.2.2,
   f3CliElf_libsignal_mallocng_code_disjoint_of_inElf hpl₁ hin₁ hpl₂ hin₂,
   fun _ hd₁ _ hd₂ =>
     Or.inr (f3CliElf_libsignal_mallocng_data_disjoint_of_inElf hpl₁ hin₁ hpl₂ hin₂ hd₁ hd₂),
   f3CliElf_mallocng_code_externAt_none_of_inElf hpl₁ hin₁ hpl₂ hin₂,
   fun _ hsym => f3CliElf_dehooked_witness_of_inElf hpl₁ hin₁ hsym⟩

/-- Concrete witness `CliElfCodeMatchesPlaced f3LsMpl f3MallocngMpl f3TrialElf`. -/
theorem f3TrialElf_codeMatchesPlaced :
    CliElfCodeMatchesPlaced f3LsMpl f3MallocngMpl f3TrialElf :=
  f3TrialElf_codeMatchesPlaced_of_inElf
    f3CliElf_libsignal_placed.1 f3CliElf_libsignal_placed.2.1
    f3CliElf_mallocng_placed.1 f3CliElf_mallocng_placed.2.1

/-- Universal `LinkedAt` witness for `CliElfCodeMatchesPlaced mpl mmpl f3TrialElf`. -/
theorem f3TrialElf_codeMatchesPlaced_of_linkedAt {mpl mmpl : Obj.MultiPlacement}
    (hls : libsignalSessionLib.LinkedAt f3TrialElfBytes mpl)
    (hmng : VerifiedLibraries.mallocngLib.LinkedAt f3TrialElfBytes mmpl) :
    CliElfCodeMatchesPlaced mpl mmpl f3TrialElf := by
  obtain ⟨_, hp₁, hpl₁, hin₁⟩ := hls
  obtain ⟨_, hp₂, hpl₂, hin₂⟩ := hmng
  cases f3TrialElf_parse.symm.trans hp₁
  cases f3TrialElf_parse.symm.trans hp₂
  exact f3TrialElf_codeMatchesPlaced_of_inElf hpl₁ hin₁ hpl₂ hin₂

end

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesPlaced
