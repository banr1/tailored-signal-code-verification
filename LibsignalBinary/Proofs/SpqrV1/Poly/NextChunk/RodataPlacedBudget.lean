/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: Budget-Threaded Placed `.rodata` Bridges

Re-exports `[LibsignalPlacement]` `.rodata` assertions for `COMPLETE_POINTS_POLYS_{5,30,34,36}`
and defines `withLsCodeLoaded` `.rodata` budget contracts (`PolyNextChunkRodataPlacedOkExt`) with
discharge bridges to `withLsCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlacedBudget

open Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.GF.Mul2U16
  (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
  (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkSize polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (PolyNextChunkGhost completePointsPolysPlacedAt polyNextChunkStack
   rodata_completePointsPolys_placed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (PolyNextChunkEnv PolyNextChunkPlacedOkExt PolyNextChunkPlacedOkExtOfEnv
   PolyNextChunkRodataCodeLoadedOkExt PolyNextChunkRodataCodeLoadedOkExtOfEnv
   polyNextChunkPlacedOkExt_of_rodata_codeLoaded
   polyNextChunkPlacedSpec polyNextChunkPlacedSpecOfEnv
   polyNextChunkRodataPlacedSpec polyNextChunkRodataPlacedSpecOfEnv)

/-! ## 1. Re-Exports of Allocator-Free `.rodata` Definitions & Lemmas -/

export CryptoVerification.SpqrV1.Poly.NextChunk
  (completePointsPolys5Sym completePointsPolys30Sym
   completePointsPolys34Sym completePointsPolys36Sym)

export CryptoVerification.SpqrV1.Poly.NextChunk
  (completePointsPolys5PlacedAt rodata_completePointsPolys5_placed
   completePointsPolys30PlacedAt rodata_completePointsPolys30_placed
   completePointsPolys34PlacedAt)

export CryptoVerification.SpqrV1.Poly.NextChunk
  (rodata_completePointsPolys34_placed completePointsPolys36PlacedAt
   rodata_completePointsPolys36_placed completePointsPolysPlacedAt
   rodata_completePointsPolys_placed)

export CryptoVerification.SpqrV1.Poly.NextChunk
  (sepWPp_intro_rodata_placed completePointsPolys5RestPlacedAt
   completePointsPolys5PlacedAt_split)

/-! ## 2. Budget-Threaded Relocatable `.rodata` Specifications & Contracts (Block `416`) -/

export LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (polyNextChunkRodataPlacedSpecOfEnv polyNextChunkRodataPlacedSpec
   polyNextChunkPlacedSpecOfEnv polyNextChunkPlacedSpec)

export LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (PolyNextChunkBlockOkXOfEnv PolyNextChunkBlockOkX
   PolyNextChunkCallerOkXOfEnv PolyNextChunkCallerOkX
   polyNextChunkBlockOkX_of_placedOkExt)

export LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (polyNextChunkCallerOkX_of_placedOkExt
   subroutine_ok_polyNextChunkPlacedSpecOfEnv_mono
   polyNextChunkPlacedOkExtOfEnv_mono)

/-- Envelope-parametric relocatable `[LibsignalPlacement]` contract for
    `<PolyEncoder as Encoder>::next_chunk` (Block `416`) with explicit
    `completePointsPolysPlacedAt` wrapped with `withLsCodeLoaded lsmpl`
    (exact budget counterpart of `RodataPlaced.PolyNextChunkRodataPlacedOkExt`, definitionally
    equal to `DefsPlacedBudget.PolyNextChunkRodataCodeLoadedOkExtOfEnv`). -/
abbrev PolyNextChunkRodataPlacedOkExtOfEnv [LibsignalPlacement]
    (Env : PolyNextChunkGhost → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PolyNextChunkRodataCodeLoadedOkExtOfEnv Env M A lim ext

/-- Canonical relocatable `[LibsignalPlacement]` contract for
    `<PolyEncoder as Encoder>::next_chunk` (Block `416`) with explicit
    `completePointsPolysPlacedAt` wrapped with `withLsCodeLoaded lsmpl`. -/
abbrev PolyNextChunkRodataPlacedOkExt [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PolyNextChunkRodataCodeLoadedOkExt M A lim ext

/-- Weaken `withLsCodeLoaded` `PolyNextChunkRodataPlacedOkExtOfEnv` to `DefsBudget`'s
    `withLsCodeRoLoaded` form. -/
theorem to_defsBudget_rodataPlacedOkExt_ofEnv [LibsignalPlacement]
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : PolyNextChunkRodataPlacedOkExtOfEnv Env M A lim ext) :
    LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget.PolyNextChunkRodataPlacedOkExtOfEnv
      Env M A lim ext := by
  refine subroutine_ok_mono h (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨⟨hcl, _⟩, hpre⟩ := extract_withLsCodeRoLoaded hp
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

/-- Discharge `completePointsPolysPlacedAt` from `LibsignalCodeRoLoaded lsmpl` to lift
    `PolyNextChunkRodataPlacedOkExtOfEnv` (`withLsCodeLoaded`) to `PolyNextChunkPlacedOkExtOfEnv`
    (`withLsCodeRoLoaded`). -/
theorem polyNextChunkPlacedOkExt_of_rodata_ofEnv [LibsignalPlacement]
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hro_ok : PolyNextChunkRodataPlacedOkExtOfEnv Env M A lim ext) :
    PolyNextChunkPlacedOkExtOfEnv Env M A lim ext :=
  polyNextChunkPlacedOkExt_of_rodata_codeLoaded hro_ok

/-- Canonical `PolyNextChunkEnv` specialization of `polyNextChunkPlacedOkExt_of_rodata_ofEnv`. -/
theorem polyNextChunkPlacedOkExt_of_rodata [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hro_ok : PolyNextChunkRodataPlacedOkExt M A lim ext) :
    PolyNextChunkPlacedOkExt M A lim ext :=
  polyNextChunkPlacedOkExt_of_rodata_codeLoaded hro_ok

/-- Discharge `completePointsPolysPlacedAt` from `DefsBudget.PolyNextChunkRodataPlacedOkExtOfEnv`
    (`withLsCodeRoLoaded`). -/
theorem polyNextChunkPlacedOkExt_of_rodataRo_ofEnv [LibsignalPlacement]
    {Env : PolyNextChunkGhost → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hro_ok :
      LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget.PolyNextChunkRodataPlacedOkExtOfEnv
        Env M A lim ext) :
    PolyNextChunkPlacedOkExtOfEnv Env M A lim ext :=
  LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget.polyNextChunkPlacedOkExt_of_rodata
    hro_ok

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlacedBudget
