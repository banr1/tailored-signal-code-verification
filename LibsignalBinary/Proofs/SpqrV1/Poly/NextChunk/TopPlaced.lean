/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedB

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Unconditional Placed Contracts

Instantiates `ProofPlaced` with `pointsToPolysLoop_polyList_placed_sepWPp` to establish
unconditional `[LibsignalPlacement]` contracts (`poly_next_chunk_rodata_placed_ok` and
`poly_next_chunk_placed_ok`) for Block `416`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Alloc

/-- Discharges `PointsToPolysLoopPlacedProp A ext` under `[LibsignalPlacement]` via
    `pointsToPolysLoop_polyList_placed_sepWPp`. -/
theorem pointsToPolysLoop_placed_prop [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext) :
    PointsToPolysLoopPlacedProp A ext :=
  fun s0 s hcl fsp ptsBase hfsp_align pts hlen hbounds
      u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
      Frame R hpc hrun hsp htrace hx19 hx20 hx28 hx29 hcont =>
    pointsToPolysLoop_polyList_placed_sepWPp hA s0 s hcl fsp ptsBase hfsp_align
      pts hlen hbounds u16 u24 u32 u40 u64 u72 u80 u96 u640 u648 u1040 u1048 u1056
      Frame R hpc hrun hsp htrace hx19 hx20 hx28 hx29 hcont

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `PolyNextChunkRodataPlacedOkExt A ext` under `[LibsignalPlacement]`. -/
theorem poly_next_chunk_rodata_placed_ok [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext) :
    PolyNextChunkRodataPlacedOkExt A ext :=
  poly_next_chunk_rodata_placed_ok_of_p2p A ext hA (pointsToPolysLoop_placed_prop A ext hA)

theorem poly_next_chunk_rodata_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    PolyNextChunkRodataPlacedOkExt A ext :=
  poly_next_chunk_rodata_placed_ok A ext hA

/-- `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk` (Block `416`)
    satisfies `PolyNextChunkPlacedOkExt A ext` (`withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec A)`)
    under `[LibsignalPlacement]`. -/
theorem poly_next_chunk_placed_ok [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext) :
    PolyNextChunkPlacedOkExt A ext :=
  poly_next_chunk_placed_ok_of_p2p A ext hA (pointsToPolysLoop_placed_prop A ext hA)

theorem poly_next_chunk_placed_ok_ext [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext) :
    PolyNextChunkPlacedOkExt A ext :=
  poly_next_chunk_placed_ok A ext hA

end CryptoVerification.SpqrV1.Poly.NextChunk

namespace CryptoVerification.SpqrV1.Poly
export NextChunk (pointsToPolysLoop_placed_prop
  poly_next_chunk_rodata_placed_ok poly_next_chunk_rodata_placed_ok_ext
  poly_next_chunk_placed_ok poly_next_chunk_placed_ok_ext)
end CryptoVerification.SpqrV1.Poly
