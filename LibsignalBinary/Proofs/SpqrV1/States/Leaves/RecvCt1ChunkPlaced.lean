/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1Chunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt1Chunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.CommonPlaced
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.AsmConstants -- shake: keep

/-!
# `<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk` (Block `337`)

Relocatable `[LibsignalPlacement]` verification of `<HeaderSent>::recv_ct1_chunk` (Block `337`,
113 instructions), proving `header_sent_recv_ct1_chunk_placed_cl_ext_of_drop` and
`header_sent_recv_ct1_chunk_placed_cl_ext` (`HeaderSentRecvCt1ChunkPlacedOkX`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Stack Address Normalization (`1568`B Frame) -/

@[local arm64_norm, local wp_norm] private theorem sp_sub_64_align (sp : BitVec 64) :
    ((sp - 64#64) &&& 15#64 == 0#64) = (sp &&& 15#64 == 0#64) := by
  have h : (sp - 64#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  rw [h]
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_sub_1504 (sp : BitVec 64) : (sp - 64#64) - 1504#64 = sp - 1568#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_1504 (sp : BitVec 64) : (sp - 1568#64) + 1504#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_8 (sp : BitVec 64) : (sp - 64#64) + 8#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_16 (sp : BitVec 64) : (sp - 64#64) + 16#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_24 (sp : BitVec 64) : (sp - 64#64) + 24#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_32 (sp : BitVec 64) : (sp - 64#64) + 32#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_40 (sp : BitVec 64) : (sp - 64#64) + 40#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_48 (sp : BitVec 64) : (sp - 64#64) + 48#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_56 (sp : BitVec 64) : (sp - 64#64) + 56#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_64_add_64 (sp : BitVec 64) : (sp - 64#64) + 64#64 = sp := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_48_add_8 (sp : BitVec 64) : (sp - 48#64) + 8#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_32_add_8 (sp : BitVec 64) : (sp - 32#64) + 8#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_16_add_8 (sp : BitVec 64) : (sp - 16#64) + 8#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_8 (sp : BitVec 64) : (sp - 1568#64) + 8#64 = sp - 1560#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_16 (sp : BitVec 64) : (sp - 1568#64) + 16#64 = sp - 1552#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_24 (sp : BitVec 64) : (sp - 1568#64) + 24#64 = sp - 1544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_32 (sp : BitVec 64) : (sp - 1568#64) + 32#64 = sp - 1536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_40 (sp : BitVec 64) : (sp - 1568#64) + 40#64 = sp - 1528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_48 (sp : BitVec 64) : (sp - 1568#64) + 48#64 = sp - 1520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_56 (sp : BitVec 64) : (sp - 1568#64) + 56#64 = sp - 1512#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_64 (sp : BitVec 64) : (sp - 1568#64) + 64#64 = sp - 1504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_72 (sp : BitVec 64) : (sp - 1568#64) + 72#64 = sp - 1496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_80 (sp : BitVec 64) : (sp - 1568#64) + 80#64 = sp - 1488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_88 (sp : BitVec 64) : (sp - 1568#64) + 88#64 = sp - 1480#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_104 (sp : BitVec 64) : (sp - 1568#64) + 104#64 = sp - 1464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_249 (sp : BitVec 64) : (sp - 1568#64) + 249#64 = sp - 1319#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_504 (sp : BitVec 64) : (sp - 1568#64) + 504#64 = sp - 1064#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_520 (sp : BitVec 64) : (sp - 1568#64) + 520#64 = sp - 1048#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_528 (sp : BitVec 64) : (sp - 1568#64) + 528#64 = sp - 1040#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_592 (sp : BitVec 64) : (sp - 1568#64) + 592#64 = sp - 976#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_616 (sp : BitVec 64) : (sp - 1568#64) + 616#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1568_add_624 (sp : BitVec 64) : (sp - 1568#64) + 624#64 = sp - 944#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1552_add_8 (sp : BitVec 64) : (sp - 1552#64) + 8#64 = sp - 1544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1552_add_16 (sp : BitVec 64) : (sp - 1552#64) + 16#64 = sp - 1536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1552_add_24 (sp : BitVec 64) : (sp - 1552#64) + 24#64 = sp - 1528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1520_add_8 (sp : BitVec 64) : (sp - 1520#64) + 8#64 = sp - 1512#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1520_add_16 (sp : BitVec 64) : (sp - 1520#64) + 16#64 = sp - 1504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1520_add_24 (sp : BitVec 64) : (sp - 1520#64) + 24#64 = sp - 1496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1488_add_8 (sp : BitVec 64) : (sp - 1488#64) + 8#64 = sp - 1480#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1319_add_255 (sp : BitVec 64) : (sp - 1319#64) + 255#64 = sp - 1064#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1064_add_8 (sp : BitVec 64) : (sp - 1064#64) + 8#64 = sp - 1056#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_944_add_480 (sp : BitVec 64) : (sp - 944#64) + 480#64 = sp - 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_944_add_400 (sp : BitVec 64) : (sp - 944#64) + 400#64 = sp - 544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_8 (sp : BitVec 64) : (sp - 1040#64) + 8#64 = sp - 1032#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_16 (sp : BitVec 64) : (sp - 1040#64) + 16#64 = sp - 1024#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_24 (sp : BitVec 64) : (sp - 1040#64) + 24#64 = sp - 1016#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_32 (sp : BitVec 64) : (sp - 1040#64) + 32#64 = sp - 1008#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_40 (sp : BitVec 64) : (sp - 1040#64) + 40#64 = sp - 1000#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_48 (sp : BitVec 64) : (sp - 1040#64) + 48#64 = sp - 992#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_56 (sp : BitVec 64) : (sp - 1040#64) + 56#64 = sp - 984#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_64 (sp : BitVec 64) : (sp - 1040#64) + 64#64 = sp - 976#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_72 (sp : BitVec 64) : (sp - 1040#64) + 72#64 = sp - 968#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_80 (sp : BitVec 64) : (sp - 1040#64) + 80#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_88 (sp : BitVec 64) : (sp - 1040#64) + 88#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_496 (sp : BitVec 64) : (sp - 1040#64) + 496#64 = sp - 544#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_504 (sp : BitVec 64) : (sp - 1040#64) + 504#64 = sp - 536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_512 (sp : BitVec 64) : (sp - 1040#64) + 512#64 = sp - 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_520 (sp : BitVec 64) : (sp - 1040#64) + 520#64 = sp - 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_528 (sp : BitVec 64) : (sp - 1040#64) + 528#64 = sp - 512#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_536 (sp : BitVec 64) : (sp - 1040#64) + 536#64 = sp - 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_544 (sp : BitVec 64) : (sp - 1040#64) + 544#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_552 (sp : BitVec 64) : (sp - 1040#64) + 552#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_560 (sp : BitVec 64) : (sp - 1040#64) + 560#64 = sp - 480#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_568 (sp : BitVec 64) : (sp - 1040#64) + 568#64 = sp - 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_576 (sp : BitVec 64) : (sp - 1040#64) + 576#64 = sp - 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1040_add_584 (sp : BitVec 64) : (sp - 1040#64) + 584#64 = sp - 456#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1024_add_8 (sp : BitVec 64) : (sp - 1024#64) + 8#64 = sp - 1016#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1024_add_16 (sp : BitVec 64) : (sp - 1024#64) + 16#64 = sp - 1008#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1024_add_24 (sp : BitVec 64) : (sp - 1024#64) + 24#64 = sp - 1000#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1008_add_8 (sp : BitVec 64) : (sp - 1008#64) + 8#64 = sp - 1000#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1008_add_16 (sp : BitVec 64) : (sp - 1008#64) + 16#64 = sp - 992#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_1008_add_24 (sp : BitVec 64) : (sp - 1008#64) + 24#64 = sp - 984#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_992_add_8 (sp : BitVec 64) : (sp - 992#64) + 8#64 = sp - 984#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_976_add_8 (sp : BitVec 64) : (sp - 976#64) + 8#64 = sp - 968#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_976_add_16 (sp : BitVec 64) : (sp - 976#64) + 16#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_976_add_24 (sp : BitVec 64) : (sp - 976#64) + 24#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_968_add_8 (sp : BitVec 64) : (sp - 968#64) + 8#64 = sp - 960#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_960_add_8 (sp : BitVec 64) : (sp - 960#64) + 8#64 = sp - 952#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_544_add_8 (sp : BitVec 64) : (sp - 544#64) + 8#64 = sp - 536#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_544_add_16 (sp : BitVec 64) : (sp - 544#64) + 16#64 = sp - 528#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_544_add_24 (sp : BitVec 64) : (sp - 544#64) + 24#64 = sp - 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_528_add_8 (sp : BitVec 64) : (sp - 528#64) + 8#64 = sp - 520#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_512_add_8' (sp : BitVec 64) : (sp - 512#64) + 8#64 = sp - 504#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_512_add_16' (sp : BitVec 64) : (sp - 512#64) + 16#64 = sp - 496#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_512_add_24' (sp : BitVec 64) : (sp - 512#64) + 24#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_496_add_8' (sp : BitVec 64) : (sp - 496#64) + 8#64 = sp - 488#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_480_add_8 (sp : BitVec 64) : (sp - 480#64) + 8#64 = sp - 472#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_480_add_16 (sp : BitVec 64) : (sp - 480#64) + 16#64 = sp - 464#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_480_add_24 (sp : BitVec 64) : (sp - 480#64) + 24#64 = sp - 456#64 := by bv_omega
@[local arm64_norm, local wp_norm] private theorem sp_sub_464_add_8 (sp : BitVec 64) : (sp - 464#64) + 8#64 = sp - 456#64 := by bv_omega

private theorem wordsAt_10_sp_1552 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    wordsAt (sp - 1552#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] =
    (((sp - 1552#64) ↦₆₄ v0) ∗ ((sp - 1544#64) ↦₆₄ v1) ∗ ((sp - 1536#64) ↦₆₄ v2) ∗
     ((sp - 1528#64) ↦₆₄ v3) ∗ ((sp - 1520#64) ↦₆₄ v4) ∗ ((sp - 1512#64) ↦₆₄ v5) ∗
     ((sp - 1504#64) ↦₆₄ v6) ∗ ((sp - 1496#64) ↦₆₄ v7) ∗ ((sp - 1488#64) ↦₆₄ v8) ∗
     ((sp - 1480#64) ↦₆₄ v9)) := by simp only [wordsAt_10, arm64_norm]

private theorem wordsAt_10_sp_544 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 64) :
    wordsAt (sp - 544#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] =
    (((sp - 544#64) ↦₆₄ v0) ∗ ((sp - 536#64) ↦₆₄ v1) ∗ ((sp - 528#64) ↦₆₄ v2) ∗
     ((sp - 520#64) ↦₆₄ v3) ∗ ((sp - 512#64) ↦₆₄ v4) ∗ ((sp - 504#64) ↦₆₄ v5) ∗
     ((sp - 496#64) ↦₆₄ v6) ∗ ((sp - 488#64) ↦₆₄ v7) ∗ ((sp - 480#64) ↦₆₄ v8) ∗
     ((sp - 472#64) ↦₆₄ v9)) := by simp only [wordsAt_10, arm64_norm]

private theorem wordsAt_12_sp_1040 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    wordsAt (sp - 1040#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] =
    (((sp - 1040#64) ↦₆₄ v0) ∗ ((sp - 1032#64) ↦₆₄ v1) ∗ ((sp - 1024#64) ↦₆₄ v2) ∗
     ((sp - 1016#64) ↦₆₄ v3) ∗ ((sp - 1008#64) ↦₆₄ v4) ∗ ((sp - 1000#64) ↦₆₄ v5) ∗
     ((sp - 992#64) ↦₆₄ v6) ∗ ((sp - 984#64) ↦₆₄ v7) ∗ ((sp - 976#64) ↦₆₄ v8) ∗
     ((sp - 968#64) ↦₆₄ v9) ∗ ((sp - 960#64) ↦₆₄ v10) ∗ ((sp - 952#64) ↦₆₄ v11)) := by simp only [wordsAt_12, arm64_norm]

private theorem wordsAt_12_sp_544 (sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : BitVec 64) :
    wordsAt (sp - 544#64) [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] =
    (((sp - 544#64) ↦₆₄ v0) ∗ ((sp - 536#64) ↦₆₄ v1) ∗ ((sp - 528#64) ↦₆₄ v2) ∗
     ((sp - 520#64) ↦₆₄ v3) ∗ ((sp - 512#64) ↦₆₄ v4) ∗ ((sp - 504#64) ↦₆₄ v5) ∗
     ((sp - 496#64) ↦₆₄ v6) ∗ ((sp - 488#64) ↦₆₄ v7) ∗ ((sp - 480#64) ↦₆₄ v8) ∗
     ((sp - 472#64) ↦₆₄ v9) ∗ ((sp - 464#64) ↦₆₄ v10) ∗ ((sp - 456#64) ↦₆₄ v11)) := by simp only [wordsAt_12, arm64_norm]

/-! ## 2. Relocatable Framed Call Helpers -/

private theorem call_addChunk_cro [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addChunkSpec A)))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
        (fun sm Pm =>
          LibsignalCodeRoLoaded lsmpl sm.mem →
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcro
  refine sepWPp_call_frozen
    (fun _ _ h hkf => h.of_keepsFrozen hkf) hcro
    hcall (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcro_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, addChunkSpec]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [withLsCodeLoaded, addChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    apply of_sepWP_lscro hcro_sf (mid := next_pc)
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStack))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted'

private theorem call_decodedMessage_cro [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)))
    (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdm : spqrPolyApi.decoded_message dec = .ok outMsg)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = outA)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A decA dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
      stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
          stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeRoLoaded lsmpl sm.mem →
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  intro hcro
  refine sepWPp_call_frozen
    (fun _ _ h hkf => h.of_keepsFrozen hkf) hcro
    hcall (x := ⟨outA, decA, dec, outMsg⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf hcro_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpec]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hsorted, hdm⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (optVecU8At A outA outMsg ∗ polyDecoderAt A decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
          stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame =
        (optVecU8At A outA outMsg ∗ (polyDecoderAt A decA dec ∗
          (tokenInitPlacedAt ∗ (reduceTablePlacedAt ∗
            (A.pool ∗ stackAt sp_call polyDecoderDecodedMessageStack))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hcro_sf.1

private theorem call_dropGlueSortedSetPt16_cl [LibsignalPlacement]
    {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
    (arrA : BitVec 64) (vecs : List (List Pt))
    (hvecs_len : vecs.length = NUM_POLYS)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = arrA)
    (hsplit : P = (vecPtListOf A arrA vecs ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf
        ((memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        LibsignalCodeLoaded lsmpl sm.mem →
        SepWP prog target_pc sm Pm post) := by
  apply SepWP.done hpc hrun
  intro hcl
  refine SepWP.call_subroutine_frame hcall (x := ⟨arrA, vecs⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded, dropGlueSortedSetPt16Spec]
    rw [hsp]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hvecs_len⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [withLsCodeLoaded, dropGlueSortedSetPt16Spec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_
    have hassoc :
        (memRegion arrA polyArrayBytes ∗ A.pool ∗ stackAt sp_call dropGluePoly16Stack) ∗ Frame =
        (memRegion arrA polyArrayBytes ∗ (A.pool ∗ stackAt sp_call dropGluePoly16Stack)) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 3. Branch 1 (`outMsg = none`) -/

set_option maxHeartbeats 800000 in
private theorem header_sent_recv_ct1_chunk_none_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_337).rebase (blkPl_337).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec1 : PolyDecoder)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (hout : outRes = .stillReceiving { uc := st.uc, sending_ek := st.sending_ek, receiving_ct1 := dec1 })
    (g : AuthWords) (gdk : VecWords)
    {s0 s : State} {P R : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 1568#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_337).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1568#64)
    (hx19 : s.readReg64 .x19 = outA) (hx20 : s.readReg64 .x20 = stA)
    (_hx21 : s.readReg64 .x21 = st.uc.epoch) (_hx22 : s.readReg64 .x22 = chunkA)
    (hx23 : s.readReg64 .x23 = s0.sp - 1040#64) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (_hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hfp : s.readReg64 .fp = s0.sp - 64#64) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      optVecU8At A (s0.sp - 1064#64) none ∗ polyDecoderAt A (s0.sp - 1464#64) dec1 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 1568#64) polyDecoderDecodedMessageStack ∗
      memRegion outA 880 ∗ polyEncoderAt A stA st.sending_ek ∗
      wordsAt (stA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (stA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      ((stA + 472#64) ↦₆₄ st.uc.epoch) ∗ memRegion (stA + 480#64) 400 ∗ chunkAt chunkA chunk ∗
      ((s0.sp - 1568#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1560#64) ↦₆₄ st.uc.epoch) ∗
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) ∗
      memRegion (s0.sp - 1472#64) 8 ∗ memRegion (s0.sp - 1040#64) 96 ∗
      memRegion (s0.sp - 944#64) 400 ∗ memRegion (s0.sp - 544#64) 480 ∗ recvCt1SavedCells s0)) :
    SepWP ((blkPC_337).rebase (blkPl_337).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
            headerSentRecvChunkAt A outA outRes ∗ memRegion stA chunkedHeaderSentSize ∗
            chunkAt chunkA chunk ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool ∗ stackAt s0.sp headerSentRecvCt1ChunkStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  dsimp only [chunkedHeaderSentSize, optVecU8At, noneCap, AsmConstants.optionVecNoneWord] at *
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := s0.sp - 544#64) (n := 80) (k := 400)
        (b' := s0.sp - 464#64) rfl (by bv_omega) (by decide)]
    simp only [sepConj_assoc]
  wp_steps
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyDecoderAt A dec1) (s0.sp - 464#64) (s0.sp - 1464#64)
    (ret_pc := (blkPl_337).base + 312#64) (sp_call := s0.sp - 1568#64)
    rfl (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hsp])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx23, hx24, hx25, hx26, hx27, hfp, hvregs]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  have hst_auth :
      wordsAt (stA + 400#64) (authWordsList g) =
      (((stA + 400#64) ↦₆₄ g.v1.w0) ∗ ((stA + 408#64) ↦₆₄ g.v1.w1) ∗
       ((stA + 416#64) ↦₆₄ g.v1.w2) ∗ ((stA + 424#64) ↦₆₄ g.v2.w0) ∗
       ((stA + 432#64) ↦₆₄ g.v2.w1) ∗ ((stA + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]; simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk :
      wordsAt (stA + 448#64) (vecWordsList gdk) =
      (((stA + 448#64) ↦₆₄ gdk.w0) ∗ ((stA + 456#64) ↦₆₄ gdk.w1) ∗
       ((stA + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_544_words :
      wordsAt (s0.sp - 544#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
      (((s0.sp - 544#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 536#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 528#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 520#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 512#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 504#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 496#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 488#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 480#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 472#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_10, arm64_norm]
  refine SepWP.fold (cells_10_unfold (s0.sp - 544#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [hst_auth, hst_dk, wordsAt_10_sp_544]; simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_auth.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_544_words.symm) (by sep_focus) ?_
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyEncoderAt A st.sending_ek) (s0.sp - 944#64) stA
    (ret_pc := (blkPl_337).base + 352#64) (sp_call := s0.sp - 1568#64)
    rfl (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [trace_writeVReg128, arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hx20_1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  let outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F) :=
    { uc := st.uc, sending_ek := st.sending_ek, receiving_ct1 := dec1 }
  refine SepWP.fold (stA_880_rejoin stA g gdk st.uc.epoch) (by sep_focus) ?_
  refine SepWP.fold (sp_944_headerSent_recompose A s0.sp st outSt dec1 rfl g gdk) (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_chunkedHeaderSentAt A outSt) outA (s0.sp - 944#64)
    (ret_pc := (blkPl_337).base + 368#64) (sp_call := s0.sp - 1568#64)
    rfl (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm, hx19_2]) (by simp only [Reg.x1, arm64_norm, hsp2])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  have hnone_24 :
      ((s0.sp - 1064#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (s0.sp - 1056#64) 16 ⊢
      memRegion (s0.sp - 1064#64) 24 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1064#64) (n := 8) (k := 16)
        (b' := s0.sp - 1056#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
  refine SepWP.fold hnone_24 (by sep_focus) ?_
  wp_conv_pre => unfold recvCt1SavedCells
  wp_steps
  refine SepWP.fold (stackAt_1568_rejoin s0 0#64 st.uc.epoch
    (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) rfl)
    (by dsimp only [recvCt1SavedCells]; sep_focus) ?_
  subst hout
  dsimp only [headerSentRecvChunkAt]
  wp_done

/-! ## 4. Branch 2 (`outMsg = some ct1`) -/

set_option maxHeartbeats 800000 in
private theorem header_sent_recv_ct1_chunk_some_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_337).rebase (blkPl_337).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (hpt16 : subroutine_ok ((blkPC_337).rebase (blkPl_337).base (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec1 : PolyDecoder) (ct1 : Bytes)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (hout : outRes = .done { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk, ct1 := ct1 },
                             sending_ek := st.sending_ek })
    (g : AuthWords) (gdk : VecWords)
    {s0 s : State} {P R : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 1568#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_337).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1568#64)
    (hx19 : s.readReg64 .x19 = outA) (hx20 : s.readReg64 .x20 = stA)
    (hx21 : s.readReg64 .x21 = st.uc.epoch) (_hx22 : s.readReg64 .x22 = chunkA)
    (hx23 : s.readReg64 .x23 = s0.sp - 1040#64) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (_hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hfp : s.readReg64 .fp = s0.sp - 64#64) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      optVecU8At A (s0.sp - 1064#64) (some ct1) ∗ polyDecoderAt A (s0.sp - 1464#64) dec1 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool ∗
      stackAt (s0.sp - 1568#64) polyDecoderDecodedMessageStack ∗
      memRegion outA 880 ∗ polyEncoderAt A stA st.sending_ek ∗
      wordsAt (stA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (stA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      ((stA + 472#64) ↦₆₄ st.uc.epoch) ∗ memRegion (stA + 480#64) 400 ∗ chunkAt chunkA chunk ∗
      ((s0.sp - 1568#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1560#64) ↦₆₄ st.uc.epoch) ∗
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) ∗
      memRegion (s0.sp - 1472#64) 8 ∗ memRegion (s0.sp - 1040#64) 96 ∗
      memRegion (s0.sp - 944#64) 400 ∗ memRegion (s0.sp - 544#64) 480 ∗ recvCt1SavedCells s0)) :
    SepWP ((blkPC_337).rebase (blkPl_337).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
            headerSentRecvChunkAt A outA outRes ∗ memRegion stA chunkedHeaderSentSize ∗
            chunkAt chunkA chunk ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool ∗ stackAt s0.sp headerSentRecvCt1ChunkStack ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  dsimp only [chunkedHeaderSentSize, optVecU8At] at *
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 264)
  refine SepWP.fold (vecU8_extract_with_cap_lt A (s0.sp - 1064#64) ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i gct1
  wp_focus_pure; intro hcap_lt
  have hadds_z := cap_add_one_beq_zero_false hcap_lt
  have hct1_words :
      wordsAt (s0.sp - 1064#64) (vecWordsList gct1) =
      (((s0.sp - 1064#64) ↦₆₄ gct1.w0) ∗ ((s0.sp - 1056#64) ↦₆₄ gct1.w1) ∗
       ((s0.sp - 1048#64) ↦₆₄ gct1.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, arm64_norm]
  have hsp_1552_words :
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
      (((s0.sp - 1552#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 1544#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 1536#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 1528#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 1520#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 1512#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 1504#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 1496#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 1488#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 1480#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_10, arm64_norm]
  have hst_auth :
      wordsAt (stA + 400#64) (authWordsList g) =
      (((stA + 400#64) ↦₆₄ g.v1.w0) ∗ ((stA + 408#64) ↦₆₄ g.v1.w1) ∗
       ((stA + 416#64) ↦₆₄ g.v1.w2) ∗ ((stA + 424#64) ↦₆₄ g.v2.w0) ∗
       ((stA + 432#64) ↦₆₄ g.v2.w1) ∗ ((stA + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]; simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk :
      wordsAt (stA + 448#64) (vecWordsList gdk) =
      (((stA + 448#64) ↦₆₄ gdk.w0) ∗ ((stA + 456#64) ↦₆₄ gdk.w1) ∗
       ((stA + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_544_words12 :
      wordsAt ((s0.sp - 944#64) + 400#64) (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) =
      (((s0.sp - 544#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 536#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 528#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 520#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 512#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 504#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 496#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 488#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 480#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 472#64) ↦₆₄ gct1.w0) ∗
       ((s0.sp - 464#64) ↦₆₄ gct1.w1) ∗ ((s0.sp - 456#64) ↦₆₄ gct1.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_12, arm64_norm]
  have hsp_1040_words12 :
      wordsAt (s0.sp - 1040#64) (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) =
      (((s0.sp - 1040#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 1032#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 1024#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 1016#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 1008#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 1000#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 992#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 984#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 976#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 968#64) ↦₆₄ gct1.w0) ∗
       ((s0.sp - 960#64) ↦₆₄ gct1.w1) ∗ ((s0.sp - 952#64) ↦₆₄ gct1.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_12, arm64_norm]
  wp_conv_pre =>
    rw [hct1_words, hsp_1552_words, hst_auth, hst_dk,
        ProofLib.memRegion_split' (b := outA) (n := 8) (k := 872) (b' := outA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 8#64) (n := 496) (k := 376) (b' := outA + 504#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 504#64) (n := 8) (k := 368) (b' := outA + 512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 944#64) (n := 8) (k := 392)
          (b' := s0.sp - 936#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 544#64) (n := 96) (k := 384)
          (b' := s0.sp - 448#64) rfl (by bv_omega) (by decide)]
    simp only [sepConj_assoc]
  refine SepWP.fold (cells_1_unfold outA) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (outA + 504#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 944#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_12_unfold (s0.sp - 1040#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_12_unfold (s0.sp - 544#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [wordsAt_12_sp_1040, wordsAt_12_sp_544]; simp only [sepConj_assoc]
  wp_steps
  refine SepWP.fold (Entails.of_eq hsp_1552_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_auth.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hct1_words.symm) (by sep_focus) ?_
  refine SepWP.fold (wordsAt_entails_memRegion (vecWordsList gct1) (s0.sp - 1064#64) 24 rfl) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_1040_words12.symm) (by sep_focus) ?_
  refine SepWP.fold (wordsAt_entails_memRegion (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) (s0.sp - 1040#64) 96 rfl) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_544_words12.symm) (by sep_focus) ?_
  refine SepWP.fold (cell_0_rejoin_400 s0.sp 944#64 936#64 st.uc.epoch (by bv_omega)) (by sep_focus) ?_
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyEncoderAt A st.sending_ek) (s0.sp - 944#64) stA
    (ret_pc := (blkPl_337).base + 232#64) (sp_call := s0.sp - 1568#64)
    rfl (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [trace_writeVReg128, arm64_norm, htrace])
    (by simp only [Reg.x0, arm64_norm, hsp]) (by simp only [Reg.x1, arm64_norm, hx20])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, hfp, hvregs]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (stA_880_rejoin stA g gdk st.uc.epoch) (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyEncoder_and_words12 A st.sending_ek
      (authWordsList g ++ vecWordsList gdk ++ vecWordsList gct1) rfl)
    (outA + 8#64) (s0.sp - 944#64)
    (ret_pc := (blkPl_337).base + 248#64) (sp_call := s0.sp - 1568#64)
    rfl (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx19_1]) (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  have hrejoin_880 :
      memRegion (s0.sp - 944#64) 496 ∗ memRegion (s0.sp - 448#64) 384 ⊢
      memRegion (s0.sp - 944#64) 880 := by
    rw [← ProofLib.memRegion_split' (b := s0.sp - 944#64) (n := 496) (k := 384)
        (b' := s0.sp - 448#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine SepWP.fold hrejoin_880 (by sep_focus) ?_
  refine SepWP.fold (polyDecoderAt_entails_vecs_tail A (s0.sp - 1464#64) dec1) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs
  wp_focus_pure; intro hvecs_len
  wp_conv_pre => rw [stackAt_decodedMessage_to_dropPoly16 (s0.sp - 1568#64)]
  wp_steps
  refine SepWP.fold (outA_done_recompose A outA st ct1 outRes hout g gdk gct1) (by sep_focus) ?_
  refine call_dropGlueSortedSetPt16_cl hpt16 (s0.sp - 1464#64) vecs hvecs_len (s0 := s0)
    (ret_pc := (blkPl_337).base + 268#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr2])
    (by simp only [Reg.x0, arm64_norm, hsp2]) (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  refine SepWP.fold (polyDecoder_post_join (s0.sp - 1464#64)) (by sep_focus) ?_
  refine SepWP.fold (stackAt_decodedMessage_from_dropPoly16 (s0.sp - 1568#64)) (by sep_focus) ?_
  wp_conv_pre => unfold recvCt1SavedCells
  wp_steps
  refine SepWP.fold (stackAt_1568_rejoin s0 0#64 st.uc.epoch
    (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) rfl)
    (by dsimp only [recvCt1SavedCells]; sep_focus) ?_
  wp_done

/-! ## 5. Main Theorems: `<HeaderSent>::recv_ct1_chunk` (Block `337`, 113 insns) -/

attribute [local irreducible] Chunked.SendEk.HeaderSent.recv_ct1_chunk

set_option maxHeartbeats 800000 in
/-- Relocatable `<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk` (Block `337`, 113 insns)
    parameterized by `add_chunk` (Block `419`), `decoded_message` (Block `418`), and
    `drop_glue::<[SortedSet<Pt>; 16]>` (Block `264`). -/
theorem header_sent_recv_ct1_chunk_placed_cl_ext_of_drop [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hadd : subroutine_ok (lsProg_337 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec A)))
    (hdec : subroutine_ok (lsProg_337 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A)))
    (hpt16 : subroutine_ok (lsProg_337 (Rust.withPanics ext))
      (lsmpl.base 264) (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A))) :
    HeaderSentRecvCt1ChunkPlacedOkX A F ext := by
  unfold HeaderSentRecvCt1ChunkPlacedOkX
  have hmemcpy : subroutine_ok (lsProg_337 (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec :=
    spqr_hook_ok_of_mem (sym := "memcpy") hmemcpy_sat
  apply subroutine_ok_withLsCodeRoLoaded_of_left
  simp only [lsProg_337] at hmemcpy hadd hdec hpt16 ⊢
  unfold headerSentRecvCt1ChunkPlacedSpec
  wpp_init x s0
  conv => arg 6; ext sf P_f; rw [sepConj_assoc]
  have hcro0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  rcases x with ⟨outA, stA, chunkA, st, chunk, outRes⟩
  have h_none := header_sent_recv_ct1_chunk_none_placed (A := A) (F := F) hmemcpy
  have h_some := header_sent_recv_ct1_chunk_some_placed (A := A) (F := F) hmemcpy hpt16
  dsimp only [chunkedHeaderSentSize] at *
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = st.uc.epoch := by assumption
  have hsorted : PolyDecoderStrictSorted st.receiving_ct1 := by assumption
  have hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes := by assumption
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hfsp_align : ((s0.sp - 1568#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 1568#64 hsp0_align (by decide)
  apply of_sepWP_lscro hcro0 (mid := lsmpl.base 419)
  wp_conv_pre =>
    rw [stackAt_1568_split s0.sp,
        stackAt_decodedMessage_to_addChunk (s0.sp - 1568#64)]
    unfold chunkedHeaderSentAt
  refine SepWP.fold (polyDecoderAt_dup_pts_len A (s0.readReg64 (Reg.gpr 1#5) + 480#64) st.receiving_ct1)
    (by sep_focus) ?_
  wp_focus_pure; intro hpts
  obtain ⟨outMsg, hdm, hcases⟩ := header_sent_recv_ct1_chunk_ok_elim hpts hrecv
  wp_conv_pre => rw [unchunkedEkSentAt_400_eq]
  refine SepWP.fold (authenticatorAt_extract A (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.fold (vecU8_extract A (s0.readReg64 (Reg.gpr 1#5) + 448#64) st.uc.dk)
    (by sep_focus) ?_
  wp_pull_exists; rename_i gdk
  have hst_auth :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (authWordsList g) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]; simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 448#64) (vecWordsList gdk) =
      (((s0.readReg64 (Reg.gpr 1#5) + 448#64) ↦₆₄ gdk.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 456#64) ↦₆₄ gdk.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_1552_words :
      wordsAt (s0.sp - 1552#64) (authWordsList g ++ vecWordsList gdk ++ [st.uc.epoch]) =
      (((s0.sp - 1552#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 1544#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 1536#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 1528#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 1520#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 1512#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 1504#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 1496#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 1488#64) ↦₆₄ gdk.w2) ∗ ((s0.sp - 1480#64) ↦₆₄ st.uc.epoch)) := by
    dsimp only [authWordsList, vecWordsList, List.append]; simp only [wordsAt_10, arm64_norm]
  refine SepWP.fold (cells_1_unfold (s0.sp - 1568#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 1560#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_10_unfold (s0.sp - 1552#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_8_unfold (s0.sp - 64#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [hst_auth, hst_dk, wordsAt_10_sp_1552, sp_sub_64_add_8, sp_sub_64_add_16,
    sp_sub_64_add_24, sp_sub_64_add_32, sp_sub_64_add_40, sp_sub_64_add_48, sp_sub_64_add_56]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_auth.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_1552_words.symm) (by sep_focus) ?_
  have hfold_saved :
      (((s0.sp - 64#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      recvCt1SavedCells s0 := Entails.refl _
  refine SepWP.fold hfold_saved (by dsimp only [Reg.fp, Reg.lr, Reg.x28, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_focus) ?_
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyDecoderAt A st.receiving_ct1)
    (s0.sp - 1464#64) (s0.readReg64 (Reg.gpr 1#5) + 480#64)
    (ret_pc := (blkPl_337).base + 104#64) (sp_call := s0.sp - 1568#64)
    rfl (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [trace_writeVReg128, arm64_norm])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx2]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  wp_steps
  refine call_addChunk_cro hadd (s0.sp - 1464#64) (s0.readReg64 (Reg.gpr 3#5)) st.receiving_ct1 chunk hsorted
    (s0 := s0) (ret_pc := (blkPl_337).base + 116#64) (next_pc := lsmpl.base 418) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) htr1
    (by simp only [Reg.x0, arm64_norm, hsp1]) (by simp only [Reg.x1, arm64_norm, hx22_1])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 hsorted1 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.fold (stackAt_decodedMessage_from_addChunk (s0.sp - 1568#64)) (by sep_focus) ?_
  wp_steps
  refine call_decodedMessage_cro hdec (s0.sp - 1064#64) (s0.sp - 1464#64)
    (addChunkTotal st.receiving_ct1 chunk) outMsg hsorted1 hdm
    (s0 := s0) (ret_pc := (blkPl_337).base + 128#64) (sp_call := s0.sp - 1568#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) htr2
    (by simp only [Reg.x8, arm64_norm, hsp2]) (by simp only [Reg.x0, arm64_norm, hsp2])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 hcl3 => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2]
    at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
  rcases hcases with ⟨rfl, hout⟩ | ⟨ct1, rfl, hout⟩
  · refine h_none (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
      st chunk (addChunkTotal st.receiving_ct1 chunk) outRes hout g gdk
      hsp0_align hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
      hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3 htr3 ?_
    ac_rfl
  · refine h_some (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
      st chunk (addChunkTotal st.receiving_ct1 chunk) ct1 outRes hout g gdk
      hcl3 hsp0_align hfsp_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
      hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3 htr3 ?_
    ac_rfl

/-- `[LibsignalPlacement]` contract for `<spqr::v1::chunked::send_ek::HeaderSent>::recv_ct1_chunk`
    (Block `337`), discharging `drop_glue::<[SortedSet<Pt>; 16]>` (Block `264`) from `hdealloc`
    and taking `add_chunk` (Block `419`) and `decoded_message` (Block `418`). -/
theorem header_sent_recv_ct1_chunk_placed_cl_ext [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) "memcpy" sessionMemcpyRegionSpec)
    (hadd : subroutine_ok (lsProg_337 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpec A)))
    (hdec : subroutine_ok (lsProg_337 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec A))) :
    HeaderSentRecvCt1ChunkPlacedOkX A F ext :=
  header_sent_recv_ct1_chunk_placed_cl_ext_of_drop
    hmemcpy hadd hdec
    (ls_subroutine_ok_of_block (i := 337) (j := 264)
      (subroutine_ok_withLsCodeLoaded_of_plain
        (drop_glue_sorted_set_pt16_placed_ok (spqr_hook_ok_of_mem hdealloc))))

end CryptoVerification.SpqrV1.States.Leaves
