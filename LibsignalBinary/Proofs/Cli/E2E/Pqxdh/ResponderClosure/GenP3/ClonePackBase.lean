/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Segment 5 Packing Helpers

Spatial layout decomposition of `memRegion (sp + 0xa90#64) 344` into destination stack cells and
reassembly into `∃∗ G₁ : SessionGhost, ⌜CloneRel recG G₁⌝ ∗ sessionStateAt A (sp + 0xa90#64) G₁ st`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-- Uninitialized cell values of the 344-byte destination `SessionStructure` slot at `sp + 0xa90`. -/
structure PackDstVals where
  ua90 : BitVec 64
  ua98 : BitVec 64
  uaa0 : BitVec 64
  uaa8 : BitVec 64
  uab0 : BitVec 64
  uab8 : BitVec 64
  uac0 : BitVec 64
  uac8 : BitVec 64
  uad0 : BitVec 64
  uad8 : BitVec 64
  uae0 : BitVec 64
  uae8 : BitVec 64
  uaf0 : BitVec 64
  uaf8 : BitVec 64
  ub00 : BitVec 64
  ub08 : BitVec 64
  ub10 : BitVec 64
  ub18 : BitVec 64
  ub20 : BitVec 64
  ub28 : BitVec 64
  ub30 : BitVec 64
  ub38 : BitVec 64
  ub40 : BitVec 64
  ub48 : BitVec 64
  ub50 : BitVec 64
  ub58 : BitVec 64
  ub60 : BitVec 64
  ub68 : BitVec 64
  ub70 : BitVec 64
  ub78 : BitVec 64
  ub80 : BitVec 64
  ub88 : BitVec 64
  ub90 : BitVec 64
  ub98 : BitVec 64
  uba0 : BitVec 32
  uba4 : BitVec 32
  uba8 : BitVec 64
  ubb0 : BitVec 32
  ubb8 : BitVec 64
  ubc0 : BitVec 64
  ubc8 : BitVec 64
  ubd0 : BitVec 32
  ubd8 : BitVec 32
  ubdc : BitVec 32
  ube0 : BitVec 32
  ube4 : BitVec 32

/-- Spatial layout of the 344-byte destination `SessionStructure` slot at `sp + 0xa90`. -/
def packDstSlotsAt (sp : BitVec 64) (dv : PackDstVals) : SepProp :=
  ((sp + 0xa90#64) ↦₆₄ dv.ua90) ∗ ((sp + 0xa98#64) ↦₆₄ dv.ua98) ∗ ((sp + 0xaa0#64) ↦₆₄ dv.uaa0) ∗
  ((sp + 0xaa8#64) ↦₆₄ dv.uaa8) ∗ ((sp + 0xab0#64) ↦₆₄ dv.uab0) ∗ ((sp + 0xab8#64) ↦₆₄ dv.uab8) ∗
  ((sp + 0xac0#64) ↦₆₄ dv.uac0) ∗ ((sp + 0xac8#64) ↦₆₄ dv.uac8) ∗ ((sp + 0xad0#64) ↦₆₄ dv.uad0) ∗
  ((sp + 0xad8#64) ↦₆₄ dv.uad8) ∗ ((sp + 0xae0#64) ↦₆₄ dv.uae0) ∗ ((sp + 0xae8#64) ↦₆₄ dv.uae8) ∗
  ((sp + 0xaf0#64) ↦₆₄ dv.uaf0) ∗ ((sp + 0xaf8#64) ↦₆₄ dv.uaf8) ∗ ((sp + 0xb00#64) ↦₆₄ dv.ub00) ∗
  ((sp + 0xb08#64) ↦₆₄ dv.ub08) ∗ ((sp + 0xb10#64) ↦₆₄ dv.ub10) ∗ ((sp + 0xb18#64) ↦₆₄ dv.ub18) ∗
  ((sp + 0xb20#64) ↦₆₄ dv.ub20) ∗
  ((sp + 0xb28#64) ↦₆₄ dv.ub28) ∗ ((sp + 0xb30#64) ↦₆₄ dv.ub30) ∗ ((sp + 0xb38#64) ↦₆₄ dv.ub38) ∗
  ((sp + 0xb40#64) ↦₆₄ dv.ub40) ∗ ((sp + 0xb48#64) ↦₆₄ dv.ub48) ∗ ((sp + 0xb50#64) ↦₆₄ dv.ub50) ∗
  ((sp + 0xb58#64) ↦₆₄ dv.ub58) ∗ ((sp + 0xb60#64) ↦₆₄ dv.ub60) ∗ ((sp + 0xb68#64) ↦₆₄ dv.ub68) ∗
  ((sp + 0xb70#64) ↦₆₄ dv.ub70) ∗ ((sp + 0xb78#64) ↦₆₄ dv.ub78) ∗ ((sp + 0xb80#64) ↦₆₄ dv.ub80) ∗
  ((sp + 0xb88#64) ↦₆₄ dv.ub88) ∗ ((sp + 0xb90#64) ↦₆₄ dv.ub90) ∗ ((sp + 0xb98#64) ↦₆₄ dv.ub98) ∗
  ((sp + 0xba0#64) ↦₃₂ dv.uba0) ∗ ((sp + 0xba4#64) ↦₃₂ dv.uba4) ∗ ((sp + 0xba8#64) ↦₆₄ dv.uba8) ∗
  ((sp + 0xbb0#64) ↦₃₂ dv.ubb0) ∗ memRegion (sp + 0xbb4#64) 4 ∗
  ((sp + 0xbb8#64) ↦₆₄ dv.ubb8) ∗ ((sp + 0xbc0#64) ↦₆₄ dv.ubc0) ∗ ((sp + 0xbc8#64) ↦₆₄ dv.ubc8) ∗
  ((sp + 0xbd0#64) ↦₃₂ dv.ubd0) ∗ memRegion (sp + 0xbd4#64) 4 ∗
  ((sp + 0xbd8#64) ↦₃₂ dv.ubd8) ∗ ((sp + 0xbdc#64) ↦₃₂ dv.ubdc) ∗
  ((sp + 0xbe0#64) ↦₃₂ dv.ube0) ∗ ((sp + 0xbe4#64) ↦₃₂ dv.ube4)

set_option maxHeartbeats 400000 in
theorem memRegion_344_entails_packDstSlotsAt (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 344 ⊢ ∃∗ dv : PackDstVals, packDstSlotsAt sp dv := by
  rw [← sepConj_emp (memRegion (sp + 0xa90#64) 344)]
  refine elim_region8 (b' := sp + 0xa98#64) (rem := 336) rfl (by bv_arith) (by decide) fun ua90 => ?_
  refine elim_region8 (b' := sp + 0xaa0#64) (rem := 328) rfl (by bv_arith) (by decide) fun ua98 => ?_
  refine elim_region8 (b' := sp + 0xaa8#64) (rem := 320) rfl (by bv_arith) (by decide) fun uaa0 => ?_
  refine elim_region8 (b' := sp + 0xab0#64) (rem := 312) rfl (by bv_arith) (by decide) fun uaa8 => ?_
  refine elim_region8 (b' := sp + 0xab8#64) (rem := 304) rfl (by bv_arith) (by decide) fun uab0 => ?_
  refine elim_region8 (b' := sp + 0xac0#64) (rem := 296) rfl (by bv_arith) (by decide) fun uab8 => ?_
  refine elim_region8 (b' := sp + 0xac8#64) (rem := 288) rfl (by bv_arith) (by decide) fun uac0 => ?_
  refine elim_region8 (b' := sp + 0xad0#64) (rem := 280) rfl (by bv_arith) (by decide) fun uac8 => ?_
  refine elim_region8 (b' := sp + 0xad8#64) (rem := 272) rfl (by bv_arith) (by decide) fun uad0 => ?_
  refine elim_region8 (b' := sp + 0xae0#64) (rem := 264) rfl (by bv_arith) (by decide) fun uad8 => ?_
  refine elim_region8 (b' := sp + 0xae8#64) (rem := 256) rfl (by bv_arith) (by decide) fun uae0 => ?_
  refine elim_region8 (b' := sp + 0xaf0#64) (rem := 248) rfl (by bv_arith) (by decide) fun uae8 => ?_
  refine elim_region8 (b' := sp + 0xaf8#64) (rem := 240) rfl (by bv_arith) (by decide) fun uaf0 => ?_
  refine elim_region8 (b' := sp + 0xb00#64) (rem := 232) rfl (by bv_arith) (by decide) fun uaf8 => ?_
  refine elim_region8 (b' := sp + 0xb08#64) (rem := 224) rfl (by bv_arith) (by decide) fun ub00 => ?_
  refine elim_region8 (b' := sp + 0xb10#64) (rem := 216) rfl (by bv_arith) (by decide) fun ub08 => ?_
  refine elim_region8 (b' := sp + 0xb18#64) (rem := 208) rfl (by bv_arith) (by decide) fun ub10 => ?_
  refine elim_region8 (b' := sp + 0xb20#64) (rem := 200) rfl (by bv_arith) (by decide) fun ub18 => ?_
  refine elim_region8 (b' := sp + 0xb28#64) (rem := 192) rfl (by bv_arith) (by decide) fun ub20 => ?_
  refine elim_region8 (b' := sp + 0xb30#64) (rem := 184) rfl (by bv_arith) (by decide) fun ub28 => ?_
  refine elim_region8 (b' := sp + 0xb38#64) (rem := 176) rfl (by bv_arith) (by decide) fun ub30 => ?_
  refine elim_region8 (b' := sp + 0xb40#64) (rem := 168) rfl (by bv_arith) (by decide) fun ub38 => ?_
  refine elim_region8 (b' := sp + 0xb48#64) (rem := 160) rfl (by bv_arith) (by decide) fun ub40 => ?_
  refine elim_region8 (b' := sp + 0xb50#64) (rem := 152) rfl (by bv_arith) (by decide) fun ub48 => ?_
  refine elim_region8 (b' := sp + 0xb58#64) (rem := 144) rfl (by bv_arith) (by decide) fun ub50 => ?_
  refine elim_region8 (b' := sp + 0xb60#64) (rem := 136) rfl (by bv_arith) (by decide) fun ub58 => ?_
  refine elim_region8 (b' := sp + 0xb68#64) (rem := 128) rfl (by bv_arith) (by decide) fun ub60 => ?_
  refine elim_region8 (b' := sp + 0xb70#64) (rem := 120) rfl (by bv_arith) (by decide) fun ub68 => ?_
  refine elim_region8 (b' := sp + 0xb78#64) (rem := 112) rfl (by bv_arith) (by decide) fun ub70 => ?_
  refine elim_region8 (b' := sp + 0xb80#64) (rem := 104) rfl (by bv_arith) (by decide) fun ub78 => ?_
  refine elim_region8 (b' := sp + 0xb88#64) (rem := 96) rfl (by bv_arith) (by decide) fun ub80 => ?_
  refine elim_region8 (b' := sp + 0xb90#64) (rem := 88) rfl (by bv_arith) (by decide) fun ub88 => ?_
  refine elim_region8 (b' := sp + 0xb98#64) (rem := 80) rfl (by bv_arith) (by decide) fun ub90 => ?_
  refine elim_region8 (b' := sp + 0xba0#64) (rem := 72) rfl (by bv_arith) (by decide) fun ub98 => ?_
  refine elim_region4 (b' := sp + 0xba4#64) (rem := 68) rfl (by bv_arith) (by decide) fun uba0 => ?_
  refine elim_region4 (b' := sp + 0xba8#64) (rem := 64) rfl (by bv_arith) (by decide) fun uba4 => ?_
  refine elim_region8 (b' := sp + 0xbb0#64) (rem := 56) rfl (by bv_arith) (by decide) fun uba8 => ?_
  refine elim_region4 (b' := sp + 0xbb4#64) (rem := 52) rfl (by bv_arith) (by decide) fun ubb0 => ?_
  refine elim_region_skip (b' := sp + 0xbb8#64) (n := 4) (rem := 48) rfl (by bv_arith) (by decide) ?_
  refine elim_region8 (b' := sp + 0xbc0#64) (rem := 40) rfl (by bv_arith) (by decide) fun ubb8 => ?_
  refine elim_region8 (b' := sp + 0xbc8#64) (rem := 32) rfl (by bv_arith) (by decide) fun ubc0 => ?_
  refine elim_region8 (b' := sp + 0xbd0#64) (rem := 24) rfl (by bv_arith) (by decide) fun ubc8 => ?_
  refine elim_region4 (b' := sp + 0xbd4#64) (rem := 20) rfl (by bv_arith) (by decide) fun ubd0 => ?_
  refine elim_region_skip (b' := sp + 0xbd8#64) (n := 4) (rem := 16) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0xbdc#64) (rem := 12) rfl (by bv_arith) (by decide) fun ubd8 => ?_
  refine elim_region4 (b' := sp + 0xbe0#64) (rem := 8) rfl (by bv_arith) (by decide) fun ubdc => ?_
  refine elim_region4 (b' := sp + 0xbe4#64) (rem := 4) rfl (by bv_arith) (by decide) fun ube0 => ?_
  rw [memRegion_four (sp + 0xbe4#64), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ube4
  refine Entails.sepExists_right
    ⟨ua90, ua98, uaa0, uaa8, uab0, uab8, uac0, uac8, uad0, uad8, uae0, uae8, uaf0, uaf8, ub00,
      ub08, ub10, ub18, ub20, ub28, ub30, ub38, ub40, ub48, ub50, ub58, ub60, ub68, ub70, ub78,
      ub80, ub88, ub90, ub98, uba0, uba4, uba8, ubb0, ubb8, ubc0, ubc8, ubd0, ubd8, ubdc, ube0,
      ube4⟩ ?_
  dsimp only [packDstSlotsAt]
  exact Entails.of_eq (by ac_rfl)

/-- Spatial layout of the 344-byte destination `SessionStructure` slot at `sp + 0xa90` after
storing all cloned fields from `w : GenP3J4Witness` and `w20 : BitVec 32`. -/
def packDstSlotsWrittenAt (sp : BitVec 64) (recG : SessionGhost)
    (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness) (w20 : BitVec 32) : SepProp :=
  let locIdLen := BitVec.ofNat 64 recG.localIk.bytes.length
  let remIdLen := BitVec.ofNat 64 recG.remoteIk.bytes.length
  let rcLen := BitVec.ofNat 64 st.receiverChains.length
  let aliceLen := BitVec.ofNat 64 recG.alice.bytes.length
  let pqLen := BitVec.ofNat 64 st.pqRatchetState.length
  ((sp + 0xa90#64) ↦₆₄ locIdLen) ∗ ((sp + 0xa98#64) ↦₆₄ w.newLocIdPtr) ∗ ((sp + 0xaa0#64) ↦₆₄ locIdLen) ∗
  ((sp + 0xaa8#64) ↦₆₄ remIdLen) ∗ ((sp + 0xab0#64) ↦₆₄ w.newRemIdPtr) ∗ ((sp + 0xab8#64) ↦₆₄ remIdLen) ∗
  ((sp + 0xac0#64) ↦₆₄ 32#64) ∗ ((sp + 0xac8#64) ↦₆₄ w.newRootKeyPtr) ∗ ((sp + 0xad0#64) ↦₆₄ 32#64) ∗
  ((sp + 0xad8#64) ↦₆₄ rcLen) ∗ ((sp + 0xae0#64) ↦₆₄ w.newRcPtr) ∗ ((sp + 0xae8#64) ↦₆₄ rcLen) ∗
  ((sp + 0xaf0#64) ↦₆₄ aliceLen) ∗ ((sp + 0xaf8#64) ↦₆₄ w.newAlicePtr) ∗ ((sp + 0xb00#64) ↦₆₄ aliceLen) ∗
  ((sp + 0xb08#64) ↦₆₄ pqLen) ∗ ((sp + 0xb10#64) ↦₆₄ w.newPqPtr) ∗ ((sp + 0xb18#64) ↦₆₄ pqLen) ∗
  ((sp + 0xb20#64) ↦₆₄ w.c0) ∗
  ((sp + 0xb28#64) ↦₆₄ w.sq0.extractLsb' 0 64) ∗ ((sp + 0xb30#64) ↦₆₄ w.sq0.extractLsb' 64 64) ∗
  ((sp + 0xb38#64) ↦₆₄ w.sq1.extractLsb' 0 64) ∗ ((sp + 0xb40#64) ↦₆₄ w.sq1.extractLsb' 64 64) ∗
  ((sp + 0xb48#64) ↦₆₄ w.sq2.extractLsb' 0 64) ∗ ((sp + 0xb50#64) ↦₆₄ w.sq2.extractLsb' 64 64) ∗
  ((sp + 0xb58#64) ↦₆₄ w.sq3.extractLsb' 0 64) ∗ ((sp + 0xb60#64) ↦₆₄ w.sq3.extractLsb' 64 64) ∗
  ((sp + 0xb68#64) ↦₆₄ w.sq4.extractLsb' 0 64) ∗ ((sp + 0xb70#64) ↦₆₄ w.sq4.extractLsb' 64 64) ∗
  ((sp + 0xb78#64) ↦₆₄ w.sq5.extractLsb' 0 64) ∗ ((sp + 0xb80#64) ↦₆₄ w.sq5.extractLsb' 64 64) ∗
  ((sp + 0xb88#64) ↦₆₄ w.pendCap') ∗ ((sp + 0xb90#64) ↦₆₄ w.pendPtr') ∗ ((sp + 0xb98#64) ↦₆₄ w.pendCap') ∗
  ((sp + 0xba0#64) ↦₃₂ w.w2c) ∗ ((sp + 0xba4#64) ↦₃₂ w20) ∗ ((sp + 0xba8#64) ↦₆₄ w.d10) ∗
  ((sp + 0xbb0#64) ↦₃₂ w.w28) ∗ memRegion (sp + 0xbb4#64) 4 ∗
  ((sp + 0xbb8#64) ↦₆₄ w.kybCap') ∗ ((sp + 0xbc0#64) ↦₆₄ w.kybPtr') ∗ ((sp + 0xbc8#64) ↦₆₄ w.kybCap') ∗
  ((sp + 0xbd0#64) ↦₃₂ w.w24) ∗ memRegion (sp + 0xbd4#64) 4 ∗
  ((sp + 0xbd8#64) ↦₃₂ st.sessionVersion) ∗ ((sp + 0xbdc#64) ↦₃₂ st.previousCounter) ∗
  ((sp + 0xbe0#64) ↦₃₂ w.regW0) ∗ ((sp + 0xbe4#64) ↦₃₂ w.regW1)

theorem chunks96_6QAt_sp_0xb28 (sp : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) :
    chunks96_6QAt (sp + 0xb28#64) sq0 sq1 sq2 sq3 sq4 sq5 =
      ((sp + 0xb28#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((sp + 0xb30#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
      ((sp + 0xb38#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((sp + 0xb40#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
      ((sp + 0xb48#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((sp + 0xb50#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
      ((sp + 0xb58#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((sp + 0xb60#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
      ((sp + 0xb68#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((sp + 0xb70#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
      ((sp + 0xb78#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((sp + 0xb80#64) ↦₆₄ sq5.extractLsb' 64 64) := by
  unfold chunks96_6QAt
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

set_option maxHeartbeats 400000 in
theorem packDstSlotsWrittenAt_entails_sessionStateAt
    (A : RustAlloc) (sp : BitVec 64) (recG : SessionGhost)
    (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness) (w20 : BitVec 32)
    (h_loc_deser : PublicKey.deserialize recG.localIk.bytes = .ok st.localIdentity.publicKey)
    (h_rem_deser : match st.remoteIdentity with
      | none => recG.remoteIk.bytes = []
      | some ik => PublicKey.deserialize recG.remoteIk.bytes = .ok ik.publicKey)
    (h_pend_some : recG.pending.isSome = st.pendingPreKey)
    (h_reg_len : recG.regIds.length = 8)
    (h_loc_len : recG.localIk.bytes.length = 33)
    (h_rem_len : st.remoteIdentity.isSome → recG.remoteIk.bytes.length = 33)
    (hreg_eq : recG.regIds = unpack32 w.regW0 ++ unpack32 w.regW1)
    (hchains_len : w.chains'.length = st.receiverChains.length)
    (hsc_inl : OptSenderChainInline w.sender' st.senderChain
      (bytes104OfW6Q w.c0 w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5)) :
    (packDstSlotsWrittenAt sp recG st w w20 ∗
      vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
      vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
      vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
        (w.chains'.zip st.receiverChains) ∗
      vecU8Buf A (BitVec.ofNat 64 recG.alice.bytes.length) w.newAlicePtr recG.alice.bytes ∗
      vecU8Buf A (BitVec.ofNat 64 st.pqRatchetState.length) w.newPqPtr st.pqRatchetState ∗
      optSenderChainHeap A w.sender' st.senderChain ∗
      OptPendClone A recG.pending w.pendCap' w.pendPtr' ∗
      OptKybClone A recG.kyber w.kybCap' w.kybPtr') ⊢
      ∃∗ G₁ : SessionGhost,
        ⌜CloneRel recG G₁⌝ ∗ sessionStateAt A (sp + 0xa90#64) G₁ st := by
  let localIk' : VecGhost := ⟨BitVec.ofNat 64 recG.localIk.bytes.length, w.newLocIdPtr, recG.localIk.bytes⟩
  let remoteIk' : VecGhost := ⟨BitVec.ofNat 64 recG.remoteIk.bytes.length, w.newRemIdPtr, recG.remoteIk.bytes⟩
  let alice' : VecGhost := ⟨BitVec.ofNat 64 recG.alice.bytes.length, w.newAlicePtr, recG.alice.bytes⟩
  let chainsCap' := BitVec.ofNat 64 st.receiverChains.length
  let pqCap' := BitVec.ofNat 64 st.pqRatchetState.length
  have hloc_hdr :
      ((sp + 0xa90#64) ↦₆₄ localIk'.cap) ∗ ((sp + 0xa98#64) ↦₆₄ localIk'.ptr) ∗
        ((sp + 0xaa0#64) ↦₆₄ localIk'.cap) ∗
        vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes =
      vecGhostAt A localIk' (sp + 0xa90#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : sp + 0xa90#64 + 8#64 = sp + 0xa98#64 := by bv_arith
    have h2 : sp + 0xa90#64 + 16#64 = sp + 0xaa0#64 := by bv_arith
    rw [h1, h2]
    ac_rfl
  have hrem_hdr :
      ((sp + 0xaa8#64) ↦₆₄ remoteIk'.cap) ∗ ((sp + 0xab0#64) ↦₆₄ remoteIk'.ptr) ∗
        ((sp + 0xab8#64) ↦₆₄ remoteIk'.cap) ∗
        vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes =
      vecGhostAt A remoteIk' (sp + 0xa90#64 + 0x18#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h0 : sp + 0xa90#64 + 0x18#64 = sp + 0xaa8#64 := by bv_arith
    have h1 : sp + 0xaa8#64 + 8#64 = sp + 0xab0#64 := by bv_arith
    have h2 : sp + 0xaa8#64 + 16#64 = sp + 0xab8#64 := by bv_arith
    rw [h0, h1, h2]
    ac_rfl
  have hroot_hdr :
      ((sp + 0xac0#64) ↦₆₄ 32#64) ∗ ((sp + 0xac8#64) ↦₆₄ w.newRootKeyPtr) ∗
        ((sp + 0xad0#64) ↦₆₄ 32#64) ∗
        vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) =
      vecU8At A (sp + 0xa90#64 + 0x30#64) 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) := by
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h0 : sp + 0xa90#64 + 0x30#64 = sp + 0xac0#64 := by bv_arith
    have h1 : sp + 0xac0#64 + 8#64 = sp + 0xac8#64 := by bv_arith
    have h2 : sp + 0xac0#64 + 16#64 = sp + 0xad0#64 := by bv_arith
    have h3 : BitVec.ofNat 64 (keyToBytes32 st.rootKey).length = 32#64 := by simp [keyToBytes32]
    rw [h0, h1, h2, h3]
    ac_rfl
  have hchains_hdr :
      ((sp + 0xad8#64) ↦₆₄ chainsCap') ∗ ((sp + 0xae0#64) ↦₆₄ w.newRcPtr) ∗
        ((sp + 0xae8#64) ↦₆₄ chainsCap') ∗
        vecBuf A 104 8 (chainAt A) chainsCap' w.newRcPtr (w.chains'.zip st.receiverChains) =
      vecAt A 104 8 (chainAt A) (sp + 0xa90#64 + 0x48#64) chainsCap' w.newRcPtr
        (w.chains'.zip st.receiverChains) := by
    unfold vecAt vecHeader
    have h0 : sp + 0xa90#64 + 0x48#64 = sp + 0xad8#64 := by bv_arith
    have h1 : sp + 0xad8#64 + 8#64 = sp + 0xae0#64 := by bv_arith
    have h2 : sp + 0xad8#64 + 16#64 = sp + 0xae8#64 := by bv_arith
    have h3 : BitVec.ofNat 64 (w.chains'.zip st.receiverChains).length = chainsCap' := by
      simp [hchains_len, chainsCap']
    rw [h0, h1, h2, h3]
    ac_rfl
  have halice_hdr :
      ((sp + 0xaf0#64) ↦₆₄ alice'.cap) ∗ ((sp + 0xaf8#64) ↦₆₄ alice'.ptr) ∗
        ((sp + 0xb00#64) ↦₆₄ alice'.cap) ∗
        vecU8Buf A alice'.cap alice'.ptr alice'.bytes =
      vecGhostAt A alice' (sp + 0xa90#64 + 0x60#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h0 : sp + 0xa90#64 + 0x60#64 = sp + 0xaf0#64 := by bv_arith
    have h1 : sp + 0xaf0#64 + 8#64 = sp + 0xaf8#64 := by bv_arith
    have h2 : sp + 0xaf0#64 + 16#64 = sp + 0xb00#64 := by bv_arith
    rw [h0, h1, h2]
    ac_rfl
  have hpq_hdr :
      ((sp + 0xb08#64) ↦₆₄ pqCap') ∗ ((sp + 0xb10#64) ↦₆₄ w.newPqPtr) ∗
        ((sp + 0xb18#64) ↦₆₄ pqCap') ∗
        vecU8Buf A pqCap' w.newPqPtr st.pqRatchetState =
      vecU8At A (sp + 0xa90#64 + 0x78#64) pqCap' w.newPqPtr st.pqRatchetState := by
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h0 : sp + 0xa90#64 + 0x78#64 = sp + 0xb08#64 := by bv_arith
    have h1 : sp + 0xb08#64 + 8#64 = sp + 0xb10#64 := by bv_arith
    have h2 : sp + 0xb08#64 + 16#64 = sp + 0xb18#64 := by bv_arith
    rw [h0, h1, h2]
    ac_rfl
  have hsc_reasm :
      (((sp + 0xb20#64) ↦₆₄ w.c0) ∗
        chunks96_6QAt (sp + 0xb28#64) w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5 ∗
        optSenderChainHeap A w.sender' st.senderChain) ⊢
      optSenderChainAt A (sp + 0xa90#64 + 0x90#64) w.sender' st.senderChain := by
    have h0 : sp + 0xa90#64 + 0x90#64 = sp + 0xb20#64 := by bv_arith
    have h8 : sp + 0xb20#64 + 0x8#64 = sp + 0xb28#64 := by bv_arith
    rw [h0, ← h8, ← sepConj_assoc, ← chunks104W6QAt_eq_word_sep_chunks96]
    exact optSenderChainAt_of_chunks104W6Q A (sp + 0xb20#64) w.sender' st.senderChain hsc_inl
  have hpend_reasm :
      (((sp + 0xb88#64) ↦₆₄ w.pendCap') ∗ ((sp + 0xb90#64) ↦₆₄ w.pendPtr') ∗
        ((sp + 0xb98#64) ↦₆₄ w.pendCap') ∗ ((sp + 0xba0#64) ↦₃₂ w.w2c) ∗
        ((sp + 0xba4#64) ↦₃₂ w20) ∗ ((sp + 0xba8#64) ↦₆₄ w.d10) ∗
        ((sp + 0xbb0#64) ↦₃₂ w.w28) ∗ memRegion (sp + 0xbb4#64) 4 ∗
        OptPendClone A recG.pending w.pendCap' w.pendPtr') ⊢
      ∃∗ pend' : Option TailVecGhost,
        ⌜pend'.isSome = recG.pending.isSome⌝ ∗
          optTailVecAt A 48 (sp + 0xa90#64 + 0xf8#64) pend' := by
    have h0 : sp + 0xa90#64 + 0xf8#64 = sp + 0xb88#64 := by bv_arith
    have h8 : sp + 0xb88#64 + 8#64 = sp + 0xb90#64 := by bv_arith
    have h16 : sp + 0xb88#64 + 16#64 = sp + 0xb98#64 := by bv_arith
    have h24 : sp + 0xb88#64 + 24#64 = sp + 0xba0#64 := by bv_arith
    have h28 : sp + 0xb88#64 + 28#64 = sp + 0xba4#64 := by bv_arith
    have h32 : sp + 0xb88#64 + 32#64 = sp + 0xba8#64 := by bv_arith
    have h40 : sp + 0xb88#64 + 40#64 = sp + 0xbb0#64 := by bv_arith
    have h44 : sp + 0xb88#64 + 44#64 = sp + 0xbb4#64 := by bv_arith
    rw [h0, ← h8, ← h16, ← h24, ← h28, ← h32, ← h40, ← h44]
    exact optTailVecAt_48_of_optPendClone A (sp + 0xb88#64) recG.pending w.pendCap' w.pendPtr'
      w.w2c w20 w.d10 w.w28
  have hkyb_reasm :
      (((sp + 0xbb8#64) ↦₆₄ w.kybCap') ∗ ((sp + 0xbc0#64) ↦₆₄ w.kybPtr') ∗
        ((sp + 0xbc8#64) ↦₆₄ w.kybCap') ∗ ((sp + 0xbd0#64) ↦₃₂ w.w24) ∗
        memRegion (sp + 0xbd4#64) 4 ∗
        OptKybClone A recG.kyber w.kybCap' w.kybPtr') ⊢
      ∃∗ kyb' : Option TailVecGhost,
        optTailVecAt A 32 (sp + 0xa90#64 + 0x128#64) kyb' := by
    have h0 : sp + 0xa90#64 + 0x128#64 = sp + 0xbb8#64 := by bv_arith
    have h8 : sp + 0xbb8#64 + 8#64 = sp + 0xbc0#64 := by bv_arith
    have h16 : sp + 0xbb8#64 + 16#64 = sp + 0xbc8#64 := by bv_arith
    have h24 : sp + 0xbb8#64 + 24#64 = sp + 0xbd0#64 := by bv_arith
    have h28 : sp + 0xbb8#64 + 28#64 = sp + 0xbd4#64 := by bv_arith
    rw [h0, ← h8, ← h16, ← h24, ← h28]
    exact optTailVecAt_32_of_optKybClone A (sp + 0xbb8#64) recG.kyber w.kybCap' w.kybPtr' w.w24
  have htail_eq :
      ((sp + 0xbd8#64) ↦₃₂ st.sessionVersion) ∗
        ((sp + 0xbdc#64) ↦₃₂ st.previousCounter) ∗
        ((sp + 0xbe0#64) ↦₃₂ w.regW0) ∗ ((sp + 0xbe4#64) ↦₃₂ w.regW1) =
      ((sp + 0xa90#64 + 0x148#64) ↦₃₂ st.sessionVersion) ∗
        ((sp + 0xa90#64 + 0x14c#64) ↦₃₂ st.previousCounter) ∗
        ((sp + 0xa90#64 + 0x150#64) ↦ₛ recG.regIds) := by
    have h148 : sp + 0xa90#64 + 0x148#64 = sp + 0xbd8#64 := by bv_arith
    have h14c : sp + 0xa90#64 + 0x14c#64 = sp + 0xbdc#64 := by bv_arith
    have h150 : sp + 0xa90#64 + 0x150#64 = sp + 0xbe0#64 := by bv_arith
    have h154 : sp + 0xbe0#64 + 4#64 = sp + 0xbe4#64 := by bv_arith
    have hreg_pts : ((sp + 0xbe0#64) ↦ₛ recG.regIds) =
        ((sp + 0xbe0#64) ↦₃₂ w.regW0) ∗ ((sp + 0xbe0#64 + 4#64) ↦₃₂ w.regW1) := by
      conv => lhs; rw [hreg_eq]
      rw [pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes,
          ← pointsTo32_eq_pointsToBytes]
    rw [h148, h14c, h150, hreg_pts, h154]
  unfold packDstSlotsWrittenAt
  dsimp only []
  refine Entails.trans
    (Q := (((sp + 0xb88#64) ↦₆₄ w.pendCap') ∗ ((sp + 0xb90#64) ↦₆₄ w.pendPtr') ∗
            ((sp + 0xb98#64) ↦₆₄ w.pendCap') ∗ ((sp + 0xba0#64) ↦₃₂ w.w2c) ∗
            ((sp + 0xba4#64) ↦₃₂ w20) ∗ ((sp + 0xba8#64) ↦₆₄ w.d10) ∗
            ((sp + 0xbb0#64) ↦₃₂ w.w28) ∗ memRegion (sp + 0xbb4#64) 4 ∗
            OptPendClone A recG.pending w.pendCap' w.pendPtr') ∗
          (((sp + 0xbb8#64) ↦₆₄ w.kybCap') ∗ ((sp + 0xbc0#64) ↦₆₄ w.kybPtr') ∗
            ((sp + 0xbc8#64) ↦₆₄ w.kybCap') ∗ ((sp + 0xbd0#64) ↦₃₂ w.w24) ∗
            memRegion (sp + 0xbd4#64) 4 ∗
            OptKybClone A recG.kyber w.kybCap' w.kybPtr') ∗
          (((sp + 0xb20#64) ↦₆₄ w.c0) ∗
            chunks96_6QAt (sp + 0xb28#64) w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5 ∗
            optSenderChainHeap A w.sender' st.senderChain) ∗
          (((sp + 0xa90#64) ↦₆₄ localIk'.cap) ∗ ((sp + 0xa98#64) ↦₆₄ localIk'.ptr) ∗
            ((sp + 0xaa0#64) ↦₆₄ localIk'.cap) ∗
            vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes) ∗
          (((sp + 0xaa8#64) ↦₆₄ remoteIk'.cap) ∗ ((sp + 0xab0#64) ↦₆₄ remoteIk'.ptr) ∗
            ((sp + 0xab8#64) ↦₆₄ remoteIk'.cap) ∗
            vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes) ∗
          (((sp + 0xac0#64) ↦₆₄ 32#64) ∗ ((sp + 0xac8#64) ↦₆₄ w.newRootKeyPtr) ∗
            ((sp + 0xad0#64) ↦₆₄ 32#64) ∗
            vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey)) ∗
          (((sp + 0xad8#64) ↦₆₄ chainsCap') ∗ ((sp + 0xae0#64) ↦₆₄ w.newRcPtr) ∗
            ((sp + 0xae8#64) ↦₆₄ chainsCap') ∗
            vecBuf A 104 8 (chainAt A) chainsCap' w.newRcPtr (w.chains'.zip st.receiverChains)) ∗
          (((sp + 0xaf0#64) ↦₆₄ alice'.cap) ∗ ((sp + 0xaf8#64) ↦₆₄ alice'.ptr) ∗
            ((sp + 0xb00#64) ↦₆₄ alice'.cap) ∗
            vecU8Buf A alice'.cap alice'.ptr alice'.bytes) ∗
          (((sp + 0xb08#64) ↦₆₄ pqCap') ∗ ((sp + 0xb10#64) ↦₆₄ w.newPqPtr) ∗
            ((sp + 0xb18#64) ↦₆₄ pqCap') ∗
            vecU8Buf A pqCap' w.newPqPtr st.pqRatchetState) ∗
          (((sp + 0xbd8#64) ↦₃₂ st.sessionVersion) ∗
            ((sp + 0xbdc#64) ↦₃₂ st.previousCounter) ∗
            ((sp + 0xbe0#64) ↦₃₂ w.regW0) ∗ ((sp + 0xbe4#64) ↦₃₂ w.regW1)))
    (Entails.of_eq (by
      rw [chunks96_6QAt_sp_0xb28]
      dsimp only [localIk', remoteIk', alice', chainsCap', pqCap']
      ac_rfl)) ?_
  rw [hloc_hdr, hrem_hdr, hroot_hdr, hchains_hdr, halice_hdr, hpq_hdr, htail_eq]
  refine Entails.trans
    (sepConj_mono hpend_reasm (sepConj_mono hkyb_reasm (sepConj_mono_left hsc_reasm))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kyb'
  apply Entails.sepExists_elim; intro pend'
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hpend'_some
  let G₁ : SessionGhost :=
    { localIk := localIk'
      remoteIk := remoteIk'
      root := ⟨32#64, w.newRootKeyPtr⟩
      chainsCap := chainsCap'
      chainsPtr := w.newRcPtr
      chains := w.chains'
      alice := alice'
      pq := ⟨pqCap', w.newPqPtr⟩
      sender := w.sender'
      pending := pend'
      kyber := kyb'
      regIds := recG.regIds }
  refine Entails.sepExists_right G₁ ?_
  have hclone : CloneRel recG G₁ := ⟨rfl, rfl, rfl, rfl⟩
  apply Entails.pure_right hclone
  unfold sessionStateAt
  have hpure :
      PublicKey.deserialize G₁.localIk.bytes = .ok st.localIdentity.publicKey ∧
      (match st.remoteIdentity with
       | none => G₁.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G₁.remoteIk.bytes = .ok ik.publicKey) ∧
      G₁.chains.length = st.receiverChains.length ∧
      G₁.pending.isSome = st.pendingPreKey ∧ G₁.regIds.length = 8 ∧
      G₁.localIk.bytes.length = 33 ∧
      (st.remoteIdentity.isSome → G₁.remoteIk.bytes.length = 33) := by
    dsimp [G₁, localIk', remoteIk']
    rw [hpend'_some]
    exact ⟨h_loc_deser, h_rem_deser, hchains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩
  apply Entails.pure_right hpure
  dsimp only [G₁]
  exact Entails.of_eq (by ac_rfl)

theorem sessionStateAt_entails_pure_sep (A : RustAlloc) (addr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A addr G st ⊢
      ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
        (match st.remoteIdentity with
         | none => G.remoteIk.bytes = []
         | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
        G.chains.length = st.receiverChains.length ∧
        G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
        G.localIk.bytes.length = 33 ∧
        (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
      sessionStateAt A addr G st := by
  unfold sessionStateAt
  apply Entails.pure_left; intro hp
  exact Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))

set_option maxHeartbeats 400000 in
theorem spillSlots_entails_genP3SpillAll (sp : BitVec 64)
    (recG : SessionGhost) (st : SessionState (List (BitVec 8))) (w : GenP3J4Witness) :
    (((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗
      ((sp + 0x10#64) ↦₆₄ w.d10) ∗
      ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗
      ((sp + 0x24#64) ↦₃₂ w.w24) ∗
      ((sp + 0x28#64) ↦₃₂ w.w28) ∗
      ((sp + 0x2c#64) ↦₃₂ w.w2c) ∗
      ((sp + 0x30#64) ↦₃₂ w.regW0) ∗
      ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
      ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
      ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length) ∗
      ((sp + 0x48#64) ↦₆₄ w.c0) ∗
      ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
      ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
      ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
      ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
      ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x98#64) ↦₆₄ 32#64) ∗
      ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
      genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5) ⊢
      genP3SpillAll sp := by
  have hpend :
      (((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗ ((sp + 0x10#64) ↦₆₄ w.d10) ∗
        ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗ ((sp + 0x24#64) ↦₃₂ w.w24) ∗
        ((sp + 0x28#64) ↦₃₂ w.w28) ∗ ((sp + 0x2c#64) ↦₃₂ w.w2c)) ⊢
      genP3PendSpillScratch sp := by
    unfold genP3PendSpillScratch
    exact Entails.sepExists_right ⟨w.kybPtr', w.d10, w.pendPtr', w.w24, w.w28, w.w2c⟩
      (Entails.of_eq (by ac_rfl))
  have htail :
      (((sp + 0x30#64) ↦₃₂ w.regW0) ∗ ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
        ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
        ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length)) ⊢
      genP3TailSpillScratch sp := by
    unfold genP3TailSpillScratch
    exact Entails.sepExists_right ⟨w.regW0, w.regW1, w.kybCap', BitVec.ofNat 64 st.receiverChains.length⟩
      (Entails.of_eq (by ac_rfl))
  have hchains :
      (((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
        ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
        ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr)) ⊢
      genP3ChainsSpillScratch sp := by
    unfold genP3ChainsSpillScratch
    exact Entails.sepExists_right ⟨w.newRemIdPtr, BitVec.ofNat 64 recG.remoteIk.bytes.length, w.newLocIdPtr⟩
      (Entails.of_eq (by ac_rfl))
  have hfront :
      (((sp + 0x48#64) ↦₆₄ w.c0) ∗ ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
        ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗ ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
        ((sp + 0x98#64) ↦₆₄ 32#64) ∗
        ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
        genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5) ⊢
      ∃∗ fs : GenP3FrontSpill,
        ((sp + 0x48#64) ↦₆₄ fs.u_48) ∗ ((sp + 0x50#64) ↦₆₄ fs.u_50) ∗
        ((sp + 0x5c#64) ↦₃₂ fs.u_5c) ∗ ((sp + 0x7c#64) ↦₃₂ fs.u_7c) ∗
        ((sp + 0x98#64) ↦₆₄ fs.u_98) ∗ ((sp + 0xd0#64) ↦₆₄ fs.u_d0) ∗
        ((sp + 0x930#64) ↦₆₄ fs.u930) ∗ ((sp + 0x938#64) ↦₆₄ fs.u938) ∗
        ((sp + 0x940#64) ↦₆₄ fs.u940) ∗ ((sp + 0x948#64) ↦₆₄ fs.u948) ∗
        ((sp + 0x950#64) ↦₆₄ fs.u950) ∗ ((sp + 0x958#64) ↦₆₄ fs.u958) ∗
        ((sp + 0x960#64) ↦₆₄ fs.u960) ∗ ((sp + 0x968#64) ↦₆₄ fs.u968) ∗
        ((sp + 0x970#64) ↦₆₄ fs.u970) ∗ ((sp + 0x978#64) ↦₆₄ fs.u978) ∗
        ((sp + 0x980#64) ↦₆₄ fs.u980) ∗ ((sp + 0x988#64) ↦₆₄ fs.u988) := by
    unfold genP3SenderInlineWords
    exact Entails.sepExists_right
      ⟨w.c0, w.newRootKeyPtr, st.previousCounter, st.sessionVersion, 32#64,
        BitVec.ofNat 64 recG.localIk.bytes.length,
        w.sq0.extractLsb' 0 64, w.sq0.extractLsb' 64 64,
        w.sq1.extractLsb' 0 64, w.sq1.extractLsb' 64 64,
        w.sq2.extractLsb' 0 64, w.sq2.extractLsb' 64 64,
        w.sq3.extractLsb' 0 64, w.sq3.extractLsb' 64 64,
        w.sq4.extractLsb' 0 64, w.sq4.extractLsb' 64 64,
        w.sq5.extractLsb' 0 64, w.sq5.extractLsb' 64 64⟩
      (Entails.of_eq (by ac_rfl))
  unfold genP3SpillAll
  refine Entails.trans
    (Q := (((sp + 0x8#64) ↦₆₄ w.kybPtr') ∗ ((sp + 0x10#64) ↦₆₄ w.d10) ∗
            ((sp + 0x18#64) ↦₆₄ w.pendPtr') ∗ ((sp + 0x24#64) ↦₃₂ w.w24) ∗
            ((sp + 0x28#64) ↦₃₂ w.w28) ∗ ((sp + 0x2c#64) ↦₃₂ w.w2c)) ∗
          (((sp + 0x30#64) ↦₃₂ w.regW0) ∗ ((sp + 0x34#64) ↦₃₂ w.regW1) ∗
            ((sp + 0x38#64) ↦₆₄ w.kybCap') ∗
            ((sp + 0x40#64) ↦₆₄ BitVec.ofNat 64 st.receiverChains.length)) ∗
          (((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
            ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
            ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr)) ∗
          (((sp + 0x48#64) ↦₆₄ w.c0) ∗ ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
            ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗ ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
            ((sp + 0x98#64) ↦₆₄ 32#64) ∗
            ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
            genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
    (Entails.of_eq (by ac_rfl)) ?_
  exact sepConj_mono hpend (sepConj_mono htail (sepConj_mono hchains hfront))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4
