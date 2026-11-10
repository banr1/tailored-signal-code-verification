/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8d
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant10b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant8c
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 8 (`EkReceivedCt1Sampled`, `+1764`)

Reconstructs `resultChunkedStatesAt` for `InnerState.ekReceivedCt1Sampled` from `epilogueOutFull`
and assembles the top-level variant theorem `states_from_pb_ekReceivedCt1Sampled_1764` (`+1764 -> s0.x30`).
-/

@[expose] public section
namespace CryptoVerification.SpqrV1.States.FromPb
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
/-! ## 1. Realignment & Output Reconstruction After Epilogue (`+8180 -> ret`) -/
theorem v8_out_96_realign (out w80 : BitVec 64) : ((out + 96#64) ↦₈ w80.extractLsb' 0 8) ∗ ((out + 97#64) ↦₃₂ w80.extractLsb' 8 32) ∗ ((out + 101#64) ↦₁₆ w80.extractLsb' 40 16) ∗
      ((out + 103#64) ↦₈ w80.extractLsb' 56 8) = (out + 96#64) ↦₆₄ w80 := by
  have h := (v10_pointsTo64_split_1_4_2_1 (out + 96#64) w80).symm
  have ha97 : (out + 96#64) + 1#64 = out + 97#64 := by bv_omega
  have ha101 : (out + 96#64) + 5#64 = out + 101#64 := by bv_omega
  have ha103 : (out + 96#64) + 7#64 = out + 103#64 := by bv_omega
  rw [ha97, ha101, ha103] at h
  exact h
theorem v8_out_120_realign (out w104 w112 : BitVec 64) : ((out + 120#64) ↦₈ loByte w104) ∗ ((out + 121#64) ↦₆₄ unshiftWord w104 (loByte w112)) ∗ ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7
        (overlapWord7 (unshiftWord w104 (loByte w112)) (w112 >>> 8))) = ((out + 120#64) ↦₆₄ w104) ∗ ((out + 128#64) ↦₆₄ w112) := by
  rw [v8_overlapWord7_unshift_lsr8 w104 w112]
  have h := (pair64_to_byte_word_tail7 (out + 120#64) w104 w112).symm
  have ha121 : (out + 120#64) + 1#64 = out + 121#64 := by bv_omega
  have ha129 : (out + 120#64) + 9#64 = out + 129#64 := by bv_omega
  have ha128 : (out + 120#64) + 8#64 = out + 128#64 := by bv_omega
  rw [ha121, ha129, ha128] at h
  exact h
theorem v8_out_144_realign (out w128 w136 w144 : BitVec 64) : ((out + 144#64) ↦₈ ((loByte w128).zeroExtend 32).setWidth 8) ∗ ((out + 145#64) ↦₆₄ (v8_midQ128 w128 w136 w144).extractLsb' 0 64) ∗
      ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v8_midQ128 w128 w136 w144).extractLsb' 64 64)) ∗ ((out + 160#64) ↦₆₄ overlapWord7 ((v8_midQ128 w128 w136 w144).extractLsb' 64 64) (w144 >>> 8)) =
    ((out + 144#64) ↦₆₄ w128) ∗ ((out + 152#64) ↦₆₄ w136) ∗ ((out + 160#64) ↦₆₄ w144) := by
  rw [v8_zext32_setWidth8 (loByte w128)]
  have hlo : (v8_midQ128 w128 w136 w144).extractLsb' 0 64 = unshiftWord w128 (loByte w136) := by
    unfold v8_midQ128; bv_kernel
  have hhi : (v8_midQ128 w128 w136 w144).extractLsb' 64 64 = unshiftWord w136 (loByte w144) := by
    unfold v8_midQ128; bv_kernel
  rw [hlo, hhi, v8_overlapWord7_unshift_lsr8 w136 w144]
  have hr := loBytes7_pointsTo64_eq_overlap (out + 153#64) (unshiftWord w136 (loByte w144)) w144
  have hov : overlapLow7 (unshiftWord w136 (loByte w144)) w144 = unshiftWord w136 (loByte w144) := by
    unfold overlapLow7 unshiftWord loByte; bv_kernel
  have ha160 : (out + 153#64) + 7#64 = out + 160#64 := by bv_omega
  have ha161 : (out + 153#64) + 8#64 = out + 161#64 := by bv_omega
  rw [ha160, ha161, hov] at hr
  have hq := pointsTo64_pair_eq_pointsTo128 (out + 145#64) (unshiftWord w128 (loByte w136)) (unshiftWord w136 (loByte w144))
  have ha153 : (out + 145#64) + 8#64 = out + 153#64 := by bv_omega
  rw [ha153] at hq
  have ht := (v10_triple64_eq_byte_q128_tail7 (out + 144#64) w128 w136 w144).symm
  have hd145 : (out + 144#64) + 1#64 = out + 145#64 := by bv_omega
  have hd161 : (out + 144#64) + 17#64 = out + 161#64 := by bv_omega
  have hd152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  have hd160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  rw [hd145, hd161, hd152, hd160] at ht
  rw [hr, ← sepConj_assoc ((out + 145#64) ↦₆₄ _), hq, ht]
theorem v8_out_16_to_400_eq_bs (out : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) : ((out + 16#64) ↦₆₄ v8_wordAt bs 0) ∗ ((out + 24#64) ↦₆₄ v8_wordAt bs 8) ∗
      ((out + 32#64) ↦₆₄ v8_wordAt bs 16) ∗ ((out + 40#64) ↦₆₄ v8_wordAt bs 24) ∗ ((out + 48#64) ↦₆₄ v8_wordAt bs 32) ∗ ((out + 56#64) ↦₆₄ v8_wordAt bs 40) ∗
      ((out + 64#64) ↦₆₄ v8_wordAt bs 48) ∗ ((out + 72#64) ↦₆₄ v8_wordAt bs 56) ∗ ((out + 80#64) ↦₆₄ v8_wordAt bs 64) ∗ ((out + 88#64) ↦₆₄ v8_wordAt bs 72) ∗ (((out + 96#64) ↦₈ (v8_wordAt bs 80).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v8_wordAt bs 80).extractLsb' 8 32) ∗ ((out + 101#64) ↦₁₆ (v8_wordAt bs 80).extractLsb' 40 16) ∗ ((out + 103#64) ↦₈ (v8_wordAt bs 80).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v8_wordAt bs 88) ∗ ((out + 112#64) ↦₆₄ v8_wordAt bs 96) ∗ (((out + 120#64) ↦₈ loByte (v8_wordAt bs 104)) ∗ ((out + 121#64) ↦₆₄ unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)))) ∗ ((out + 136#64) ↦₆₄ v8_wordAt bs 120) ∗
      (((out + 144#64) ↦₈ ((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8) ∗ ((out + 145#64) ↦₆₄ (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64)) ∗ ((out + 160#64) ↦₆₄ overlapWord7
           ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64) (v8_wordAt bs 144 >>> 8))) ∗ ((out + 168#64) ↦₁₂₈ v8_quadAt bs 152) ∗ ((out + 184#64) ↦₁₂₈ v8_quadAt bs 168) ∗
      ((out + 200#64) ↦₁₂₈ v8_quadAt bs 184) ∗ ((out + 216#64) ↦₁₂₈ v8_quadAt bs 200) ∗ ((out + 232#64) ↦₁₂₈ v8_quadAt bs 216) ∗ ((out + 248#64) ↦₁₂₈ v8_quadAt bs 232) ∗
      ((out + 264#64) ↦₁₂₈ v8_quadAt bs 248) ∗ ((out + 280#64) ↦₁₂₈ v8_quadAt bs 264) ∗ ((out + 296#64) ↦₁₂₈ v8_quadAt bs 280) ∗ ((out + 312#64) ↦₁₂₈ v8_quadAt bs 296) ∗
      ((out + 328#64) ↦₁₂₈ v8_quadAt bs 312) ∗ ((out + 344#64) ↦₁₂₈ v8_quadAt bs 328) ∗ ((out + 360#64) ↦₁₂₈ v8_quadAt bs 344) ∗ ((out + 376#64) ↦₁₂₈ v8_quadAt bs 360) ∗ ((out + 392#64) ↦₆₄ v8_wordAt bs 376) =
    ((out + 8#64) + 8#64) ↦ₛ bs := by
  rw [v8_out_96_realign out (v8_wordAt bs 80), v8_out_120_realign out (v8_wordAt bs 104) (v8_wordAt bs 112), v8_out_144_realign out (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144),
      v8_bs384_eq_encCells bs hbs (out + 8#64)]; unfold v8_encCellsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
theorem v8_fsp_1888_entails_epilogue (fsp tag w2280 : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) : ((fsp + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt (fsp + 1888#64) bs ∗
      ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16 ⊢ ((fsp + 1888#64) ↦₁₂₈ (v8_wordAt bs 0 ++ tag)) ∗ ((fsp + 1904#64) ↦₁₂₈ (v8_wordAt bs 16 ++ v8_wordAt bs 8)) ∗
      ((fsp + 1920#64) ↦₆₄ v8_wordAt bs 24) ∗ memRegion (fsp + 1928#64) 376 := by
  rw [← v8_bs384_eq_encCells bs hbs (fsp + 1888#64)]
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  rw [ha1896]
  have hbs_split : ((fsp + 1896#64) ↦ₛ bs) = ((fsp + 1896#64) ↦₆₄ v8_wordAt bs 0) ∗ ((fsp + 1904#64) ↦₆₄ v8_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v8_wordAt bs 16) ∗ ((fsp + 1920#64) ↦₆₄ v8_wordAt bs 24) ∗
      ((fsp + 1928#64) ↦ₛ bs.drop 32) := by
    have h := v8_bs_drop_step8 hbs (fsp + 1888#64) 8#64 16#64 0 <| v8_bs_drop_step8 hbs (fsp + 1888#64) 16#64 24#64 8 <| v8_bs_drop_step8 hbs (fsp + 1888#64) 24#64 32#64 16 <|
      v8_bs_drop_step8 hbs (fsp + 1888#64) 32#64 40#64 24 rfl
    change (((fsp + 1888#64) + 8#64) ↦ₛ bs) = _ at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, sepConj_assoc] at h
    exact h
  rw [hbs_split]
  have hq1888 : ((fsp + 1888#64) ↦₆₄ tag) ∗ ((fsp + 1896#64) ↦₆₄ v8_wordAt bs 0) = ((fsp + 1888#64) ↦₁₂₈ (v8_wordAt bs 0 ++ tag)) := by
    rw [← ha1896, pointsTo64_pair_eq_pointsTo128]
  have hq1904 : ((fsp + 1904#64) ↦₆₄ v8_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v8_wordAt bs 16) = ((fsp + 1904#64) ↦₁₂₈ (v8_wordAt bs 16 ++ v8_wordAt bs 8)) := by
    have ha : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
    rw [← ha, pointsTo64_pair_eq_pointsTo128]
  have hlen352 : (bs.drop 32).length = 352 := by rw [List.length_drop, hbs]
  have hm352 : ((fsp + 1928#64) ↦ₛ bs.drop 32) ⊢ memRegion (fsp + 1928#64) 352 := hlen352 ▸ ProofLib.pointsToBytes_entails_memRegion (fsp + 1928#64) (bs.drop 32)
  have hm376 : ((fsp + 1928#64) ↦ₛ bs.drop 32) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16 ⊢ memRegion (fsp + 1928#64) 376 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1928#64) (n := 352) (k := 24) (b' := fsp + 2280#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := fsp + 2280#64) (n := 8) (k := 16)
          (b' := fsp + 2288#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono hm352 (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 2280#64) w2280))
  refine Entails.trans (Entails.of_eq (show _ = (((fsp + 1888#64) ↦₆₄ tag) ∗ ((fsp + 1896#64) ↦₆₄ v8_wordAt bs 0)) ∗ (((fsp + 1904#64) ↦₆₄ v8_wordAt bs 8) ∗ ((fsp + 1912#64) ↦₆₄ v8_wordAt bs 16)) ∗
    ((fsp + 1920#64) ↦₆₄ v8_wordAt bs 24) ∗ (((fsp + 1928#64) ↦ₛ bs.drop 32) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ memRegion (fsp + 2288#64) 16) by ac_rfl)) ?_
  rw [hq1888, hq1904]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm376))
theorem v8_memRegion_loBytes7_gap_at (a o1 o2 : BitVec 64) (k : Nat) (ho : o1 + 7#64 = o2 := by rfl) (hk : 8 + k ≤ 2 ^ 64 := by decide) : ProofLib.memRegion (a + o1) (7 + (1 + k)) ⊢
      (∃∗ u0 : BitVec 64, ((a + o1) ↦ₛ EncoderFromPb.loBytes7 u0)) ∗ ProofLib.memRegion (a + o2) (1 + k) := by
  have h1 : 7 + (1 + k) = 8 + k := by omega
  rw [h1, ProofLib.memRegion_split' (b := a + o1) (n := 8) (k := k) (b' := a + o1 + 8#64) rfl rfl hk, ProofLib.memRegion_eight (a + o1), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro u0
  rw [pointsTo64_split_7_1 (a + o1) u0, sepConj_assoc, sepExists_sepConj_left]
  refine Entails.sepExists_right u0 (sepConj_mono_right ?_)
  have ha7 : a + o1 + 7#64 = a + o2 := by rw [BitVec.add_assoc, ho]
  have ha8 : a + o1 + 8#64 = a + o2 + 1#64 := by rw [← ha7]; bv_omega
  rw [ha7, ha8, ProofLib.memRegion_split' (b := a + o2) (n := 1) (k := k) (b' := a + o2 + 1#64) rfl rfl (by omega)]
  exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)
theorem v8_memRegion_entails_bs : ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 → ProofLib.memRegion a n ⊢ ∃∗ bs : { l : List (BitVec 8) // l.length = n }, (a ↦ₛ bs.val)
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]
    refine Entails.sepExists_right ⟨[], rfl⟩ ?_
    rw [ProofLib.pointsToBytes_nil]
    exact Entails.refl _
  | n + 1, a, hn => by
    have hsplit : n + 1 = 1 + n := by omega
    rw [hsplit, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro b0
    refine Entails.trans (sepConj_mono_right (v8_memRegion_entails_bs n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ⟨bs, hlen⟩
    refine Entails.sepExists_right ⟨b0 :: bs, by simp [hlen]; omega⟩ ?_
    rw [ProofLib.pointsToBytes_cons]
    exact Entails.refl _
theorem v8_memRegion_328_entails_bs (a : BitVec 64) : ProofLib.memRegion a 328 ⊢ ∃∗ bs : { l : List (BitVec 8) // l.length = 328 }, (a ↦ₛ bs.val) := v8_memRegion_entails_bs 328 a (by decide)
theorem v8_fsp_128_152_entails_32 (fsp ep : BitVec 64) : memRegion (fsp + 128#64) 24 ∗ ((fsp + 152#64) ↦₆₄ ep) ⊢ memRegion (fsp + 128#64) 32 := by
  rw [ProofLib.memRegion_split' (b := fsp + 128#64) (n := 24) (k := 8) (b' := fsp + 152#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (ProofLib.pointsTo64_entails_memRegion (fsp + 152#64) ep)
theorem v8_fsp_176_184_cells_entails_16 (fsp pa3 pa2 : BitVec 64) : ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ⊢ memRegion (fsp + 176#64) 16 := by
  rw [ProofLib.memRegion_split' (b := fsp + 176#64) (n := 8) (k := 8) (b' := fsp + 184#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 176#64) pa3) (ProofLib.pointsTo64_entails_memRegion (fsp + 184#64) pa2)
theorem v8_fsp_64_72_entails_92 (fsp ca5 : BitVec 64) : memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ ca5) ∗ memRegion (fsp + 72#64) 20 ⊢ memRegion fsp 92 := collapse_top <| collapse_step0 (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
theorem v8_fsp_96_100_entails_8 (fsp : BitVec 64) (d96 : BitVec 32) : ((fsp + 96#64) ↦₃₂ d96) ∗ memRegion (fsp + 100#64) 4 ⊢ memRegion (fsp + 96#64) 8 := by
  rw [ProofLib.memRegion_split' (b := fsp + 96#64) (n := 4) (k := 4) (b' := fsp + 100#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (pointsTo32_entails_memRegion_4 (fsp + 96#64) d96)
theorem v8_memRegion_72_48_split_11264 (fsp : BitVec 64) : memRegion (fsp + 72#64) 48 ⊢ memRegion (fsp + 72#64) 20 ∗ (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      (∃∗ d96 : BitVec 32, ((fsp + 96#64) ↦₃₂ d96)) ∗ memRegion (fsp + 100#64) 4 ∗ (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗ (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) := by
  exact split_top <| split_step (Entails.refl _) <| split_step (mem32_entails _) <| split_step (mem32_entails _) <| split_step (Entails.refl _) <| split_step (mem64_entails _) <| mem64_entails _
theorem v8_memRegion_160_16_split_11264 (fsp : BitVec 64) : memRegion (fsp + 160#64) 16 ⊢ (∃∗ u160 : BitVec 64, ((fsp + 160#64) ↦₆₄ u160)) ∗
      memRegion (fsp + 168#64) 4 ∗ (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) := by
  exact split_top <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| mem32_entails _
theorem v8_memRegion_240_1648_split_11264 (fsp : BitVec 64) : memRegion (fsp + 240#64) 1648 ⊢ (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
      memRegion (fsp + 568#64) 8 ∗ (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗ ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ uq608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ uq608)) ∗ (∃∗ uq624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ uq624)) ∗ (∃∗ uq640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ uq640)) ∗
      (∃∗ uq656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ uq656)) ∗ (∃∗ uq672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ uq672)) ∗ (∃∗ uq688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ uq688)) ∗
      (∃∗ uq704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ uq704)) ∗ (∃∗ uq720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ uq720)) ∗ (∃∗ uq736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ uq736)) ∗
      (∃∗ uq752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ uq752)) ∗ (∃∗ uq768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ uq768)) ∗ (∃∗ uq784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ uq784)) ∗
      (∃∗ uq800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ uq800)) ∗ (∃∗ uq816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ uq816)) ∗ (∃∗ u832 : BitVec 64, ((fsp + 832#64) ↦₆₄ u832)) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ uq848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ uq848)) ∗ ((∃∗ u864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864)) ∗ memRegion (fsp + 871#64) 9) ∗
      ((∃∗ u880 : BitVec 64, ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880)) ∗ (∃∗ u887 : BitVec 64, ((fsp + 887#64) ↦₆₄ u887))) ∗ memRegion (fsp + 895#64) 993 := by
  exact split_top <| split_step (v8_memRegion_328_entails_bs _) <| split_step (Entails.refl _) <| split_step (mem128_entails _) <| split_step (v8_memRegion_loBytes7_gap_at fsp 592#64 599#64 8) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem128_entails _) <|
    split_step (mem128_entails _) <| split_step (mem128_entails _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| split_step (mem128_entails _) <|
    split_step (v8_memRegion_loBytes7_gap_at fsp 864#64 871#64 8) <| split_step (memRegion_15_entails_loBytes7_and_64_at fsp 880#64 887#64) <| Entails.refl _
theorem v8_fsp_split_11264_all (fsp : BitVec 64) : memRegion (fsp + 72#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 192#64) 8 ∗
      memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 1648 ⊢ memRegion (fsp + 72#64) 20 ∗ (∃∗ d92 : BitVec 32, ((fsp + 92#64) ↦₃₂ d92)) ∗
      (∃∗ d96 : BitVec 32, ((fsp + 96#64) ↦₃₂ d96)) ∗ memRegion (fsp + 100#64) 4 ∗ (∃∗ w104 : BitVec 64, ((fsp + 104#64) ↦₆₄ w104)) ∗ (∃∗ w112 : BitVec 64, ((fsp + 112#64) ↦₆₄ w112)) ∗
      (∃∗ u160 : BitVec 64, ((fsp + 160#64) ↦₆₄ u160)) ∗ memRegion (fsp + 168#64) 4 ∗ (∃∗ d172 : BitVec 32, ((fsp + 172#64) ↦₃₂ d172)) ∗ (∃∗ w192 : BitVec 64, ((fsp + 192#64) ↦₆₄ w192)) ∗
      (∃∗ u208 : BitVec 64, ((fsp + 208#64) ↦₆₄ u208)) ∗ (∃∗ u232 : BitVec 64, ((fsp + 232#64) ↦₆₄ u232)) ∗ (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
      memRegion (fsp + 568#64) 8 ∗ (∃∗ q576 : BitVec 128, ((fsp + 576#64) ↦₁₂₈ q576)) ∗ ((∃∗ w592 : BitVec 64, ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592)) ∗ memRegion (fsp + 599#64) 9) ∗
      (∃∗ uq608 : BitVec 128, ((fsp + 608#64) ↦₁₂₈ uq608)) ∗ (∃∗ uq624 : BitVec 128, ((fsp + 624#64) ↦₁₂₈ uq624)) ∗ (∃∗ uq640 : BitVec 128, ((fsp + 640#64) ↦₁₂₈ uq640)) ∗
      (∃∗ uq656 : BitVec 128, ((fsp + 656#64) ↦₁₂₈ uq656)) ∗ (∃∗ uq672 : BitVec 128, ((fsp + 672#64) ↦₁₂₈ uq672)) ∗ (∃∗ uq688 : BitVec 128, ((fsp + 688#64) ↦₁₂₈ uq688)) ∗
      (∃∗ uq704 : BitVec 128, ((fsp + 704#64) ↦₁₂₈ uq704)) ∗ (∃∗ uq720 : BitVec 128, ((fsp + 720#64) ↦₁₂₈ uq720)) ∗ (∃∗ uq736 : BitVec 128, ((fsp + 736#64) ↦₁₂₈ uq736)) ∗
      (∃∗ uq752 : BitVec 128, ((fsp + 752#64) ↦₁₂₈ uq752)) ∗ (∃∗ uq768 : BitVec 128, ((fsp + 768#64) ↦₁₂₈ uq768)) ∗ (∃∗ uq784 : BitVec 128, ((fsp + 784#64) ↦₁₂₈ uq784)) ∗
      (∃∗ uq800 : BitVec 128, ((fsp + 800#64) ↦₁₂₈ uq800)) ∗ (∃∗ uq816 : BitVec 128, ((fsp + 816#64) ↦₁₂₈ uq816)) ∗ (∃∗ u832 : BitVec 64, ((fsp + 832#64) ↦₆₄ u832)) ∗ memRegion (fsp + 840#64) 8 ∗
      (∃∗ uq848 : BitVec 128, ((fsp + 848#64) ↦₁₂₈ uq848)) ∗ ((∃∗ u864 : BitVec 64, ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 u864)) ∗ memRegion (fsp + 871#64) 9) ∗
      ((∃∗ u880 : BitVec 64, ((fsp + 880#64) ↦ₛ EncoderFromPb.loBytes7 u880)) ∗ (∃∗ u887 : BitVec 64, ((fsp + 887#64) ↦₆₄ u887))) ∗ memRegion (fsp + 895#64) 993 := by
  refine Entails.trans (sepConj_mono (v8_memRegion_72_48_split_11264 fsp) (sepConj_mono (v8_memRegion_160_16_split_11264 fsp) (sepConj_mono (mem64_entails (fsp + 192#64)) (sepConj_mono (mem64_entails (fsp + 208#64))
            (sepConj_mono (mem64_entails (fsp + 232#64)) (v8_memRegion_240_1648_split_11264 fsp)))))) ?_
  exact Entails.of_eq (by ac_rfl)
theorem v8_vecU8_of_header_payload_cap (A : RustAlloc) (a cap ptr len : BitVec 64) (bs : List (BitVec 8)) (hlen : len = BitVec.ofNat 64 bs.length) : (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
      vecU8Payload A cap ptr bs ⊢ vecU8 A a bs := by
  subst hlen; unfold vecU8 vecU8At vecHeader vecU8Payload
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)
theorem v8_unchunkedCt1SentEkReceivedAt_408_pack (A : RustAlloc) {F : ShaCompress} (out l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep : BitVec 64) (rootKey macKey es ek ct1 : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length) (hl2 : l2 = BitVec.ofNat 64 macKey.length) (hes : es.length = 2080) (hek : ek.length = 1152) (hct1 : ct1.length = 960) :
    ((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗ ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
      ((out + 456#64) ↦₆₄ ca3) ∗ ((out + 464#64) ↦₆₄ pa3) ∗ ((out + 472#64) ↦₆₄ 2080#64) ∗ ((out + 480#64) ↦₆₄ ca4) ∗ ((out + 488#64) ↦₆₄ pa4) ∗ ((out + 496#64) ↦₆₄ 1152#64) ∗
      ((out + 504#64) ↦₆₄ ca5) ∗ ((out + 512#64) ↦₆₄ pa5) ∗ ((out + 520#64) ↦₆₄ 960#64) ∗ ((out + 528#64) ↦₆₄ ep) ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗
      vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ⊢ unchunkedCt1SentEkReceivedAt A (F := F) (out + 408#64)
        { auth := { rootKey := rootKey, macKey := macKey }, es := es, ek := ek, ct1 := ct1, epoch := ep } := by
  dsimp only [unchunkedCt1SentEkReceivedAt, authenticatorAt]
  have h1 := v8_vecU8_of_header_payload_cap A (out + 408#64) l1 pa1 l1 rootKey hl1
  have h2 := v8_vecU8_of_header_payload_cap A (out + 432#64) l2 pa2 l2 macKey hl2
  have h3 := v8_vecU8_of_header_payload_cap A (out + 456#64) ca3 pa3 2080#64 es (by rw [hes])
  have h4 := v8_vecU8_of_header_payload_cap A (out + 480#64) ca4 pa4 1152#64 ek (by rw [hek])
  have h5 := v8_vecU8_of_header_payload_cap A (out + 504#64) ca5 pa5 960#64 ct1 (by rw [hct1])
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h1 h2 h3 h4 h5 ⊢
  refine Entails.trans (Entails.of_eq (show _ = (((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗ vecU8Payload A l1 pa1 rootKey) ∗
    (((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗ vecU8Payload A l2 pa2 macKey) ∗ (((out + 456#64) ↦₆₄ ca3) ∗ ((out + 464#64) ↦₆₄ pa3) ∗ ((out + 472#64) ↦₆₄ 2080#64) ∗
     vecU8Payload A ca3 pa3 es) ∗ (((out + 480#64) ↦₆₄ ca4) ∗ ((out + 488#64) ↦₆₄ pa4) ∗ ((out + 496#64) ↦₆₄ 1152#64) ∗ vecU8Payload A ca4 pa4 ek) ∗
    (((out + 504#64) ↦₆₄ ca5) ∗ ((out + 512#64) ↦₆₄ pa5) ∗ ((out + 520#64) ↦₆₄ 960#64) ∗ vecU8Payload A ca5 pa5 ct1) ∗ ((out + 528#64) ↦₆₄ ep) by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (sepConj_mono h4 (sepConj_mono_left h5))))
theorem v8_epilogueOutFull_entails_ekReceivedCt1Sampled (A : RustAlloc) {F : ShaCompress} (out tag l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384)
    (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp) (hreloc : ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗ (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
        polyEncoderAt A (out + 8#64) enc) (rootKey macKey es ek ct1 : List (BitVec 8)) (hl1 : l1 = BitVec.ofNat 64 rootKey.length) (hl2 : l2 = BitVec.ofNat 64 macKey.length) (hes : es.length = 2080)
    (hek : ek.length = 1152) (hct1 : ct1.length = 960) (b536 : BitVec 8) (q537 : BitVec 128) (w552 : BitVec 64) (bs240 : List (BitVec 8)) (hbs240 : bs240.length = 328) (q888 q904 : BitVec 128) (w920 : BitVec 64) :
    epilogueOutFull out 10#64 tag (v8_wordAt bs 0) (v8_wordAt bs 8) (v8_wordAt bs 16) (v8_wordAt bs 24) (v8_wordAt bs 32) (v8_wordAt bs 40) (v8_wordAt bs 48) (v8_wordAt bs 56) (v8_wordAt bs 64) (v8_wordAt bs 72)
      ((v8_wordAt bs 80).extractLsb' 0 8) ((v8_wordAt bs 80).extractLsb' 8 32) ((v8_wordAt bs 80).extractLsb' 40 16) ((v8_wordAt bs 80).extractLsb' 56 8) (v8_wordAt bs 88) (v8_wordAt bs 96) (loByte (v8_wordAt bs 104))
      (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)) (v8_wordAt bs 120)
      (((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8) (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) (overlapWord7
        ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64) (v8_wordAt bs 144 >>> 8)) (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200)
      (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264) (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360)
      (v8_wordAt bs 376) (hi32 ++ enc.idx) l1 pa1 l1 l2 pa2 l2 ca3 pa3 2080#64 ca4 pa4 1152#64 ca5 pa5 960#64 ep b536 q537 w552 bs240 q888 q904 w920 ∗ P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗
      vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ⊢ resultChunkedStatesAt A (F := F) out (.ok (.ekReceivedCt1Sampled
        { uc := { auth := { rootKey := rootKey, macKey := macKey }, es := es, ek := ek, ct1 := ct1, epoch := ep }, sending_ct1 := enc })) := by
  dsimp only [resultChunkedStatesAt, chunkedStatesAt, chunkedEkReceivedCt1SampledAt]
  have ha408 : (out + 8#64) + 400#64 = out + 408#64 := by bv_omega
  have ha400 : (out + 8#64) + 392#64 = out + 400#64 := by bv_omega
  rw [ha408, sepConj_assoc (polyEncoderAt A (out + 8#64) enc)]
  rw [ha400] at hreloc; unfold epilogueOutFull
  have hbs_eq := v8_out_16_to_400_eq_bs out bs hbs
  have huc := v8_unchunkedCt1SentEkReceivedAt_408_pack A (F := F) out l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep rootKey macKey es ek ct1 hl1 hl2 hes hek hct1
  have htail := epilogueOut_tail_536_entails_392 out b536 q537 w552 bs240 hbs240 q888 q904 w920
  refine Entails.trans (Entails.of_eq (show _ = (out ↦₆₄ 10#64) ∗ (((out + 8#64) ↦₆₄ tag) ∗ (((out + 16#64) ↦₆₄ v8_wordAt bs 0) ∗ ((out + 24#64) ↦₆₄ v8_wordAt bs 8) ∗
      ((out + 32#64) ↦₆₄ v8_wordAt bs 16) ∗ ((out + 40#64) ↦₆₄ v8_wordAt bs 24) ∗ ((out + 48#64) ↦₆₄ v8_wordAt bs 32) ∗ ((out + 56#64) ↦₆₄ v8_wordAt bs 40) ∗
      ((out + 64#64) ↦₆₄ v8_wordAt bs 48) ∗ ((out + 72#64) ↦₆₄ v8_wordAt bs 56) ∗ ((out + 80#64) ↦₆₄ v8_wordAt bs 64) ∗ ((out + 88#64) ↦₆₄ v8_wordAt bs 72) ∗ (((out + 96#64) ↦₈ (v8_wordAt bs 80).extractLsb' 0 8) ∗
       ((out + 97#64) ↦₃₂ (v8_wordAt bs 80).extractLsb' 8 32) ∗ ((out + 101#64) ↦₁₆ (v8_wordAt bs 80).extractLsb' 40 16) ∗ ((out + 103#64) ↦₈ (v8_wordAt bs 80).extractLsb' 56 8)) ∗
      ((out + 104#64) ↦₆₄ v8_wordAt bs 88) ∗ ((out + 112#64) ↦₆₄ v8_wordAt bs 96) ∗ (((out + 120#64) ↦₈ loByte (v8_wordAt bs 104)) ∗ ((out + 121#64) ↦₆₄ unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) ∗
       ((out + 129#64) ↦ₛ EncoderFromPb.hiBytes7 (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)))) ∗ ((out + 136#64) ↦₆₄ v8_wordAt bs 120) ∗
      (((out + 144#64) ↦₈ ((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8) ∗ ((out + 145#64) ↦₆₄ (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 0 64) ∗
       ((out + 153#64) ↦ₛ EncoderFromPb.loBytes7 ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64)) ∗ ((out + 160#64) ↦₆₄ overlapWord7
           ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64) (v8_wordAt bs 144 >>> 8))) ∗ ((out + 168#64) ↦₁₂₈ v8_quadAt bs 152) ∗ ((out + 184#64) ↦₁₂₈ v8_quadAt bs 168) ∗
      ((out + 200#64) ↦₁₂₈ v8_quadAt bs 184) ∗ ((out + 216#64) ↦₁₂₈ v8_quadAt bs 200) ∗ ((out + 232#64) ↦₁₂₈ v8_quadAt bs 216) ∗ ((out + 248#64) ↦₁₂₈ v8_quadAt bs 232) ∗
      ((out + 264#64) ↦₁₂₈ v8_quadAt bs 248) ∗ ((out + 280#64) ↦₁₂₈ v8_quadAt bs 264) ∗ ((out + 296#64) ↦₁₂₈ v8_quadAt bs 280) ∗ ((out + 312#64) ↦₁₂₈ v8_quadAt bs 296) ∗
      ((out + 328#64) ↦₁₂₈ v8_quadAt bs 312) ∗ ((out + 344#64) ↦₁₂₈ v8_quadAt bs 328) ∗ ((out + 360#64) ↦₁₂₈ v8_quadAt bs 344) ∗ ((out + 376#64) ↦₁₂₈ v8_quadAt bs 360) ∗ ((out + 392#64) ↦₆₄ v8_wordAt bs 376)) ∗
     ((out + 400#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap) ∗ (((out + 408#64) ↦₆₄ l1) ∗ ((out + 416#64) ↦₆₄ pa1) ∗ ((out + 424#64) ↦₆₄ l1) ∗ ((out + 432#64) ↦₆₄ l2) ∗ ((out + 440#64) ↦₆₄ pa2) ∗ ((out + 448#64) ↦₆₄ l2) ∗
     ((out + 456#64) ↦₆₄ ca3) ∗ ((out + 464#64) ↦₆₄ pa3) ∗ ((out + 472#64) ↦₆₄ 2080#64) ∗ ((out + 480#64) ↦₆₄ ca4) ∗ ((out + 488#64) ↦₆₄ pa4) ∗ ((out + 496#64) ↦₆₄ 1152#64) ∗
     ((out + 504#64) ↦₆₄ ca5) ∗ ((out + 512#64) ↦₆₄ pa5) ∗ ((out + 520#64) ↦₆₄ 960#64) ∗ ((out + 528#64) ↦₆₄ ep) ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗
     vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1) ∗ (((out + 536#64) ↦₈ b536) ∗ ((out + 537#64) ↦₁₂₈ q537) ∗
     ((out + 553#64) ↦ₛ EncoderFromPb.hiBytes7 w552) ∗ ((out + 560#64) ↦ₛ bs240) ∗ ((out + 888#64) ↦₁₂₈ q888) ∗ ((out + 904#64) ↦₁₂₈ q904) ∗ ((out + 920#64) ↦₆₄ w920)) by ac_rfl)) ?_
  rw [hbs_eq]
  exact sepConj_mono_right (sepConj_mono hreloc (sepConj_mono huc htail))
set_option maxHeartbeats 800000 in
theorem v8_stage_11264_to_ret {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s : State) (fsp out tag ep pa1 l1 pa2 l2 ca3 pa3 ca4 pa4 ca5 pa5 : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 : BitVec 32) (enc : PolyEncoder) (P_heap : SepProp) (hreloc :
      ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗ (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢ polyEncoderAt A (out + 8#64) enc) (rootKey macKey es ek ct1 : List (BitVec 8))
    (hl1 : l1 = BitVec.ofNat 64 rootKey.length) (hl2 : l2 = BitVec.ofNat 64 macKey.length) (hes : es.length = 2080) (hek : ek.length = 1152) (hct1 : ct1.length = 960) (Frame : SepProp)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64) (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11264#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx15 : s.readReg64 .x15 = tag) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa5) (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = fsp + 848#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s ((memRegion (fsp + 72#64) 48 ∗ memRegion (fsp + 160#64) 16 ∗ memRegion (fsp + 192#64) 8 ∗
        memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 1648) ∗ stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ ca5) ∗ ((fsp + 120#64) ↦₆₄ ep) ∗ memRegion (fsp + 128#64) 32 ∗ ((fsp + 176#64) ↦₆₄ pa3) ∗ ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 200#64) ↦₆₄ pa1) ∗ ((fsp + 216#64) ↦₆₄ pa4) ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt (fsp + 1888#64) bs ∗
       ((fsp + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗
       vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.ok (.ekReceivedCt1Sampled { uc := { auth := { rootKey := rootKey, macKey := macKey }, es := es, ek := ek, ct1 := ct1, epoch := ep }, sending_ct1 := enc })) ∗
          stackAt s0.sp statesFromPbStack ∗ Frame) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp ▸ sp_sub_2400_align s0.sp halign
  refine SepWP.weaken_pre (sepConj_mono_left (v8_fsp_split_11264_all fsp)) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine ProofLib.SepWP.exists_left fun u887 => ProofLib.SepWP.exists_left fun u880 =>
    ProofLib.SepWP.exists_left fun u864 => ProofLib.SepWP.exists_left fun uq848 =>
    ProofLib.SepWP.exists_left fun u832 => ProofLib.SepWP.exists_left fun uq816 =>
    ProofLib.SepWP.exists_left fun uq800 => ProofLib.SepWP.exists_left fun uq784 =>
    ProofLib.SepWP.exists_left fun uq768 => ProofLib.SepWP.exists_left fun uq752 =>
    ProofLib.SepWP.exists_left fun uq736 => ProofLib.SepWP.exists_left fun uq720 =>
    ProofLib.SepWP.exists_left fun uq704 => ProofLib.SepWP.exists_left fun uq688 =>
    ProofLib.SepWP.exists_left fun uq672 => ProofLib.SepWP.exists_left fun uq656 =>
    ProofLib.SepWP.exists_left fun uq640 => ProofLib.SepWP.exists_left fun uq624 =>
    ProofLib.SepWP.exists_left fun uq608 => ProofLib.SepWP.exists_left fun w592 =>
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun bs240 =>
    ProofLib.SepWP.exists_left fun u232 => ProofLib.SepWP.exists_left fun u208 =>
    ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
    ProofLib.SepWP.exists_left fun u160 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d96 =>
    ProofLib.SepWP.exists_left fun d92 => ?_
  have hstep := v8_stage_11264_to_8180 s0 s fsp out tag l1 pa1 l2 pa2 ca3 pa3 pa4 ca5 pa5 (hi32 ++ enc.idx) bs d96 w104 w112 u160 d172 w192 u208 u232
    uq608 uq624 uq640 uq656 uq672 uq688 uq704 uq720 uq736 uq752 uq768 uq784 uq800 uq816 u832 uq848 u864 u880 u887 (stackAt fsp encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
     memRegion fsp 64 ∗ memRegion (fsp + 72#64) 20 ∗ ((fsp + 92#64) ↦₃₂ d92) ∗ memRegion (fsp + 100#64) 4 ∗ ((fsp + 120#64) ↦₆₄ ep) ∗ memRegion (fsp + 128#64) 32 ∗
     memRegion (fsp + 168#64) 4 ∗ ((fsp + 224#64) ↦₆₄ ca4) ∗ ((fsp + 240#64) ↦ₛ bs240.val) ∗ memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗
     ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 993 ∗
     ((fsp + 1888#64) ↦₆₄ tag) ∗ memRegion (fsp + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗
     vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) hfsp_align hpc hrun hsp hx15 hx19 hx21 hx22 hx23 hx26 hx28 htr
  refine SepWP.weaken_pre ?_ (EncoderFromPb.seq_clean hstep ?_)
  · unfold v8_stagingSlotsPre; exact Entails.of_eq (by ac_rfl)
  intro s2 hpc2 hrun2 ⟨hsp2, hx6_2, hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2,
    hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2, hx16_2, hx19_2, hx23_2, htr2⟩
  subst hfsp
  have h92 := v8_fsp_64_72_entails_92 (s0.sp - 2400#64) ca5
  have h96 := v8_fsp_96_100_entails_8 (s0.sp - 2400#64) ((loByte (v8_wordAt bs 104)).zeroExtend 32)
  have h176 := v8_fsp_176_184_cells_entails_16 (s0.sp - 2400#64) pa3 pa2
  have h200 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 200#64) pa1
  have h216 := ProofLib.pointsTo64_entails_memRegion ((s0.sp - 2400#64) + 216#64) pa4
  have h1888 := v8_fsp_1888_entails_epilogue (s0.sp - 2400#64) tag (hi32 ++ enc.idx) bs hbs
  have hP2_ep : (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗
      v8_stagingSlotsPost (s0.sp - 2400#64) bs pa5 l2 ∗ v8_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗ (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗ memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 20 ∗
       (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗ memRegion ((s0.sp - 2400#64) + 100#64) 4 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ ep) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
       memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗
       (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗ (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗ memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗ epilogueStackSlots (s0.sp - 2400#64) d92 ((loByte (v8_wordAt bs 128)).zeroExtend 32)
        pa5 960#64 ep l2 1152#64 (v8_wordAt bs 0) ca4 l2 bs240.val q576 w592 (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200)
        (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264) (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376)
        (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) (v8_wordAt bs 144 >>> 8) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)
        (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24) ∗ epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
      (P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) := by
    unfold v8_stagingSlotsPost epilogueStackSlots epilogueStackGaps
    refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ ca5) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 20) ∗
      ((((s0.sp - 2400#64) + 96#64) ↦₃₂ (loByte (v8_wordAt bs 104)).zeroExtend 32) ∗ memRegion ((s0.sp - 2400#64) + 100#64) 4) ∗ ((((s0.sp - 2400#64) + 176#64) ↦₆₄ pa3) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2)) ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ pa4) ∗ ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ tag) ∗ v8_encCellsAt ((s0.sp - 2400#64) + 1888#64) bs ∗
       (((s0.sp - 2400#64) + 2280#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
       (((s0.sp - 2400#64) + 92#64) ↦₃₂ d92) ∗ (((s0.sp - 2400#64) + 104#64) ↦₆₄ pa5) ∗ (((s0.sp - 2400#64) + 112#64) ↦₆₄ 960#64) ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ ep) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ (((s0.sp - 2400#64) + 160#64) ↦₆₄ l2) ∗ memRegion ((s0.sp - 2400#64) + 168#64) 4 ∗ (((s0.sp - 2400#64) + 172#64) ↦₃₂ (loByte (v8_wordAt bs 128)).zeroExtend 32) ∗
       (((s0.sp - 2400#64) + 192#64) ↦₆₄ 1152#64) ∗ (((s0.sp - 2400#64) + 208#64) ↦₆₄ v8_wordAt bs 0) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ ca4) ∗ (((s0.sp - 2400#64) + 232#64) ↦₆₄ l2) ∗
       (((s0.sp - 2400#64) + 240#64) ↦ₛ bs240.val) ∗ memRegion ((s0.sp - 2400#64) + 568#64) 8 ∗ (((s0.sp - 2400#64) + 576#64) ↦₁₂₈ q576) ∗ (((s0.sp - 2400#64) + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion ((s0.sp - 2400#64) + 599#64) 9 ∗ (((s0.sp - 2400#64) + 608#64) ↦₁₂₈ v8_quadAt bs 152) ∗ (((s0.sp - 2400#64) + 624#64) ↦₁₂₈ v8_quadAt bs 168) ∗ (((s0.sp - 2400#64) + 640#64) ↦₁₂₈ v8_quadAt bs 184) ∗
       (((s0.sp - 2400#64) + 656#64) ↦₁₂₈ v8_quadAt bs 200) ∗ (((s0.sp - 2400#64) + 672#64) ↦₁₂₈ v8_quadAt bs 216) ∗ (((s0.sp - 2400#64) + 688#64) ↦₁₂₈ v8_quadAt bs 232) ∗
       (((s0.sp - 2400#64) + 704#64) ↦₁₂₈ v8_quadAt bs 248) ∗ (((s0.sp - 2400#64) + 720#64) ↦₁₂₈ v8_quadAt bs 264) ∗ (((s0.sp - 2400#64) + 736#64) ↦₁₂₈ v8_quadAt bs 280) ∗
       (((s0.sp - 2400#64) + 752#64) ↦₁₂₈ v8_quadAt bs 296) ∗ (((s0.sp - 2400#64) + 768#64) ↦₁₂₈ v8_quadAt bs 312) ∗ (((s0.sp - 2400#64) + 784#64) ↦₁₂₈ v8_quadAt bs 328) ∗
       (((s0.sp - 2400#64) + 800#64) ↦₁₂₈ v8_quadAt bs 344) ∗ (((s0.sp - 2400#64) + 816#64) ↦₁₂₈ v8_quadAt bs 360) ∗ (((s0.sp - 2400#64) + 832#64) ↦₆₄ v8_wordAt bs 376) ∗ memRegion ((s0.sp - 2400#64) + 840#64) 8 ∗
       (((s0.sp - 2400#64) + 848#64) ↦₁₂₈ v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) ∗ (((s0.sp - 2400#64) + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v8_wordAt bs 144 >>> 8)) ∗
       memRegion ((s0.sp - 2400#64) + 871#64) 9 ∗ (((s0.sp - 2400#64) + 880#64) ↦₆₄ unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) ∗
       (((s0.sp - 2400#64) + 888#64) ↦ₛ EncoderFromPb.loBytes7 (v8_wordAt bs 112 >>> 8)) ∗ memRegion ((s0.sp - 2400#64) + 895#64) 993 ∗ statesFromPbSavedCells s0 ∗ P_heap ∗
       vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono h92 (sepConj_mono h96 (sepConj_mono h176 (sepConj_mono h200 (sepConj_mono h216 (sepConj_mono_left h1888)))))) ?_
    exact Entails.of_eq (by ac_rfl)
  have hep := states_from_pb_epilogue_8180 hA s0 s2 out d92 ((loByte (v8_wordAt bs 128)).zeroExtend 32) pa5 960#64 ep l2 1152#64 (v8_wordAt bs 0) ca4 l2 bs240.val bs240.property q576 w592
    (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200) (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264)
    (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376) (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144))
    (v8_wordAt bs 144 >>> 8) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8) (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24)
    (P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1 ∗ Frame) halign hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_lo_2, hx27_mid_2, hx27_hi_2, hx4_2, hx5_2, hx21_2, hx7_2,
      hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2, hx1_2, hx28_2, hx16_2] at hep
  refine SepWP.weaken_pre hP2_ep (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  have hout := v8_epilogueOutFull_entails_ekReceivedCt1Sampled A (F := F) out tag l1 pa1 l2 pa2 ca3 pa3 ca4 pa4 ca5 pa5 ep bs hbs hi32 enc P_heap hreloc rootKey macKey es ek ct1 hl1 hl2 hes hek hct1
    (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val bs240.property (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24)
  refine Entails.trans (Entails.of_eq (show _ = (epilogueOutFull out 10#64 tag (v8_wordAt bs 0) (v8_wordAt bs 8) (v8_wordAt bs 16) (v8_wordAt bs 24) (v8_wordAt bs 32) (v8_wordAt bs 40)
      (v8_wordAt bs 48) (v8_wordAt bs 56) (v8_wordAt bs 64) (v8_wordAt bs 72) ((v8_wordAt bs 80).extractLsb' 0 8) ((v8_wordAt bs 80).extractLsb' 8 32)
      ((v8_wordAt bs 80).extractLsb' 40 16) ((v8_wordAt bs 80).extractLsb' 56 8) (v8_wordAt bs 88) (v8_wordAt bs 96) (loByte (v8_wordAt bs 104)) (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112)))
      (overlapWord7 (unshiftWord (v8_wordAt bs 104) (loByte (v8_wordAt bs 112))) (v8_wordAt bs 112 >>> 8)) (v8_wordAt bs 120) (((loByte (v8_wordAt bs 128)).zeroExtend 32).setWidth 8)
      (v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)) (overlapWord7 ((v8_midQ128 (v8_wordAt bs 128) (v8_wordAt bs 136) (v8_wordAt bs 144)).extractLsb' 64 64) (v8_wordAt bs 144 >>> 8))
      (v8_quadAt bs 152) (v8_quadAt bs 168) (v8_quadAt bs 184) (v8_quadAt bs 200) (v8_quadAt bs 216) (v8_quadAt bs 232) (v8_quadAt bs 248) (v8_quadAt bs 264)
      (v8_quadAt bs 280) (v8_quadAt bs 296) (v8_quadAt bs 312) (v8_quadAt bs 328) (v8_quadAt bs 344) (v8_quadAt bs 360) (v8_wordAt bs 376) (hi32 ++ enc.idx) l1 pa1 l1 l2 pa2 l2
      ca3 pa3 2080#64 ca4 pa4 1152#64 ca5 pa5 960#64 ep (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val (v8_wordAt bs 0 ++ tag) (v8_wordAt bs 16 ++ v8_wordAt bs 8) (v8_wordAt bs 24) ∗
     P_heap ∗ vecU8Payload A l1 pa1 rootKey ∗ vecU8Payload A l2 pa2 macKey ∗ vecU8Payload A ca3 pa3 es ∗ vecU8Payload A ca4 pa4 ek ∗ vecU8Payload A ca5 pa5 ct1) ∗ stackAt s0.sp statesFromPbStack ∗ Frame by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hout) (Entails.of_eq (by ac_rfl))
theorem v8_call_encoder_from_pb_10900_to_10904 {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hE : EncoderFromPbOkExt b A ext) (s0 s : State) (fsp out pa5 l1 u8 pbA l2 : BitVec 64)
    (pbEnc : PolynomialEncoder) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (Frame : SepProp) (hpts : ∀ bs ∈ (pbToProtoPolyEncoder pbEnc).pts, bs.length ≤ 2 * 0x0555555555555555)
    (halign : (s0.sp &&& 15#64 == 0#64) = true) (hfsp : fsp = s0.sp - 2400#64) (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10900#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 1888#64) (hx1 : s.readReg64 .x1 = fsp + 240#64) (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = pa5) (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA) (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) : SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10904#64) s (memRegion (fsp + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt (fsp + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt fsp encoderFromPbStack ∗ A.pool ∗ Frame) (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderFromPbAt A (fsp + 1888#64) (fromPbResult (pbToProtoPolyEncoder pbEnc)) ∗ memRegion (fsp + 240#64) 56 ∗ stackAt fsp encoderFromPbStack ∗ A.pool ∗ Frame) ∧ sf.sp = fsp ∧
        sf.readReg64 .x19 = out ∧ sf.readReg64 .x21 = pa5 ∧ sf.readReg64 .x22 = l1 ∧ sf.readReg64 .x23 = fsp + 848#64 ∧ sf.readReg64 .x26 = u8 ∧ sf.readReg64 .x27 = pbA ∧ sf.readReg64 .x28 = l2 ∧ TraceCalleeSaved sf s0)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  subst hfsp
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 2400#64 halign (by decide)
  have hpre : memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗ Frame ⊢
      (memRegion ((s0.sp - 2400#64) + 1888#64) polyEncoderSize ∗ protoPolynomialEncoderAt A ((s0.sp - 2400#64) + 240#64) (pbToProtoPolyEncoder pbEnc) ∗ A.pool ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack) ∗ Frame := by
    dsimp only [polyEncoderSize]
    refine Entails.trans (Entails.of_eq (show _ = (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48) ∗ (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (v1_optProtoPolyEncoderAt_pack_some A ((s0.sp - 2400#64) + 240#64) (pbToProtoPolyEncoder pbEnc) w0 w8 w16 w24 w32 w40 w48)) (Entails.of_eq (by ac_rfl))
  refine SepWPp.weaken_pre hpre ?_
  have hsub := v1_encoder_from_pb_ok_at_statesFromPb hE
  states_from_pb_fetches_range b (Rust.withPanics ext) 10900 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hsub hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 32996#64)
  wp_step
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (ret_pc := entry + 10904#64) (x := { out := (s0.sp - 2400#64) + 1888#64, pbA := (s0.sp - 2400#64) + 240#64, pb := pbToProtoPolyEncoder pbEnc }) (F := Frame) hsub
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.spAligned, wp_norm, arm64_norm, *]) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
    (by dsimp only [encoderFromPbSpec]
        rw [show ((s.writeReg64 (Reg.gpr 30#5) (entry + 10904#64)).setPC (entry + 32996#64)).sp = s0.sp - 2400#64 by simp only [wp_norm, arm64_norm, *]]) (by exact ⟨by simp only [Reg.x0, wp_norm, arm64_norm, *],
         by simp only [Reg.x1, wp_norm, arm64_norm, *], hpts⟩)
    rfl (fun _ _ _ _ hm => not_satisfies_false_sepConj hm) (fun sf _ => by
      dsimp only [encoderFromPbSpec, encoderFromPbOnPanic, statesFromPbOnPanic]
      exact v10_onPanic_frame_entails ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩) (fun sf hpcf hrunf hspf hcsf => ?_)
  dsimp only [encoderFromPbSpec, protoPolynomialEncoderSize]
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine SepWPp.pure_left fun htr_sf => ?_
  refine SepWPp.done hpcf hrunf ?_
  rcases hcsf with ⟨hx19_f, _hx20_f, hx21_f, hx22_f, hx23_f, _hx24_f, _hx25_f, hx26_f, hx27_f, hx28_f, _hx29_f, hvregs_f⟩
  have hsp_c : ((s.writeReg64 (Reg.gpr 30#5) (entry + 10904#64)).setPC (entry + 32996#64)).sp = s0.sp - 2400#64 := by simp only [wp_norm, arm64_norm, *]
  rw [hsp_c] at hspf ⊢
  refine ⟨Entails.of_eq (by ac_rfl), hspf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx19_f]; simp only [Reg.x19, wp_norm, arm64_norm, *]
  · rw [hx21_f]; simp only [Reg.x21, wp_norm, arm64_norm, *]
  · rw [hx22_f]; simp only [Reg.x22, wp_norm, arm64_norm, *]
  · rw [hx23_f]; simp only [Reg.x23, wp_norm, arm64_norm, *]
  · rw [hx26_f]; simp only [Reg.x26, wp_norm, arm64_norm, *]
  · rw [hx27_f]; simp only [Reg.x27, wp_norm, arm64_norm, *]
  · rw [hx28_f]; simp only [Reg.x28, wp_norm, arm64_norm, *]
  · exact ⟨by rw [htr_sf]; simp only [wp_norm, arm64_norm, *], by rw [hvregs_f]; simp only [wp_norm, arm64_norm, *]⟩
theorem v8_fsp_collapse_240_to_1888 (fsp w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : memRegion (fsp + 240#64) 56 ∗ memRegion (fsp + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt (fsp + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
      memRegion (fsp + 1576#64) 312 ⊢ memRegion (fsp + 240#64) 1648 := collapse_top <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
    collapse_step (v1_optProtoPolyEncoderWordsAt_entails_56 (fsp + 1520#64) w0 w8 w16 w24 w32 w40 w48) <| Entails.refl _
theorem v8_fsp_collapse_2304 (fsp v64 v120 v176 v184 v200 v216 v224 : BitVec 64) : memRegion fsp 64 ∗ ((fsp + 64#64) ↦₆₄ v64) ∗ memRegion (fsp + 72#64) 48 ∗
      ((fsp + 120#64) ↦₆₄ v120) ∗ memRegion (fsp + 128#64) 32 ∗ memRegion (fsp + 160#64) 16 ∗ ((fsp + 176#64) ↦₆₄ v176) ∗ ((fsp + 184#64) ↦₆₄ v184) ∗ memRegion (fsp + 192#64) 8 ∗
      ((fsp + 200#64) ↦₆₄ v200) ∗ memRegion (fsp + 208#64) 8 ∗ ((fsp + 216#64) ↦₆₄ v216) ∗ ((fsp + 224#64) ↦₆₄ v224) ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 1648 ∗ memRegion (fsp + 1888#64) 400 ∗
      memRegion (fsp + 2288#64) 16 ⊢ memRegion fsp 2304 := collapse_top <| collapse_step0 (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <|
    collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| collapse_step (Entails.refl _) <| collapse_step (Entails.refl _) <|
    collapse_step (Entails.refl _) <| Entails.refl _
theorem v8_fsp_896_split_1984 (fsp : BitVec 64) : memRegion fsp 896 ⊢ memRegion fsp 64 ∗ (∃∗ v64 : BitVec 64, ((fsp + 64#64) ↦₆₄ v64)) ∗ memRegion (fsp + 72#64) 48 ∗ (∃∗ v120 : BitVec 64, ((fsp + 120#64) ↦₆₄ v120)) ∗
      memRegion (fsp + 128#64) 32 ∗ memRegion (fsp + 160#64) 16 ∗ (∃∗ v176 : BitVec 64, ((fsp + 176#64) ↦₆₄ v176)) ∗ (∃∗ v184 : BitVec 64, ((fsp + 184#64) ↦₆₄ v184)) ∗
      memRegion (fsp + 192#64) 8 ∗ (∃∗ v200 : BitVec 64, ((fsp + 200#64) ↦₆₄ v200)) ∗ memRegion (fsp + 208#64) 8 ∗ (∃∗ v216 : BitVec 64, ((fsp + 216#64) ↦₆₄ v216)) ∗
      (∃∗ v224 : BitVec 64, ((fsp + 224#64) ↦₆₄ v224)) ∗ memRegion (fsp + 232#64) 8 ∗ memRegion (fsp + 240#64) 56 ∗ memRegion (fsp + 296#64) 600 := by
  exact split_top <| split_step0 (Entails.refl _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (Entails.refl _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _
theorem v8_fsp_1576_split_728 (fsp : BitVec 64) : memRegion (fsp + 1576#64) 728 ⊢ memRegion (fsp + 1576#64) 312 ∗ memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16 := by
  exact split_top <| split_step (Entails.refl _) <| split_step (Entails.refl _) <| Entails.refl _
theorem v8_fsp_296_to_1520_collapse (fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) : memRegion (fsp + 296#64) 600 ∗
      v8_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ memRegion (fsp + 1024#64) 496 ⊢ memRegion (fsp + 296#64) 1224 := collapse_top <| collapse_step (Entails.refl _) <|
    collapse_step (v8_ucWordsAt_entails_128 (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128) <| Entails.refl _
theorem v8_sepWPp_weaken_panic {prog : Program} {ret : BitVec 64} {s0 s : State} {P : SepProp} {Q : State → SepProp → Prop} (R : SepProp) (h : SepWPp prog ret s P Q (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf)) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hret | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ := h R' hm hL
  · exact ⟨sf, hsteps, Or.inl hret⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, fun hmR => Satisfies.mono (sepConj_mono_left hqp) hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩
theorem v8_sepWPp_seq {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp} {Q_mid Q Qp : State → SepProp → Prop} (h1 : SepWPp prog mid s P Q_mid Qp)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q_mid sm Pm → SepWPp prog ret sm Pm Q Qp) : SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hmm, hqm⟩ | hpan⟩ := h1 R hm hL
  · obtain ⟨sf, hsteps2, hout⟩ := h2 sm Pm hpcm hrunm hqm R hmm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout⟩
  · exact ⟨sm, hsteps1, Or.inr hpan⟩
theorem v8_fsp_240_split_56 (fsp : BitVec 64) : memRegion (fsp + 240#64) 56 ⊢ (∃∗ z240 : BitVec 64, (fsp + 240#64) ↦₆₄ z240) ∗ (∃∗ z248 : BitVec 64, (fsp + 248#64) ↦₆₄ z248) ∗
      (∃∗ z256 : BitVec 64, (fsp + 256#64) ↦₆₄ z256) ∗ (∃∗ z264 : BitVec 64, (fsp + 264#64) ↦₆₄ z264) ∗ (∃∗ z272 : BitVec 64, (fsp + 272#64) ↦₆₄ z272) ∗ (∃∗ z280 : BitVec 64, (fsp + 280#64) ↦₆₄ z280) ∗
      (∃∗ z288 : BitVec 64, (fsp + 288#64) ↦₆₄ z288) := by
  exact split_top <| split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <| split_step (mem64_entails _) <|
    split_step (mem64_entails _) <| split_step (mem64_entails _) <| mem64_entails _
theorem v8_pb_uc_enc_entails_224 (pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48 : BitVec 64) : (pbA ↦₆₄ 0x8000000000000008#64) ∗
      v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ⊢
      memRegion pbA optProtoInnerStateSize := by
  have h := v8_pb128_entails_full_224 pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
  rw [← v8_uc_and_enc_words_eq_pb128] at h
  exact Entails.trans (Entails.of_eq (by ac_rfl)) h
theorem v8_states_from_pb_sendingCt1_err_any_eq {F : ShaCompress} (u : V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator) (pbEnc : PolynomialEncoder) (err : PolynomialError)
    (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) = true) (hauth : u.auth = some auth)
    (henc : fromPbResult (pbToProtoPolyEncoder pbEnc) = .error err) : States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := some pbEnc }) } =
    .error (.err .stateDecode) := by
  have henc' := fromPb_eq_ok (pbToProtoPolyEncoder pbEnc)
  rw [henc] at henc'
  simp only [States.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb, Unchunked.SendCt.Ct1SentEkReceived.from_pb, hlen, hauth, ↓reduceIte,
    encoderFromPbStateDecode, spqrPolyApi, henc', StatesResult.ofPanic, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]
theorem v8_tag2_392_entails_400 (fsp : BitVec 64) : ((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392 ⊢ memRegion (fsp + 1888#64) 400 :=
  collapse_top <| collapse_step (Drop.pointsTo64_entails_memRegion _ _) <| Entails.refl _
theorem v8_5vecs_entails_dealloc (A : RustAlloc) (c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : BitVec 64) (b1 b2 b3 b4 b5 : List (BitVec 8)) : vecU8Payload A c1 p1 b1 ∗ vecU8Payload A c2 p2 b2 ∗ vecU8Payload A c3 p3 b3 ∗
      vecU8Payload A c4 p4 b4 ∗ vecU8Payload A c5 p5 b5 ⊢ vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ vecCapPtrDealloc A c3 p3 ∗ vecCapPtrDealloc A c4 p4 ∗ vecCapPtrDealloc A c5 p5 :=
  sepConj_mono (vecU8Payload_entails_dealloc A c1 p1 b1) (sepConj_mono (vecU8Payload_entails_dealloc A c2 p2 b2) (sepConj_mono (vecU8Payload_entails_dealloc A c3 p3 b3)
        (sepConj_mono (vecU8Payload_entails_dealloc A c4 p4 b4) (vecU8Payload_entails_dealloc A c5 p5 b5))))
set_option maxHeartbeats 800000 in
theorem v8_ekReceivedCt1Sampled_from_10836 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext) (hE : EncoderFromPbOkExt b A ext)
    (s0 s : State) (out pbA : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator) (sendingCt1 : Option PolynomialEncoder) (hpts : optEncoderPtsBound sendingCt1)
    (u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 : BitVec 64) (pa1 l1 pa2 l2 : BitVec 64) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE &&
      u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) = true) (hes : u.es.length = 2080) (hek : u.ek.length = 1152) (hct1 : u.ct1.length = 960) (hauth : u.auth = some auth)
    (hl1 : l1 = BitVec.ofNat 64 auth.rootKey.length) (hl2 : l2 = BitVec.ofNat 64 auth.macKey.length) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 10836#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64) (hx9 : s.readReg64 .x9 = u64) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = u64) (hx22 : s.readReg64 .x22 = l1) (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA)
    (hx28 : s.readReg64 .x28 = l2) (htr : TraceCalleeSaved s s0) : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
        memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
        memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
        vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTableAt b ∗ A.pool) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch w0 w8 w16 w24 w32 w40 w48
  cases sendingCt1 with
  | none =>
    rw [v8_states_from_pb_sendingCt1_none_eq u auth hlen hauth]
    simp only [Option.map_none, v1_optProtoPolyEncoderHeap]
    rw [show stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
        (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
        (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
        (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
        v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ ⌜w0 = noneCap⌝ ∗
        memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool = ⌜w0 = noneCap⌝ ∗ ((vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
        vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1) ∗ ((pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32) ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl]
    refine SepWPp.pure_left fun hw0 => ?_
    apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre (sepConj_mono (v8_5vecs_entails_dealloc A l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 auth.rootKey auth.macKey u.es u.ek u.ct1) (sepConj_mono_left hpb_col)) ?_
    subst hw0
    have hw_eq : v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 = (((s0.sp - 2400#64) + 1520#64) ↦₆₄ noneCap) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 8#64) ↦₆₄ w8) ∗ (((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗
         (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) := rfl
    have hstep1 := v8_check_sendingCt1_10836_none s0 s out u64 l1 l2 u8 (((((s0.sp - 2400#64) + 1520#64 + 8#64) ↦₆₄ w8) ∗ (((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗
        (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗ (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ vecCapPtrDealloc A l1 pa1 ∗ vecCapPtrDealloc A l2 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
       vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ A.pool ∗ (memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
        memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
        memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) hsp0_align hpc hrun hsp hx9 hx19 hx21 hx22 hx26 hx28 htr
    refine SepWP.weaken_pre (by rw [hw_eq]; exact Entails.of_eq (by ac_rfl)) (SepWP.seq hstep1 ?_)
    intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx9_2, hx19_2, hx21_2, hx22_2, hx26_2, hx28_2, htr2⟩
    have hstep2 := v8_cleanup_5vecs_11120 hA s0 s2 out l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 (v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 ∗
       memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) hsp0_align hpc2 hrun2 hsp2 hx9_2 hx19_2 hx21_2 hx22_2 hx26_2 hx28_2 htr2
    refine SepWP.weaken_pre (Entails.trans hP2 (by rw [hw_eq]; exact Entails.of_eq (by ac_rfl))) (SepWP.seq hstep2 ?_)
    intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx20_3, htr3⟩
    have hcol1 := v8_fsp_collapse_240_to_1888 (s0.sp - 2400#64) noneCap w8 w16 w24 w32 w40 w48
    have hcol2 := v8_fsp_collapse_2304 (s0.sp - 2400#64) u56 u.epoch u16 pa2 pa1 u40 u32
    have hP3' : P3 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) := by
      refine Entails.trans hP3 ?_
      refine Entails.trans (Entails.of_eq (show _ = (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
          v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) noneCap w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗
        (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hcol1) ?_
      refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
          (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
          (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
          memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hcol2) (Entails.of_eq (by ac_rfl))
    have hx20_byte : (s3.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx20_3]; rfl
    refine SepWP.weaken_pre hP3' (SepWP.mono (v8_err_4240 (A := A) (F := F) s0 s3 out (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_byte htr3) ?_)
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
  | some pbEnc =>
    dsimp only [optEncoderPtsBound] at hpts
    simp only [Option.map_some]
    refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ = v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
         v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) (sepConj_mono (v1_optProtoPolyEncoderHeap_extract_w0 A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48)
          (sepConj_mono_left (v8_fsp_240_split_56 (s0.sp - 2400#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro z288; apply SepWPp.exists_elim; intro z280; apply SepWPp.exists_elim; intro z272; apply SepWPp.exists_elim; intro z264; apply SepWPp.exists_elim; intro z256
    apply SepWPp.exists_elim; intro z248; apply SepWPp.exists_elim; intro z240
    refine SepWPp.pure_left fun hw0_lt => ?_
    have hw_fsp : v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 = (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48)) := by
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      have h1528 : (s0.sp - 2400#64 + 1520#64) + 8#64 = s0.sp - 2400#64 + 1528#64 := by bv_omega
      rw [h1528]
    have hw_pbA : v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 = ((pbA + 136#64) ↦₆₄ w0) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗
        ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) := by
      dsimp only [v1_optProtoPolyEncoderWordsAt]
      simp only [v8_bv_add_add_lit, BitVec.ofNat_eq_ofNat]
    have hcopy := v8_copy_enc_10836_to_10900 s0 s out pbA u64 l1 u8 l2 w0 w8 w16 w24 w32 w40 w48 z240 z248 z256 z264 z272 z280 z288
      ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
       (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48) ∗ ((pbA + 136#64) ↦₆₄ w0) ∗ v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
       vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
       v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hw0_lt hsp0_align hpc hrun hsp hx19 hx21 hx22 hx23 hx26 hx27 hx28 htr
    refine SepWPp.weaken_pre (by rw [hw_fsp, hw_pbA]; exact Entails.of_eq (by ac_rfl)) (v10_sepWPp_seq_clean hcopy ?_)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hx23_2, hx26_2, hx27_2, hx28_2, htr2⟩
    have hP2_col : v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗ (((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
        ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48) ∗
        ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
         (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48) ∗ ((pbA + 136#64) ↦₆₄ w0) ∗ v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
         vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
         v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) ⊢
        memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
        (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) := by
      refine Entails.trans (Entails.of_eq (show _ = ((pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗
         (((pbA + 136#64) ↦₆₄ w0) ∗ ((pbA + 144#64) ↦₆₄ w8) ∗ ((pbA + 152#64) ↦₆₄ w16) ∗ ((pbA + 160#64) ↦₆₄ w24) ∗ ((pbA + 168#64) ↦₆₄ w32) ∗ ((pbA + 176#64) ↦₆₄ w40) ∗ ((pbA + 184#64) ↦₆₄ w48)) ∗
         memRegion (pbA + 192#64) 32) ∗ ((((s0.sp - 2400#64) + 1520#64) ↦₆₄ w0) ∗ (((s0.sp - 2400#64) + 1528#64) ↦₆₄ w8) ∗
         ((((s0.sp - 2400#64) + 1520#64 + 16#64) ↦₆₄ w16) ∗ (((s0.sp - 2400#64) + 1520#64 + 24#64) ↦₆₄ w24) ∗ (((s0.sp - 2400#64) + 1520#64 + 32#64) ↦₆₄ w32) ∗ (((s0.sp - 2400#64) + 1520#64 + 40#64) ↦₆₄ w40) ∗
          (((s0.sp - 2400#64) + 1520#64 + 48#64) ↦₆₄ w48))) ∗ (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 240#64) w0 w8 w16 w24 w32 w40 w48 ∗
         v1_optProtoPolyEncoderHeap A (some (pbToProtoPolyEncoder pbEnc)) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
         memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
         (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
         (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
      rw [← hw_pbA, ← hw_fsp]
      exact Entails.trans (sepConj_mono_left hpb_col) (Entails.of_eq (by ac_rfl))
    have hcall := v8_call_encoder_from_pb_10900_to_10904 hE s0 s2 (s0.sp - 2400#64) out u64 l1 u8 pbA l2 pbEnc w0 w8 w16 w24 w32 w40 w48
      (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
       (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
       (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
       memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
       memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) hpts hsp0_align rfl hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2 hx21_2 hx22_2 hx23_2 hx26_2 hx27_2 hx28_2 htr2
    refine SepWPp.weaken_pre hP2_col (v8_sepWPp_seq hcall ?_)
    intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx21_3, hx22_3, hx23_3, hx26_3, hx27_3, hx28_3, htr3⟩; apply SepWPp.of_sepWP_ret
    refine SepWP.weaken_pre hP3 ?_
    have hcol_1648 : memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        memRegion ((s0.sp - 2400#64) + 1576#64) 312 ⊢ memRegion ((s0.sp - 2400#64) + 240#64) 1648 := v8_fsp_collapse_240_to_1888 (s0.sp - 2400#64) w0 w8 w16 w24 w32 w40 w48
    cases henc : fromPbResult (pbToProtoPolyEncoder pbEnc) with
    | error err =>
      rw [v8_states_from_pb_sendingCt1_err_any_eq u auth pbEnc err hlen hauth henc]
      have herr_tag := v8_resultPolyEncoder_err_entails_tag_392 A (s0.sp - 2400#64) err
      have hpre_err : resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
          (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
           (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
           (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) ⊢ (((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
           (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ vecCapPtrDealloc A l1 pa1 ∗ vecCapPtrDealloc A l2 pa2 ∗ vecCapPtrDealloc A u8 u16 ∗
           vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ A.pool ∗ (memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
            memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
            memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)) := by
        refine Entails.trans (Entails.of_eq (show _ = resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗ (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
           v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗ (vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
           vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
           memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
           (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
           (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono herr_tag (sepConj_mono hcol_1648 (sepConj_mono_left (v8_5vecs_entails_dealloc A l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 auth.rootKey auth.macKey u.es u.ek u.ct1))))
          (Entails.of_eq (by ac_rfl))
      refine SepWP.weaken_pre hpre_err (SepWP.seq (v8_check_enc_res_10904_err s0 s3 _ hsp0_align hpc3 hrun3 hsp3 htr3) ?_)
      intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, hx21_4, hx22_4, hx26_4, hx28_4, htr4⟩
      rw [hx19_3] at hx19_4; rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4
      rw [hx26_3] at hx26_4; rw [hx28_3] at hx28_4
      have hclean := v8_cleanup_5vecs_10916 hA s0 s4 out l1 pa1 l2 pa2 u8 u16 u32 u40 u56 u64 ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗
         memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
         memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
         memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392 ∗
         memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
        hsp0_align hpc4 hrun4 hsp4 hx19_4 hx21_4 hx22_4 hx26_4 hx28_4 htr4
      refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) (SepWP.seq hclean ?_)
      intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, hx19_5, hx20_5, htr5⟩
      have hcol2 := v8_fsp_collapse_2304 (s0.sp - 2400#64) u56 u.epoch u16 pa2 pa1 u40 u32
      have hP5' : P5 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) := by
        refine Entails.trans hP5 ?_
        refine Entails.trans (Entails.of_eq (show _ = ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 2#64) ∗ memRegion ((s0.sp - 2400#64) + 1896#64) 392) ∗
          (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
            (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
            memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left (v8_tag2_392_entails_400 (s0.sp - 2400#64))) ?_
        refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
            (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
            (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
            (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
            memRegion ((s0.sp - 2400#64) + 240#64) 1648 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hcol2) (Entails.of_eq (by ac_rfl))
      have hx20_byte : (s5.readReg64 .x20).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
        rw [hx20_5]; rfl
      refine SepWP.weaken_pre hP5' (SepWP.mono (v8_err_4240 (A := A) (F := F) s0 s5 out (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) hsp0_align hpc5 hrun5 hsp5 hx19_5 hx20_byte htr5) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | ok enc =>
      rw [v8_states_from_pb_ok_eq u auth pbEnc enc hlen hauth henc]
      dsimp only [resultPolyEncoderFromPbAt]
      have hrel := v8_polyEncoderAt_relocate A ((s0.sp - 2400#64) + 1888#64) (out + 8#64) enc
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ = polyEncoderAt A ((s0.sp - 2400#64) + 1888#64) enc ∗ (memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 1224 ∗
           v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ A.pool ∗
           memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗
           (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
           (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
           (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
           memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A l1 pa1 auth.rootKey ∗ vecU8Payload A l2 pa2 auth.macKey ∗
           vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl))
          (sepConj_mono hrel (sepConj_mono_left hcol_1648))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro tag; apply ProofLib.SepWP.exists_left; intro bs; apply ProofLib.SepWP.exists_left; intro hi32; apply ProofLib.SepWP.exists_left; intro P_heap
      apply ProofLib.SepWP.pure_elim; rintro ⟨htag, hreloc⟩
      have hbs_cells := v8_bs384_eq_encCells bs.val bs.property ((s0.sp - 2400#64) + 1888#64)
      have ha2280 : ((s0.sp - 2400#64) + 1888#64) + 392#64 = (s0.sp - 2400#64) + 2280#64 := by bv_omega
      rw [hbs_cells, ha2280]
      refine SepWP.seq (v8_check_enc_res_10904_ok s0 s3 tag htag _ hsp0_align hpc3 hrun3 hsp3 htr3) ?_
      intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx15_4, hx19_4, hx21_4, hx22_4, hx23_4, hx26_4, hx28_4, htr4⟩
      rw [hx19_3] at hx19_4; rw [hx21_3] at hx21_4; rw [hx22_3] at hx22_4
      rw [hx23_3] at hx23_4; rw [hx26_3] at hx26_4; rw [hx28_3] at hx28_4
      have hstage := v8_stage_11264_to_ret (F := F) hA s0 s4 (s0.sp - 2400#64) out tag u.epoch pa1 l1 pa2 l2 u8 u16 u32 u40 u56 u64 bs.val bs.property hi32 enc P_heap hreloc
        auth.rootKey auth.macKey u.es u.ek u.ct1 hl1 hl2 hes hek hct1 (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
        hsp0_align rfl hpc4 hrun4 hsp4 hx15_4 hx19_4 hx21_4 hx22_4 hx23_4 hx26_4 hx28_4 htr4
      refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) (SepWP.mono hstage ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
theorem v8_ucWordsAt_896_eq (fsp u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64) : v8_ucWordsAt (fsp + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 =
      ((fsp + 896#64) ↦₆₄ u8) ∗ ((fsp + 904#64) ↦₆₄ u16) ∗ ((fsp + 912#64) ↦₆₄ u24) ∗ ((fsp + 920#64) ↦₆₄ u32) ∗ ((fsp + 928#64) ↦₆₄ u40) ∗ ((fsp + 936#64) ↦₆₄ u48) ∗
      ((fsp + 944#64) ↦₆₄ u56) ∗ ((fsp + 952#64) ↦₆₄ u64) ∗ ((fsp + 960#64) ↦₆₄ u72) ∗ ((fsp + 968#64) ↦₆₄ u80) ∗ ((fsp + 976#64) ↦₆₄ u88) ∗ ((fsp + 984#64) ↦₆₄ u96) ∗
      ((fsp + 992#64) ↦₆₄ u104) ∗ ((fsp + 1000#64) ↦₆₄ u112) ∗ ((fsp + 1008#64) ↦₆₄ u120) ∗ ((fsp + 1016#64) ↦₆₄ u128) := by
  dsimp only [v8_ucWordsAt]
  simp only [v8_bv_add_add_lit, BitVec.ofNat_eq_ofNat]
set_option maxHeartbeats 800000 in
theorem v8_ekReceivedCt1Sampled_from_1984 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext) (hE : EncoderFromPbOkExt b A ext)
    (s0 s : State) (out pbA : BitVec 64) (u : V1State.Unchunked.Ct1SentEkReceived) (auth : ProtoAuthenticator) (sendingCt1 : Option PolynomialEncoder) (hpts : optEncoderPtsBound sendingCt1)
    (u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 : BitVec 64) (w0 w8 w16 w24 w32 w40 w48 : BitVec 64) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE &&
      u.ek.length == ENCAPSULATION_KEY_SIZE) = true) (hes : u.es.length = 2080) (hek : u.ek.length = 1152) (hct1 : u.ct1.length = 960) (hauth : u.auth = some auth) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1984#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64) (hx19 : s.readReg64 .x19 = out) (hx23 : s.readReg64 .x23 = u80)
    (hx26 : s.readReg64 .x26 = u8) (hx27 : s.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s s0) : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt ((s0.sp - 2400#64) + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112
          (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
        v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled { uc := some u, sendingCt1 := sendingCt1 }) }) ∗
          memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ = vecU8Payload A u80 u88 auth.rootKey ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 728 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ v8_ucWordsAt ((s0.sp - 2400#64) + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112
         (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
       v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u104 u112 auth.macKey ∗
       vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
         (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) (sepConj_mono (vecU8Payload_extract_len_lt63 A u80 u88 auth.rootKey) (sepConj_mono (v8_fsp_896_split_1984 (s0.sp - 2400#64))
          (sepConj_mono_left (v8_fsp_1576_split_728 (s0.sp - 2400#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro v224; apply SepWPp.exists_elim; intro v216; apply SepWPp.exists_elim; intro v200; apply SepWPp.exists_elim; intro v184; apply SepWPp.exists_elim; intro v176
  apply SepWPp.exists_elim; intro v120; apply SepWPp.exists_elim; intro v64
  refine SepWPp.pure_left fun hr_lt63 => ?_
  have hl1_lt : (BitVec.ofNat 64 auth.rootKey.length).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hr_lt63
  have hclone1 := v8_clone_rootKey_1984_to_10680 hA s0 s out pbA u8 u80 u88 u.epoch v120 v200 auth.rootKey (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
     ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗
     ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
     ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗ ((s0.sp - 2400#64 + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗
     memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ v184) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
     v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ vecU8Payload A u104 u112 auth.macKey ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗
     v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
     v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b) hsp0_align hpc hrun hsp hx19 hx23 hx26 hx27 htr
  refine SepWPp.weaken_pre (by rw [v8_ucWordsAt_896_eq]; exact Entails.of_eq (by ac_rfl)) (v8_sepWPp_seq hclone1 ?_)
  intro s2 P2 hpc2 hrun2 ⟨pa1, hP2, hsp2, hx19_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, htr2⟩
  have hclone2 := v8_clone_macKey_10680_to_10740 hA s0 s2 out pbA u8 (BitVec.ofNat 64 auth.rootKey.length) u80 u88 u104 u112 v184 auth.macKey
    ((((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗ (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
     (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u.epoch) ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗ vecCapPtrDealloc A u80 u88 ∗
     ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗ ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗
     ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗ ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗
     ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ v64) ∗
     memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ v176) ∗ memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ v216) ∗ (((s0.sp - 2400#64) + 224#64) ↦₆₄ v224) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗
     memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗ memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗
     v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
       (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
     memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b) hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx23_2 hx24_2 hx26_2 hx27_2 htr2
  refine SepWPp.weaken_pre (Entails.trans hP2 (Entails.of_eq (by ac_rfl))) (v8_sepWPp_seq hclone2 ?_)
  intro s3 P3 hpc3 hrun3 ⟨pa2, hP3, hsp3, hx19_3, hx20_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, htr3⟩
  have hdealloc := v8_dealloc_old_auth_10740_to_10836 hA s0 s3 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 (BitVec.ofNat 64 auth.rootKey.length) (BitVec.ofNat 64 auth.macKey.length) v64 v176 v216 v224
    ((((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗ (((s0.sp - 2400#64) + 1000#64) ↦₆₄ u112) ∗ (((s0.sp - 2400#64) + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
     vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ (((s0.sp - 2400#64) + 976#64) ↦₆₄ u88) ∗
     (((s0.sp - 2400#64) + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ (((s0.sp - 2400#64) + 1016#64) ↦₆₄ u.epoch) ∗ vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗
     ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
     memRegion (s0.sp - 2400#64) 64 ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗
     memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
     memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
     v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
     memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
     (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗
     v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b)
    hl1_lt hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx22_3 hx23_3 hx24_3 hx26_3 hx27_3 hx28_3 htr3
  refine SepWPp.weaken_pre (Entails.trans hP3 (Entails.of_eq (by ac_rfl))) (v10_sepWPp_seq_clean hdealloc ?_)
  intro s4 hpc4 hrun4 ⟨hsp4, hx9_4, hx19_4, hx21_4, hx22_4, hx23_4, hx26_4, hx27_4, hx28_4, htr4⟩
  have hcol_1224 := v8_fsp_296_to_1520_collapse (s0.sp - 2400#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch
  rw [v8_ucWordsAt_896_eq] at hcol_1224
  refine SepWPp.weaken_pre ?_ (v8_ekReceivedCt1Sampled_from_10836 (F := F) hA hE s0 s4 out pbA u auth sendingCt1 hpts u8 u16 u32 u40 u56 u64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112
      (BitVec.ofNat 64 auth.macKey.length) pa1 (BitVec.ofNat 64 auth.rootKey.length) pa2 (BitVec.ofNat 64 auth.macKey.length) w0 w8 w16 w24 w32 w40 w48
      hlen hes hek hct1 hauth rfl rfl hsp0_align hpc4 hrun4 hsp4 hx9_4 hx19_4 hx21_4 hx22_4 hx23_4 hx26_4 hx27_4 hx28_4 htr4)
  exact Entails.trans (Entails.of_eq (show _ = (memRegion ((s0.sp - 2400#64) + 296#64) 600 ∗ (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ 2080#64) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ 1152#64) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ 960#64) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗
        ((s0.sp - 2400#64 + 984#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗ ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u.epoch)) ∗ memRegion ((s0.sp - 2400#64) + 1024#64) 496) ∗ (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 64 ∗ (((s0.sp - 2400#64) + 64#64) ↦₆₄ u56) ∗ memRegion ((s0.sp - 2400#64) + 72#64) 48 ∗ (((s0.sp - 2400#64) + 120#64) ↦₆₄ u.epoch) ∗
       memRegion ((s0.sp - 2400#64) + 128#64) 32 ∗ memRegion ((s0.sp - 2400#64) + 160#64) 16 ∗ (((s0.sp - 2400#64) + 176#64) ↦₆₄ u16) ∗ (((s0.sp - 2400#64) + 184#64) ↦₆₄ pa2) ∗
       memRegion ((s0.sp - 2400#64) + 192#64) 8 ∗ (((s0.sp - 2400#64) + 200#64) ↦₆₄ pa1) ∗ memRegion ((s0.sp - 2400#64) + 208#64) 8 ∗ (((s0.sp - 2400#64) + 216#64) ↦₆₄ u40) ∗
       (((s0.sp - 2400#64) + 224#64) ↦₆₄ u32) ∗ memRegion ((s0.sp - 2400#64) + 232#64) 8 ∗ memRegion ((s0.sp - 2400#64) + 240#64) 56 ∗
       v1_optProtoPolyEncoderWordsAt ((s0.sp - 2400#64) + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion ((s0.sp - 2400#64) + 1576#64) 312 ∗ memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ memRegion ((s0.sp - 2400#64) + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       vecU8Payload A (BitVec.ofNat 64 auth.rootKey.length) pa1 auth.rootKey ∗ vecU8Payload A (BitVec.ofNat 64 auth.macKey.length) pa2 auth.macKey ∗
       vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
         (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
       memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) (Entails.trans (sepConj_mono_left hcol_1224) (Entails.of_eq (by ac_rfl)))
theorem v8_check_lengths_1936_err_x26 {b : BitVec 64} {ext : String → Option (State → State)} (s0 s1 : State) (out : BitVec 64) (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (z928 z936 z944 z952 : BitVec 64) (Rest : SepProp) (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1936#64) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64) (hx9_1 : s1.readReg64 .x9 = u24)
    (hq0_1 : s1.readVReg128 0#5 = u48 ++ u40) (hq1_1 : s1.readVReg128 1#5 = u64 ++ u56) (hx19_1 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2100#64) s1 (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
        ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗ Rest) (fun sm Pm =>
        (Pm ⊢ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest) ∧ sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧
        sm.readReg64 .x26 = s1.readReg64 .x26 ∧ TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  states_from_pb_fetches_range b (Rust.withPanics ext) 1936 36
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  by_cases h24 : u24 = 2080#64
  · subst h24
    by_cases h72 : u72 = 960#64
    · subst h72
      have h48 : u48 ≠ 1152#64 := by
        rcases herr with h | h | h
        · exact False.elim (h rfl)
        · exact False.elim (h rfl)
        · exact h
      have h48_bne : (u48 != 1152#64) = true := bne_iff_ne.mpr h48
      wp_steps; simp only [v8_ucWordsAt, sepConj_assoc]; wp_done
    · have h72_bne : (u72 != 960#64) = true := bne_iff_ne.mpr h72
      wp_steps; simp only [v8_ucWordsAt, sepConj_assoc]; wp_done
  · have h24_bne : (u24 != 2080#64) = true := bne_iff_ne.mpr h24
    wp_steps; simp only [v8_ucWordsAt, sepConj_assoc]; wp_done
theorem v8_step_1872_to_2100_len_err_x26 {b : BitVec 64} {ext : String → Option (State → State)} (s0 s1 : State) (out pbA : BitVec 64) (u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 : BitVec 64)
    (Rest : SepProp) (herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1872#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64) (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = s0.sp - 2400#64 + 848#64)
    (hx26_1 : s1.readReg64 .x26 = u8) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) : SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2100#64) s1
      (memRegion (s0.sp - 2400#64) 1392 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 1392#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ v8_ucWordsAt (pbA + 8#64)
          u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest) (fun sm Pm =>
        (Pm ⊢ memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
          v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest) ∧ sm.sp = s0.sp - 2400#64 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x26 = u8 ∧ TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre (sepConj_mono_left (v8_memRegion_1392_split_896_128_368 (s0.sp - 2400#64))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro z1016; apply ProofLib.SepWP.exists_left; intro z1008; apply ProofLib.SepWP.exists_left; intro z1000; apply ProofLib.SepWP.exists_left; intro z992
  apply ProofLib.SepWP.exists_left; intro z984; apply ProofLib.SepWP.exists_left; intro z976; apply ProofLib.SepWP.exists_left; intro z968; apply ProofLib.SepWP.exists_left; intro z960
  apply ProofLib.SepWP.exists_left; intro z952; apply ProofLib.SepWP.exists_left; intro z944; apply ProofLib.SepWP.exists_left; intro z936; apply ProofLib.SepWP.exists_left; intro z928
  apply ProofLib.SepWP.exists_left; intro z920; apply ProofLib.SepWP.exists_left; intro z912; apply ProofLib.SepWP.exists_left; intro z904; apply ProofLib.SepWP.exists_left; intro z896
  have hcopy := v8_copy_uc_1872_to_1936 s0 s1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 z896 z904 z912 z920 z960 z968 z976 z984 z992 z1000 z1008 z1016 (memRegion (s0.sp - 2400#64) 896 ∗
      ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗ ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗ memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗
      ((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗
      ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ u48) ∗ ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ u72) ∗
      ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗ ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗
      ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗ ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128) ∗ Rest)
    hsp0_align hpc1 hrun1 hsp1 hx19_1 hx23_1 hx26_1 hx27_1 htr1
  have h1400 : (s0.sp - 2400#64 + 1392#64) + 8#64 = s0.sp - 2400#64 + 1400#64 := by bv_omega
  refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1936#64) (P_mid := ((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
      ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
      ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
      ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
      ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗ (memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v8_ucWordsAt (pbA + 8#64)
         u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest)) (Q := fun s2 =>
      s2.sp = s0.sp - 2400#64 ∧ s2.readReg64 .x9 = u24 ∧ s2.readVReg128 0#5 = u48 ++ u40 ∧ s2.readVReg128 1#5 = u64 ++ u56 ∧ s2.readReg64 .x19 = out ∧ s2.readReg64 .x26 = u8 ∧ TraceCalleeSaved s2 s0)
    (SepWP.weaken_pre (by dsimp only [v8_ucWordsAt]; rw [h1400]; exact Entails.of_eq (by ac_rfl)) (SepWP.mono hcopy fun s2 P2 _ _ ⟨hP2, hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, _, htr2⟩ => ?_)) ?_
  · refine ⟨Entails.trans hP2 ?_, hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, htr2⟩
    have hm496 := v8_merge_368_ucWords_496 (s0.sp - 2400#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
    dsimp only [v8_ucWordsAt] at hm496 ⊢
    rw [h1400] at hm496
    refine Entails.trans (Entails.of_eq (show _ = (memRegion (s0.sp - 2400#64 + 1024#64) 368 ∗ (((s0.sp - 2400#64 + 1392#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 1400#64) ↦₆₄ u16) ∗
        ((s0.sp - 2400#64 + 1392#64 + 16#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 1392#64 + 24#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 1392#64 + 32#64) ↦₆₄ u40) ∗ ((s0.sp - 2400#64 + 1392#64 + 40#64) ↦₆₄ u48) ∗
        ((s0.sp - 2400#64 + 1392#64 + 48#64) ↦₆₄ u56) ∗ ((s0.sp - 2400#64 + 1392#64 + 56#64) ↦₆₄ u64) ∗ ((s0.sp - 2400#64 + 1392#64 + 64#64) ↦₆₄ u72) ∗ ((s0.sp - 2400#64 + 1392#64 + 72#64) ↦₆₄ u80) ∗
        ((s0.sp - 2400#64 + 1392#64 + 80#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 1392#64 + 88#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 1392#64 + 96#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1392#64 + 104#64) ↦₆₄ u112) ∗
        ((s0.sp - 2400#64 + 1392#64 + 112#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1392#64 + 120#64) ↦₆₄ u128))) ∗ (((s0.sp - 2400#64 + 896#64) ↦₆₄ u8) ∗ ((s0.sp - 2400#64 + 904#64) ↦₆₄ u16) ∗
       ((s0.sp - 2400#64 + 912#64) ↦₆₄ u24) ∗ ((s0.sp - 2400#64 + 920#64) ↦₆₄ u32) ∗ ((s0.sp - 2400#64 + 928#64) ↦₆₄ z928) ∗ ((s0.sp - 2400#64 + 936#64) ↦₆₄ z936) ∗
       ((s0.sp - 2400#64 + 944#64) ↦₆₄ z944) ∗ ((s0.sp - 2400#64 + 952#64) ↦₆₄ z952) ∗ ((s0.sp - 2400#64 + 960#64) ↦₆₄ u72) ∗ ((s0.sp - 2400#64 + 968#64) ↦₆₄ u80) ∗
       ((s0.sp - 2400#64 + 976#64) ↦₆₄ u88) ∗ ((s0.sp - 2400#64 + 984#64) ↦₆₄ u96) ∗ ((s0.sp - 2400#64 + 992#64) ↦₆₄ u104) ∗ ((s0.sp - 2400#64 + 1000#64) ↦₆₄ u112) ∗
       ((s0.sp - 2400#64 + 1008#64) ↦₆₄ u120) ∗ ((s0.sp - 2400#64 + 1016#64) ↦₆₄ u128) ∗ memRegion (s0.sp - 2400#64) 896 ∗ ((pbA + 8#64) ↦₆₄ u8) ∗ ((pbA + 8#64 + 8#64) ↦₆₄ u16) ∗
       ((pbA + 8#64 + 16#64) ↦₆₄ u24) ∗ ((pbA + 8#64 + 24#64) ↦₆₄ u32) ∗ ((pbA + 8#64 + 32#64) ↦₆₄ u40) ∗ ((pbA + 8#64 + 40#64) ↦₆₄ u48) ∗ ((pbA + 8#64 + 48#64) ↦₆₄ u56) ∗ ((pbA + 8#64 + 56#64) ↦₆₄ u64) ∗
       ((pbA + 8#64 + 64#64) ↦₆₄ u72) ∗ ((pbA + 8#64 + 72#64) ↦₆₄ u80) ∗ ((pbA + 8#64 + 80#64) ↦₆₄ u88) ∗ ((pbA + 8#64 + 88#64) ↦₆₄ u96) ∗ ((pbA + 8#64 + 96#64) ↦₆₄ u104) ∗ ((pbA + 8#64 + 104#64) ↦₆₄ u112) ∗
       ((pbA + 8#64 + 112#64) ↦₆₄ u120) ∗ ((pbA + 8#64 + 120#64) ↦₆₄ u128) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm496) (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, hx9_2, hq0_2, hq1_2, hx19_2, hx26_2, htr2⟩
    have hchk := v8_check_lengths_1936_err_x26 s0 s2 out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 z928 z936 z944 z952
      (memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ Rest)
      herr hsp0_align hpc2 hrun2 hsp2 hx9_2 hq0_2 hq1_2 hx19_2 htr2
    refine SepWP.mono hchk fun sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx26_f, htr_f⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hx19_f, Eq.trans hx26_f hx26_2, htr_f⟩
theorem v8_len_ok_of_true (u : V1State.Unchunked.Ct1SentEkReceived) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) = true) :
    u.es.length = 2080 ∧ u.ct1.length = 960 ∧ u.ek.length = 1152 := by
  dsimp only [ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE, ENCAPSULATION_KEY_SIZE] at hlen
  simp only [Bool.and_eq_true, beq_iff_eq] at hlen
  exact ⟨hlen.1.1, hlen.1.2, hlen.2⟩
theorem v8_len_err_of_false (u : V1State.Unchunked.Ct1SentEkReceived) (hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) = false)
    (hes_lt : u.es.length < 2 ^ 63) (hct1_lt : u.ct1.length < 2 ^ 63) (hek_lt : u.ek.length < 2 ^ 63) : BitVec.ofNat 64 u.es.length ≠ 2080#64 ∨ BitVec.ofNat 64 u.ct1.length ≠ 960#64 ∨
    BitVec.ofNat 64 u.ek.length ≠ 1152#64 := by
  dsimp only [ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE, ENCAPSULATION_KEY_SIZE] at hlen
  by_cases h1 : u.es.length = 2080
  · by_cases h2 : u.ct1.length = 960
    · by_cases h3 : u.ek.length = 1152
      · simp [h1, h2, h3] at hlen
      · right; right; intro heq
        have hto := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
        exact h3 hto
    · right; left; intro heq
      have hto := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
      exact h2 hto
  · left; intro heq
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    exact h1 hto
theorem v8_optProtoInnerStateAt_ekReceivedCt1Sampled_eq (A : RustAlloc) (pbA : BitVec 64) (s : V1State.Chunked.EkReceivedCt1Sampled) : optProtoInnerStateAt A pbA (some (.ekReceivedCt1Sampled s)) =
      (pbA ↦₆₄ 0x8000000000000008#64) ∗ optProtoUnchunkedCt1SentEkReceivedAt A (pbA + 8#64) s.uc ∗ optProtoPolynomialEncoderAt A (pbA + 136#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗ memRegion (pbA + 192#64) 32 := by
  dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt]
  have h136 : (pbA + 8#64) + 128#64 = pbA + 136#64 := by bv_omega
  rw [h136]; ac_rfl
theorem v8_3vecs_entails_dealloc (A : RustAlloc) (c1 p1 c2 p2 c3 p3 : BitVec 64) (b1 b2 b3 : List (BitVec 8)) : vecU8Payload A c1 p1 b1 ∗ vecU8Payload A c2 p2 b2 ∗ vecU8Payload A c3 p3 b3 ⊢
    vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ vecCapPtrDealloc A c3 p3 := sepConj_mono (vecU8Payload_entails_dealloc A c1 p1 b1) (sepConj_mono (vecU8Payload_entails_dealloc A c2 p2 b2)
      (vecU8Payload_entails_dealloc A c3 p3 b3))
set_option maxHeartbeats 800000 in
theorem states_from_pb_ekReceivedCt1Sampled_1764 {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext) (hE : EncoderFromPbOkExt b A ext)
    (s : V1State.Chunked.EkReceivedCt1Sampled) (hpts : optEncoderPtsBound s.sendingCt1) (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 1764#64) (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out) (hx23_1 : s1.readReg64 .x23 = (s0.sp - 2400#64) + 848#64) (hx27_1 : s1.readReg64 .x27 = pbA) (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1 (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        optProtoInnerStateAt A pbA (some (.ekReceivedCt1Sampled s)) ∗ statesFromPbJumpTableAt b ∗ A.pool) (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekReceivedCt1Sampled s) }) ∗ memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  refine v8_sepWPp_weaken_panic R ?_
  rw [v8_optProtoInnerStateAt_ekReceivedCt1Sampled_eq]
  refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ = optProtoUnchunkedCt1SentEkReceivedAt A (pbA + 8#64) s.uc ∗ optProtoPolynomialEncoderAt A (pbA + 136#64) (s.sendingCt1.map pbToProtoPolyEncoder) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗
       statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) (sepConj_mono (v8_optProtoUnchunkedCt1SentEkReceivedAt_unpack A (pbA + 8#64) s.uc) (sepConj_mono_left (v1_optProtoPolyEncoderAt_unpack A (pbA + 136#64)
          (s.sendingCt1.map pbToProtoPolyEncoder))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro w0; apply SepWPp.exists_elim; intro w8; apply SepWPp.exists_elim; intro w16; apply SepWPp.exists_elim; intro w24; apply SepWPp.exists_elim; intro w32; apply SepWPp.exists_elim; intro w40
  apply SepWPp.exists_elim; intro w48; apply SepWPp.exists_elim; intro u8; apply SepWPp.exists_elim; intro u16; apply SepWPp.exists_elim; intro u24; apply SepWPp.exists_elim; intro u32
  apply SepWPp.exists_elim; intro u40; apply SepWPp.exists_elim; intro u48; apply SepWPp.exists_elim; intro u56; apply SepWPp.exists_elim; intro u64
  apply SepWPp.exists_elim; intro u72; apply SepWPp.exists_elim; intro u80; apply SepWPp.exists_elim; intro u88; apply SepWPp.exists_elim; intro u96
  apply SepWPp.exists_elim; intro u104; apply SepWPp.exists_elim; intro u112; apply SepWPp.exists_elim; intro u120; apply SepWPp.exists_elim; intro u128
  cases s with | mk uc sendingCt1 =>
  dsimp only at hpts ⊢
  cases uc with
  | none =>
    rw [v8_states_from_pb_uc_none_eq]
    simp only [v8_optProtoUcHeap, sepConj_assoc]
    rw [show v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ ⌜u8 = noneCap⌝ ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool = ⌜u8 = noneCap⌝ ∗
      ((v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48) ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗
       v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl]
    refine SepWPp.pure_left fun hu8 => ?_
    subst hu8
    rw [v8_uc_and_enc_words_eq_pb128]
    apply SepWPp.of_sepWP_ret
    exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (v8_ekReceivedCt1Sampled_uc_none (F := F) hA s0 s1 out pbA u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128
        (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1)
  | some u =>
    simp only [v8_optProtoUcHeap, sepConj_assoc]
    rw [show v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗ ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.es.length ∧
          u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 u.ek.length ∧ u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 u.ct1.length ∧ u128 = u.epoch⌝ ∗
        vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗
        statesFromPbJumpTableAt b ∗ A.pool = ⌜u8.toNat < 2 ^ 63 ∧ u24 = BitVec.ofNat 64 u.es.length ∧ u32.toNat < 2 ^ 63 ∧ u48 = BitVec.ofNat 64 u.ek.length ∧ u56.toNat < 2 ^ 63 ∧ u72 = BitVec.ofNat 64 u.ct1.length ∧
        u128 = u.epoch⌝ ∗ (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ ((v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
         v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48) ∗ memRegion (s0.sp - 2400#64) 2304 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl]
    refine SepWPp.pure_left fun ⟨hu8, hu24, hu32, hu48, hu56, hu72, hu128⟩ => ?_
    rw [v8_uc_and_enc_words_eq_pb128]
    refine SepWPp.weaken_pre (sepConj_mono (vecU8Payload_extract_len_lt63 A u8 u16 u.es) (sepConj_mono (vecU8Payload_extract_len_lt63 A u32 u40 u.ek)
          (sepConj_mono_left (vecU8Payload_extract_len_lt63 A u56 u64 u.ct1)))) ?_
    rw [show (⌜u.es.length < 2 ^ 63⌝ ∗ vecU8Payload A u8 u16 u.es) ∗ (⌜u.ek.length < 2 ^ 63⌝ ∗ vecU8Payload A u32 u40 u.ek) ∗ (⌜u.ct1.length < 2 ^ 63⌝ ∗ vecU8Payload A u56 u64 u.ct1) ∗
        (v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (s0.sp - 2400#64) 2304 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
         v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) = ⌜u.es.length < 2 ^ 63⌝ ∗ ⌜u.ek.length < 2 ^ 63⌝ ∗ ⌜u.ct1.length < 2 ^ 63⌝ ∗
      (memRegion (s0.sp - 2400#64) 2304 ∗ v8_pb128At pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48 ∗
       (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
        v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl]
    refine SepWPp.pure_left fun hes_lt =>
      SepWPp.pure_left fun hek_lt =>
      SepWPp.pure_left fun hct1_lt => ?_
    have hcopy := v8_copy_pb_to_stack_1764 s0 s1 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
      (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗
       v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
    have hu8_ne : (u8 + 1#64 == 0#64) = false := v10_cap_add_one_beq_zero_false hu8
    simp only [hu8_ne, Bool.false_eq_true, ↓reduceIte] at hcopy
    refine v10_sepWPp_seq_clean hcopy ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx26_2, hx27_2, htr2⟩
    rw [hx23_1] at hx23_2
    rw [← v8_uc_and_enc_words_eq_pb128]
    cases hlen : (u.es.length == ENCAPSULATION_STATE_SIZE && u.ct1.length == CIPHERTEXT1_SIZE && u.ek.length == ENCAPSULATION_KEY_SIZE) with
    | false =>
      rw [v8_states_from_pb_len_err_eq u sendingCt1 hlen]
      have herr : u24 ≠ 2080#64 ∨ u72 ≠ 960#64 ∨ u48 ≠ 1152#64 := by
        rw [hu24, hu72, hu48]
        exact v8_len_err_of_false u hlen hes_lt hct1_lt hek_lt
      apply SepWPp.of_sepWP_ret
      have hstep := v8_step_1872_to_2100_len_err_x26 s0 s2 out pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
         v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)
        herr hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hx27_2 htr2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq hstep ?_)
      intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx26_3, htr3⟩
      have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 w0 w8 w16 w24 w32 w40 w48
      have h3v := v8_3vecs_entails_dealloc A u8 u16 u32 u40 u56 u64 u.es u.ek u.ct1
      have hP3' : P3 ⊢ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
          memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
          v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
          vecCapPtrDealloc A u8 u16 ∗ vecCapPtrDealloc A u32 u40 ∗ vecCapPtrDealloc A u56 u64 ∗ v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ A.pool ∗
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) := by
        refine Entails.trans hP3 ?_
        refine Entails.trans (Entails.of_eq (show _ = ((pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
           v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32) ∗ (vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1) ∗
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 ∗
           memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗ v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
           v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ A.pool ∗ statesFromPbJumpTableAt b) by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hpb_col (sepConj_mono_left h3v)) (Entails.of_eq (by ac_rfl))
      refine SepWP.weaken_pre hP3' (SepWP.mono (v8_drop_uc_and_sendingCt1_2100 (F := F) hA s0 s3 out u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 u128 u.auth
        (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 htr3) ?_)
      intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
    | true =>
      obtain ⟨hes, hct1, hek⟩ := v8_len_ok_of_true u hlen
      have hu24_eq : u24 = 2080#64 := by rw [hu24, hes]
      have hu48_eq : u48 = 1152#64 := by rw [hu48, hek]
      have hu72_eq : u72 = 960#64 := by rw [hu72, hct1]
      subst hu24_eq hu48_eq hu72_eq hu128
      have hstep := v8_step_1872_to_1972_len_ok s0 s2 out pbA u8 u16 u32 u40 u56 u64 u80 u88 u96 u104 u112 u120 u.epoch (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
         memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
         v1_optProtoAuthHeap A u.auth u80 u88 u96 u104 u112 u120 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)
        hsp0_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 hx27_2 htr2
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (v10_sepWPp_seq_clean hstep ?_)
      intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx26_3, hx27_3, htr3⟩
      cases hauth : u.auth with
      | none =>
        rw [v8_states_from_pb_auth_none_eq u sendingCt1 hlen hauth]
        dsimp only [v1_optProtoAuthHeap]
        rw [show memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
             ⌜u80 = noneCap⌝ ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) = ⌜u80 = noneCap⌝ ∗
          (v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ ((pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ memRegion (pbA + 192#64) 32) ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
           statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl]
        refine SepWPp.pure_left fun hu80 => ?_
        subst hu80
        apply SepWPp.of_sepWP_ret
        have hpb_col := v8_pb_uc_enc_entails_224 pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 noneCap u88 u96 u104 u112 u120 u.epoch w0 w8 w16 w24 w32 w40 w48
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left hpb_col)) ?_
        have hchk := v8_check_auth_1972_none s0 s3 out u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u88 u96 u104 u112 u120 u.epoch (memRegion pbA optProtoInnerStateSize ∗
           stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
           statesFromPbJumpTableAt b ∗ A.pool) hsp0_align hpc3 hrun3 hsp3 hx19_3 htr3
        refine SepWP.seq hchk ?_
        intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, htr4⟩
        have hdrop := v8_drop_uc_auth_none_10544 (F := F) hA s0 s4 out u u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u88 u96 u104 u112 u120 (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48
          (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) hsp0_align hu8 (by rw [hes]; rfl) hu32 (by rw [hek]; rfl) hu56 (by rw [hct1]; rfl) hauth hpc4 hrun4 hsp4 hx19_4 htr4
        refine SepWP.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) (SepWP.mono hdrop ?_)
        intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩
      | some auth =>
        dsimp only [v1_optProtoAuthHeap]
        rw [show memRegion (s0.sp - 2400#64) 896 ∗ v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ (v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗
             memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗ vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗
             (⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length ∧ u120 = BitVec.ofNat 64 auth.macKey.length⌝ ∗ vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey) ∗
             v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗ stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             (pbA ↦₆₄ 0x8000000000000008#64) ∗ memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) = ⌜u80.toNat < 2 ^ 63 ∧ u96 = BitVec.ofNat 64 auth.rootKey.length ∧
            u120 = BitVec.ofNat 64 auth.macKey.length⌝ ∗ (v8_ucWordsAt (s0.sp - 2400#64 + 896#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗
           (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
            v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗
            vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64)
              u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 u96 u104 u112 u120 u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
            memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool)) by ac_rfl]
        refine SepWPp.pure_left fun ⟨hu80, hu96, hu120⟩ => ?_
        subst hu96 hu120
        have hchk := v8_check_auth_1972_some s0 s3 out pbA u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88 (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch
          (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 896 ∗ memRegion (s0.sp - 2400#64 + 1024#64) 496 ∗
           v1_optProtoPolyEncoderWordsAt (s0.sp - 2400#64 + 1520#64) w0 w8 w16 w24 w32 w40 w48 ∗ v1_optProtoPolyEncoderHeap A (sendingCt1.map pbToProtoPolyEncoder) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (s0.sp - 2400#64 + 1576#64) 728 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ vecU8Payload A u80 u88 auth.rootKey ∗ vecU8Payload A u104 u112 auth.macKey ∗
           vecU8Payload A u8 u16 u.es ∗ vecU8Payload A u32 u40 u.ek ∗ vecU8Payload A u56 u64 u.ct1 ∗ (pbA ↦₆₄ 0x8000000000000008#64) ∗ v8_ucWordsAt (pbA + 8#64) u8 u16 2080#64 u32 u40 1152#64 u56 u64 960#64 u80 u88
             (BitVec.ofNat 64 auth.rootKey.length) u104 u112 (BitVec.ofNat 64 auth.macKey.length) u.epoch ∗ v1_optProtoPolyEncoderWordsAt (pbA + 136#64) w0 w8 w16 w24 w32 w40 w48 ∗
           memRegion (pbA + 192#64) 32 ∗ statesFromPbJumpTableAt b ∗ A.pool) hu80 hsp0_align hpc3 hrun3 hsp3 hx19_3 hx26_3 hx27_3 htr3
        refine v10_sepWPp_seq_clean hchk ?_
        intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx23_4, hx26_4, hx27_4, htr4⟩
        exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (v8_ekReceivedCt1Sampled_from_1984 (F := F) hA hE s0 s4 out pbA u auth sendingCt1 hpts u8 u16 u32 u40 u56 u64 u80 u88 u104 u112 w0 w8 w16 w24 w32 w40 w48
            hlen hes hek hct1 hauth hsp0_align hpc4 hrun4 hsp4 hx19_4 hx23_4 hx26_4 hx27_4 htr4)
end CryptoVerification.SpqrV1.States.FromPb
