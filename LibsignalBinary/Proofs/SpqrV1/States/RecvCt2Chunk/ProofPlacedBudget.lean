/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1cPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2bPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2cPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3cPlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Top-Level Budget Relocatable Verification

Composes all `RustCliAllocBudget` relocatable segments of `<EkSentCt1Received>::recv_ct2_chunk`
(Block `350`, `514` instructions) to prove `RecvCt2ChunkPlacedOkExt` and `RecvCt2ChunkPlacedOkX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.HKDF (hkdfBlocks hkdfExpand)
open CryptoGames.HMAC (hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalPlacement blkPC_379 blkPC_419 blkPl_350 blkPl_379 blkPl_419
  lsProg_350 lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator Bytes MlKem compare_prefix isNonZero length_hmacWith mlkemDecapsSpec
  sckaKeyInfoPrefix spqrAuthApi spqrHkdfWith spqrPolyApi
)
open CryptoVerification.LibsignalTripleRatchet (
  HkdfPlacedHooks LibsignalCodeRoLoaded extHookStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Keys (SepWPp.rw_pre)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.SpqrV1.Alloc (
  spqrHandleErrorSym spqrMemcpySym spqrPanicConstAddOverflowSym
  spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
)
open CryptoVerification.SpqrV1.Auth (
  SepWPp.pure_left_focus authenticatorPinAt vecBufAt
)
open CryptoVerification.SpqrV1.ChainProofs (hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Drop (chunkedEkSentCt1ReceivedSize)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Kdf (spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  RecvCt2ChunkGhost auth_update_macKey_length_32 auth_update_rootKey_length_32 ct2DeallocAt
  ekSentCt1ReceivedAt macCtUnchecked_eq_hmacWith recvCt2ChunkStackX recvCt2RoPlacedAt
  recv_ct2_chunk_eq_err_macVerifyFailed savedRegsAt spqrAssertFailedU64Sym spqrLibcruxHmacSym'
  spqrMlkemDecapsSym spqrPanicBoundsCheckSym spqrRustDeallocSym' spqrSliceIndexFailSym
  spqrUnwrapFailedSym unusedFrameAt vecU8At_expose_sp_1280
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget rustAllocEvents rustCliAllocBudgetSpec
  rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (
  framelessMemcpyAcpSpec sessionMemcpyRegionROSpec
)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux (AuthUpdateLenEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  OptSecret32AllocEnv PolyDecodedMessagePlacedOkX RecvCt2ChunkEnv
  RecvCt2ChunkPlacedOkExt RecvCt2ChunkPlacedOkExtOfEnv
  RecvCt2ChunkPlacedOkExtOfPrePostEnv RecvCt2ChunkPlacedOkX
  RecvCt2ChunkPlacedOkXOfEnv RecvCt2ChunkPlacedOkXOfPrePostEnv
  RecvCt2PlacedAlloc RecvCt2PostDecapsEnv RecvCt2ReserveCt1Env ctLabelSym
  fitsEnv_authUpdate_of_postDecaps fitsEnv_optSecret32_of_postDecaps
  fitsEnv_reserveCt1_of_postDecaps fitsEvents_hmac_of_postDecaps
  fitsEvents_preAuth_of_postDecaps hkdfToSlice_placed_ok_of_hooks
  optSecret32AllocEnv_alloc32 optSecret32AllocEnv_nil
  recvCt2ChunkBudgetOnPanic recvCt2ChunkEnv_of_postDecaps
  recvCt2ChunkPlacedOkExtOfEnv_of_okX recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX
  recvCt2ChunkPlacedOkExt_of_okX recvCt2ChunkPlacedSpecOfPrePostEnv
  recvCt2HmacEvents recvCt2MacCt2AllocEvents recvCt2PlacedPostQOfPrePostEnv
  recvCt2PlacedPostQp recvCt2PostDecapsEnv_mk recvCt2PreAuthUpdateEvents
  sckaKeyInfoPrefixSym subroutine_ok_withLsCodeRoLoaded_rodata3_keep zeros32Sym
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part1cPlacedBudget (
  recv_ct2_chunk_part1_placed_wpp_ofPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2PlacedBudget (
  recv_ct2_chunk_ss_hkdf_update_placed_wpp_ofPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2bPlacedBudget (
  recv_ct2_chunk_append_hmac_placed_wpp recv_ct2_chunk_reserve_ct1_placed_wpp
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part2cPlacedBudget (
  recv_ct2_chunk_mac_compare_placed_wpp
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3PlacedBudget (
  recv_ct2_chunk_err_placed_wpp
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3cPlacedBudget (
  recv_ct2_chunk_ok_done_dealloc_placed_wpp
)

private theorem spqrHkdfWith_32_length (F : ShaCompress) (salt ikm info : Bytes) :
    (spqrHkdfWith F salt ikm info 32).length = 32 := by
  simp only [spqrHkdfWith, hkdfExpand]
  have hdiv : (32 + 31) / 32 = 1 := rfl
  rw [hdiv]
  simp only [hkdfBlocks, List.nil_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.length_take, length_hmacWith]
  decide

private theorem ro3_pre_assoc (φ : Prop) (r1 r2 r3 P R : SepProp) :
    (⌜φ⌝ ∗ r1 ∗ r2 ∗ r3 ∗ P) ∗ R = (⌜φ⌝ ∗ (r1 ∗ r2 ∗ r3) ∗ P) ∗ R := by
  simp only [sepConj_assoc]

private theorem ro3_post_assoc (r1 r2 r3 Q R : SepProp) :
    ((r1 ∗ r2 ∗ r3) ∗ Q) ∗ R = (r1 ∗ r2 ∗ r3 ∗ Q) ∗ R := by
  simp only [sepConj_assoc]

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  addChunkTotal decodedMessageTotal
  spqrHkdfWith Authenticator.update
  CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk

private theorem lt_128_of_compare_prefix_drop_bne_placed {ct2Full tag : List (BitVec 8)}
    (hcmp : (compare_prefix (ct2Full.drop 128) tag != 0#8) = true) :
    128 < ct2Full.length := by
  by_contra hle
  have hdrop : ct2Full.drop 128 = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop, compare_prefix] at hcmp
  change (isNonZero 0#8 != 0#8) = true at hcmp
  revert hcmp; decide

/-! ## Top-Level Composition (`recvCt2ChunkStackX = 19552`B) -/

set_option maxHeartbeats 1600000 in
/-- Two-envelope (`PreEnv` / `PostEnv`) top-level relocatable `[LibsignalPlacement]` proof of
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackX`) parameterized
    by `RecvCt2PlacedAlloc` and explicit callee contracts for Block `419` (`add_chunk`),
    Block `418` (`decoded_message`), and Block `379` (`hkdf_to_slice`). -/
theorem recv_ct2_chunk_placed_ok_of_contracts_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hsub_pre : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PreEnv x evs)
    (hsub_post : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PostEnv x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkXOfPrePostEnv K F M A lim PreEnv PostEnv ext := by
  unfold RecvCt2ChunkPlacedOkXOfPrePostEnv DefsPlacedBudget.RecvCt2ChunkPlacedOkXOfPrePostEnv
    DefsBudget.RecvCt2ChunkPlacedOkXOfPrePostEnv
  refine subroutine_ok_withLsCodeRoLoaded_rodata3_keep
    (s1 := sckaKeyInfoPrefixSym) (b1 := sckaKeyInfoPrefix)
    (s2 := zeros32Sym) (b2 := List.replicate 32 0#8)
    (s3 := ctLabelSym) (b3 := Authenticator.ctLabel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ?_
  let roSpec : Spec (RecvCt2ChunkGhost F × M.σ) :=
    { DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim PreEnv PostEnv with
      pre := fun (x, st) s =>
        ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗
          recvCt2RoPlacedAt ∗
          (DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim PreEnv PostEnv).pre
            (x, st) s
      post := fun (x, st) s0 sf =>
        recvCt2RoPlacedAt ∗
          (DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim PreEnv PostEnv).post
            (x, st) s0 sf }
  have hro_ok : subroutine_ok (lsProg_350 (Rust.withPanics ext)) (blkPl_350).base roSpec := by
    refine subroutine_ok_of_sepWPp_init fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp => ?_
    have hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true := hsp
    dsimp only [roSpec, DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv,
      DefsBudget.recvCt2ChunkPlacedSpecOfPrePostEnv] at hpre
    have hpre' : s0.mem ⊨
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          (⌜s0.readReg64 .x0 = x.outA ∧
            s0.readReg64 .x1 = x.selfA ∧
            s0.readReg64 .x2 = x.epoch ∧
            s0.readReg64 .x3 = x.chunkA ∧
            PolyDecoderStrictSorted x.self.receiving_ct2 ∧
            x.self.uc.auth.rootKey.length + 32 < 2 ^ 63 ∧
            FitsEnv M lim st0 (PreEnv x)⌝ ∗
          ((recvCt2RoPlacedAt ∗
            memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
            ekSentCt1ReceivedAt A.repAlloc x.selfA x.self ∗
            chunkAt x.chunkA x.chunk ∗
            tokenInitPlacedAt ∗
            reduceTablePlacedAt ∗
            A.pool lim st0 s0 ∗
            stackAt s0.sp recvCt2ChunkStackX) ∗ R)) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hpre'
    rcases hpre' with ⟨hinv, hpre'⟩
    rw [satisfies_pure_sepConj] at hpre'
    rcases hpre' with ⟨⟨hx0, hx1, hx2, hx3, hsort_self, hroot_lt, hfits_pre⟩, hm⟩
    have hfits : FitsEnv M lim st0 (RecvCt2ChunkEnv x) :=
      fun evs hevs => hfits_pre evs (hsub_pre x hevs)
    refine ⟨_, hm, ?_⟩
    change SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) s0 _
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R)
    exact recv_ct2_chunk_part1_placed_wpp_ofPrePostEnv
      hA hadd_ok hdec_ok hdecaps x st0 s0 R
      hfits (fun {evs} hevs => hsub_post x hevs)
      hsort_self hpc hrun hsp_s0 hinv hx0 hx1 hx2 hx3
      (fun st2 receivingCt2 ct2Full cap_ct2 ptr_ct2 ptr_mac ptr_ct2_128 c3 _c7
        g_auth cap_dk ptr_dk cap_ct1 ptr_ct1 eAdd eDec
        hepoch hadd _hadd_tot _hsort hdec hdec_tot heAdd heDec hfit_post
        hge128 hlt_max hct1_len htake128_len hdk_len
        hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
        hpc2 hrun2 hsp2 htr2 hvregs2 hinv2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 => by
      let ss_raw :=
        (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩
          ⟨ct2Full.take 128, htake128_len⟩).toList
      have hss_raw_len : ss_raw.length = 32 :=
        (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩
          ⟨ct2Full.take 128, htake128_len⟩).2
      have hge_not_lt : ¬ ct2Full.length < 128 := by omega
      let st_dec0 := M.stepEvents eDec (M.stepEvents eAdd st0)
      let σ_dec := M.stepEvents (recvCt2MacCt2AllocEvents ct2Full.length) st_dec0
      have hfit_pre : FitsEvents M lim σ_dec recvCt2PreAuthUpdateEvents :=
        fitsEvents_preAuth_of_postDecaps hfit_post
      have hfit_upd :
          FitsEnv M lim (M.stepEvents recvCt2PreAuthUpdateEvents σ_dec)
            (AuthUpdateLenEnv x.self.uc.auth.rootKey.length 32) := by
        have h := fitsEnv_authUpdate_of_postDecaps hfit_post
        dsimp only [σ_dec, st_dec0]
        rwa [M.stepEvents_append] at h
      refine SepWPp.rw_pre ?_
        (recv_ct2_chunk_ss_hkdf_update_placed_wpp_ofPrePostEnv hA hhkdf
          x ss_raw ct2Full ptr_ct2 ptr_dk ptr_ct2_128 cap_ct2 c3 g_auth
          st0 σ_dec s0 st2
          (memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
            memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
            ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
            ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
            (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
            A.live ptr_ct2_128 128 1 ∗
            vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
            vecU8At A.repAlloc (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ∗
            memRegion (s0.sp - 2000#64) 144 ∗
            memRegion (s0.sp - 1344#64) 16 ∗
            unusedFrameAt (s0.sp - 2496#64) ∗
            ((s0.sp - 2496#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
            ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
            ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
            ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
            ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
            ((s0.sp - 2440#64) ↦₆₄ ptr_ct1) ∗
            ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
            polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
            memRegion (s0.sp - 2024#64) 24 ∗
            memRegion (s0.sp - 1856#64) 504 ∗
            chunkAt x.chunkA x.chunk ∗
            tokenInitPlacedAt ∗
            reduceTablePlacedAt ∗
            savedRegsAt s0)
          R hss_raw_len htake128_len hroot_lt hfit_pre hfit_upd
          hpc2 hrun2 hsp2 hsp_s0 htr2 hvregs2 hinv2
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2
          (fun st3 cap_info ptr_info ptr_ss_raw ptr_ss g_auth' evs_upd hevs_upd
            _hptr_ss_raw_ne _hptr_ss_ne
            hpc3 hrun3 hsp3 htr3 hvregs3 hinv3
            hx19_3 _hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 _hx26_3 hx27_3 hx28_3 hx29_3 => ?_))
      · dsimp only [ss_raw, σ_dec, st_dec0]; sep_ac_rfl
      have hexp_ct1 :
          vecU8At A.repAlloc (s0.sp - 1280#64) cap_ct1 ptr_ct1 x.self.uc.ct1 ⊢
            ⌜x.self.uc.ct1.length ≤ cap_ct1.toNat ∧
              cap_ct1.toNat < 2 ^ 63 ∧
              ptr_ct1 ≠ 0#64 ∧
              cap_ct1 ≠ 0#64⌝ ∗
              ((s0.sp - 1280#64) ↦₆₄ cap_ct1) ∗
              ((s0.sp - 1272#64) ↦₆₄ ptr_ct1) ∗
              ((s0.sp - 1264#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.ct1.length) ∗
              (ptr_ct1 ↦ₛ x.self.uc.ct1) ∗
              memRegion (ptr_ct1 + BitVec.ofNat 64 x.self.uc.ct1.length)
                (cap_ct1.toNat - x.self.uc.ct1.length) ∗
              A.live ptr_ct1 cap_ct1.toNat 1 :=
        vecU8At_expose_sp_1280 A.repAlloc s0.sp cap_ct1 ptr_ct1 x.self.uc.ct1 (by omega)
      refine SepWPp.fold hexp_ct1 (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) fun _ => ?_
      refine SepWPp.rw_pre (by rw [hct1_len]) ?_
      let σ_upd := M.stepEvents evs_upd (M.stepEvents recvCt2PreAuthUpdateEvents σ_dec)
      have hfit_res : FitsEnv M lim σ_upd RecvCt2ReserveCt1Env := by
        have h := fitsEnv_reserveCt1_of_postDecaps hevs_upd hfit_post
        dsimp only [σ_upd, σ_dec, st_dec0]
        rwa [M.stepEvents_append] at h
      refine SepWPp.rw_pre ?_
        (recv_ct2_chunk_reserve_ct1_placed_wpp hA x st0 σ_upd cap_ct1 ptr_ct1 s0 st3
          (recvCt2RoPlacedAt ∗
            authenticatorPinAt A.repAlloc g_auth' (s0.sp - 1328#64)
              (x.self.uc.auth.update F x.epoch
                (spqrHkdfWith F (List.replicate 32 0#8) ss_raw
                  (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32)) ∗
            (ptr_ss_raw ↦ₛ ss_raw) ∗
            A.live ptr_ss_raw 32 1 ∗
            (ptr_ss ↦ₛ
              spqrHkdfWith F (List.replicate 32 0#8) ss_raw
                (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32) ∗
            A.live ptr_ss 32 1 ∗
            ct2DeallocAt A.repAlloc cap_info ptr_info ∗
            ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
            ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
            ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
            memRegion (s0.sp - 128#64) 8 ∗
            memRegion (s0.sp - 288#64) 128 ∗
            memRegion (s0.sp - 1248#64) 960 ∗
            ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
            memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
            memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
            ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
            ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
            (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
            A.live ptr_ct2_128 128 1 ∗
            vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
            memRegion (s0.sp - 2000#64) 144 ∗
            memRegion (s0.sp - 1344#64) 16 ∗
            unusedFrameAt (s0.sp - 2496#64) ∗
            ((s0.sp - 2496#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
            ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
            ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
            ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
            ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
            ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
            polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
            memRegion (s0.sp - 2024#64) 24 ∗
            memRegion (s0.sp - 1856#64) 504 ∗
            chunkAt x.chunkA x.chunk ∗
            tokenInitPlacedAt ∗
            reduceTablePlacedAt ∗
            savedRegsAt s0)
          R hfit_res hct1_len hcap_ct1 hle_ct1 hmax_ct1 hptr_ct1
          hpc3 hrun3 hsp3 hsp_s0 htr3 hvregs3 hinv3
          (fun st4 cap_ct1' ptr_ct1' eRes heRes
            hcap_ct1'_ne hge1088 hmax_ct1' hptr_ct1'_ne
            hpc4 hrun4 hsp4 htr4 hvregs4 hinv4
            hx8_4 hx19_4 _hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 _hx26_4 hx27_4 hx28_4 hx29_4 => ?_))
      · dsimp only [σ_upd]; sep_ac_rfl
      let ss :=
        spqrHkdfWith F (List.replicate 32 0#8) ss_raw
          (sckaKeyInfoPrefix ++ toBEBytes 8 x.epoch) 32
      let auth' := x.self.uc.auth.update F x.epoch ss
      have hss_len : ss.length = 32 := spqrHkdfWith_32_length F _ _ _
      have hmk_len : auth'.macKey.length = 32 :=
        auth_update_macKey_length_32 F x.self.uc.auth x.epoch ss
      have hrk_len : auth'.rootKey.length = 32 :=
        auth_update_rootKey_length_32 F x.self.uc.auth x.epoch ss
      let σ_res := M.stepEvents eRes σ_upd
      have hfit_hmac : FitsEvents M lim σ_res recvCt2HmacEvents := by
        have h := fitsEvents_hmac_of_postDecaps hevs_upd heRes hfit_post
        dsimp only [σ_res, σ_upd, σ_dec, st_dec0]
        rwa [M.stepEvents_append] at h
      refine SepWPp.rw_pre ?_
        (recv_ct2_chunk_append_hmac_placed_wpp hA hhmac x st0 σ_res ct2Full auth' g_auth'
          cap_ct1' ptr_ct1' ptr_ct2_128 0#64 s0 st4
          (((lsρ sckaKeyInfoPrefixSym) ↦ᵣ sckaKeyInfoPrefix) ∗
            ((lsρ zeros32Sym) ↦ᵣ List.replicate 32 0#8) ∗
            (ptr_ss_raw ↦ₛ ss_raw) ∗
            A.live ptr_ss_raw 32 1 ∗
            (ptr_ss ↦ₛ ss) ∗
            A.live ptr_ss 32 1 ∗
            ct2DeallocAt A.repAlloc cap_info ptr_info ∗
            ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
            ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
            ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
            memRegion (s0.sp - 128#64) 8 ∗
            ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
            memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
            memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
            ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
            ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
            A.live ptr_ct2_128 128 1 ∗
            vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
            memRegion (s0.sp - 1344#64) 16 ∗
            unusedFrameAt (s0.sp - 2496#64) ∗
            ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
            ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
            ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
            ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
            ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
            ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
            polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
            memRegion (s0.sp - 2024#64) 24 ∗
            memRegion (s0.sp - 1856#64) 504 ∗
            chunkAt x.chunkA x.chunk ∗
            tokenInitPlacedAt ∗
            reduceTablePlacedAt ∗
            memRegion (s0.sp - 19552#64) 672 ∗
            savedRegsAt s0)
          R hfit_hmac hct1_len htake128_len hmk_len hcap_ct1'_ne hge1088 hmax_ct1' hptr_ct1'_ne
          hpc4 hrun4 hsp4 hsp_s0 htr4 hvregs4 hinv4
          hx8_4 (by rw [hx25_4, hx25_3]) (by rw [hx28_4, hx28_3]) (by rw [hx29_4, hx29_3])
          (fun st5 eMdFree heMdFree hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
            hpc5 hrun5 hsp5 htr5 hvregs5 hinv5
            hx19_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 _hx26_5 hx27_5 hx29_5 => ?_))
      · dsimp only [recvCt2RoPlacedAt, auth', ss, σ_res]; sep_ac_rfl
      let σ_hmac := M.stepEvents eMdFree (M.stepEvents recvCt2HmacEvents σ_res)
      refine SepWPp.rw_pre ?_
        (recv_ct2_chunk_mac_compare_placed_wpp hA x st0 σ_hmac
          receivingCt2 ct2Full auth' ptr_mac s0 st5
          (((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗
            ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
            ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗
            ct2DeallocAt A.repAlloc cap_ct1' ptr_ct1' ∗
            ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗
            (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗
            vecU8At A.repAlloc (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
            ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗
            ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
            ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗
            (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
            memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
            A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
            ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗
            memRegion (s0.sp - 288#64) 128 ∗
            memRegion (s0.sp - 2000#64) 144 ∗
            ((lsρ ctLabelSym) ↦ᵣ Authenticator.ctLabel) ∗
            ((lsρ sckaKeyInfoPrefixSym) ↦ᵣ sckaKeyInfoPrefix) ∗
            ((lsρ zeros32Sym) ↦ᵣ List.replicate 32 0#8) ∗
            (ptr_ss_raw ↦ₛ ss_raw) ∗
            A.live ptr_ss_raw 32 1 ∗
            (ptr_ss ↦ₛ ss) ∗
            A.live ptr_ss 32 1 ∗
            ct2DeallocAt A.repAlloc cap_info ptr_info ∗
            ((s0.sp - 152#64) ↦₆₄ cap_info) ∗
            ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
            ((s0.sp - 136#64) ↦₆₄ 41#64) ∗
            memRegion (s0.sp - 128#64) 8 ∗
            ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗
            memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
            memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
            ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
            ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
            A.live ptr_ct2_128 128 1 ∗
            memRegion (s0.sp - 1344#64) 16 ∗
            unusedFrameAt (s0.sp - 2496#64) ∗
            ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
            ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
            ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗
            ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
            polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
            memRegion (s0.sp - 2024#64) 24 ∗
            memRegion (s0.sp - 1856#64) 504 ∗
            chunkAt x.chunkA x.chunk ∗
            tokenInitPlacedAt ∗
            reduceTablePlacedAt ∗
            memRegion (s0.sp - 19552#64) 672 ∗
            savedRegsAt s0)
          R hepoch hadd hdec hge_not_lt hlt_max hct1_len hdk_len
          hpc5 hrun5 hsp5 hsp_s0 htr5 hvregs5 hinv5
          (by rw [hx23_5, hx23_4, hx23_3])
          (fun st_err eTagFree heTagFree hm_le32 hcmp_err
            hpc_err hrun_err hsp_err htr_err hvregs_err hinv_err
            hx19_err hx20_err hx21_err _hx22_err hx23_err hx24_err hx25_err hx27_err hx29_err => ?_)
          (fun st_ok eTagFree heTagFree hm_le32 hcmp_ok
            hpc_ok hrun_ok hsp_ok htr_ok hvregs_ok hinv_ok
            hx19_ok hx20_ok hx21_ok hx22_ok hx23_ok hx24_ok hx25_ok hx27_ok hx29_ok => ?_))
      · dsimp only [σ_hmac]; sep_ac_rfl
      · -- `Err(Error::MacVerifyFailed)` at `+968`
        let σ_err := M.stepEvents eTagFree σ_hmac
        have hpost_env_err : ∀ evs_err : List AllocEvent, FreeOnlyEvs evs_err →
            ∃ evs_all : List AllocEvent, PostEnv x evs_all ∧
              M.stepEvents evs_err σ_err = M.stepEvents evs_all st0 := by
          intro evs_err hfree_err
          let ePost : List AllocEvent :=
            recvCt2MacCt2AllocEvents ct2Full.length ++ recvCt2PreAuthUpdateEvents ++
              evs_upd ++ eRes ++ recvCt2HmacEvents ++ (eMdFree ++ eTagFree) ++ [] ++ evs_err
          have hpost_ev :
              RecvCt2PostDecapsEnv x.self.uc.auth.rootKey.length ct2Full.length ePost :=
            recvCt2PostDecapsEnv_mk hevs_upd heRes (heMdFree.append heTagFree)
              optSecret32AllocEnv_nil hfree_err
          have henv_all : RecvCt2ChunkEnv x (eAdd ++ eDec ++ ePost) :=
            recvCt2ChunkEnv_of_postDecaps x hepoch hdec_tot hge_not_lt hct1_len hdk_len
              heAdd heDec hpost_ev
          refine ⟨eAdd ++ eDec ++ ePost, hsub_post x henv_all, ?_⟩
          dsimp only [ePost, σ_err, σ_hmac, σ_res, σ_upd, σ_dec, st_dec0]
          simp only [List.append_nil, M.stepEvents_append]
        have hcmp_err' :
            (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
             let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
             let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
             let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
             let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
             let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
             let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
             compare_prefix (ct2Full.drop 128) tag0 != 0#8) = true := by
          dsimp only
          rw [← macCtUnchecked_eq_hmacWith]
          simpa only [auth', ss, ss_raw, hepoch] using hcmp_err
        have hres_err : x.self.recv_ct2_chunk K x.epoch x.chunk = .error (.err .macVerifyFailed) :=
          recv_ct2_chunk_eq_err_macVerifyFailed x.self x.epoch x.chunk receivingCt2 ct2Full
            hepoch hadd hdec hge_not_lt hct1_len hdk_len hm_le32 hcmp_err'
        have hgt128 : 128 < ct2Full.length :=
          lt_128_of_compare_prefix_drop_bne_placed hcmp_err
        refine SepWPp.rw_pre ?_
          (recv_ct2_chunk_err_placed_wpp hA x st0 σ_err receivingCt2 ct2Full ss_raw ss auth' g_auth'
            cap_ct2 ptr_ct2 cap_dk ptr_dk cap_ct1' ptr_ct1'
            cap_info ptr_info ptr_ss_raw ptr_ss ptr_mac ptr_ct2_128
            s0 st_err R
            hpost_env_err hres_err hgt128 hlt_max hss_raw_len hss_len htake128_len hrk_len hmk_len
            hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
            hpc_err hrun_err hsp_err hsp_s0 htr_err hvregs_err hinv_err
            (by rw [hx19_err, hx19_5, hx19_4, hx19_3])
            hx20_err
            (by rw [hx21_err, hx21_5, hx21_4, hx21_3])
            hx23_err
            (by rw [hx24_err, hx24_5, hx24_4, hx24_3])
            (by rw [hx25_err, hx25_5])
            (by rw [hx27_err, hx27_5, hx27_4, hx27_3])
            (by rw [hx29_err, hx29_5]))
        · dsimp only [recvCt2RoPlacedAt, σ_err]; sep_ac_rfl
      · -- `Ok(Done(NoHeaderReceived, EpochSecret))` at `+1308`
        let σ_ok := M.stepEvents eTagFree σ_hmac
        have hfit_sec : FitsEnv M lim σ_ok OptSecret32AllocEnv := by
          have h := fitsEnv_optSecret32_of_postDecaps hevs_upd heRes
            (heMdFree.append heTagFree) hfit_post
          dsimp only [σ_ok, σ_hmac, σ_res, σ_upd, σ_dec, st_dec0]
          rwa [M.stepEvents_append, M.stepEvents_append] at h
        have hpost_env_ok : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
            ∃ evs_all : List AllocEvent, PostEnv x evs_all ∧
              M.stepEvents evs_free (M.stepEvents (rustAllocEvents 32 1) σ_ok) =
                M.stepEvents evs_all st0 := by
          intro evs_free hfree_ep
          let ePost : List AllocEvent :=
            recvCt2MacCt2AllocEvents ct2Full.length ++ recvCt2PreAuthUpdateEvents ++
              evs_upd ++ eRes ++ recvCt2HmacEvents ++ (eMdFree ++ eTagFree) ++
              rustAllocEvents 32 1 ++ evs_free
          have hpost_ev :
              RecvCt2PostDecapsEnv x.self.uc.auth.rootKey.length ct2Full.length ePost :=
            recvCt2PostDecapsEnv_mk hevs_upd heRes (heMdFree.append heTagFree)
              optSecret32AllocEnv_alloc32 hfree_ep
          have henv_all : RecvCt2ChunkEnv x (eAdd ++ eDec ++ ePost) :=
            recvCt2ChunkEnv_of_postDecaps x hepoch hdec_tot hge_not_lt hct1_len hdk_len
              heAdd heDec hpost_ev
          refine ⟨eAdd ++ eDec ++ ePost, hsub_post x henv_all, ?_⟩
          dsimp only [ePost, σ_ok, σ_hmac, σ_res, σ_upd, σ_dec, st_dec0]
          simp only [M.stepEvents_append]
        have hcmp_ok' :
            (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
             let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
             let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
             let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
             let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
             let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
             let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
             compare_prefix (ct2Full.drop 128) tag0 != 0#8) = false := by
          dsimp only
          rw [← macCtUnchecked_eq_hmacWith]
          simpa only [auth', ss, ss_raw, hepoch] using hcmp_ok
        have hss_eq :
            (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
             let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
             let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
             ss = spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32) := by
          dsimp only [ss, ss_raw]
          rw [hepoch]
        have hauth'_eq : auth' = x.self.uc.auth.update F x.self.uc.epoch ss := by
          dsimp only [auth']
          rw [hepoch]
        refine SepWPp.rw_pre ?_
          (recv_ct2_chunk_ok_done_dealloc_placed_wpp hA x st0 σ_ok receivingCt2 ct2Full
            cap_ct2 ptr_ct2 ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1'
            ptr_ss_raw cap_info ptr_info ptr_ss ss_raw ss auth' g_auth' s0 st_ok R
            hfit_sec hpost_env_ok hepoch hadd hdec hge128 hlt_max hct1_len hdk_len hm_le32 hcmp_ok'
            hss_eq hauth'_eq hss_len hss_raw_len htake128_len hrk_len hmk_len
            hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
            hpc_ok hrun_ok hsp_ok hsp_s0 htr_ok hvregs_ok hinv_ok
            (by rw [hx19_ok, hx19_5, hx19_4, hx19_3])
            hx20_ok
            (by rw [hx21_ok, hx21_5, hx21_4, hx21_3])
            (by rw [hx22_ok, hx22_5, hx22_4, hx22_3])
            hx23_ok
            (by rw [hx24_ok, hx24_5, hx24_4, hx24_3])
            (by rw [hx25_ok, hx25_5])
            (by rw [hx27_ok, hx27_5, hx27_4, hx27_3])
            (by rw [hx29_ok, hx29_5]))
        · dsimp only [recvCt2RoPlacedAt, σ_ok]; sep_ac_rfl)
  refine subroutine_ok_mono hro_ok (fun ⟨x, st0⟩ R s0 hp => ?_) (fun ⟨x, st0⟩ R s0 sf hq => ?_)
  · exact Satisfies.mono (Entails.of_eq (ro3_pre_assoc
      (LibsignalCodeRoLoaded lsmpl s0.mem)
      (lsρ sckaKeyInfoPrefixSym ↦ᵣ sckaKeyInfoPrefix)
      (lsρ zeros32Sym ↦ᵣ List.replicate 32 0#8)
      (lsρ ctLabelSym ↦ᵣ Authenticator.ctLabel)
      ((DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim PreEnv PostEnv).pre
        (x, st0) s0)
      R)) hp
  · exact Satisfies.mono (Entails.of_eq (ro3_post_assoc
      (lsρ sckaKeyInfoPrefixSym ↦ᵣ sckaKeyInfoPrefix)
      (lsρ zeros32Sym ↦ᵣ List.replicate 32 0#8)
      (lsρ ctLabelSym ↦ᵣ Authenticator.ctLabel)
      ((DefsPlacedBudget.recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim PreEnv PostEnv).post
        (x, st0) s0 sf)
      R)) hq

/-- Single-envelope (`Env = PreEnv = PostEnv`) specialization of
    `recv_ct2_chunk_placed_ok_of_contracts_ofPrePostEnv`. -/
theorem recv_ct2_chunk_placed_ok_of_contracts_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkXOfEnv K F M A lim Env ext :=
  recv_ct2_chunk_placed_ok_of_contracts_ofPrePostEnv hsub hsub hA hadd_ok hdec_ok hdecaps hhkdf
    hhmac

/-- Canonical (`RecvCt2ChunkEnv`) top-level relocatable `[LibsignalPlacement]` proof of
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackX`) parameterized
    by `RecvCt2PlacedAlloc` and explicit callee contracts. -/
theorem recv_ct2_chunk_placed_ok_of_contracts [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  recv_ct2_chunk_placed_ok_of_contracts_ofEnv (fun _ {_} h => h) hA hadd_ok hdec_ok hdecaps hhkdf
    hhmac

/-- Two-envelope (`PreEnv` / `PostEnv`) top-level relocatable `[LibsignalPlacement]` contract for
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackX`), discharging
    `hkdf_to_slice` via `[HkdfPlacedHooks F (Rust.withPanics ext)]`. -/
theorem recv_ct2_chunk_placed_ok_x_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hsub_pre : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PreEnv x evs)
    (hsub_post : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PostEnv x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkXOfPrePostEnv K F M A lim PreEnv PostEnv ext :=
  recv_ct2_chunk_placed_ok_of_contracts_ofPrePostEnv hsub_pre hsub_post hA hadd_ok hdec_ok hdecaps
    (hkdfToSlice_placed_ok_of_hooks F) hhmac

/-- Single-envelope (`Env`) top-level relocatable `[LibsignalPlacement]` contract for
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackX`), discharging
    `hkdf_to_slice` via `[HkdfPlacedHooks F (Rust.withPanics ext)]`. -/
theorem recv_ct2_chunk_placed_ok_x_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkXOfEnv K F M A lim Env ext :=
  recv_ct2_chunk_placed_ok_of_contracts_ofEnv hsub hA hadd_ok hdec_ok hdecaps
    (hkdfToSlice_placed_ok_of_hooks F) hhmac

/-- Canonical top-level relocatable `[LibsignalPlacement]` budget contract for
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackX`), discharging
    `hkdf_to_slice` via `[HkdfPlacedHooks F (Rust.withPanics ext)]`. -/
theorem recv_ct2_chunk_placed_ok_x [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  recv_ct2_chunk_placed_ok_of_contracts hA hadd_ok hdec_ok hdecaps
    (hkdfToSlice_placed_ok_of_hooks F) hhmac

/-- Top-level relocatable `[LibsignalPlacement]` budget contract for
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackX`) taking
    individual external hook and panic hypotheses directly. -/
theorem recv_ct2_chunk_placed_ok_x_of_hooks [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hallocZeroed :
      HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustCliAllocBudgetSpec M A lim true))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed_u64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked)
    (h_slice_index_fail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked)
    (h_unwrap_failed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked)
    (h_panic_bounds_check : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked)
    (h_panic_add_overflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked) :
    RecvCt2ChunkPlacedOkX K F M A lim ext :=
  recv_ct2_chunk_placed_ok_x
    { handleError := h_handle_error
      assertFailedU64 := h_assert_failed_u64
      sliceIndexFail := h_slice_index_fail
      unwrapFailed := h_unwrap_failed
      panicBoundsCheck := h_panic_bounds_check
      panicConstAddOverflow := h_panic_add_overflow
      shim := hshim
      alloc := halloc
      allocZeroed := hallocZeroed
      dealloc := hdealloc
      realloc := hrealloc
      memcpy := hmemcpy
      memcpyRO := hRO }
    hadd_ok hdec_ok hdecaps hhmac

/-! ## Contract-Backed Stack Lifts (`recvCt2ChunkStackExt = 20272`B) -/

/-- Two-envelope (`PreEnv` / `PostEnv`) contract-backed (`recvCt2ChunkStackExt`) top-level
    relocatable `[LibsignalPlacement]` proof of `<EkSentCt1Received>::recv_ct2_chunk`
    (Block `350`) from explicit callee contracts. -/
theorem recv_ct2_chunk_placed_ok_ext_of_contracts_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hsub_pre : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PreEnv x evs)
    (hsub_post : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PostEnv x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExtOfPrePostEnv K F M A lim PreEnv PostEnv ext :=
  recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX
    (recv_ct2_chunk_placed_ok_of_contracts_ofPrePostEnv hsub_pre hsub_post hA hadd_ok hdec_ok
      hdecaps hhkdf hhmac)

/-- Single-envelope (`Env`) contract-backed (`recvCt2ChunkStackExt`) top-level relocatable
    `[LibsignalPlacement]` proof of `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`). -/
theorem recv_ct2_chunk_placed_ok_ext_of_contracts_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExtOfEnv K F M A lim Env ext :=
  recvCt2ChunkPlacedOkExtOfEnv_of_okX
    (recv_ct2_chunk_placed_ok_of_contracts_ofEnv hsub hA hadd_ok hdec_ok hdecaps hhkdf hhmac)

/-- Canonical contract-backed (`recvCt2ChunkStackExt`) top-level relocatable
    `[LibsignalPlacement]` proof of `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`). -/
theorem recv_ct2_chunk_placed_ok_ext_of_contracts [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhkdf : subroutine_ok ((blkPC_379).rebase (blkPl_379).base (Rust.withPanics ext))
      (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith F)))))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recvCt2ChunkPlacedOkExt_of_okX
    (recv_ct2_chunk_placed_ok_of_contracts hA hadd_ok hdec_ok hdecaps hhkdf hhmac)

/-- Two-envelope (`PreEnv` / `PostEnv`) contract-backed (`recvCt2ChunkStackExt`) top-level
    relocatable `[LibsignalPlacement]` contract for `<EkSentCt1Received>::recv_ct2_chunk`
    (Block `350`), discharging `hkdf_to_slice` via `[HkdfPlacedHooks F (Rust.withPanics ext)]`. -/
theorem recv_ct2_chunk_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hsub_pre : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PreEnv x evs)
    (hsub_post : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → PostEnv x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExtOfPrePostEnv K F M A lim PreEnv PostEnv ext :=
  recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX
    (recv_ct2_chunk_placed_ok_x_ofPrePostEnv hsub_pre hsub_post hA hadd_ok hdec_ok hdecaps hhmac)

/-- Single-envelope (`Env`) contract-backed (`recvCt2ChunkStackExt`) top-level relocatable
    `[LibsignalPlacement]` contract for `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`),
    discharging `hkdf_to_slice` via `[HkdfPlacedHooks F (Rust.withPanics ext)]`. -/
theorem recv_ct2_chunk_placed_ok_ext_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hsub : ∀ (x : RecvCt2ChunkGhost F) {evs : List AllocEvent},
      RecvCt2ChunkEnv x evs → Env x evs)
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExtOfEnv K F M A lim Env ext :=
  recvCt2ChunkPlacedOkExtOfEnv_of_okX
    (recv_ct2_chunk_placed_ok_x_ofEnv hsub hA hadd_ok hdec_ok hdecaps hhmac)

/-- Canonical contract-backed (`recvCt2ChunkStackExt`) top-level relocatable
    `[LibsignalPlacement]` budget contract for `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`),
    discharging `hkdf_to_slice` via `[HkdfPlacedHooks F (Rust.withPanics ext)]`. -/
theorem recv_ct2_chunk_placed_ok_ext [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim)) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recvCt2ChunkPlacedOkExt_of_okX
    (recv_ct2_chunk_placed_ok_x hA hadd_ok hdec_ok hdecaps hhmac)

/-- Contract-backed (`recvCt2ChunkStackExt`) top-level relocatable `[LibsignalPlacement]` budget
    contract for `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`) taking individual external
    hook and panic hypotheses directly. -/
theorem recv_ct2_chunk_placed_ok_ext_of_hooks [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [HkdfPlacedHooks F (Rust.withPanics ext)]
    (hadd_ok : subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
      (blkPl_419).base (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_ok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hallocZeroed :
      HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustCliAllocBudgetSpec M A lim true))
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym' (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym framelessMemcpyAcpSpec)
    (hRO : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpyRegionROSpec)
    (hdecaps : HookSat (Rust.withPanics ext) spqrMlkemDecapsSym
      (withVmPreserved (mlkemDecapsSpec K)))
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym'
      (libcruxHmacBudgetSpec F M A lim))
    (h_handle_error : Rust.withPanics ext spqrHandleErrorSym = some Rust.panicked)
    (h_assert_failed_u64 : Rust.withPanics ext spqrAssertFailedU64Sym = some Rust.panicked)
    (h_slice_index_fail : Rust.withPanics ext spqrSliceIndexFailSym = some Rust.panicked)
    (h_unwrap_failed : Rust.withPanics ext spqrUnwrapFailedSym = some Rust.panicked)
    (h_panic_bounds_check : Rust.withPanics ext spqrPanicBoundsCheckSym = some Rust.panicked)
    (h_panic_add_overflow : Rust.withPanics ext spqrPanicConstAddOverflowSym = some Rust.panicked) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recvCt2ChunkPlacedOkExt_of_okX
    (recv_ct2_chunk_placed_ok_x_of_hooks hadd_ok hdec_ok hshim halloc hallocZeroed hdealloc
      hrealloc hmemcpy hRO hdecaps hhmac h_handle_error h_assert_failed_u64 h_slice_index_fail
      h_unwrap_failed h_panic_bounds_check h_panic_add_overflow)

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.ProofPlacedBudget
