/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3bPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import Lean -- shake: keep
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Budget `Ok(Done)` Deallocations

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` proof of `x.epoch + 1` overflow check,
OOM-free 32-byte `secret` allocation, and 7-buffer deallocation chain (`+1308 .. +1520`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3cPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement blkLib_eq_350 blkPC_350 blkPl_350 lsProg_350 lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator Bytes MlKem PolyDecoder compare_prefix sckaKeyInfoPrefix spqrAuthApi spqrHkdfWith
  spqrPolyApi
)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded extHookStack)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.SpqrV1.Alloc (
  spqrPanicConstAddOverflowSym spqrRustAllocSym spqrRustNoAllocShimSym
)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost vecBufAt)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.Drop (chunkedEkSentCt1ReceivedSize)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  Ct2DeallocProp RecvCt2ChunkGhost add_one_ult_self_eq_beq_allOnes b0 b7
  bytes_rem_entails_vecU8HeapAt_32 ct2DeallocAt ct2DeallocAt_expose fold_4cells_memRegion_32
  fold_ptr_ss_raw low7At memRegion_32_cells memRegion_8_eq_cell memRegion_split_4cells
  polyDecoderNew96 recvCt2RoPlacedAt recv_ct2_chunk_eq_done recv_ct2_chunk_isPanic_of_epoch_allOnes
  rejoin_cells_5_sp_2464 rejoin_memRegion_24_sp_1280 rejoin_memRegion_32_sp_152
  rejoin_memRegion_48_sp_1328 reshape_x20_1960_to_1929 savedRegsAt shiftWord8 shift_5words_1320
  spqrRustDeallocSym' unusedFrameAt vecBufAt_entails_memRegion_live vecBufAt_zero_entails_emp
  vecU8At_expose_cells_heap_sp_1328 vecU8HeapAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomExternSpecWithStack
  rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (session2ShimAcpSpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonPlacedBudget (
  OptSecret32AllocEnv RecvCt2ChunkEnv RecvCt2PlacedAlloc allowPanic_isPanic_budget_recvCt2
  freeOnlyEvs_rustDealloc1 optSecret32AllocEnv_alloc32 recvCt2PlacedPostQ recvCt2PlacedPostQOfEnv
  recvCt2PlacedPostQOfPrePostEnv recvCt2PlacedPostQp sepWPp_of_sepWP_lscro
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3bPlacedBudget (
  recv_ct2_chunk_ok_done_write_out_placed_wpp
)

private theorem rustLayoutOk_one {n : Nat} (hpos : 0 < n) (hmax : n < 2 ^ 63) :
    RustLayoutOk n 1 :=
  ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩

private theorem sepWPp_rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

private theorem sepWPp_rw_pre' {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (h : SepWPp prog ret s P' Q Qp) (hP : P = P') :
    SepWPp prog ret s P Q Qp :=
  hP ▸ h

private theorem sepWPp_pure_left_focus {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post post_err : State → SepProp → Prop} (φ : Prop)
    (hf : P = ⌜φ⌝ ∗ P')
    (h : φ → SepWPp prog pc s P' post post_err) :
    SepWPp prog pc s P post post_err := by
  intro R hm hL
  rw [hf, sepConj_assoc, satisfies_pure_sepConj] at hm
  exact (h hm.1) R hm.2 hL

private theorem exists_unpack64_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64, ∀ a : BitVec 64,
      (a ↦ₛ bs) =
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  rcases bs with _ | ⟨b00, _ | ⟨b01, _ | ⟨b02, _ | ⟨b03, _ | ⟨b04, _ | ⟨b05, _ | ⟨b06, _ | ⟨b07,
    _ | ⟨b08, _ | ⟨b09, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at h; done)
  refine ⟨pack64 b00 b01 b02 b03 b04 b05 b06 b07,
    pack64 b08 b09 b10 b11 b12 b13 b14 b15,
    pack64 b16 b17 b18 b19 b20 b21 b22 b23,
    pack64 b24 b25 b26 b27 b28 b29 b30 b31, fun a => ?_⟩
  change (a ↦ₛ ([b00, b01, b02, b03, b04, b05, b06, b07] ++
      ([b08, b09, b10, b11, b12, b13, b14, b15] ++
        ([b16, b17, b18, b19, b20, b21, b22, b23] ++
          [b24, b25, b26, b27, b28, b29, b30, b31])))) = _
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    pointsToBytes8_eq_pointsTo64, pointsToBytes8_eq_pointsTo64,
    pointsToBytes8_eq_pointsTo64, pointsToBytes8_eq_pointsTo64]
  change (a ↦₆₄ _) ∗ (((a + 8#64) ↦₆₄ _) ∗
    (((a + 8#64 + 8#64) ↦₆₄ _) ∗ ((a + 8#64 + 8#64 + 8#64) ↦₆₄ _))) = _
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_kernel
  have h24 : a + 16#64 + 8#64 = a + 24#64 := by bv_kernel
  rw [h16, h24]
  sep_ac_rfl

local macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

local macro "wp_steps_sync_pool_350 " ext:term:max mid:term:max : tactic =>
  `(tactic| (
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_350).rebase (blkPl_350).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics $ext)))
      blkLib_eq_350 (mid := $mid)
    intro _m_strip
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_goal)) (hnext := ?_)
    simp only [State.setMem_setMem]))

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  spqrHkdfWith
  CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false

local elab "erase_hkdf_sp_norm" : command =>
  Lean.Elab.Command.liftCoreM do
    for nm in [
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
      ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
    ] do
      try Lean.Attribute.erase nm `arm64_norm catch _ => pure ()

erase_hkdf_sp_norm

/-! ## `Ok(Done)` Epoch Check, `secret` Alloc, Header Staging & Deallocations (`+1308 .. +1520`) -/

set_option maxHeartbeats 1600000 in
/-- `+1308 .. +1520` + `+2044`: verifies the budget-threaded `Ok(Done)` branch from the
`x.epoch + 1` overflow check through the 32-byte `secret` allocation (`rustAllocEvents 32 1`
under `OptSecret32AllocEnv`), `ss` copy, `auth'` header staging, and 6/7-buffer `__rust_dealloc`
cleanup chain, handing off at `+1520` to `recv_ct2_chunk_ok_done_write_out_placed_wpp`. -/
theorem recv_ct2_chunk_ok_done_dealloc_placed_wpp [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F)
    (st0 σ : M.σ)
    (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1'
      ptr_ss_raw cap_info ptr_info ptr_ss : BitVec 64)
    (ss_raw ss : Bytes) (auth' : Authenticator) (g_auth' : AuthenticatorGhost)
    (s0 st : State) (R : SepProp)
    (hfit_sec : FitsEnv M lim σ OptSecret32AllocEnv)
    (hpost_env : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
      ∃ evs_all : List AllocEvent, PostEnv x evs_all ∧
        M.stepEvents evs_free (M.stepEvents (rustAllocEvents 32 1) σ) =
          M.stepEvents evs_all st0)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge128 : 128 ≤ ct2Full.length) (hmax_ct2 : ct2Full.length < 2 ^ 63)
    (hct1_len : x.self.uc.ct1.length = 960) (hdk_len : x.self.uc.dk.length = 2400)
    (hm_le32 : (ct2Full.drop 128).length ≤ 32)
    (hcmp :
      (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
       let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
       let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
       let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
       let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
       compare_prefix (ct2Full.drop 128) tag0 != 0#8) = false)
    (hss_eq :
      let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
       ss = spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32)
    (hauth'_eq : auth' = x.self.uc.auth.update F x.self.uc.epoch ss)
    (hss_len : ss.length = 32) (hss_raw_len : ss_raw.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hrk_len : auth'.rootKey.length = 32) (hmk_len : auth'.macKey.length = 32)
    (hmk_cap_ne : g_auth'.macKey.cap ≠ 0#64)
    (hmk_le : 32 ≤ g_auth'.macKey.cap.toNat) (hmk_max : g_auth'.macKey.cap.toNat < 2 ^ 63)
    (hmk_ptr_ne : g_auth'.macKey.ptr ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 1308#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 2000#64) (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx24 : st.readReg64 .x24 = ptr_ss_raw) (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx27 : st.readReg64 .x27 = ptr_ss) (hx29 : st.readReg64 .x29 = s0.sp - 96#64) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      ((ptr_ss ↦ₛ ss) ∗ A.live ptr_ss 32 1 ∗
        ct2DeallocAt A.repAlloc cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗ ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗ memRegion (s0.sp - 128#64) 8 ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗ A.live ptr_ss_raw 32 1 ∗
        ((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗ ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗ ct2DeallocAt A.repAlloc cap_ct1' ptr_ct1' ∗
        ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
        vecU8At A.repAlloc (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗ ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗ (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗ A.live ptr_ct2_128 128 1 ∗
        ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗ ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗ ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗ ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗ ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion (s0.sp - 2000#64) 144 ∗ memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1248#64) 960 ∗ memRegion (s0.sp - 288#64) 128 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗ memRegion (s0.sp - 1856#64) 504 ∗
        polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2RoPlacedAt ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim σ st ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2PlacedPostQOfPrePostEnv K F M A lim PreEnv PostEnv x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) := by
  have hge_not_lt : ¬ ct2Full.length < 128 := by omega
  by_cases hep_max : (x.self.uc.epoch == BitVec.allOnes 64) = true
  · have hult_t : (x.self.uc.epoch + 1#64).ult x.self.uc.epoch = true :=
      (add_one_ult_self_eq_beq_allOnes x.self.uc.epoch).trans hep_max
    have hult_t' : (x.epoch + 1#64).ult x.epoch = true := by rw [hepoch]; exact hult_t
    have hpan_model := recv_ct2_chunk_isPanic_of_epoch_allOnes (K := K)
      x.self x.epoch x.chunk receivingCt2 ct2Full hepoch hadd hdec hge_not_lt
      hct1_len hdk_len hm_le32 hcmp hep_max
    have h_pan_add := hA.panic_add_overflow
    have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
    simp only [wp_norm, arm64_norm] at hsp_norm hx22
    clear hA
    simp only [lsProg_350] at h_pan_add ⊢
    apply SepWPp.of_sepWP (mid := lsρ spqrPanicConstAddOverflowSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) fun hm => ?_
    exact allowPanic_isPanic_budget_recvCt2 hpan_model
      (by simp only [Rust.panicked, wp_norm, arm64_norm, *]) hm
  · have hep_max_f : (x.self.uc.epoch == BitVec.allOnes 64) = false :=
      Bool.eq_false_iff.mpr hep_max
    have hult_f : (x.self.uc.epoch + 1#64).ult x.self.uc.epoch = false :=
      (add_one_ult_self_eq_beq_allOnes x.self.uc.epoch).trans hep_max_f
    have hult_f' : (x.epoch + 1#64).ult x.epoch = false := by rw [hepoch]; exact hult_f
    have hres_raw := recv_ct2_chunk_eq_done (K := K)
      x.self x.epoch x.chunk receivingCt2 ct2Full hepoch hadd hdec hge_not_lt
      hct1_len hdk_len hm_le32 hcmp hep_max_f
    dsimp only at hres_raw hss_eq
    have hres : x.self.recv_ct2_chunk K x.epoch x.chunk =
        .ok (.done ({ uc := { epoch := x.epoch + 1#64, auth := auth' },
                       receiving_hdr := polyDecoderNew96 },
                     { epoch := x.epoch, secret := ss })) := by
      rw [hres_raw, ← hss_eq, ← hauth'_eq, ← hepoch]
    have h_shim := hA.shim_acp_lscro
    have h_alloc := hA.allocNoOom_extern_lscro
    have h_dealloc := hA.dealloc_lscro
    dsimp only [session2ShimAcpSpecWithStack] at h_shim
    dsimp only [LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomExternSpecWithStack,
      rustCliAllocNoOomExternSpecWithStack] at h_alloc
    dsimp only [LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      rustCliDeallocBudgetExternSpecWithStack] at h_dealloc
    have h_write :=
      @recv_ct2_chunk_ok_done_write_out_placed_wpp _ K F M A lim PreEnv PostEnv ext hA x st0
    have hfit_32 : FitsEvents M lim σ (rustAllocEvents 32 1) :=
      hfit_sec (rustAllocEvents 32 1) optSecret32AllocEnv_alloc32
    have hss_raw_mr : (ptr_ss_raw ↦ₛ ss_raw) ⊢ memRegion ptr_ss_raw 32 := by
      rw [← hss_raw_len]; exact pointsToBytes_entails_memRegion ptr_ss_raw ss_raw
    have hct2_128_mr : (ptr_ct2_128 ↦ₛ ct2Full.take 128) ⊢ memRegion ptr_ct2_128 128 := by
      have h := pointsToBytes_entails_memRegion ptr_ct2_128 (ct2Full.take 128)
      rwa [htake128_len] at h
    have hmk_heap :
        (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
          memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
          A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ⊢
        vecU8HeapAt A.repAlloc g_auth'.macKey.cap g_auth'.macKey.ptr auth'.macKey :=
      bytes_rem_entails_vecU8HeapAt_32 A.repAlloc g_auth'.macKey.cap g_auth'.macKey.ptr
        auth'.macKey hmk_len hmk_cap_ne hmk_le hmk_max hmk_ptr_ne
    refine SepWPp.fold hss_raw_mr (by sep_focus) ?_
    refine SepWPp.fold hct2_128_mr (by sep_focus) ?_
    refine SepWPp.fold hmk_heap (by sep_focus) ?_
    refine SepWPp.fold
      (vecU8At_expose_cells_heap_sp_1328 A.repAlloc s0.sp g_auth'.rootKey.cap
        g_auth'.rootKey.ptr auth'.rootKey hrk_len)
      (by sep_focus) ?_
    refine sepWPp_pure_left_focus (g_auth'.rootKey.cap.toNat < 2 ^ 63) (by sep_focus)
      fun hcap_rk_lt => ?_
    refine SepWPp.fold (ct2DeallocAt_expose A.repAlloc cap_info ptr_info) (by sep_focus) ?_
    refine sepWPp_pure_left_focus (Ct2DeallocProp cap_info ptr_info) (by sep_focus)
      fun ⟨hinfo_beq, hinfo_pos, hinfo_max, hinfo_ptr⟩ => ?_
    refine SepWPp.fold (ct2DeallocAt_expose A.repAlloc cap_ct1' ptr_ct1') (by sep_focus) ?_
    refine sepWPp_pure_left_focus (Ct2DeallocProp cap_ct1' ptr_ct1') (by sep_focus)
      fun ⟨hct1_beq, hct1_pos, hct1_max, hct1_ptr⟩ => ?_
    refine SepWPp.fold (ct2DeallocAt_expose A.repAlloc cap_dk ptr_dk) (by sep_focus) ?_
    refine sepWPp_pure_left_focus (Ct2DeallocProp cap_dk ptr_dk) (by sep_focus)
      fun ⟨hdk_beq, hdk_pos, hdk_max, hdk_ptr⟩ => ?_
    have hrlay_32 : RustLayoutOk 32 1 := rustLayoutOk_one (by decide) (by decide)
    have hrlay_128 : RustLayoutOk 128 1 := rustLayoutOk_one (by decide) (by decide)
    have hrlay_info : RustLayoutOk cap_info.toNat 1 := rustLayoutOk_one hinfo_pos hinfo_max
    have hrlay_ct1 : RustLayoutOk cap_ct1'.toNat 1 := rustLayoutOk_one hct1_pos hct1_max
    have hrlay_dk : RustLayoutOk cap_dk.toNat 1 := rustLayoutOk_one hdk_pos hdk_max
    refine sepWPp_rw_pre (by
      rw [ProofLib.memRegion_split' (b := s0.sp - 2000#64) (n := 32) (k := 112)
        (b' := s0.sp - 1968#64) rfl (by bv_omega) (by decide)]) ?_
    refine SepWPp.fold (memRegion_split_4cells
      (s0.sp - 1968#64) (s0.sp - 1960#64) (s0.sp - 1952#64) (s0.sp - 1944#64)
      (s0.sp - 1936#64) 112 80 rfl
      (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by decide)) (by sep_focus) ?_
    sep_elim_exists; rename_i z0 z1 z2 z3
    refine sepWPp_rw_pre (by
      rw [ProofLib.memRegion_split' (b := s0.sp - 1936#64) (n := 8) (k := 72)
        (b' := s0.sp - 1928#64) rfl (by bv_omega) (by decide)]) ?_
    refine SepWPp.fold (memRegion_8_eq_cell (s0.sp - 1936#64)) (by sep_focus) ?_
    sep_elim_exists; rename_i z4
    have hsp_norm : st.readReg64 .sp = s0.sp - 2496#64 := hsp
    simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx29
    clear hA
    simp only [lsProg_350] at h_shim h_alloc h_dealloc h_write ⊢
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustNoAllocShimSym) hinv ?_
    wp_steps_sync_pool_350 ext (lsρ spqrRustNoAllocShimSym)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvCt2_budget h_shim () hinv1
    have hsp_1 : sf.readReg64 .sp = s0.sp - 2496#64 := by
      simp only [State.sp, wp_norm, arm64_norm, *]
    simp only [wp_norm, arm64_norm] at hsp_1
    conv => arg 4; simp only [State.sp, hsp_sf, hsp, hsp_norm, hsp_1, wp_norm, arm64_norm]
    refine sepWPp_pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hacp1, hvm1⟩
    have htr1 : sf.trace = s0.trace := by
      have h := hacp1.2.1
      simp only [wp_norm, arm64_norm, *] at h
      exact h
    rw [← A.pool_of_vmPreserved hvm1]
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustAllocSym) hF_sf ?_
    wp_steps_sync_pool_350 ext (lsρ spqrRustAllocSym)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvCt2_budget h_alloc (32, 1, σ) hinv2
    have hsp_2 : sf_1.readReg64 .sp = s0.sp - 2496#64 := by
      simp only [State.sp, wp_norm, arm64_norm, *]
    simp only [wp_norm, arm64_norm] at hsp_2
    conv =>
      arg 4
      simp only [Bool.false_eq_true, ↓reduceIte, State.sp, hsp_sf_1, hsp_1,
        wp_norm, arm64_norm, sepConj_assoc]
    refine sepWPp_pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr2, hoom, _⟩
    have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
    let σ₀ : M.σ := M.stepEvents (rustAllocEvents 32 1) σ
    let σ₁ : M.σ := M.stepEvents (rustDeallocEvents 32 1) σ₀
    let σ₂ : M.σ := M.stepEvents (rustDeallocEvents cap_info.toNat 1) σ₁
    let σ₃ : M.σ := M.stepEvents (rustDeallocEvents 32 1) σ₂
    let σ₄ : M.σ := M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1) σ₃
    let σ₅ : M.σ := M.stepEvents (rustDeallocEvents cap_dk.toNat 1) σ₄
    obtain ⟨s0_w, s1_w, s2_w, s3_w, ha_ss⟩ := exists_unpack64_32 hss_len
    refine sepWPp_rw_pre (by
      rw [memRegion_32_cells (sf_1.readReg64 Reg.x0), ha_ss ptr_ss]) ?_
    sep_elim_exists
    refine SepWPp.fold (Entails.of_eq (shift_5words_1320 s0.sp
      g_auth'.rootKey.ptr 32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64)) (by sep_focus) ?_
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_1 ?_
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_350).rebase (blkPl_350).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException (Rust.withPanics ext)))
      blkLib_eq_350 (mid := lsρ spqrRustDeallocSym')
    intro _m_strip
    wp_steps
    refine SepWP.fold
      (fold_ptr_ss_raw (sf_1.readReg64 Reg.x0) ss s0_w s1_w s2_w s3_w ha_ss)
      (by sep_focus) ?_
    refine SepWP.fold
      (fold_4cells_memRegion_32 ptr_ss s0_w s1_w s2_w s3_w)
      (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (shift_5words_1320 s0.sp
      g_auth'.rootKey.ptr 32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64).symm)
      (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (Entails.of_eq (reshape_x20_1960_to_1929 s0.sp
      32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64 z4)) (by sep_focus) ?_
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_goal) fun _m_real _hnsp => ?_
    refine ProofLib.SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_goal)) (hnext := ?_)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ss, 32, 1, σ₀) hinv3
    have hsp_3 : sf_2.readReg64 .sp = s0.sp - 2496#64 := by
      simp only [State.sp, wp_norm, arm64_norm, *]
    simp only [wp_norm, arm64_norm] at hsp_3
    conv => arg 4; simp only [State.sp, hsp_sf_2, hsp_2, wp_norm, arm64_norm]
    refine sepWPp_pure_left_focus (sf_2.trace = _) (by sep_focus) fun htr3 => ?_
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_2 ?_
    wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv4
    wpp_call_lscro_recvCt2_budget h_dealloc (ptr_info, cap_info.toNat, 1, σ₁) hinv4
    have hsp_4 : sf_3.readReg64 .sp = s0.sp - 2496#64 := by
      simp only [State.sp, wp_norm, arm64_norm, *]
    simp only [wp_norm, arm64_norm] at hsp_4
    conv => arg 4; simp only [State.sp, hsp_sf_3, hsp_3, wp_norm, arm64_norm]
    refine sepWPp_pure_left_focus (sf_3.trace = _) (by sep_focus) fun htr4 => ?_
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_3 ?_
    wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv5
    wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ss_raw, 32, 1, σ₂) hinv5
    have hsp_5 : sf_4.readReg64 .sp = s0.sp - 2496#64 := by
      simp only [State.sp, wp_norm, arm64_norm, *]
    simp only [wp_norm, arm64_norm] at hsp_5
    conv => arg 4; simp only [State.sp, hsp_sf_4, hsp_4, wp_norm, arm64_norm]
    refine sepWPp_pure_left_focus (sf_4.trace = _) (by sep_focus) fun htr5 => ?_
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_4 ?_
    wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv6
    wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ct1', cap_ct1'.toNat, 1, σ₃) hinv6
    have hsp_6 : sf_5.readReg64 .sp = s0.sp - 2496#64 := by
      simp only [State.sp, wp_norm, arm64_norm, *]
    simp only [wp_norm, arm64_norm] at hsp_6
    conv => arg 4; simp only [State.sp, hsp_sf_5, hsp_5, wp_norm, arm64_norm]
    refine sepWPp_pure_left_focus (sf_5.trace = _) (by sep_focus) fun htr6 => ?_
    refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_5 ?_
    wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv7
    wpp_call_lscro_recvCt2_budget h_dealloc (ptr_dk, cap_dk.toNat, 1, σ₄) hinv7
    have hsp_7 : sf_6.readReg64 .sp = s0.sp - 2496#64 := by
      simp only [State.sp, wp_norm, arm64_norm, *]
    simp only [wp_norm, arm64_norm] at hsp_7
    conv => arg 4; simp only [State.sp, hsp_sf_6, hsp_6, wp_norm, arm64_norm]
    refine sepWPp_pure_left_focus (sf_6.trace = _) (by sep_focus) fun htr7 => ?_
    by_cases heq128 : ct2Full.length = 128
    · have hsub0 : ct2Full.length - 128 = 0 := by omega
      have hx23_0 : BitVec.ofNat 64 (ct2Full.length - 128) = 0#64 := by rw [hsub0]
      have hdrop_nil : ct2Full.drop 128 = [] := List.drop_eq_nil_of_le (by omega)
      have hmac_emp :
          vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ⊢
            emp := by
        rw [hx23_0]
        exact vecBufAt_zero_entails_emp A.repAlloc ptr_mac (ct2Full.drop 128) hdrop_nil
      let evs_6 : List AllocEvent :=
        rustDeallocEvents 32 1 ++
          rustDeallocEvents cap_info.toNat 1 ++
          rustDeallocEvents 32 1 ++
          rustDeallocEvents cap_ct1'.toNat 1 ++
          rustDeallocEvents cap_dk.toNat 1 ++
          rustDeallocEvents 128 1
      have hfree_6 : FreeOnlyEvs evs_6 :=
        (((((freeOnlyEvs_rustDealloc1 32).append
          (freeOnlyEvs_rustDealloc1 cap_info.toNat)).append
          (freeOnlyEvs_rustDealloc1 32)).append
          (freeOnlyEvs_rustDealloc1 cap_ct1'.toNat)).append
          (freeOnlyEvs_rustDealloc1 cap_dk.toNat)).append
          (freeOnlyEvs_rustDealloc1 128)
      have hstep_6 :
          M.stepEvents (rustDeallocEvents 128 1)
            (M.stepEvents (rustDeallocEvents cap_dk.toNat 1)
              (M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1)
                (M.stepEvents (rustDeallocEvents 32 1)
                  (M.stepEvents (rustDeallocEvents cap_info.toNat 1)
                    (M.stepEvents (rustDeallocEvents 32 1) σ₀))))) =
            M.stepEvents evs_6 σ₀ := by
        dsimp only [evs_6]
        simp only [M.stepEvents_append]
      have hpost_env_6 :
          ∀ evs_ep : List AllocEvent, FreeOnlyEvs evs_ep →
            ∃ evs_all : List AllocEvent, PostEnv x evs_all ∧
              M.stepEvents evs_ep (M.stepEvents evs_6 σ₀) = M.stepEvents evs_all st0 := by
        intro evs_ep hfree_ep
        obtain ⟨evs_all, hpost_all, hstep_all⟩ :=
          hpost_env (evs_6 ++ evs_ep) (hfree_6.append hfree_ep)
        exact ⟨evs_all, hpost_all, (M.stepEvents_append evs_6 evs_ep σ₀).symm.trans hstep_all⟩
      refine SepWPp.fold hmac_emp (by sep_focus) ?_
      refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_6 ?_
      wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv8
      wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ct2_128, 128, 1, σ₅) hinv8
      have hsp_8 : sf_7.readReg64 .sp = s0.sp - 2496#64 := by
        simp only [State.sp, wp_norm, arm64_norm, *]
      simp only [wp_norm, arm64_norm] at hsp_8
      conv => arg 4; simp only [State.sp, hsp_sf_7, hsp_7, wp_norm, arm64_norm]
      refine sepWPp_pure_left_focus (sf_7.trace = _) (by sep_focus) fun htr8 => ?_
      dsimp only [σ₅, σ₄, σ₃, σ₂, σ₁]
      rw [hstep_6]
      refine SepWPp.fold (rejoin_memRegion_32_sp_152 s0.sp cap_info ptr_info 41#64) (by sep_focus) ?_
      refine SepWPp.fold (rejoin_memRegion_24_sp_1280 s0.sp cap_ct1' ptr_ct1' 960#64) (by sep_focus) ?_
      refine SepWPp.fold
        (rejoin_memRegion_48_sp_1328 s0.sp g_auth'.rootKey.cap g_auth'.rootKey.ptr
          32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64)
        (by sep_focus) ?_
      refine SepWPp.fold
        (rejoin_cells_5_sp_2464 s0.sp cap_ct2 cap_dk ptr_mac ptr_ct1' x.epoch)
        (by sep_focus) ?_
      refine sepWPp_rw_pre'
        (h_write (M.stepEvents evs_6 σ₀) receivingCt2 cap_ct2 ptr_ct2
          (sf_1.readReg64 Reg.x0) ptr_dk ptr_info (b7 z4) auth' g_auth' ss s0 sf_7 R
          hpost_env_6 hrk_len hmk_len hss_len hoom hcap_rk_lt hres
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *]) hsp_s0
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hF_sf_7
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by rw [hepoch]; simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
        (by dsimp only [recvCt2RoPlacedAt, Reg.x0]; rw [← hepoch]; sep_ac_rfl)
    · have hmac_mr_live :
          vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac
              (ct2Full.drop 128) ⊢
            memRegion ptr_mac (BitVec.ofNat 64 (ct2Full.length - 128)).toNat ∗
              A.live ptr_mac (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1 := by
        have hlen : (ct2Full.drop 128).length = ct2Full.length - 128 := List.length_drop
        rw [← hlen]
        exact vecBufAt_entails_memRegion_live A.repAlloc ptr_mac (ct2Full.drop 128)
          (by omega) (by omega)
      have hmac_toNat : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = ct2Full.length - 128 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hmac_pos : 0 < (BitVec.ofNat 64 (ct2Full.length - 128)).toNat := by omega
      have hmac_max : (BitVec.ofNat 64 (ct2Full.length - 128)).toNat < 2 ^ 63 := by omega
      have hrlay_mac : RustLayoutOk (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1 :=
        rustLayoutOk_one hmac_pos hmac_max
      have hrlay_mac' : RustLayoutOk (ct2Full.length - 128) 1 :=
        rustLayoutOk_one (by omega) (by omega)
      have hpow2_1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
      have hmac_beq : (BitVec.ofNat 64 (ct2Full.length - 128) == 0#64) = false := by
        apply beq_false_of_ne
        intro h0
        have h1 := congrArg BitVec.toNat h0
        change (BitVec.ofNat 64 (ct2Full.length - 128)).toNat = 0 at h1
        omega
      let σ₆ : M.σ :=
        M.stepEvents (rustDeallocEvents (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1) σ₅
      let evs_7 : List AllocEvent :=
        rustDeallocEvents 32 1 ++
          rustDeallocEvents cap_info.toNat 1 ++
          rustDeallocEvents 32 1 ++
          rustDeallocEvents cap_ct1'.toNat 1 ++
          rustDeallocEvents cap_dk.toNat 1 ++
          rustDeallocEvents (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1 ++
          rustDeallocEvents 128 1
      have hfree_7 : FreeOnlyEvs evs_7 :=
        ((((((freeOnlyEvs_rustDealloc1 32).append
          (freeOnlyEvs_rustDealloc1 cap_info.toNat)).append
          (freeOnlyEvs_rustDealloc1 32)).append
          (freeOnlyEvs_rustDealloc1 cap_ct1'.toNat)).append
          (freeOnlyEvs_rustDealloc1 cap_dk.toNat)).append
          (freeOnlyEvs_rustDealloc1 (BitVec.ofNat 64 (ct2Full.length - 128)).toNat)).append
          (freeOnlyEvs_rustDealloc1 128)
      have hstep_7 :
          M.stepEvents (rustDeallocEvents 128 1)
            (M.stepEvents (rustDeallocEvents (BitVec.ofNat 64 (ct2Full.length - 128)).toNat 1)
              (M.stepEvents (rustDeallocEvents cap_dk.toNat 1)
                (M.stepEvents (rustDeallocEvents cap_ct1'.toNat 1)
                  (M.stepEvents (rustDeallocEvents 32 1)
                    (M.stepEvents (rustDeallocEvents cap_info.toNat 1)
                      (M.stepEvents (rustDeallocEvents 32 1) σ₀)))))) =
            M.stepEvents evs_7 σ₀ := by
        dsimp only [evs_7]
        simp only [M.stepEvents_append]
      have hpost_env_7 :
          ∀ evs_ep : List AllocEvent, FreeOnlyEvs evs_ep →
            ∃ evs_all : List AllocEvent, PostEnv x evs_all ∧
              M.stepEvents evs_ep (M.stepEvents evs_7 σ₀) = M.stepEvents evs_all st0 := by
        intro evs_ep hfree_ep
        obtain ⟨evs_all, hpost_all, hstep_all⟩ :=
          hpost_env (evs_7 ++ evs_ep) (hfree_7.append hfree_ep)
        exact ⟨evs_all, hpost_all, (M.stepEvents_append evs_7 evs_ep σ₀).symm.trans hstep_all⟩
      refine SepWPp.fold hmac_mr_live (by sep_focus) ?_
      refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_6 ?_
      wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv8
      wpp_call_lscro_recvCt2_budget h_dealloc
        (ptr_mac, (BitVec.ofNat 64 (ct2Full.length - 128)).toNat, 1, σ₅) hinv8
      have hsp_8 : sf_7.readReg64 .sp = s0.sp - 2496#64 := by
        simp only [State.sp, wp_norm, arm64_norm, *]
      simp only [wp_norm, arm64_norm] at hsp_8
      conv => arg 4; simp only [State.sp, hsp_sf_7, hsp_7, wp_norm, arm64_norm]
      refine sepWPp_pure_left_focus (sf_7.trace = _) (by sep_focus) fun htr8 => ?_
      refine sepWPp_of_sepWP_lscro (mid := lsρ spqrRustDeallocSym') hF_sf_7 ?_
      wp_steps_sync_pool_350 ext (lsρ spqrRustDeallocSym')
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv9
      wpp_call_lscro_recvCt2_budget h_dealloc (ptr_ct2_128, 128, 1, σ₆) hinv9
      have hsp_9 : sf_8.readReg64 .sp = s0.sp - 2496#64 := by
        simp only [State.sp, wp_norm, arm64_norm, *]
      simp only [wp_norm, arm64_norm] at hsp_9
      conv => arg 4; simp only [State.sp, hsp_sf_8, hsp_8, wp_norm, arm64_norm]
      refine sepWPp_pure_left_focus (sf_8.trace = _) (by sep_focus) fun htr9 => ?_
      dsimp only [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁]
      rw [hstep_7]
      refine SepWPp.fold (rejoin_memRegion_32_sp_152 s0.sp cap_info ptr_info 41#64) (by sep_focus) ?_
      refine SepWPp.fold (rejoin_memRegion_24_sp_1280 s0.sp cap_ct1' ptr_ct1' 960#64) (by sep_focus) ?_
      refine SepWPp.fold
        (rejoin_memRegion_48_sp_1328 s0.sp g_auth'.rootKey.cap g_auth'.rootKey.ptr
          32#64 g_auth'.macKey.cap g_auth'.macKey.ptr 32#64)
        (by sep_focus) ?_
      refine SepWPp.fold
        (rejoin_cells_5_sp_2464 s0.sp cap_ct2 cap_dk ptr_mac ptr_ct1' x.epoch)
        (by sep_focus) ?_
      refine sepWPp_rw_pre'
        (h_write (M.stepEvents evs_7 σ₀) receivingCt2 cap_ct2 ptr_ct2
          (sf_1.readReg64 Reg.x0) ptr_dk ptr_info (b7 z4) auth' g_auth' ss s0 sf_8 R
          hpost_env_7 hrk_len hmk_len hss_len hoom hcap_rk_lt hres
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *]) hsp_s0
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hF_sf_8
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by rw [hepoch]; simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
        (by dsimp only [recvCt2RoPlacedAt, Reg.x0]; rw [← hepoch]; sep_ac_rfl)

/-! ## Single-Envelope (`_ofEnv`) and Canonical (`_canon`) Specializations -/

/-- Single-envelope (`Env = PreEnv = PostEnv`) specialization of
`recv_ct2_chunk_ok_done_dealloc_placed_wpp`. -/
theorem recv_ct2_chunk_ok_done_dealloc_placed_wpp_ofEnv [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F)
    (st0 σ : M.σ)
    (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1'
      ptr_ss_raw cap_info ptr_info ptr_ss : BitVec 64)
    (ss_raw ss : Bytes) (auth' : Authenticator) (g_auth' : AuthenticatorGhost)
    (s0 st : State) (R : SepProp)
    (hfit_sec : FitsEnv M lim σ OptSecret32AllocEnv)
    (hpost_env : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
      ∃ evs_all : List AllocEvent, Env x evs_all ∧
        M.stepEvents evs_free (M.stepEvents (rustAllocEvents 32 1) σ) =
          M.stepEvents evs_all st0)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge128 : 128 ≤ ct2Full.length) (hmax_ct2 : ct2Full.length < 2 ^ 63)
    (hct1_len : x.self.uc.ct1.length = 960) (hdk_len : x.self.uc.dk.length = 2400)
    (hm_le32 : (ct2Full.drop 128).length ≤ 32)
    (hcmp :
      (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
       let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
       let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
       let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
       let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
       compare_prefix (ct2Full.drop 128) tag0 != 0#8) = false)
    (hss_eq :
      let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
       ss = spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32)
    (hauth'_eq : auth' = x.self.uc.auth.update F x.self.uc.epoch ss)
    (hss_len : ss.length = 32) (hss_raw_len : ss_raw.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hrk_len : auth'.rootKey.length = 32) (hmk_len : auth'.macKey.length = 32)
    (hmk_cap_ne : g_auth'.macKey.cap ≠ 0#64)
    (hmk_le : 32 ≤ g_auth'.macKey.cap.toNat) (hmk_max : g_auth'.macKey.cap.toNat < 2 ^ 63)
    (hmk_ptr_ne : g_auth'.macKey.ptr ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 1308#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 2000#64) (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx24 : st.readReg64 .x24 = ptr_ss_raw) (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx27 : st.readReg64 .x27 = ptr_ss) (hx29 : st.readReg64 .x29 = s0.sp - 96#64) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      ((ptr_ss ↦ₛ ss) ∗ A.live ptr_ss 32 1 ∗
        ct2DeallocAt A.repAlloc cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗ ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗ memRegion (s0.sp - 128#64) 8 ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗ A.live ptr_ss_raw 32 1 ∗
        ((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗ ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗ ct2DeallocAt A.repAlloc cap_ct1' ptr_ct1' ∗
        ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
        vecU8At A.repAlloc (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗ ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗ (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗ A.live ptr_ct2_128 128 1 ∗
        ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗ ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗ ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗ ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗ ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion (s0.sp - 2000#64) 144 ∗ memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1248#64) 960 ∗ memRegion (s0.sp - 288#64) 128 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗ memRegion (s0.sp - 1856#64) 504 ∗
        polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2RoPlacedAt ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim σ st ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2PlacedPostQOfEnv K F M A lim Env x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_ok_done_dealloc_placed_wpp hA x st0 σ receivingCt2 ct2Full cap_ct2 ptr_ct2
    ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1' ptr_ss_raw cap_info ptr_info ptr_ss ss_raw
    ss auth' g_auth' s0 st R hfit_sec hpost_env hepoch hadd hdec hge128 hmax_ct2 hct1_len hdk_len
    hm_le32 hcmp hss_eq hauth'_eq hss_len hss_raw_len htake128_len hrk_len hmk_len hmk_cap_ne
    hmk_le hmk_max hmk_ptr_ne hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22 hx23 hx24
    hx25 hx27 hx29

/-- Canonical (`RecvCt2ChunkEnv`) specialization of
`recv_ct2_chunk_ok_done_dealloc_placed_wpp`. -/
theorem recv_ct2_chunk_ok_done_dealloc_placed_wpp_canon [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : RecvCt2PlacedAlloc M A lim ext)
    (x : RecvCt2ChunkGhost F)
    (st0 σ : M.σ)
    (receivingCt2 : PolyDecoder) (ct2Full : Bytes)
    (cap_ct2 ptr_ct2 ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1'
      ptr_ss_raw cap_info ptr_info ptr_ss : BitVec 64)
    (ss_raw ss : Bytes) (auth' : Authenticator) (g_auth' : AuthenticatorGhost)
    (s0 st : State) (R : SepProp)
    (hfit_sec : FitsEnv M lim σ OptSecret32AllocEnv)
    (hpost_env : ∀ evs_free : List AllocEvent, FreeOnlyEvs evs_free →
      ∃ evs_all : List AllocEvent, RecvCt2ChunkEnv x evs_all ∧
        M.stepEvents evs_free (M.stepEvents (rustAllocEvents 32 1) σ) =
          M.stepEvents evs_all st0)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_ct2 x.chunk = .ok receivingCt2)
    (hdec : receivingCt2.decodedMessage = .ok (some ct2Full))
    (hge128 : 128 ≤ ct2Full.length) (hmax_ct2 : ct2Full.length < 2 ^ 63)
    (hct1_len : x.self.uc.ct1.length = 960) (hdk_len : x.self.uc.dk.length = 2400)
    (hm_le32 : (ct2Full.drop 128).length ≤ 32)
    (hcmp :
      (let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
       let ss0 := spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32
       let auth0 := x.self.uc.auth.update F x.self.uc.epoch ss0
       let ct1Full0 := x.self.uc.ct1 ++ ct2Full.take 128
       let tag0 := hmacWith F auth0.macKey (Authenticator.ctLabel ++ toBEBytes 8 x.self.uc.epoch ++ ct1Full0)
       compare_prefix (ct2Full.drop 128) tag0 != 0#8) = false)
    (hss_eq :
      let hct2 : (ct2Full.take 128).length = 128 := by rw [List.length_take]; omega
       let ss_raw0 := (K.decaps ⟨x.self.uc.dk, hdk_len⟩ ⟨x.self.uc.ct1, hct1_len⟩ ⟨ct2Full.take 128, hct2⟩).toList
       let info0 := sckaKeyInfoPrefix ++ toBEBytes 8 x.self.uc.epoch
       ss = spqrHkdfWith F (List.replicate 32 0#8) ss_raw0 info0 32)
    (hauth'_eq : auth' = x.self.uc.auth.update F x.self.uc.epoch ss)
    (hss_len : ss.length = 32) (hss_raw_len : ss_raw.length = 32)
    (htake128_len : (ct2Full.take 128).length = 128)
    (hrk_len : auth'.rootKey.length = 32) (hmk_len : auth'.macKey.length = 32)
    (hmk_cap_ne : g_auth'.macKey.cap ≠ 0#64)
    (hmk_le : 32 ≤ g_auth'.macKey.cap.toNat) (hmk_max : g_auth'.macKey.cap.toNat < 2 ^ 63)
    (hmk_ptr_ne : g_auth'.macKey.ptr ≠ 0#64)
    (hpc : st.pc = (blkPl_350).base + 1308#64)
    (hrun : st.status = .Running) (hsp : st.sp = s0.sp - 2496#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace) (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem) (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = s0.sp - 2000#64) (hx21 : st.readReg64 .x21 = ptr_ct2)
    (hx22 : st.readReg64 .x22 = x.epoch)
    (hx23 : st.readReg64 .x23 = BitVec.ofNat 64 (ct2Full.length - 128))
    (hx24 : st.readReg64 .x24 = ptr_ss_raw) (hx25 : st.readReg64 .x25 = ptr_ct2_128)
    (hx27 : st.readReg64 .x27 = ptr_ss) (hx29 : st.readReg64 .x29 = s0.sp - 96#64) :
    SepWPp (lsProg_350 (Rust.withPanics ext)) (s0.readReg64 .x30) st
      ((ptr_ss ↦ₛ ss) ∗ A.live ptr_ss 32 1 ∗
        ct2DeallocAt A.repAlloc cap_info ptr_info ∗
        ((s0.sp - 152#64) ↦₆₄ cap_info) ∗ ((s0.sp - 144#64) ↦₆₄ ptr_info) ∗
        ((s0.sp - 136#64) ↦₆₄ 41#64) ∗ memRegion (s0.sp - 128#64) 8 ∗
        (ptr_ss_raw ↦ₛ ss_raw) ∗ A.live ptr_ss_raw 32 1 ∗
        ((s0.sp - 1280#64) ↦₆₄ cap_ct1') ∗ ((s0.sp - 1272#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 1264#64) ↦₆₄ 960#64) ∗ ct2DeallocAt A.repAlloc cap_ct1' ptr_ct1' ∗
        ct2DeallocAt A.repAlloc cap_dk ptr_dk ∗
        vecU8At A.repAlloc (s0.sp - 1328#64) g_auth'.rootKey.cap g_auth'.rootKey.ptr auth'.rootKey ∗
        ((s0.sp - 1304#64) ↦₆₄ g_auth'.macKey.cap) ∗ ((s0.sp - 1296#64) ↦₆₄ g_auth'.macKey.ptr) ∗
        ((s0.sp - 1288#64) ↦₆₄ 32#64) ∗ (g_auth'.macKey.ptr ↦ₛ auth'.macKey) ∗
        memRegion (g_auth'.macKey.ptr + 32#64) (g_auth'.macKey.cap.toNat - 32) ∗
        A.live g_auth'.macKey.ptr g_auth'.macKey.cap.toNat 1 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (ct2Full.length - 128)) ptr_mac (ct2Full.drop 128) ∗
        (ptr_ct2_128 ↦ₛ ct2Full.take 128) ∗ A.live ptr_ct2_128 128 1 ∗
        ((s0.sp - 2496#64) ↦₆₄ g_auth'.macKey.ptr) ∗ ((s0.sp - 2488#64) ↦₆₄ ptr_dk) ∗
        ((s0.sp - 2480#64) ↦₆₄ BitVec.ofNat 64 ct2Full.length) ∗
        ((s0.sp - 2472#64) ↦₆₄ ptr_info) ∗ ((s0.sp - 2464#64) ↦₆₄ cap_ct2) ∗
        ((s0.sp - 2456#64) ↦₆₄ cap_dk) ∗ ((s0.sp - 2448#64) ↦₆₄ ptr_mac) ∗
        ((s0.sp - 2440#64) ↦₆₄ ptr_ct1') ∗ ((s0.sp - 2432#64) ↦₆₄ x.epoch) ∗
        ct2DeallocAt A.repAlloc cap_ct2 ptr_ct2 ∗
        memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
        memRegion (s0.sp - 2000#64) 144 ∗ memRegion (s0.sp - 1344#64) 16 ∗
        memRegion (s0.sp - 1248#64) 960 ∗ memRegion (s0.sp - 288#64) 128 ∗
        unusedFrameAt (s0.sp - 2496#64) ∗ memRegion (s0.sp - 1856#64) 504 ∗
        polyDecoderAt A.repAlloc (s0.sp - 2424#64) receivingCt2 ∗
        memRegion (s0.sp - 2024#64) 24 ∗
        memRegion (s0.sp - 19552#64) 672 ∗ savedRegsAt s0 ∗ recvCt2RoPlacedAt ∗
        memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗ chunkAt x.chunkA x.chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim σ st ∗
        stackAt (s0.sp - 2496#64) extHookStack)
      (recvCt2PlacedPostQ K F M A lim x st0 s0 R)
      (recvCt2PlacedPostQp K x s0 R) :=
  recv_ct2_chunk_ok_done_dealloc_placed_wpp_ofEnv hA x st0 σ receivingCt2 ct2Full cap_ct2 ptr_ct2
    ptr_ct2_128 ptr_mac cap_dk ptr_dk cap_ct1' ptr_ct1' ptr_ss_raw cap_info ptr_info ptr_ss ss_raw
    ss auth' g_auth' s0 st R hfit_sec hpost_env hepoch hadd hdec hge128 hmax_ct2 hct1_len hdk_len
    hm_le32 hcmp hss_eq hauth'_eq hss_len hss_raw_len htake128_len hrk_len hmk_len hmk_cap_ne
    hmk_le hmk_max hmk_ptr_ne hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22 hx23 hx24
    hx25 hx27 hx29

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Part3cPlacedBudget
