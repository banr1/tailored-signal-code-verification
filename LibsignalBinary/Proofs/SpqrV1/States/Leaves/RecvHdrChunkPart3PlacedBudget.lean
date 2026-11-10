/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
meta import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Budget-Threaded Part 3

Budget-threaded `[LibsignalPlacement]` proof of `recv_hdr_chunk_hmac_placed_wpp{,_ofPrePostEnv,_ofEnv}`
(offsets `564 .. 696`): `sliceConcat3` (Block `386`), `libcrux_hmac`, and `ct_mac_data` deallocation.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_369 blkPC_369_pairStep_0x234 blkPl_369 lsProg_369 lsmpl lsρ)
open CryptoVerification.RustHeap
  (LayoutOk vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (SepWPp.rw_pre)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes LibcruxHmacCall PolyDecoder spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Alloc
  (SliceConcat3Ghost)
open CryptoVerification.SpqrV1.Auth
  (AuthenticatorGhost pointsTo64_rev64_eq_toBEBytes toBEBytes_8_length)
open CryptoVerification.SpqrV1.Auth.MacHdrFacts
  (hdrLabel_length)
open CryptoVerification.SpqrV1.Auth.NewFacts
  (authenticatorHeapAt)
open CryptoVerification.SpqrV1.ChainProofs
  (bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.States.Leaves
  (of_sepWP_lscro)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
  (NoHeaderReceivedRecvHdrChunkGhost bytes_rem_entails_memRegion_hdr fold_sp_168_24_24
   hdrLabelSym macHdrUnchecked_eq_hmacWith_hdr memRegion_24_of_sp_192 memRegion_48_sp_168_cells
   recv_hdr_chunk_isPanic_of_macKey_ge_32)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (vecU8HeapAt)
open CryptoVerification.SpqrV1.Unchunked
  (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents
   rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (LibcruxHmacEnv libcruxHmacBudgetSpec libcruxHmacSha256Events)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
  (SliceConcat3Env fitsEnv_sliceConcat3_iff sliceConcat3Events vecU8_of_exists_vecU8At)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (NoHeaderReceivedRecvHdrChunkEnv recvHdrChunkHmacEvents)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
  (RecvHdrChunkContractsPlaced call_allowPanic_lscro_mid dealloc_placed_ok_at_recvHdr
   onPanic_same_entails_recvHdr recvHdrChunkPlacedPostQ recvHdrChunkPlacedPostQOfEnv
   recvHdrChunkPlacedPostQOfPrePostEnv recvHdrChunkPlacedPostQp recvHdrChunkPlacedRoAt
   sliceConcat3_placed_ok_at_recvHdr spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3Budget
  (authenticatorHeapAt_expose_macKey_budget authenticatorHeapAt_unexpose_macKey_budget
   fitsEnv_libcruxHmacEnv_of_fitsEvents libcruxHmacHdrSpec vecU8_expose_nonempty_192_budget)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length hdrLabel_length
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible]
  CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk

/-! ## Re-Export from `RecvHdrChunkPart3Budget` -/

abbrev libcrux_hmac_hdr_placed_ok_at_recvHdr :=
  @RecvHdrChunkPart3Budget.libcrux_hmac_hdr_placed_ok_at_recvHdr

/-! ## Local Stack Alignment Helpers -/

private theorem prep_ext_stack {prog : Program} {mid : BitVec 64} {s : State}
    {P R : SepProp} {post : State → SepProp → Prop} (sp0 : BitVec 64)
    (hf : P = stackAt (sp0 - 1648#64) extHookStack ∗ R)
    (hsp_eq : s.sp = sp0 - 1648#64)
    (hnext : SepWP prog mid s (stackAt s.sp extHookStack ∗ R) post) :
    SepWP prog mid s P post := by
  rw [hf, ← hsp_eq]
  exact hnext

private theorem unprep_ext_stack {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    {sp1 : BitVec 64} (sp0 : BitVec 64) {R : SepProp}
    (hf : P = stackAt sp1 extHookStack ∗ R)
    (hsp_eq : sp1 = sp0 - 1648#64)
    (hnext : SepWPp prog ret s (stackAt (sp0 - 1648#64) extHookStack ∗ R) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.rw_pre (by rw [hf, hsp_eq]) hnext

private theorem transport_pool_step {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st_cur : M.σ) (s1 : State)
    {prog : Program} {tgt : BitVec 64} {s2 : State} {P F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hvm : VmPreserved s1 s2)
    (hf : P = A.pool lim st_cur s1 ∗ F)
    (hnext : SepWP prog tgt s2 (A.pool lim st_cur s2 ∗ F) post oom) :
    SepWP prog tgt s2 P post oom :=
  ProofLib.SepWP.transport_budgetPool hvm hf hnext

/-! ## 1. `sliceConcat3`, `libcrux_hmac`, and `ct_mac_data` Dealloc (offsets `564 .. 696`) -/

set_option maxHeartbeats 1600000 in
/-- Two-envelope (`PreEnv` / `PostEnv`) budget-threaded relocatable proof of Part 3
    (offsets `564 .. 696`) of `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`):
    concatenates `hdrLabel ++ toBEBytes 8 epoch ++ hdrFull.take 64` (`105` bytes), calls
    `libcrux_hmac::hmac`, and deallocates the temporary `ct_mac_data` buffer, advancing the
    allocator state from `st_cur` to `M.stepEvents (recvHdrChunkHmacEvents ++ evs_md) st_cur`
    for some `FreeOnlyEvs evs_md`. -/
theorem recv_hdr_chunk_hmac_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length)
    (hfits_hmac : FitsEvents M lim st_cur recvHdrChunkHmacEvents)
    (hpc : st.pc = (blkPl_369).base + 564#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx25 : st.readReg64 .x25 = ptr_hdr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (evs_md : List AllocEvent),
      FreeOnlyEvs evs_md →
      x.self.uc.auth.macKey.length < 2 ^ 32 →
      st'.pc = (blkPl_369).base + 696#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = cap_hdrFull →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = BitVec.ofNat 64 x.self.uc.auth.macKey.length →
      st'.readReg64 .x24 = x.epoch →
      st'.readReg64 .x25 = ptr_hdr →
      st'.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st'.readReg64 .x27 = g_auth0.macKey.ptr →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (recvHdrChunkPlacedRoAt ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
          ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
          vecU8 A.repAlloc (s0.sp - 168#64)
            (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
          memRegion (s0.sp - 144#64) 24 ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          A.pool lim (M.stepEvents (recvHdrChunkHmacEvents ++ evs_md) st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvHdrChunkPlacedRoAt ∗
        (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
        ((s0.sp - 1640#64) ↦₆₄ c1) ∗
        ((s0.sp - 1632#64) ↦₆₄ c2) ∗
        ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗
        memRegion (s0.sp - 120#64) 8 ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  have h_concat3 := sliceConcat3_placed_ok_at_recvHdr hC
  have h_hmac := libcrux_hmac_hdr_placed_ok_at_recvHdr
    (P := (x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true) hhmac
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have hfits_split : FitsEvents M lim st_cur
      (rustAllocEvents 105 1 ++ libcruxHmacSha256Events) := hfits_hmac
  obtain ⟨hfit_105, hfit_sha⟩ :=
    (fitsEvents_append M lim (rustAllocEvents 105 1) libcruxHmacSha256Events st_cur).mp hfits_split
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx29
  clear hC hhmac hfits_split
  have htake64_len : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
  have htake64_bv : BitVec.ofNat 64 (hdrFull.take 64).length = 64#64 := by rw [htake64_len]
  let g_cc : SliceConcat3Ghost :=
    ⟨s0.sp - 192#64, s0.sp - 168#64,
      true, lsρ hdrLabelSym, Authenticator.hdrLabel,
      false, s0.sp - 120#64, toBEBytes 8 x.epoch,
      false, ptr_hdr, hdrFull.take 64⟩
  have hcc_len : g_cc.bs0.length + g_cc.bs1.length + g_cc.bs2.length = 105 := by
    dsimp only [g_cc]
    rw [hdrLabel_length, toBEBytes_8_length, htake64_len]
  have hconcat3_bound : 41 + (hdrFull.take 64).length < 9223372036854775808 := by
    rw [htake64_len]; decide
  have hfit_cc : FitsEnv M lim st_cur (SliceConcat3Env g_cc) := by
    rw [fitsEnv_sliceConcat3_iff, hcc_len]
    exact hfit_105
  dsimp only [g_cc] at hcc_len hfit_cc
  refine SepWPp.fold
    (authenticatorHeapAt_expose_macKey_budget A g_auth0 x.self.uc.auth)
    (by sep_focus) ?_
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmk_le, hmk_max, hmk_ptr_ne⟩
  have hmk_toNat :
      (BitVec.ofNat 64 x.self.uc.auth.macKey.length).toNat = x.self.uc.auth.macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.rw_pre (by
    rw [memRegion_48_sp_168_cells s0.sp,
        ProofLib.memRegion_eight (s0.sp - 120#64)]) ?_
  sep_elim_exists
  refine of_sepWP_lscro (mid := lsmpl.base 386) hinv ?_
  refine blkPC_369_pairStep_0x234 (blkPl_369).base (Rust.withPanics ext) rfl hpc hrun ?_
  apply transport_pool_step A lim st_cur st
  · exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  · sep_focus
  wp_steps_sync_pool (lsmpl.base 386)
  simp only [State.setMem_setMem]
  refine SepWP.fold
    (Entails.of_eq ((congrArg (fun e => (s0.sp - 120#64) ↦₆₄ rev64 e) hepoch.symm).trans
      (pointsTo64_rev64_eq_toBEBytes (s0.sp - 120#64) x.epoch)))
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr_budget h_concat3
    ((⟨s0.sp - 192#64, s0.sp - 168#64,
      true, lsρ hdrLabelSym, Authenticator.hdrLabel,
      false, s0.sp - 120#64, toBEBytes 8 x.epoch,
      false, ptr_hdr, hdrFull.take 64⟩ : SliceConcat3Ghost),
     st_cur)
    hinv1
  apply SepWPp.exists_elim; intro evs_cc
  apply SepWPp.exists_elim; intro ptr_cc
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr1, _, hEnv_cc⟩
  have hevs_cc : evs_cc = rustAllocEvents 105 1 := by
    dsimp only [SliceConcat3Env, sliceConcat3Events,
      LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget.sliceConcat2Events] at hEnv_cc
    rw [hcc_len] at hEnv_cc
    have h105 : ¬(105 = 0) := by decide
    simpa only [h105, ↓reduceIte] using hEnv_cc
  subst hevs_cc
  refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine SepWPp.fold
    (Entails.trans (Entails.sepExists_intro ptr_cc)
      (vecU8_of_exists_vecU8At A.repAlloc (s0.sp - 192#64) _
        (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64)))
    (by sep_focus) ?_
  have hdata_len :
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length = 105 := by
    simp only [List.length_append, hdrLabel_length, toBEBytes_8_length, htake64_len]
  have hdata_pos :
      0 < (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length := by
    omega
  refine SepWPp.fold
    (vecU8_expose_nonempty_192_budget A s0.sp
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64)
      hdata_pos)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_md ptr_md
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_md_ne, hlay_md, hptr_md_ne, hle_md⟩
  have hrlay_md : RustLayoutOk cap_md.toNat 1 := ⟨hlay_md, by decide⟩
  have ⟨_, _, hmax_md⟩ := hlay_md
  have hcap_md_beq : (cap_md == 0#64) = false := beq_false_of_ne hcap_md_ne
  have hfree_md : FreeOnlyEvs (rustDeallocEvents cap_md.toNat 1) :=
    FreeOnlyEvs.singleton 1 cap_md.toNat
  refine SepWPp.fold
    (fold_sp_168_24_24 s0.sp
      (lsρ hdrLabelSym) 33#64
      (s0.sp - 120#64) 8#64 ptr_hdr
      (BitVec.ofNat 64 (hdrFull.take 64).length))
    (by sep_focus) ?_
  have hbe_mr : ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.epoch) ⊢ memRegion (s0.sp - 120#64) 8 := by
    have hbe8 : (toBEBytes 8 x.epoch).length = 8 := toBEBytes_8_length x.epoch
    exact hbe8 ▸ pointsToBytes_entails_memRegion (s0.sp - 120#64) (toBEBytes 8 x.epoch)
  refine SepWPp.fold hbe_mr (by sep_focus) ?_
  refine of_sepWP_lscro (mid := lsρ spqrLibcruxHmacSym) hF_sf ?_
  wp_steps_sync_pool (lsρ spqrLibcruxHmacSym)
  simp only [State.setMem_setMem]
  refine prep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  have hdata_lt32 :
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length < 4294967296 := by
    rw [hdata_len]; decide
  have hmk_panic : 4294967296 ≤ x.self.uc.auth.macKey.length →
      (x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true :=
    recv_hdr_chunk_isPanic_of_macKey_ge_32 x.self x.epoch x.chunk receivingHdr hdrFull
      hepoch hadd hdec hge64
  let g_hmac : LibcruxHmacCall :=
    ⟨s0.sp - 168#64, g_auth0.macKey.ptr, x.self.uc.auth.macKey,
      ptr_md, Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64⟩
  have hfit_hmac_env :
      FitsEnv M lim (M.stepEvents (rustAllocEvents 105 1) st_cur) (LibcruxHmacEnv g_hmac) :=
    fitsEnv_libcruxHmacEnv_of_fitsEvents hfit_sha
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  apply (call_allowPanic_lscro_mid h_hmac
    (x := (g_hmac, M.stepEvents (rustAllocEvents 105 1) st_cur))
    (F := recvHdrChunkPlacedRoAt ∗
      (ptr_hdr ↦ₛ hdrFull.take 64) ∗
      vecU8HeapAt A.repAlloc g_auth0.rootKey.cap g_auth0.rootKey.ptr x.self.uc.auth.rootKey ∗
      (if g_auth0.macKey.cap = 0 then emp
       else A.live g_auth0.macKey.ptr g_auth0.macKey.cap.toNat 1 ∗
         memRegion (g_auth0.macKey.ptr + BitVec.ofNat 64 x.self.uc.auth.macKey.length)
           (g_auth0.macKey.cap.toNat - x.self.uc.auth.macKey.length)) ∗
      ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
      ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
      ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
      ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
      memRegion (s0.sp - 144#64) 24 ∗
      ((s0.sp - 192#64) ↦₆₄ cap_md) ∗
      ((s0.sp - 184#64) ↦₆₄ ptr_md) ∗
      ((s0.sp - 176#64) ↦₆₄
        BitVec.ofNat 64 (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length) ∗
      A.live ptr_md cap_md.toNat 1 ∗
      memRegion
        (ptr_md + BitVec.ofNat 64
          (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length)
        (cap_md.toNat -
          (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length) ∗
      memRegion (s0.sp - 120#64) 8 ∗
      F_frame)
    hinv2)
  · wp_norm_goal
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [libcruxHmacHdrSpec, g_hmac] at _hmR' ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by rw [← List.append_assoc Authenticator.hdrLabel, ← hepoch, hdata_len]; rfl,
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             hmk_panic,
             hdata_lt32,
             hfit_hmac_env⟩, ?_⟩
    dsimp only [recvHdrChunkPlacedRoAt]
    simp only [wp_norm, arm64_norm]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) _hmR'
  · intro _
    dsimp only [libcruxHmacHdrSpec]
    exact onPanic_same_entails_recvHdr (by simp only [wp_norm, arm64_norm, *])
  · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  intro sf_1 hpc_sf_1 hrun_sf_1 hsp_sf_1 hcs_sf_1 hF_sf_1
  dsimp only [libcruxHmacHdrSpec, g_hmac]
  simp only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hsp_sf_1 hcs_sf_1
  rcases hcs_sf_1 with ⟨hx19_sf_1, hx20_sf_1, hx21_sf_1, hx22_sf_1, hx23_sf_1,
    hx24_sf_1, hx25_sf_1, hx26_sf_1, hx27_sf_1, hx28_sf_1, hx29_sf_1, hvregs_sf_1⟩
  conv => arg 4; simp only [sepConj_assoc, wp_norm, arm64_norm, hsp_sf_1]
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus
    (x.self.uc.auth.macKey.length < 2 ^ 32 ∧ _)
    (by sep_focus) ?_
  rintro ⟨hmk_lt32, htr2⟩
  refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  rw [← List.append_assoc Authenticator.hdrLabel,
    ← macHdrUnchecked_eq_hmacWith_hdr F x.self.uc.auth x.epoch (hdrFull.take 64),
    ← M.stepEvents_append]
  refine SepWPp.fold
    (authenticatorHeapAt_unexpose_macKey_budget A g_auth0 x.self.uc.auth
      hmk_le hmk_max hmk_ptr_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (bytes_rem_entails_memRegion_hdr ptr_md cap_md
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64)
      hle_md hmax_md)
    (by sep_focus) ?_
  refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hF_sf_1 ?_
  wp_steps_sync_pool (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  wpp_call_lscro_recvHdr_budget h_dealloc
    (ptr_md, cap_md.toNat, 1, M.stepEvents recvHdrChunkHmacEvents st_cur) hinv3
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun htr3 => ?_
  refine unprep_ext_stack s0.sp (by sep_focus) (by simp only [wp_norm, arm64_norm, *]) ?_
  rw [← M.stepEvents_append]
  refine SepWPp.fold
    (memRegion_24_of_sp_192 s0.sp cap_md ptr_md
      (BitVec.ofNat 64
        (Authenticator.hdrLabel ++ (toBEBytes 8 x.epoch ++ hdrFull.take 64)).length))
    (by sep_focus) ?_
  refine SepWPp.rw_pre (by dsimp only [recvHdrChunkPlacedRoAt]; sep_ac_rfl)
    (hcont sf_2 (rustDeallocEvents cap_md.toNat 1) hfree_md hmk_lt32
      (by wp_norm_goal) (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      hF_sf_2
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))

theorem recv_hdr_chunk_hmac_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length)
    (hfits_hmac : FitsEvents M lim st_cur recvHdrChunkHmacEvents)
    (hpc : st.pc = (blkPl_369).base + 564#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx25 : st.readReg64 .x25 = ptr_hdr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (evs_md : List AllocEvent),
      FreeOnlyEvs evs_md →
      x.self.uc.auth.macKey.length < 2 ^ 32 →
      st'.pc = (blkPl_369).base + 696#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = cap_hdrFull →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = BitVec.ofNat 64 x.self.uc.auth.macKey.length →
      st'.readReg64 .x24 = x.epoch →
      st'.readReg64 .x25 = ptr_hdr →
      st'.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st'.readReg64 .x27 = g_auth0.macKey.ptr →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (recvHdrChunkPlacedRoAt ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
          ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
          vecU8 A.repAlloc (s0.sp - 168#64)
            (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
          memRegion (s0.sp - 144#64) 24 ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          A.pool lim (M.stepEvents (recvHdrChunkHmacEvents ++ evs_md) st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvHdrChunkPlacedRoAt ∗
        (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
        ((s0.sp - 1640#64) ↦₆₄ c1) ∗
        ((s0.sp - 1632#64) ↦₆₄ c2) ∗
        ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗
        memRegion (s0.sp - 120#64) 8 ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_hmac_placed_wpp_ofPrePostEnv
    (PreEnv := Env) (PostEnv := Env) hC hhmac x receivingHdr hdrFull
    cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0 st0 st_cur s0 st F_frame R
    hepoch hadd hdec hge64 hfits_hmac
    hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx29 hcont

theorem recv_hdr_chunk_hmac_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacBudgetSpec F M A lim))
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length)
    (hfits_hmac : FitsEvents M lim st_cur recvHdrChunkHmacEvents)
    (hpc : st.pc = (blkPl_369).base + 564#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx19 : st.readReg64 .x19 = x.outA)
    (hx20 : st.readReg64 .x20 = cap_hdrFull)
    (hx21 : st.readReg64 .x21 = ptr_hdrFull)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx23 : st.readReg64 .x23 = ptr_mac)
    (hx24 : st.readReg64 .x24 = x.epoch)
    (hx25 : st.readReg64 .x25 = ptr_hdr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State) (evs_md : List AllocEvent),
      FreeOnlyEvs evs_md →
      x.self.uc.auth.macKey.length < 2 ^ 32 →
      st'.pc = (blkPl_369).base + 696#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = x.outA →
      st'.readReg64 .x20 = cap_hdrFull →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = BitVec.ofNat 64 x.self.uc.auth.macKey.length →
      st'.readReg64 .x24 = x.epoch →
      st'.readReg64 .x25 = ptr_hdr →
      st'.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length →
      st'.readReg64 .x27 = g_auth0.macKey.ptr →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (recvHdrChunkPlacedRoAt ∗
          (ptr_hdr ↦ₛ hdrFull.take 64) ∗
          authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
          ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
          vecU8 A.repAlloc (s0.sp - 168#64)
            (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
          memRegion (s0.sp - 144#64) 24 ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          A.pool lim (M.stepEvents (recvHdrChunkHmacEvents ++ evs_md) st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvHdrChunkPlacedRoAt ∗
        (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        authenticatorHeapAt A.repAlloc g_auth0 x.self.uc.auth ∗
        ((s0.sp - 1640#64) ↦₆₄ c1) ∗
        ((s0.sp - 1632#64) ↦₆₄ c2) ∗
        ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗
        memRegion (s0.sp - 120#64) 8 ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_hmac_placed_wpp_ofEnv (Env := NoHeaderReceivedRecvHdrChunkEnv) hC hhmac x
    receivingHdr hdrFull cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 g_auth0
    st0 st_cur s0 st F_frame R hepoch hadd hdec hge64 hfits_hmac
    hpc hrun hsp hsp_s0 htr hvregs hinv hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx29 hcont

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3PlacedBudget
