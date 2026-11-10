/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Relocatable Part 3

Relocatable `[LibsignalPlacement]` proof of `recv_hdr_chunk_hmac_placed_wpp` (offsets `564 .. 696`):
`sliceConcat3` (Block `386`), `libcrux_hmac`, and `ct_mac_data` deallocation.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.IsNonZero
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1.PolyDecoder
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SpqrV1.ChainProofs
open UpdateFacts NextKeyInternalFacts AgreeStateSimp SplitBytes NewFacts

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length MacHdrFacts.hdrLabel_length
attribute [-arm64_norm]
  HkdfToSliceProof.sp_sub_688_eq_hsp
  HkdfToSliceProof.sp_add_neg688_eq_hsp
  HkdfToSliceProof.sp_sub_96_eq_hsp_592
  HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk

/-! ## 1. `sliceConcat3`, `libcrux_hmac`, and `ct_mac_data` Dealloc (offsets `564 .. 696`) -/

theorem libcrux_hmac_hdr_placed_ok_at_recvHdr [LibsignalPlacement]
    {s0_top : State} {P : Prop}
    {F : ShaCompress} {A : RustAlloc} {ext : String → Option (State → State)}
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
      (lsρ spqrLibcruxHmacSym)
      (withLsCodeRoLoaded lsmpl (libcruxHmacHdrSpec s0_top P F A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_plain
  have hraw :
      subroutine_ok ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext))
        (lsρ spqrLibcruxHmacSym)
        (libcruxHmacSpec F A) :=
    spqr_hook_ok_of_mem (prog := lsProg_369 (Rust.withPanics ext)) hhmac
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [libcruxHmacHdrSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, htr_eq, hk_imp, hd_lt⟩, hmem⟩
  have hpre' : s0.mem ⊨ (libcruxHmacSpec F A).pre x s0 ∗ R := by
    dsimp only [libcruxHmacSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hmem⟩
  refine hraw.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [libcruxHmacSpec, libcruxHmacHdrSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, hpost.1.2.2⟩, hpost.2⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [libcruxHmacSpec, libcruxHmacHdrSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨haf | hk_ge | hd_ge, hpref⟩, hmem'⟩
    · unfold allocFailedIn at haf ⊢
      rw [htr_eq] at haf
      exact ⟨⟨Or.inr haf, hpref⟩, hmem'⟩
    · exact ⟨⟨Or.inl (hk_imp hk_ge), hpref⟩, hmem'⟩
    · omega
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_hmac_placed_wpp [LibsignalPlacement] {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced A ext)
    (hhmac : HookSat (Rust.withPanics ext) spqrLibcruxHmacSym (libcruxHmacSpec F A))
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder) (hdrFull : Bytes)
    (cap_hdrFull ptr_hdrFull ptr_mac ptr_hdr c1 c2 : BitVec 64)
    (g_auth0 : AuthenticatorGhost)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length)
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
    (hcont : ∀ (st' : State),
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
          authenticatorHeapAt A g_auth0 x.self.uc.auth ∗
          ((s0.sp - 1640#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1632#64) ↦₆₄ ptr_hdrFull) ∗
          ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
          ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
          vecU8 A (s0.sp - 168#64) (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
          memRegion (s0.sp - 144#64) 24 ∗
          memRegion (s0.sp - 192#64) 24 ∗
          memRegion (s0.sp - 120#64) 8 ∗
          A.pool ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQ F A x s0 R)
        (recvHdrChunkPlacedPostQp F A x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (recvHdrChunkPlacedRoAt ∗
        (ptr_hdr ↦ₛ hdrFull.take 64) ∗
        authenticatorHeapAt A g_auth0 x.self.uc.auth ∗
        ((s0.sp - 1640#64) ↦₆₄ c1) ∗
        ((s0.sp - 1632#64) ↦₆₄ c2) ∗
        ((s0.sp - 1584#64) ↦₆₄ g_auth0.macKey.ptr) ∗
        ((s0.sp - 1576#64) ↦₆₄ BitVec.ofNat 64 x.self.uc.auth.macKey.length) ∗
        memRegion (s0.sp - 192#64) 24 ∗
        memRegion (s0.sp - 168#64) 48 ∗
        memRegion (s0.sp - 120#64) 8 ∗
        A.pool ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQ F A x s0 R)
      (recvHdrChunkPlacedPostQp F A x s0 R) := by
  have h_concat3 := sliceConcat3_placed_ok_at_recvHdr hC
  have h_hmac := libcrux_hmac_hdr_placed_ok_at_recvHdr (s0_top := s0)
    (P := (x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true) hhmac
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx29
  clear hC hhmac
  have htake64_len : (hdrFull.take 64).length = 64 := by rw [List.length_take]; omega
  have htake64_bv : BitVec.ofNat 64 (hdrFull.take 64).length = 64#64 := by rw [htake64_len]
  have hconcat3_bound : 41 + (hdrFull.take 64).length < 9223372036854775808 := by
    rw [htake64_len]; decide
  refine SepWPp.fold
    (authenticatorHeapAt_expose_macKey A g_auth0 x.self.uc.auth)
    (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmk_le, hmk_max, hmk_ptr_ne⟩
  have hmk_toNat : (BitVec.ofNat 64 x.self.uc.auth.macKey.length).toNat = x.self.uc.auth.macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine SepWPp.rw_pre (by
    rw [memRegion_48_sp_168_cells s0.sp,
        ProofLib.memRegion_eight (s0.sp - 120#64)]) ?_
  sep_elim_exists
  refine of_sepWP_lscro (mid := lsmpl.base 386) hinv ?_
  refine blkPC_369_pairStep_0x234 (blkPl_369).base (Rust.withPanics ext) rfl hpc hrun ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq ((congrArg (fun e => (s0.sp - 120#64) ↦₆₄ rev64 e) hepoch.symm).trans
      (pointsTo64_rev64_eq_toBEBytes (s0.sp - 120#64) x.epoch)))
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv1
  wpp_call_lscro_recvHdr h_concat3
    (⟨s0.sp - 192#64, s0.sp - 168#64,
      true, lsρ hdrLabelSym, Authenticator.hdrLabel,
      false, s0.sp - 120#64, toBEBytes 8 x.epoch,
      false, ptr_hdr, hdrFull.take 64⟩ : SliceConcat3Ghost)
    hinv1
  refine SepWPp.pure_left_focus (sf.trace = st.trace) (by sep_focus) fun htr1 => ?_
  rw [← List.append_assoc Authenticator.hdrLabel]
  have hdata_len :
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length = 105 := by
    simp only [List.length_append, MacHdrFacts.hdrLabel_length, toBEBytes_8_length, htake64_len]
  have hdata_pos :
      0 < (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length := by
    omega
  refine SepWPp.fold
    (vecU8_expose_nonempty_192 A s0.sp
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64)
      hdata_pos)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_md ptr_md
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_md_ne, hlay_md, hptr_md_ne, hle_md⟩
  have ⟨_, _, hmax_md⟩ := hlay_md
  have hcap_md_beq : (cap_md == 0#64) = false := beq_false_of_ne hcap_md_ne
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
  wp_steps
  have hstack_sf : stackAt st.sp extHookStack = stackAt sf.sp extHookStack := by
    rw [hsp_sf]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  have hdata_lt32 :
      (Authenticator.hdrLabel ++ (toBEBytes 8 x.epoch ++ hdrFull.take 64)).length < 4294967296 := by
    rw [← List.append_assoc Authenticator.hdrLabel, hdata_len]
    decide
  have hmk_panic : 4294967296 ≤ x.self.uc.auth.macKey.length →
      (x.self.recv_hdr_chunk x.epoch x.chunk).isPanic = true :=
    recv_hdr_chunk_isPanic_of_macKey_ge_32 x.self x.epoch x.chunk receivingHdr hdrFull
      hepoch hadd hdec hge64
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  apply (call_allowPanic_lscro_mid h_hmac
    (x := (⟨s0.sp - 168#64, g_auth0.macKey.ptr, x.self.uc.auth.macKey,
      ptr_md, Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64⟩ : LibcruxHmacCall))
    (F := recvHdrChunkPlacedRoAt ∗
      (ptr_hdr ↦ₛ hdrFull.take 64) ∗
      vecU8HeapAt A g_auth0.rootKey.cap g_auth0.rootKey.ptr x.self.uc.auth.rootKey ∗
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
      ((s0.sp - 176#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length) ∗
      A.live ptr_md cap_md.toNat 1 ∗
      memRegion (ptr_md + BitVec.ofNat 64 (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length)
        (cap_md.toNat - (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64).length) ∗
      memRegion (s0.sp - 120#64) 8 ∗
      F_frame)
    hinv2)
  · wp_norm_goal
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [libcruxHmacHdrSpec] at _hmR' ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by rw [← List.append_assoc Authenticator.hdrLabel, ← hepoch, hdata_len]; rfl,
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             hmk_panic,
             by rw [List.append_assoc Authenticator.hdrLabel]; exact hdata_lt32⟩, ?_⟩
    dsimp only [recvHdrChunkPlacedRoAt]
    simp only [wp_norm, arm64_norm]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) _hmR'
  · intro _
    dsimp only [libcruxHmacHdrSpec]
    exact onPanic_or_alloc_entails_recvHdr (by wp_norm_lhs)
  · exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  intro sf_1 hpc_sf_1 hrun_sf_1 hsp_sf_1 hcs_sf_1 hF_sf_1
  dsimp only [libcruxHmacHdrSpec]
  simp only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm] at hsp_sf_1 hcs_sf_1
  rcases hcs_sf_1 with ⟨hx19_sf_1, hx20_sf_1, hx21_sf_1, hx22_sf_1, hx23_sf_1,
    hx24_sf_1, hx25_sf_1, hx26_sf_1, hx27_sf_1, hx28_sf_1, hx29_sf_1, hvregs_sf_1⟩
  conv => arg 4; simp only [sepConj_assoc, wp_norm, arm64_norm, hsp_sf_1]
  refine SepWPp.pure_left_focus
    (x.self.uc.auth.macKey.length < 2 ^ 32 ∧ sf_1.trace = sf.trace)
    (by sep_focus) ?_
  rintro ⟨hmk_lt32, htr2⟩
  rw [← List.append_assoc Authenticator.hdrLabel,
    ← macHdrUnchecked_eq_hmacWith_hdr F x.self.uc.auth x.epoch (hdrFull.take 64)]
  refine SepWPp.fold
    (authenticatorHeapAt_unexpose_macKey A g_auth0 x.self.uc.auth hmk_le hmk_max hmk_ptr_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (bytes_rem_entails_memRegion_hdr ptr_md cap_md
      (Authenticator.hdrLabel ++ toBEBytes 8 x.epoch ++ hdrFull.take 64)
      hle_md hmax_md)
    (by sep_focus) ?_
  refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hF_sf_1 ?_
  wp_steps
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [hsp_sf_1]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv3
  wpp_call_lscro_recvHdr h_dealloc (ptr_md, cap_md.toNat, 1) hinv3
  refine SepWPp.pure_left_focus (sf_2.trace = sf_1.trace) (by sep_focus) fun htr3 => ?_
  have hstack_back : stackAt sf_1.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
    rw [hsp_sf_1, hsp_sf, hsp]
  refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
  refine SepWPp.fold
    (memRegion_24_of_sp_192 s0.sp cap_md ptr_md
      (BitVec.ofNat 64 (Authenticator.hdrLabel ++ (toBEBytes 8 x.epoch ++ hdrFull.take 64)).length))
    (by sep_focus) ?_
  refine SepWPp.rw_pre (by dsimp only [recvHdrChunkPlacedRoAt]; ac_rfl)
    (hcont sf_2 hmk_lt32
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

end CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
