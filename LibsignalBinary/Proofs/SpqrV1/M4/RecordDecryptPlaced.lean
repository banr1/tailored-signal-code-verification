/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.M4.DecryptPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Record.SegDecrypt
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch

/-!
# Relocatable `try_decrypt_from_record` Region over SPQR V1

Relocatable `[LibsignalPlacement]` verification of the `try_decrypt_from_record` region
(Block `197`) against `recordDecryptPlacedSpecT`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1.M4

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.SpqrV1.GF.Mul2U16

/-- `recordDecryptPlacedSpec` with the pq state shorter than `2^32` bytes in the pre and
`tokenInitPlacedAt` framed, as `tryDecryptPlacedSpecT`. -/
def recordDecryptPlacedSpecT [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec RecordDecryptGhost :=
  { recordDecryptPlacedSpec C A ctl uuidParse S with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ tokenInitPlacedAt ∗
        (recordDecryptPlacedSpec C A ctl uuidParse S).pre x s
    post := fun x s0 sf =>
      tokenInitPlacedAt ∗ (recordDecryptPlacedSpec C A ctl uuidParse S).post x s0 sf }

/-- `Record.tryDecryptPlacedSpec` with `⌜x.st.pqRatchetState.length < 2 ^ 32⌝` and
`⌜LibsignalRoLoaded lsmpl s.mem⌝` in the pre and `tokenInitPlacedAt` framed. -/
abbrev recordTryDecryptPlacedSpecT [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { Record.tryDecryptPlacedSpec C A ctl uuidParse S with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ ∗
        (Record.tryDecryptPlacedSpec C A ctl uuidParse S).pre x s ∗ tokenInitPlacedAt
    post := fun x s0 sf =>
      (Record.tryDecryptPlacedSpec C A ctl uuidParse S).post x s0 sf ∗ tokenInitPlacedAt }

theorem subroutine_ok_recordTryDecryptPlacedSpecT [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    (hTry : subroutine_ok prog entry (tryDecryptPlacedSpecT C A ctl uuidParse S)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (recordTryDecryptPlacedSpecT C A ctl uuidParse S)) := by
  refine subroutine_ok_mono hTry
    (fun x R s0 hpre => by
      have hpre' : s0.mem ⊨
          ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
          ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
          ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗
          tokenInitPlacedAt ∗
          (Record.tryDecryptPlacedSpec C A ctl uuidParse S).pre x s0 ∗ R := by
        dsimp only [recordTryDecryptPlacedSpecT, withLsCodeLoaded] at hpre
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpre
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpre'
      have hgoal : s0.mem ⊨
          ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
          ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          tokenInitPlacedAt ∗
          (Record.tryDecryptPlacedSpec C A ctl uuidParse S).pre x s0 ∗ R := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨hpre'.1, ⟨hpre'.2.1, hpre'.2.2.1⟩, hpre'.2.2.2⟩
      dsimp only [tryDecryptPlacedSpecT, withLsCodeRoLoaded, Decrypt.tryDecryptSpecPlaced,
        Decrypt.tryDecryptRawSpecPlaced, tryDecryptSpec, Spec.inImage,
        Record.tryDecryptPlacedSpec, FromRecordCallees.lsLogOff] at hgoal ⊢
      rw [Decrypt.logOff_tryDecryptPlacedImg]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hgoal)
    (fun x R s0 sf hpost => by
      dsimp only [tryDecryptPlacedSpecT, recordTryDecryptPlacedSpecT, withLsCodeLoaded,
        withLsCodeRoLoaded, Decrypt.tryDecryptSpecPlaced, Decrypt.tryDecryptRawSpecPlaced,
        tryDecryptSpec, Spec.inImage, Record.tryDecryptPlacedSpec,
        FromRecordCallees.lsLogOff] at hpost ⊢
      rw [Decrypt.logOff_tryDecryptPlacedImg] at hpost
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hpost)
    (fun _ _ _ _ hpan => hpan)
    (fun _ _ _ _ _ he => he)

theorem seg_of_sepWPp_JF_placedT [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (hm : s.mem ⊨ P ∗ R)
    (hL : ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_197).rebase (blkPl_197).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        JStatePlaced C A ctl uuidTryParse S x (tokenInitPlacedAt ∗ R) s0 sf ∨
          FStatePlaced C A ctl uuidTryParse S x (tokenInitPlacedAt ∗ R) s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptPlacedSpec C A ctl uuidTryParse S).onPanic x s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
      (JStatePlaced C A ctl uuidTryParse S x (tokenInitPlacedAt ∗ R) s0 s' ∨
        FStatePlaced C A ctl uuidTryParse S x (tokenInitPlacedAt ∗ R) s0 s' ∨
        regionOutcome (recordDecryptPlacedSpecT C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hJF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · rcases hJF hmf with hJ | hF
    · exact ⟨sf, hsteps, Or.inl hJ⟩
    · exact ⟨sf, hsteps, Or.inr (Or.inl hF)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem regionOutcome_placed_of_tokenFrame [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {x : RecordDecryptGhost} {R : SepProp} {s0 sf : State}
    (hout : regionOutcome (recordDecryptPlacedSpec C A ctl uuidTryParse S)
      recExitPlaced x (tokenInitPlacedAt ∗ R) s0 sf) :
    regionOutcome (recordDecryptPlacedSpecT C A ctl uuidTryParse S)
      recExitPlaced x R s0 sf := by
  rcases hout with ⟨hpc, hrun, hvregs, hpost⟩ | ⟨hpan, hpost⟩
  · left
    refine ⟨hpc, hrun, hvregs, ?_⟩
    dsimp only [recordDecryptPlacedSpecT]
    have heq : (recordDecryptPlacedSpec C A ctl uuidTryParse S).post x s0 sf ∗ (tokenInitPlacedAt ∗ R) =
        (tokenInitPlacedAt ∗ (recordDecryptPlacedSpec C A ctl uuidTryParse S).post x s0 sf) ∗ R := by ac_rfl
    exact heq ▸ hpost
  · right
    refine ⟨hpan, ?_⟩
    dsimp only [recordDecryptPlacedSpecT, recordDecryptPlacedSpec] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost

attribute [local arm64_norm ↓, local wp_norm ↓]
  Record.SegDecryptFacts.SegDecryptRegReadSimp.sp_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.sp_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg64_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg64_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg32_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg32_setMem_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg_setPC_pre
  Record.SegDecryptFacts.SegDecryptRegReadSimp.readReg_setMem_setPC_pre

attribute [local irreducible] Program.fetch Program.externAt?

set_option maxHeartbeats 1600000 in
theorem segDecrypt_placed_okT [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    (hmemcpy_sat : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (htry_rel : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 131)
      (withLsCodeLoaded lsmpl (recordTryDecryptPlacedSpecT C A ctl uuidTryParse S)))
    (hset_rel : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (FromRecordCallees.setSessionStateSpec A)))
    (hdrop_rel : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)))
    (hgrow_rel : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)))
    (hclosure_rel : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159)
      (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec))
    (x : RecordDecryptGhost) (G₁ : SessionGhost) (R : SepProp) (s0 s : State)
    (_hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hV : VStatePlaced A ctl x G₁ (tokenInitPlacedAt ∗ R) s0 s)
    (hsp_bound : rootStack ≤ s0.sp.toNat)
    (hL : ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
      (JStatePlaced C A ctl uuidTryParse S x (tokenInitPlacedAt ∗ R) s0 s' ∨
        FStatePlaced C A ctl uuidTryParse S x (tokenInitPlacedAt ∗ R) s0 s' ∨
        regionOutcome (recordDecryptPlacedSpecT C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  rcases hV with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hfl, hvregs⟩,
    ⟨hrem_ne, hseeds, hrc_len⟩, hclone, heq, hmem⟩
  dsimp only [recVPCPlaced] at hpc
  have hmemcpy_rel := ls_hook_ok_226 (by decide) hmemcpy_sat
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  rw [hsp0] at hsp_bound hmem
  unfold recFramePlaced at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_JF_placedT hmem hL
    (target := decryptTarget (blkPl_197).base ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1)
  apply segDecrypt_of_sepWP_placed hfl (mid := lsmpl.base 131)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  have hsp_bound1 : rootStack ≤
      ((((((((s.writeReg64 (Reg.gpr 2#5) x.remA).writeReg64
              (Reg.gpr 3#5) x.locA).writeReg64
            (Reg.gpr 4#5) x.msgA).writeReg64
          (Reg.gpr 0#5) (s.sp + 1200#64)).writeReg64
        (Reg.gpr 1#5) (s.sp + 3232#64)).writeReg64
      (Reg.gpr 5#5) 2#64).writeReg64
    (Reg.gpr 6#5) 0#64).writeReg64 (Reg.gpr 30#5) ((blkPl_197).base + bv% (1720)) |>.setPC
      (lsmpl.base 131)).sp.toNat := hsp_bound
  segDecrypt_wpp_call_placed htry_rel
    ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
       rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
       msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
       cur := x.cur, rest := x.rest : TryDecryptGhost }) hF1
    (tryDecrypt_onPanic_entails heq (by simp only [wp_norm, arm64_norm, htr]))
  apply SepWPp.exists_elim
  intro G₂
  apply SepWPp.pure_elim
  rintro ⟨⟨hnpan, htr_sf⟩, hdec⟩
  have hmk :
      ({ ret := s.sp + 1200#64, ss := s.sp + 3232#64, G := G₁, st := x.st,
         rem := x.rem, remA := x.remA, loc := x.loc, locA := x.locA,
         msgG := x.msgG, msgA := x.msgA, msg := x.msg, msgType := .whisper,
         cur := x.cur, rest := x.rest : TryDecryptGhost }) = mkTryDecryptGhost s.sp x G₁ := rfl
  rw [hmk] at hnpan hdec ⊢
  rcases hres : ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).1 with e | pt
  · -- Error branch
    dsimp only [decryptTarget, vecResultAt]
    have he_npan : e ≠ .panic := fun h => hnpan (h ▸ hres)
    cases hdup : isDupErr e
    · -- Non-duplicate Error -> FStatePlaced at (blkPl_197).base + 2128#64
      have htag_ne23 : speTag e ≠ speWord 23 := speTag_ne_speWord23_of_not_isDupErr hdup
      have hmodel_err : x.model C S uuidTryParse =
          (.error (.invalidMessage .whisper .decryptionFailed), x.st) := by
        rw [model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl),
          recordError_of_speTag_ne_speWord23 he_npan htag_ne23]
      have hmodel_err1 : (x.model C S uuidTryParse).1 =
          .error (.invalidMessage .whisper .decryptionFailed) := congrArg Prod.fst hmodel_err
      have htag_add2 : speTag e + 2#64 ≠ 0#64 := speTag_add2_ne_zero he_npan
      have htag_ne23' : speTag e ≠ 9223372036854775831#64 := htag_ne23
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 159)
      refine segDecrypt_replace_pre
        (speAt_decomp6 A (utf8 "decrypt") (s.sp + 1200#64) e he_npan) (by sep_focus) ?_
      rw [memRegion_5f0_split_b40 s.sp, memRegion48_eq_words6At (s.sp + 2880#64),
        stackAt_root_split_closure s.sp, errsAt_nil_unfold A s.sp]
      unfold words6At
      segDecrypt_wp_extract_exists
      rename_i u0 u1 u2 u3 u4 u5 w1 w2 w3 w4 w5 H_spe hreassemble
      generalize htag_def : speTag e = tag at htag_add2 htag_ne23' hreassemble ⊢
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_placed hclosure_rel () hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 42)
      segDecrypt_wp_extract_exists
      rename_i htr_cl
      rw [hsp_sf]
      refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3
      segDecrypt_wpp_call_placed hgrow_rel (s.sp + 0x5d8#64, 0#64, 8#64, []) hF3
        (grow_onPanic_entails (by simp only [wp_norm, arm64_norm, htr_cl, htr_sf, htr]))
      apply segDecrypt_of_sepWP_placed hF_sf_2 (mid := (blkPl_197).base + 2128#64)
      segDecrypt_wp_extract_exists
      rename_i p' hp'
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      wp_steps
      rw [hsp_sf_1, hsp_sf]
      refine segDecrypt_replace_pre
        (spe_errsAt_entails A s.sp p' e tag w1 w2 w3 w4 w5 H_spe hp'.2 (hreassemble p'))
        (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_4b0_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (words6_b40_to_memRegion s.sp tag w1 w2 w3 w4 w5) (by sep_focus) ?_
      refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre
        (sessionStateAt_exists_intro A (s.sp + 3232#64) G₂
          ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) (by sep_focus) ?_
      refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF4
      apply segDecrypt_of_sepWP_ret_placed hF4
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro _ hmf
      right
      refine ⟨by dsimp only [recFPCPlaced]; wp_norm_lhs, ?_, hmodel_err1, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, hp'.1, htr_cl, htr_sf, htr],
                hF4,
                by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFramePlaced
        rw [hsp0]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
    · -- Duplicate Error -> JStatePlaced at (blkPl_197).base + 7820#64
      obtain ⟨i, c, rfl⟩ := eq_duplicatedMessage_of_isDupErr hdup
      have hmodel_dup : x.model C S uuidTryParse = (.error (.duplicatedMessage i c), x.st) :=
        model_err_of_tryDecrypt_err C S s.sp x G₁ heq (Prod.ext hres rfl)
      have hmodel_dup1 : (x.model C S uuidTryParse).1 = .error (.duplicatedMessage i c) :=
        congrArg Prod.fst hmodel_dup
      apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 139)
      dsimp only [speAt]
      rw [stackAt_root_split_dropLocal2 s.sp]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF2
      segDecrypt_wpp_call_placed hdrop_rel
        ({ ss := s.sp + 3232#64, G := G₂,
           st := ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 : DropSessionStructureGhost })
        hF2 noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_placed hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i htr_drop
      rw [hsp_sf]
      refine segDecrypt_replace_pre (dropLocal2Stack_to_rootStack s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
      refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hF3 hmf
      left
      refine ⟨by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_dup1]; nofun,
        by simp only [wp_norm, arm64_norm, h_17, hsp0],
        by simp only [wp_norm, arm64_norm, h_18],
        by rw [hmodel_dup1]; dsimp only [recordResultTag, speWord]; wp_norm_lhs, ?_⟩
      · refine ⟨by wp_norm_lhs,
                by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                by simp only [wp_norm, arm64_norm, htr_drop, htr_sf, htr],
                hF3,
                by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
      · unfold recFramePlaced
        rw [hsp0, hmodel_dup1]
        dsimp only [recordResultAt, vecResultAt, speAt]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf
  · -- Ok branch
    dsimp only [decryptTarget, vecResultAt]
    have hmodel_ok : x.model C S uuidTryParse =
        (.ok pt, ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2) :=
      model_ok_of_tryDecrypt_ok C S s.sp x G₁ heq (Prod.ext hres rfl)
    have hmodel_ok1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel_ok]
    have hmodel_ok2 : (x.model C S uuidTryParse).2 =
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 := by rw [hmodel_ok]
    rw [hres] at hdec
    have hrel : x.G.AfterRecordDecrypt G₂ := recordOkRel_of_clone_dec hclone hdec
    apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.ρ "memcpy")
    rw [sessionStateAt_eq_inline_sep_heap A (s.sp + 3232#64) G₂
      ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2,
      memRegion_5f0_split344 s.sp, stackAt_root_split_set s.sp]
    unfold FromRecordCallees.lsLogOff
    segDecrypt_wp_extract_exists
    rename_i bs hbs
    rw [← hbs.1]
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF2
    segDecrypt_wpp_call_placed hmemcpy_rel (s.sp + 1520#64, s.sp + 3232#64, bs) hF2
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_placed hF_sf_1 (mid := lsmpl.base 48)
    segDecrypt_wp_extract_exists
    rename_i hmc
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF3
    segDecrypt_wpp_call_placed hset_rel
      ({ record := s.sp + 288#64, src := s.sp + 1520#64,
         cur := some (x.G, x.st), bs := bs : SetSessionStateGhost }) hF3
      noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_ret_placed hF_sf_2
    segDecrypt_wp_extract_exists
    rename_i htr_set
    wp_steps
    rw [hsp_sf_1, hsp_sf]
    refine segDecrypt_replace_pre
      (sessionStateAt_move_bytes_twice A (s.sp + 3232#64) (s.sp + 1520#64) (s.sp + 312#64)
        G₂ ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hbs.2) (by sep_focus) ?_
    refine segDecrypt_replace_pre (memRegion_5f0_join344 s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (setStack_to_rootStack s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre
      (sessionStateAt_ok_exists_intro A (s.sp + 312#64) x.G G₂
        ((mkTryDecryptGhost s.sp x G₁).model C S uuidTryParse).2 hrel) (by sep_focus) ?_
    refine segDecrypt_replace_pre (errsAt_nil_exists_intro A s.sp) (by sep_focus) ?_
    refine segDecrypt_replace_pre (tapeAfter_tryDecrypt_entails C ctl s.sp x G₁ heq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hF4 hmf
    left
    refine ⟨by dsimp only [recJPCPlaced]; wp_norm_lhs, ?_, by rw [hmodel_ok1]; nofun,
      by simp only [wp_norm, arm64_norm, h_27, h_17, hsp0],
      by simp only [wp_norm, arm64_norm, h_28, h_18],
      by rw [hmodel_ok1]; dsimp only [recordResultTag, okTagVec]; wp_norm_lhs, ?_⟩
    · refine ⟨by wp_norm_lhs,
              by simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp0],
              by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_2, hsp_sf_1, hsp_sf]; exact hsp_align,
              by simp only [wp_norm, arm64_norm, hcs_sf_2, hcs_sf_1, hcs_sf]; exact hx29,
              by simp only [wp_norm, arm64_norm, htr_set, hmc.2, htr_sf, htr],
              hF4,
              by simp only [wp_norm, arm64_norm, hvregs_3, hvregs_2, hvregs_1, hvregs]⟩
    · unfold recFramePlaced FromRecordCallees.lsLogOff
      rw [hsp0, hmodel_ok1, hmodel_ok2]
      dsimp only [recordResultAt, vecResultAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

theorem recordDecrypt_placed_region_reachesT [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hcc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
      (withLsCodeLoaded lsmpl (FromRecordChainClone.chainCloneSpec A)))
    (hsc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
      (withLsCodeLoaded lsmpl (FromRecordChainClone.senderChainCloneSpec A)))
    (hdrop1 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A)))
    (hTry : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 131)
      (tryDecryptPlacedSpecT C A ctl uuidTryParse S))
    (hset : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (FromRecordCallees.setSessionStateSpec A)))
    (hdrop2 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)))
    (hgrow : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)))
    (hclosure : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159)
      (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec))
    (hclone : SegClonePlacedSpec C A ctl uuidTryParse S H)
    (htail : SegTailPlacedSpec C A ctl uuidTryParse S H)
    (hexit : SegExitPlacedSpec C A ctl uuidTryParse S H) :
    ∀ (x : RecordDecryptGhost) (R : SepProp) (s0 : State),
      s0.pc = recEntryPlaced → s0.status = .Running →
      (s0.mem ⊨ (recordDecryptPlacedSpecT C A ctl uuidTryParse S).pre x s0 ∗ R) →
      region_reaches ((blkPC_197).rebase (blkPl_197).base H)
        (recordDecryptPlacedSpecT C A ctl uuidTryParse S) recExitPlaced x R s0 s0 := by
  have htd := subroutine_ok_recordTryDecryptPlacedSpecT hTry
  intro x R s0 hpc hst hpre hL
  dsimp only [recordDecryptPlacedSpecT] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  have hpre' : s0.mem ⊨ (recordDecryptPlacedSpec C A ctl uuidTryParse S).pre x s0 ∗ (tokenInitPlacedAt ∗ R) := by
    have heq : (tokenInitPlacedAt ∗ (recordDecryptPlacedSpec C A ctl uuidTryParse S).pre x s0) ∗ R =
        (recordDecryptPlacedSpec C A ctl uuidTryParse S).pre x s0 ∗ (tokenInitPlacedAt ∗ R) := by ac_rfl
    exact heq ▸ hpre
  have hstk := rootStack_le_of_recordPlacedPre hpre'
  have hJ : ∀ s, JStatePlaced C A ctl uuidTryParse S x (tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_197).rebase (blkPl_197).base H)
        (recordDecryptPlacedSpecT C A ctl uuidTryParse S) recExitPlaced x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hout⟩ := hexit hdealloc x (tokenInitPlacedAt ∗ R) s0 s hs hLs
    exact ⟨s', hst', regionOutcome_placed_of_tokenFrame hout⟩
  have hF : ∀ s, FStatePlaced C A ctl uuidTryParse S x (tokenInitPlacedAt ∗ R) s0 s →
      region_reaches ((blkPC_197).rebase (blkPl_197).base H)
        (recordDecryptPlacedSpecT C A ctl uuidTryParse S) recExitPlaced x R s0 s := by
    intro s hs hLs
    obtain ⟨s', hst', hj | hout⟩ := htail hshim halloc hpanic hdrop2 x (tokenInitPlacedAt ∗ R) s0 s hs hLs
    · exact region_reaches_steps hst' (hJ s' hj) hLs
    · exact ⟨s', hst', regionOutcome_placed_of_tokenFrame hout⟩
  obtain ⟨s', hst', ⟨G₁, hv⟩ | ⟨G₁, hm⟩ | hout⟩ :=
    hclone hshim halloc hdealloc hmemcpy hpanic hcc hsc hdrop1 x (tokenInitPlacedAt ∗ R) s0 hpc hst hpre' hL
  · obtain ⟨s'', hst'', hj | hf | hout⟩ :=
      segDecrypt_placed_okT hmemcpy htd hset hdrop2 hgrow hclosure x G₁ R s0 s' hQ hv
        hstk (hst'.codeLoaded hL)
    · exact region_reaches_steps (hst'.trans hst'') (hJ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', hf | hout⟩ :=
      segMismatch_placed_ok hgrow hclosure x G₁ (tokenInitPlacedAt ∗ R) s0 s' hm (hst'.codeLoaded hL)
    · exact region_reaches_steps (hst'.trans hst'') (hF s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', regionOutcome_placed_of_tokenFrame hout⟩
  · exact ⟨s', hst', regionOutcome_placed_of_tokenFrame hout⟩

/-- Block `197` (`try_decrypt_from_record` region) meets `recordDecryptPlacedSpecT` for any `S` whose `try_decrypt_with_state` meets `tryDecryptPlacedSpecT`. -/
theorem recordDecrypt_placed_region_okT [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hcc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
      (withLsCodeLoaded lsmpl (FromRecordChainClone.chainCloneSpec A)))
    (hsc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
      (withLsCodeLoaded lsmpl (FromRecordChainClone.senderChainCloneSpec A)))
    (hdrop1 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A)))
    (hTry : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 131)
      (tryDecryptPlacedSpecT C A ctl uuidTryParse S))
    (hset : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (FromRecordCallees.setSessionStateSpec A)))
    (hdrop2 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)))
    (hgrow : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)))
    (hclosure : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159)
      (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec))
    (hclone : SegClonePlacedSpec C A ctl uuidTryParse S H)
    (htail : SegTailPlacedSpec C A ctl uuidTryParse S H)
    (hexit : SegExitPlacedSpec C A ctl uuidTryParse S H) :
    region_ok ((blkPC_197).rebase (blkPl_197).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecT C A ctl uuidTryParse S) :=
  region_ok_of_reaches (recordDecrypt_placed_region_reachesT C A ctl S H
    hshim halloc hdealloc hmemcpy hpanic hcc hsc hdrop1 hTry hset hdrop2 hgrow hclosure
    hclone htail hexit)

/-- `recordDecrypt_placed_region_okT` with `calleeSavedVRegs` preservation (`Spec.withVRegs`). -/
theorem recordDecrypt_placed_region_vregs_okT [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hcc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
      (withLsCodeLoaded lsmpl (FromRecordChainClone.chainCloneSpec A)))
    (hsc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
      (withLsCodeLoaded lsmpl (FromRecordChainClone.senderChainCloneSpec A)))
    (hdrop1 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal1Spec A)))
    (hTry : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 131)
      (tryDecryptPlacedSpecT C A ctl uuidTryParse S))
    (hset : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (FromRecordCallees.setSessionStateSpec A)))
    (hdrop2 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139)
      (withLsCodeLoaded lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A)))
    (hgrow : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (FromRecordCallees.growOneSpeSpec A)))
    (hclosure : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159)
      (withLsCodeLoaded lsmpl FromRecordCallees.logClosurePlacedSpec))
    (hclone : SegClonePlacedSpec C A ctl uuidTryParse S H)
    (htail : SegTailPlacedSpec C A ctl uuidTryParse S H)
    (hexit : SegExitPlacedSpec C A ctl uuidTryParse S H) :
    region_ok ((blkPC_197).rebase (blkPl_197).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpecT C A ctl uuidTryParse S).withVRegs := by
  intro x R s0 hpc hst hpre hL
  obtain ⟨sf, hsteps, ⟨hpc', hrun', hvregs, hpost⟩ | hpan⟩ :=
    recordDecrypt_placed_region_reachesT C A ctl S H
      hshim halloc hdealloc hmemcpy hpanic hcc hsc hdrop1 hTry hset hdrop2 hgrow hclosure
      hclone htail hexit x R s0 hpc hst hpre hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc', hrun', ?_⟩⟩
    dsimp only [Spec.withVRegs]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvregs, hpost⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

end CryptoVerification.LibsignalSpqrV1.M4
