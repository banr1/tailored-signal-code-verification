/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegLoadPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegPostNonePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegRegionSomePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegWritePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `MessageDecrypt` Segments: `SegLoad`, `SegPostNone`, `SegRegionSome`, and `SegWrite`

Proves relocatable (`[LibsignalPlacement]`) `segLoadVX_placed_ok` (`+0x0 → +0x8c`),
`segPostNoneVX_placed_ok` (`+0x1f50 → +0x22a8`), `segRegionSomeV_placed_ok` (`+0x1a8 → +0x1f50`),
and `segWriteVX_placed_ok` (`+0x24d4 → ret`) on `lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced withStoresDecPlacedSpecVX withStoresDecPlacedSpecV_eq_VX DecSegVXPlaced DecSegVPlaced_eq_VX decSegVXPlaced_chain
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `segLoadVX_placed_ok` (`+0x0 → +0x8c`) -/

section SegLoadPlaced
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad hiding messageDecrypt_of_sepWP_lscro messageDecrypt_call_panic_then_wp_lscro messageDecrypt_call_panic_then_wpp_lscro loadShim_onPanic_entailsVPlaced decSegVPlaced_of_sepWPp segLoadVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad

set_option maxHeartbeats 1600000 in
theorem segLoadVX_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (x : DecryptGhost) (R : SepProp) (s0 : State)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s0)
    (hpc : s0.pc = wsEntryPCPlaced)
    (hrun : s0.status = .Running)
    (hal : s0.spAligned = true)
    (hpre : s0.mem ⊨ (withStoresDecPlacedSpecVX
      C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope Extra).pre x s0 ∗ R) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s0
      (fun s' => ∃ ans, LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s') := by
  obtain ⟨hcrl0, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [withStoresDecPlacedSpecVX] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx4, hx6, hx8, hsp_le, haddr_ss, _haddr_id⟩, hmem⟩
  simp only [← sepConj_assoc] at hmem
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx4 hx6 hx8
  unfold wsEntryPCPlaced at hpc
  have hshim := subroutine_ok_withStepsPost
    (hH.kit.loadShim (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hpoll := hH.kit.loadPoll (callerProg := lsProg_463 H) (callerBlk := 463) (by decide)
  rw [BitVec.zero_add] at hshim hpoll
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s0 :=
    (hfs.fsAt (evs := []) (List.append_nil _).symm (fun _ => NoFsEv.nil)).mono (fun _ h => h.1) id
  have hsp_lt := s0.sp.isLt
  have hn_v : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    omega
  have hsp_base : wsStack ≤ s0.sp.toNat := Nat.le_trans (wsStack_le_V kit ikit) hsp_le
  apply decSegVXPlaced_of_sepWPp (target := loadPolledPCPlaced) hmem
  unfold loadPolledPCPlaced
  dsimp only [lsProg_463] at hshim hpoll hfsAt ⊢
  apply CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad.messageDecrypt_of_sepWP_lscro hcrl0 (mid := kit.loadShimOff)
  rw [stackAt_wsStackV_split kit ikit s0.sp hsp_le, memRegion_0xe80_split (s0.sp - 0xee0#64),
    stack_wsCalleeV_shim kit ikit (s0.sp - 0xee0#64) hn_v]
  cells_unfold
  unfold decVtablesAtV decLoadVtableAtV decStoreVtableAtV decTrustVtableAtV decSaveVtableAtV
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply SepWP.exists_elim; intro _)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  apply (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad.messageDecrypt_call_panic_then_wpp_lscro hshim (x := ⟨s0.readReg64 (Reg.gpr 3#5), x.remA⟩) hF1)
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [State.spAligned, wp_norm, arm64_norm]; exact hal
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [withStepsPost, Arm64.ReachesOutcome.withStepsPost, StoreKit.withLsRoCl, kitLoadShimSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hF1, ?_⟩
    simp only [sepConj_assoc, wp_norm, arm64_norm, hx1] at _hmR' ⊢
    arm64_sep_close
  · intro _; exact loadShim_onPanic_entailsVX_placed (by wp_norm_lhs)
  · intro _ _; rfl
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf hF2
  dsimp only [withStepsPost, Arm64.ReachesOutcome.withStepsPost, StoreKit.withLsRoCl, kitLoadShimSpec]
  simp only [wp_norm, arm64_norm] at hpc_sf hsp_sf
  apply CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad.messageDecrypt_of_sepWP_lscro hF2 (mid := kit.loadPollOff)
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, _hcrl_sf, hx1_sf, hbox_ne, hbox_mod, htr_sf⟩
  have henv : kit.envOk sf.fs.files :=
    (hfsAt.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfsAt
  simp only [wp_norm, arm64_norm] at hx1_sf
  apply SepWP.fold (Entails.of_eq (stack_wsCalleeV_shim_to_poll kit ikit (s0.sp - 0xee0#64) hn_v)) (by sep_focus)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF3
  apply (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad.messageDecrypt_call_panic_then_wp_lscro hpoll
    (x := (⟨sf.readReg64 (Reg.gpr 0#5), (s0.sp - 0xee0#64) + 0x5f0#64, x.remA, x.rem⟩,
      s0.readReg64 (Reg.gpr 3#5), st0)) hF3)
  · wp_norm_lhs
  · wp_norm_lhs
  · simp only [State.spAligned, wp_norm, arm64_norm, hsp_sf]; exact hal
  · wp_norm_lhs
  · intro _R' _hmR'
    dsimp only [StoreKit.withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hF3, ?_⟩
    refine withEnvPre_pre_intro (by simp only [arm64_norm]; exact henv) ?_
    dsimp only [StoreKit.kitLoadPollPlacedSpecS]
    simp only [sepConj_assoc, wp_norm, arm64_norm, hsp_sf, haddr_ss, and_true] at _hmR' ⊢
    arm64_sep_close
  · intro _; exact loadShim_onPanic_entailsVX_placed (by simp only [wp_norm, arm64_norm]; exact htr_sf)
  · intro _ _; rfl
  intro sf1 hpc_sf1 hrun_sf1 hsp_sf1 hcs_sf1
  dsimp only [StoreKit.withLsRoCl, withEnvPre, StoreKit.kitLoadPollPlacedSpecSE, StoreKit.kitLoadPollPlacedSpecS]
  simp only [wp_norm, arm64_norm, hsp_sf] at hpc_sf1 hsp_sf1
  wp_simp_pre [wp_norm, arm64_norm, hsp_sf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w
  apply SepWP.pure_elim; rintro ⟨_hcrl_sf1, hloadRel, htr_sf1⟩
  apply SepWP.fold (wsSavedRegs_fold s0.sp s0) (by sep_focus)
  apply SepWP.fold (fold_sp0 (s0.sp - 0xee0#64) 0#64) (by sep_focus)
  apply SepWP.fold (fold_words8 (s0.sp - 0xee0#64 + 0xa0#64)
    x.msgA x.remA x.locA (s0.readReg64 (Reg.gpr 3#5))
    kit.ss_vt (s0.readReg64 (Reg.gpr 5#5))
    ikit.id_vt (s0.sp - 113#64)) (by sep_focus)
  apply SepWP.fold (fold_2c8 (s0.sp - 0xee0#64) 0#8) (by sep_focus)
  apply SepWP.fold (fold_2e0 (s0.sp - 0xee0#64) _ _ 0#64) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (stack_wsCalleeV_poll_back kit ikit (s0.sp - 0xee0#64) hn_v)) (by sep_focus)
  have hsplit_extra := wsCalleeStack_split_extra_placed kit ikit st0 ist0 s0 hsp_le
  dsimp only [Reg.x3, Reg.x5] at hsplit_extra
  apply SepWP.fold hsplit_extra (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF4 hmf
  refine ⟨⟨w, .ok false, .ok .newOrUnchanged, .ok ()⟩, ?_⟩
  refine ⟨?_, ?_, hsp_base, ?_, hloadRel, ?_, ?_⟩
  · wp_norm_lhs
  · simp only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs_sf hcs_sf1
    refine ⟨by wp_norm_lhs,
            by simp only [wp_norm, arm64_norm, hsp_sf1],
            hal,
            by simp only [State.spAligned, wp_norm, arm64_norm, hsp_sf1]; exact hal,
            by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf],
            by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf],
            hF4,
            by simp only [wp_norm, arm64_norm, hcs_sf1, hcs_sf]⟩
  · simp only [CalleeSavedPreserved, wp_norm, arm64_norm] at hcs_sf1
    simpa only [Reg.x19, wp_norm, arm64_norm, hsp_sf] using hcs_sf1.1
  · rw [htr_sf1, htr_sf]
  · dsimp only [LoadPolledStateVPlaced, wsFixedVPlaced, wsArgCellsV, decVtablesAtV,
      decLoadVtableAtV, decStoreVtableAtV, decTrustVtableAtV, decSaveVtableAtV,
      wsEnvPlaced, wsMsgCells, Reg.x3, Reg.x5] at hmf ⊢
    simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, BitVec.add_assoc] at hmf ⊢
    arm64_sep_close

end SegLoadPlaced
/-! ## `segPostNoneVX_placed_ok` (`+0x1f50 → +0x22a8`) -/

section SegPostNonePlaced
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone hiding segPostNoneVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone

set_option maxHeartbeats 800000 in
theorem segPostNoneVX_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State)
    (hPN : PostNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x false R s0 s') := by
  intro hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, hcrl, hvregs⟩,
    hx26, hx28, rec, prevCap, prevPtr, hload, hscope, hcur, htrace, hmem⟩ := hPN
  have hpc' : s.pc = (blkPl_463).base + 8016#64 := hpc
  simp only [wp_norm, arm64_norm] at hx29 hx27 hx26 hx28
  have ⟨hmod, hdraws⟩ := model_of_load_current_none C S x ans rec hload hcur
  let sp := s0.sp - 0xee0#64
  let R' := decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R
  have hmem_grp :
      s.mem ⊨
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336) ∗
        (recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
          (memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
            stackAt sp rootStack ∗ A.pool ∗ wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ R')) := by
    dsimp only [sp, R']
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  obtain ⟨pad, cap, ptr, hpad_len, hmem⟩ := recordResultAt_decryptionFailed_sat hmem_grp
  clear hmem_grp
  let w21 := cap.extractLsb' 0 32
  let bs := unpack32 (cap.extractLsb' 32 32) ++ unpack64 ptr ++
    unpack64 (BitVec.ofNat 64 decryptionFailedStr.length) ++ [msgTypeByte .whisper] ++ pad
  have hbs_len : bs.length = 36 := by
    simp [bs, hpad_len]
  obtain ⟨w0, w1, w2, w3, w4, hbs_eq⟩ := exists_split_36_regionErr hbs_len
  have hslot_orig :
      (((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗
        ((sp + 0x4b0#64 + 8#64) ↦₆₄ cap) ∗
        ((sp + 0x4b0#64 + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((sp + 0x4b0#64 + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
        ((sp + 0x4b0#64 + 32#64) ↦₈ msgTypeByte .whisper) ∗
        ((sp + 0x4b0#64 + 33#64) ↦ₛ pad) ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) =
      (((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗
        ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) := by
    have h8 := pointsTo64_split32 (sp + 0x4b0#64 + 8#64) cap
    have h36 := decryptionFailed_slot_36_eq (sp + 0x4b0#64) cap ptr .whisper pad
    have h36_te := pointsToBytes_36_regionErr_eq (sp + 0x4b0#64 + 12#64) w0 w1 w2 w3 w4
    dsimp only [bs] at hbs_eq
    rw [hbs_eq, h36_te] at h36
    rw [h8]
    simp only [w21, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h36 ⊢
    have h36' := congrArg (· ∗ CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) h36.symm
    simp only [sepConj_assoc] at h36'
    rw [h36']
  have h300_split :
      memRegion (sp + 0x300#64) 0x1b0 =
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4a4#64) 0xc := by
    rw [memRegion_split (sp + 0x300#64) 0x190 0x20 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xc (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h4e0_split :
      memRegion (sp + 0x4e0#64) 0x920 =
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x580#64) 0x24 ∗
          memRegion (sp + 0x5a4#64) 0x85c := by
    rw [memRegion_split (sp + 0x4e0#64) 0xa0 0x880 (by decide),
        memRegion_split (sp + 0x4e0#64 + 0xa0#64) 0x24 0x85c (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hmem_act : s.mem ⊨
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24) ∗
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr ∗
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗ A.pool ∗
        wsFixedVPlaced kit ikit x s0 sp ∗
        ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
        memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
        memRegion x.ret 48 ∗ R') := by
    have hws_eq :
        wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr =
          wsFixedVPlaced kit ikit x s0 sp ∗
            ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x1b0 ∗
            memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
            memRegion x.ret 48 := by
      unfold wsRegionFrameVPlaced wsFixedVPlaced
      dsimp only [sp]
      ac_rfl
    rw [hws_eq, hslot_orig, h300_split, h4e0_split] at hmem
    dsimp only [sp] at hmem ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  have hwp : SepWP (lsProg_463 H) (errJoinPCPlaced false) s
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24)
      (fun sf Pf =>
        (Pf ⊢ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4b0#64) 0x30 ∗
          ((sp + 0x580#64) ↦ₛ bs)) ∧
        sf.sp = s.sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x27 = x.ret ∧
        sf.readReg64 .x26 = sp + 0xa0#64 ∧ sf.readReg64 .x28 = speWord 24 ∧
        resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = w21 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0) := by
    unfold errJoinPCPlaced
    rw [ite_eq_right_iff.mpr nofun]
    dsimp only [lsProg_463]
    wp_conv_pre => rw [scratch20_split sp, dst36_split sp]
    dsimp only [sp]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply SepWP.exists_elim; intro _)
    have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
    dsimp only [recordResultTag, speWord] at hx28
    wp_steps
    apply SepWP.fold (scratch20_fold (s0.sp - 0xee0#64) w0 w1 w2) (by sep_focus)
    apply SepWP.fold (slot48_fold_memRegion (s0.sp - 0xee0#64) (speWord 24) w21 w0 w1 w2 w3 w4) (by sep_focus)
    apply SepWP.fold (dst36_fold (s0.sp - 0xee0#64) w0 w1 w2 w3 w4 hbs_eq) (by sep_focus)
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    refine ⟨?_, rfl, hal, rfl, ?_, ?_, ?_, ?_, ?_, hvregs⟩
    · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
      exact Entails.of_eq (by ac_rfl)
    · wp_norm_lhs
    · wp_norm_lhs
    · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
      wp_norm_lhs
    · wp_norm_lhs
    · simp only [wp_norm, arm64_norm]
      exact resWord1_ubfm_eq w21
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_pf, hsp_sf, hal_sf, htr_sf,
    hx29_sf, hx27_sf, hx26_sf, hx28_sf, hres_w1, hvregs_sf⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem_act hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hcrl_sf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
  refine ⟨sf, hsteps, Or.inl ?_⟩
  have hmf1 := Satisfies.mono (sepConj_mono_left hent_pf) hmf
  clear hmf hent_pf
  refine ⟨hpc_sf, ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf, hx27_sf, hcrl_sf, hvregs_sf⟩,
    hx26_sf, ?_, ans, none, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx28_sf]; decide
  · intro h; rw [hmod] at h; cases h
  · intro p h; rw [hmod] at h; cases h
  · intro r hr; rw [hload] at hr; cases hr; exact hscope
  · rw [hmod]; exact ⟨hload ▸ hscope.2, trivial⟩
  · rw [hmod]; trivial
  · rw [htr_sf, htrace, hmod]; simp
  · have hstaged :
        ((sp + 0x580#64) ↦ₛ bs) ∗ CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr ⊢
          StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
            (x.model C S uuidTryParse ans).1 := by
      unfold StagedRes
      refine Entails.sepExists_right bs
        (Entails.sepExists_right (CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) ?_)
      refine Entails.pure_right ⟨hbs_len, fun r => ?_⟩ (Entails.refl _)
      rw [hmod, hx28_sf, hres_w1]
      dsimp only [apiDecResultAt, recordResultAt]
      rw [vecU8_eq_exists_buf A (r + 8#64) decryptionFailedStr]
      have h36 := decryptionFailed_slot_36_eq r cap ptr .whisper pad
      have h8 := pointsTo64_split32 (r + 8#64) cap
      have hpad_mem : ((r + 33#64) ↦ₛ pad) ⊢ memRegion (r + 33#64) 15 := by
        have h := pointsToBytes_entails_memRegion (r + 33#64) pad
        rwa [hpad_len] at h
      dsimp only [bs]
      rw [h36]
      refine Entails.trans ?_
        (sepConj_mono_right
          (sepConj_mono_left
            (Entails.sepExists_right cap
              (Entails.sepExists_right ptr (Entails.refl _)))))
      rw [h8]
      simp only [w21, BitVec.add_assoc, BitVec.reduceAdd]
      have hreord_r :
          (r ↦₆₄ speWord 24) ∗ ((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
            (((r + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
              ((r + 16#64) ↦₆₄ ptr) ∗
              ((r + 24#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
              ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
              ((r + 33#64) ↦ₛ pad)) ∗
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr =
          ((r ↦₆₄ speWord 24) ∗
            ((((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗ ((r + 12#64) ↦₃₂ cap.extractLsb' 32 32)) ∗
              ((r + 16#64) ↦₆₄ ptr) ∗
              ((r + 24#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
              CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) ∗
            ((r + 32#64) ↦₈ msgTypeByte .whisper)) ∗
          ((r + 33#64) ↦ₛ pad) := by
        ac_rfl
      rw [hreord_r]
      refine Entails.trans (sepConj_mono_right hpad_mem) ?_
      exact Entails.of_eq (by ac_rfl)
    have h290_split :
        memRegion (sp + 0x290#64) 0x38 =
          memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20 := by
      rw [memRegion_split (sp + 0x290#64) 24 0x20 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h300_join :
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
          memRegion (sp + 0x4e0#64) 0xa0 =
        memRegion (sp + 0x300#64) 0x280 := by
      rw [memRegion_split (sp + 0x300#64) 0x190 0xf0 (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xdc (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64) 0xc 0xd0 (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64) 0x30 0xa0 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hcomb :
        (memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4b0#64) 0x30 ∗
          ((sp + 0x580#64) ↦ₛ bs)) ∗
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
          CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr ∗
          memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp rootStack ∗ A.pool ∗
          wsFixedVPlaced kit ikit x s0 sp ∗
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
          memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
          memRegion x.ret 48 ∗ R') ⊢
        wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
          droppableRecordAt A (sp + 0x120#64) none ∗
          memRegion (sp + 0x290#64) 24 ∗
          StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
            (x.model C S uuidTryParse ans).1 ∗
          memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := by
      have hwsEnv_eq :
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
            (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
            A.pool =
          wsEnvPlaced A x sp := by
        unfold wsEnvPlaced
        rw [stackAt_root_join_wsCallee sp]
      rw [hdraws, h290_split]
      have hreord_lhs :
          (memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4b0#64) 0x30 ∗
            ((sp + 0x580#64) ↦ₛ bs)) ∗
          (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
            ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
            ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr ∗
            memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsFixedVPlaced kit ikit x s0 sp ∗
            ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            (memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20) ∗
            memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
            memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
            memRegion x.ret 48 ∗ R') =
          ((((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
              ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
              ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336) ∗
            (((sp + 0x580#64) ↦ₛ bs) ∗ CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) ∗
            cliTapeAt ctl x.cur x.rest ∗
            (wsFixedVPlaced kit ikit x s0 sp ∗
              (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
                protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
                (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
                A.pool) ∗
              wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗
              memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
              (memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
                memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
                memRegion (sp + 0x4e0#64) 0xa0) ∗
              memRegion (sp + 0x5a4#64) 0x85c ∗ memRegion x.ret 48 ∗ R')) := by
        ac_rfl
      rw [hreord_lhs, hwsEnv_eq, h300_join]
      refine Entails.trans
        (sepConj_mono (record_none_entails_droppable A sp prevCap prevPtr)
          (sepConj_mono hstaged
            (sepConj_mono_left (cliTapeAt_entails_cliTapeAfter_zero ctl x.cur x.rest)))) ?_
      exact Entails.of_eq (by ac_rfl)
    have hfin := Satisfies.mono hcomb hmf1
    rw [hmod] at hfin ⊢
    exact hfin

end SegPostNonePlaced
/-! ## `segRegionSomeV_placed_ok` (`+0x1a8 → +0x1f50`) -/

section SegRegionSomePlaced
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome hiding post_meta_extract_placed segRegionSomeVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome

theorem segRegionSomeV_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (Q : List (BitVec 8) → Prop)
    (hreg : region_ok (lsProg_463 H)
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec
        C A ctl uuidTryParse S).withVRegs.restrictPre (Q ·.st.pqRatchetState)))
    (hQ : ScopePq kit st0 Scope Q)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hRS : RegionSomeStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope
      (fun x answers => x.recvPanics S answers) x R s0 s
      (fun s' => PostSomeStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s') := by
  intro hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hcrl, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg := wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
    decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R
  have hmem_rg : s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.pre x_rg s ∗ R_rg := by
    dsimp only [x_rg, R_rg, Spec.withVRegs]
    simpa only [sepConj_assoc] using hmem
  have hmemQ : s.mem ⊨
      ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre (Q ·.st.pqRatchetState)).pre
        x_rg s ∗ R_rg :=
    Spec.satisfies_restrictPre.mpr ⟨hQ x.rem.val rec ses hscope hcur, hmem_rg⟩
  obtain ⟨sf, hsteps, hout⟩ := hreg x_rg R_rg s hpc hrun hmemQ hL
  try dsimp only [Spec.restrictPre] at hout
  rcases hout with ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.withVRegs] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ := post_meta_extract_placed hmf
    have hcrl_sf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    have hal_sf : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      exact hal
    have hmeta_sf : wsMetaPlaced x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29,
        hx27_sf, hcrl_sf, hvregs_sf.trans hvregs⟩
    refine ⟨hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr, hsp, htrace,
      hload, hscope, hcur, hw0, ?_⟩
    dsimp only [x_rg, R_rg] at hmf
    simpa only [sepConj_assoc] using hmf
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.withVRegs, CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec, withStoresDecPlacedSpecVX,
      StoreKit.withLsCodeRoLoaded, R_rg] at hmf ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    rcases hmf with ⟨⟨hdisj, hpref⟩, hmf⟩
    have hload_pref : s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: sf.trace := by
      rwa [← htrace]
    have hs0_pref : s0.trace <+: sf.trace :=
      (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
    have hpan_pure :
        s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidTryParse answers).1 = .error .panic ∨ x.recvPanics S answers)) := by
      refine ⟨hs0_pref, ?_⟩
      rcases hdisj with hmod_pan | hrecv_pan | halloc
      · exact Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl
          (model_panic_of_region_panic C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩
      · exact Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inr
          (recvPanics_of_region_recvPanics S x ans rec ses G prevPtr hload hcur hrecv_pan)⟩
      · exact Or.inl (allocFailedIn_of_load_prefix htrace hpref halloc)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗ (wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
        decStoreExtraPlaced kit ikit st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

end SegRegionSomePlaced
/-! ## `segWriteVX_placed_ok` (`+0x24d4 → ret`) -/

section SegWritePlaced
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegWrite hiding segWriteVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegWrite

private theorem argMsgCellsV_entails_memRegion_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) :
    wsMsgCells x sp ∗ wsArgCellsV kit ikit x s0 sp ⊢ memRegion (sp + 0xe0#64) 0x40 := by
  unfold wsMsgCells wsArgCellsV
  have hreord :
      (((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA)) ∗
      (((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
       ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
       ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64))) =
      ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
      ((sp + 0xf0#64) ↦₆₄ x.locA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
      ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
      ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) := by
    ac_rfl
  rw [hreord, ProofLib.memRegion_cells (sp + 0xe0#64) 8 (by decide)]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
    (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
      (Entails.sepExists_right _ (sepConj_mono_right (Entails.sepExists_right _ (sepConj_mono_right
        (Entails.sepExists_right _ (sepConj_mono_right
          (Entails.sepExists_right _ (Entails.refl _)))))))))))))))

set_option maxHeartbeats 800000 in
theorem segWriteVX_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (hRF : ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (fun _ => False) := by
  intro hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, _hcrl, hvregs⟩,
    ans, hno_pan, hscope, hcalls, hid_calls, htrace, hmem⟩ := hRF
  unfold resultFinalPCPlaced at hpc
  simp only [wp_norm, arm64_norm] at hx29 hx27
  dsimp only [StagedRes] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_pure_left_comm, satisfies_pure_sepConj, sepConj_assoc] at hmem
  obtain ⟨bs, F, ⟨hbs_len, hres_ent⟩, hmem⟩ := hmem
  obtain ⟨w0, w1, w2, w3, w4, hbs_eq⟩ := exists_split_36 hbs_len
  let sp := s0.sp - 0xee0#64
  let stf := kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2
  let istf := ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2
  have hmem_act : s.mem ⊨
      (((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x300#64 + 8#64) ↦₆₄ w1) ∗
       ((sp + 0x300#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x300#64 + 24#64) ↦₆₄ w3) ∗
       ((sp + 0x300#64 + 32#64) ↦₃₂ w4) ∗ memRegion x.ret 48 ∗ wsSavedRegs s0.sp s0) ∗
      (wsArgCellsV kit ikit x s0 sp ∗ wsMsgCells x sp ∗ decVtablesAtV kit ikit ∗
       memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
       memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
       wsEnvPlaced A x sp ∗ F ∗
       memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
       memRegion (sp + 0x324#64) 0xadc ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
       decStoreExtraPlaced kit ikit stf istf s0 ∗ R) := by
    rw [hbs_eq, pointsToBytes_36_eq] at hmem
    dsimp only [wsFixedVPlaced, sp, stf, istf] at hmem ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  have hwp : SepWP (lsProg_463 H) (s0.readReg64 .x30) s
      (((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x300#64 + 8#64) ↦₆₄ w1) ∗
       ((sp + 0x300#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x300#64 + 24#64) ↦₆₄ w3) ∗
       ((sp + 0x300#64 + 32#64) ↦₃₂ w4) ∗ memRegion x.ret 48 ∗ wsSavedRegs s0.sp s0)
      (fun sf Pf =>
        (Pf ⊢ memRegion (sp + 0x300#64) 0x24 ∗
          ((x.ret ↦₆₄ s.readReg64 .x28) ∗
           ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
           ((x.ret + 12#64) ↦ₛ bs)) ∗
          memRegion (s0.sp - 96#64) 96) ∧
        sf.sp = s0.sp ∧ sf.trace = s.trace ∧
        CalleeSavedPreserved s0 sf) := by
    dsimp only [lsProg_463]
    rw [memRegion_48_sret_split x.ret]
    unfold wsSavedRegs
    dsimp only [sp]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply SepWP.exists_elim; intro _)
    have hal_s0 : (s0.sp &&& 15#64 == 0#64) = true := hal0
    have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
    have hal_sub96 : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
      ProofLib.spAligned_sub s0.sp 96 hal0 (by decide)
    wp_steps
    rw [bfm_24_23_eq_resWord1]
    apply SepWP.fold (staged36_entails_memRegion (s0.sp - 0xee0#64) w0 w1 w2 w3 w4) (by sep_focus)
    apply SepWP.fold (sret_36_fold x.ret w0 w1 w2 w3 w4 hbs_eq) (by sep_focus)
    apply SepWP.fold (savedRegs_entails_cells12 s0.sp s0) (by sep_focus)
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, Reg.x20, Reg.x21, Reg.x28]
      exact Entails.of_eq (by ac_rfl)
    · wp_norm_lhs
    · simp only [CalleeSavedPreserved, wp_norm, arm64_norm, hvregs]
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_pf, hsp_sf, htr_sf, hcs_sf⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem_act hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, Or.inr (Or.inl ⟨⟨hpc_sf, hsp_sf, hrun_sf⟩, ⟨hsp_sf, hcs_sf⟩, ?_⟩)⟩
  have hmf1 := Satisfies.mono (sepConj_mono_left hent_pf) hmf
  clear hmf hent_pf
  dsimp only [withStoresDecPlacedSpecVX, StoreKit.withLsCodeRoLoaded]
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨ans, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hno_pan, hscope, hcalls, hid_calls, htr_sf.trans htrace⟩, ?_⟩
  have hcomb :
      (memRegion (sp + 0x300#64) 0x24 ∗
        ((x.ret ↦₆₄ s.readReg64 .x28) ∗
         ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
         ((x.ret + 12#64) ↦ₛ bs)) ∗
        memRegion (s0.sp - 96#64) 96) ∗
      (wsArgCellsV kit ikit x s0 sp ∗ wsMsgCells x sp ∗ decVtablesAtV kit ikit ∗
       memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
       memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
       wsEnvPlaced A x sp ∗ F ∗
       memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
       memRegion (sp + 0x324#64) 0xadc ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
       decStoreExtraPlaced kit ikit stf istf s0 ∗ R) ⊢
      (kit.storeAt (s0.readReg64 .x3) stf ∗
       ikit.identityAt (s0.readReg64 .x5) istf ∗
       apiDecResultAt A x.ret (x.model C S uuidTryParse ans).1 ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
       FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ stackAt s0.sp (wsStackV kit ikit) ∗ A.pool) ∗ R := by
    unfold wsEnvPlaced
    have hreord :
        (memRegion (sp + 0x300#64) 0x24 ∗
          ((x.ret ↦₆₄ s.readReg64 .x28) ∗
           ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
           ((x.ret + 12#64) ↦ₛ bs)) ∗
          memRegion (s0.sp - 96#64) 96) ∗
        (wsArgCellsV kit ikit x s0 sp ∗ wsMsgCells x sp ∗ decVtablesAtV kit ikit ∗
         memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
         memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
         (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ stackAt sp wsCalleeStack ∗ A.pool) ∗ F ∗
         memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
         memRegion (sp + 0x324#64) 0xadc ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
         decStoreExtraPlaced kit ikit stf istf s0 ∗ R) =
        (((x.ret ↦₆₄ s.readReg64 .x28) ∗
          ((x.ret + 8#64) ↦₃₂ resWord1 (s.readReg64 .x20) (s.readReg64 .x21)) ∗
          ((x.ret + 12#64) ↦ₛ bs) ∗ F) ∗
         ((stackAt sp wsCalleeStack ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0xa0#64) 0x40 ∗
           (wsMsgCells x sp ∗ wsArgCellsV kit ikit x s0 sp) ∗
           memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2c8#64) 8 ∗
           memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗
           memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x324#64) 0xadc ∗
           memRegion (sp + 0xe00#64) 0x80 ∗ memRegion (s0.sp - 96#64) 96) ∗
          decStoreExtraPlaced kit ikit stf istf s0) ∗
         (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
          FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ A.pool ∗ R)) := by
      ac_rfl
    rw [hreord]
    have hstk :
        (stackAt sp wsCalleeStack ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0xa0#64) 0x40 ∗
          (wsMsgCells x sp ∗ wsArgCellsV kit ikit x s0 sp) ∗
          memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2c8#64) 8 ∗
          memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗
          memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x324#64) 0xadc ∗
          memRegion (sp + 0xe00#64) 0x80 ∗ memRegion (s0.sp - 96#64) 96) ∗
        decStoreExtraPlaced kit ikit stf istf s0 ⊢
        kit.storeAt (s0.readReg64 .x3) stf ∗ ikit.identityAt (s0.readReg64 .x5) istf ∗
          stackAt s0.sp (wsStackV kit ikit) := by
      refine Entails.trans (sepConj_mono_left ?_) (wsStack_join_extra_placed kit ikit stf istf s0)
      refine Entails.trans ?_ (frame_regions_fold_wsStack s0.sp)
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (argMsgCellsV_entails_memRegion_placed kit ikit x s0 sp))))
    refine Entails.trans (sepConj_mono (hres_ent x.ret) (sepConj_mono_left hstk)) ?_
    exact Entails.of_eq (by ac_rfl)
  exact Satisfies.mono hcomb hmf1

end SegWritePlaced

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
