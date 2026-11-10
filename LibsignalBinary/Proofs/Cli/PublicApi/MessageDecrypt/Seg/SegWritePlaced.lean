/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegWrite
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegWrite

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoGames
open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegWrite hiding segWriteVPlaced_ok

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


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

theorem segWriteVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegWriteSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro _hH x R s0 s hRF hL
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
  dsimp only [withStoresDecPlacedSpecV, StoreKit.withLsCodeRoLoaded]
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


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegWrite
