/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlaced
public import LibsignalBinary.Proofs.Common.StringClonePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted

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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted hiding segUntrusted_placed_wp wsUntrustedFixedEnvPlaced wsUntrustedFixedRestPlaced wsFixed_wsEnv_untrusted_split_placed wsUntrustedPrePlaced wsUntrustedCommonRestPlaced wsUntrustedFramePlaced trusted_entails_untrustedPre_placed wsUntrustedPostSpatialPlaced untrustedPost_entails_placed segUntrustedVPlaced_ok

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] protocolAddressAt vecGhostAt

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


attribute [local semireducible] protocolAddressAt vecGhostAt in
set_option maxHeartbeats 800000 in
theorem segUntrusted_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : PublicApiDecHooksPlaced A H)
    {s : State} {R : SepProp}
    {addrA e0 e1 e3 devWord : BitVec 64} {e2 : BitVec 32} {d0 : BitVec 8} {pad : List (BitVec 8)}
    {addr : AddrGhost}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hw4 : addr.device :: pad = unpack64 devWord)
    (hpc : s.pc = untrustedPCPlaced)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWPp (lsProg_463 H) (errJoinPCPlaced true) s
      (FromRecordCallees.lsLogOff ∗
        ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
        vecGhostAt A addr.name addrA ∗
        ((addrA + 0x18#64) ↦₈ addr.device) ∗
        memRegion (s.sp + 0x5f0#64) 24 ∗
        ((s.sp + 0x608#64) ↦₈ d0) ∗ ((s.sp + 0x609#64) ↦ₛ pad) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₃₂ e2) ∗ ((s.sp + 0x594#64) ↦₆₄ e3) ∗
        A.pool ∗ stackAt s.sp extHookStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          ⌜sf.readReg64 .x28 = 0x800000000000000c#64 ∧
            sf.readReg64 .x20 = ((cap.extractLsb' 0 32) >>> 8#32).zeroExtend 64 ∧
            sf.readReg64 .x21 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
            sf.trace = s.trace⌝ ∗
          FromRecordCallees.lsLogOff ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
          vecGhostAt A addr.name addrA ∗
          ((addrA + 0x18#64) ↦₈ addr.device) ∗
          ((s.sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s.sp + 0x5f8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          ((s.sp + 0x608#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
          ((s.sp + 0x584#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 addr.name.bytes.length) ∗
          ((s.sp + 0x594#64) ↦₆₄ devWord) ∗
          CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr addr.name.bytes ∗
          A.pool ∗ stackAt s.sp extHookStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  unfold untrustedPCPlaced at hpc
  unfold errJoinPCPlaced FromRecordCallees.lsLogOff lsLogFilterAddr
  dsimp only [lsProg_463, ite_true]
  have hclone : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 623)
      (withLsRoClBox lsmpl (stringCloneSpec A)) :=
    box_lscro_463 (by
      simpa only [BitVec.zero_add] using
        StoreKit.ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_463 H) (i := 463)
          (LibsignalBinary.Proofs.Common.StringClonePlaced.stringClone_blk623_ok
            hH.shim hH.alloc hH.memcpy hH.handleError))
  apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 623)
  wp_steps
  refine SepWP.done (by simp_all) (by simp_all) fun hcrl_call => ?_
  cli_messageDecrypt_call_panic_lscro hclone hcrl_call (addrA, s.sp + 1520#64, addr.name)
  apply SepWP.fold (vecU8_unpack_5f0 A s.sp addr.name.bytes) (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro (cap : BitVec 64)
  apply SepWP.exists_elim; intro (ptr : BitVec 64)
  wp_steps 5
  apply SepWP.fold
    (Entails.of_eq (repack_5f4_for_q0 s.sp cap ptr (BitVec.ofNat 64 addr.name.bytes.length)))
    (by sep_focus)
  wp_step
  apply SepWP.fold
    (Entails.of_eq (repack_5f4_for_q1 s.sp cap ptr (BitVec.ofNat 64 addr.name.bytes.length) addr.device pad devWord hw4))
    (by sep_focus)
  wp_steps 3
  apply SepWP.fold
    (Entails.of_eq (repack_588_for_q1 s.sp ptr (BitVec.ofNat 64 addr.name.bytes.length) e2))
    (by sep_focus)
  wp_steps 4
  apply SepWP.fold
    (Entails.of_eq (repack_580_after_q1 s.sp cap ptr))
    (by sep_focus)
  wp_done

def wsUntrustedFixedEnvPlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost)
    (sp : BitVec 64) : SepProp :=
  FromRecordCallees.lsLogOff ∗
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
  vecGhostAt A x.rem.name x.remA ∗
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  A.pool ∗ stackAt sp extHookStack

def wsUntrustedFixedRestPlaced (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsSavedRegs s0.sp s0 ∗
  ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  decVtablesAtV kit ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
  memRegion (x.remA + 0x19#64) 7 ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.loc x.locA ∗
  wsExtStackRest sp

theorem wsFixed_wsEnv_untrusted_split_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) :
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp =
      wsUntrustedFixedEnvPlaced A x sp ∗ wsUntrustedFixedRestPlaced A kit ikit x s0 sp := by
  unfold wsFixedVPlaced wsEnvPlaced wsArgCellsV wsUntrustedFixedEnvPlaced wsUntrustedFixedRestPlaced
  rw [protocolAddressAt_eq A x.rem x.remA, stack_wsCallee_extHook sp]
  ac_rfl

def wsUntrustedPrePlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost) (sp : BitVec 64)
    (e0 e1 e3 : BitVec 64) (e2 : BitVec 32) (d0 : BitVec 8) (pad : List (BitVec 8)) : SepProp :=
  FromRecordCallees.lsLogOff ∗
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
  vecGhostAt A x.rem.name x.remA ∗
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  memRegion (sp + 0x5f0#64) 24 ∗
  ((sp + 0x608#64) ↦₈ d0) ∗ ((sp + 0x609#64) ↦ₛ pad) ∗
  ((sp + 0x580#64) ↦₆₄ e0) ∗ ((sp + 0x588#64) ↦₆₄ e1) ∗
  ((sp + 0x590#64) ↦₃₂ e2) ∗ ((sp + 0x594#64) ↦₆₄ e3) ∗
  A.pool ∗ stackAt sp extHookStack

def wsUntrustedCommonRestPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) : SepProp :=
  wsUntrustedFixedRestPlaced A kit ikit x s0 sp ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x300#64) 0x280 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)

def wsUntrustedFramePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (e4 : BitVec 64) : SepProp :=
  ((sp + 0x59c#64) ↦₆₄ e4) ∗
  memRegion (sp + 0x610#64) 16 ∗
  wsUntrustedCommonRestPlaced C A ctl kit ikit x ans s0 sp rec' pt k

theorem trusted_entails_untrustedPre_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) :
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)) ⊢
    ∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
    ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
      ⌜pad.length = 7⌝ ∗
      wsUntrustedPrePlaced A x sp e0 e1 e3 e2 d0 pad ∗
      wsUntrustedFramePlaced C A ctl kit ikit x ans s0 sp rec' pt k e4 := by
  rw [← sepConj_assoc, wsFixed_wsEnv_untrusted_split_placed, memRegion_300_b00_split,
    memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (sp + 0x580#64) 0x24 ∗ memRegion (sp + 0x5f0#64) 48) ∗
    (wsUntrustedFixedEnvPlaced A x sp ∗
      wsUntrustedCommonRestPlaced C A ctl kit ikit x ans s0 sp rec' pt k) by
    unfold wsUntrustedCommonRestPlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (memRegion_36_untrusted_entails (sp + 0x580#64))
    (memRegion_48_untrusted_entails (sp + 0x5f0#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro (d0 : BitVec 8)
  apply Entails.sepExists_elim; intro (pad : List (BitVec 8))
  apply Entails.sepExists_elim; intro (e0 : BitVec 64)
  apply Entails.sepExists_elim; intro (e1 : BitVec 64)
  apply Entails.sepExists_elim; intro (e2 : BitVec 32)
  apply Entails.sepExists_elim; intro (e3 : BitVec 64)
  apply Entails.sepExists_elim; intro (e4 : BitVec 64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜pad.length = 7⌝ ∗
      (wsUntrustedPrePlaced A x sp e0 e1 e3 e2 d0 pad ∗
        wsUntrustedFramePlaced C A ctl kit ikit x ans s0 sp rec' pt k e4) by
    unfold wsUntrustedPrePlaced wsUntrustedFramePlaced wsUntrustedFixedEnvPlaced
    ac_rfl)) ?_
  apply Entails.pure_left; intro hpad
  exact Entails.sepExists_right e0 (Entails.sepExists_right e1
    (Entails.sepExists_right e2 (Entails.sepExists_right e3
      (Entails.sepExists_right e4 (Entails.sepExists_right d0
        (Entails.sepExists_right pad (Entails.pure_right hpad (Entails.refl _))))))))

def wsUntrustedPostSpatialPlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost) (sp : BitVec 64)
    (cap ptr devWord : BitVec 64) : SepProp :=
  FromRecordCallees.lsLogOff ∗
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
  vecGhostAt A x.rem.name x.remA ∗
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  ((sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
  ((sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
  ((sp + 0x5f8#64) ↦₆₄ ptr) ∗
  ((sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
  ((sp + 0x608#64) ↦₆₄ devWord) ∗
  ((sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
  ((sp + 0x584#64) ↦₆₄ ptr) ∗
  ((sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
  ((sp + 0x594#64) ↦₆₄ devWord) ∗
  CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr x.rem.name.bytes ∗
  A.pool ∗ stackAt sp extHookStack

theorem untrustedPost_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (pt : List (BitVec 8)) (k : IdentityKey)
    (x28 w20 w21 cap ptr devWord e4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : x.rem.device :: pad = unpack64 devWord)
    (hx28 : x28 = 0x800000000000000c#64) (hw1 : resWord1 w20 w21 = cap.extractLsb' 0 32) :
    wsUntrustedPostSpatialPlaced A x sp cap ptr devWord ∗
      wsUntrustedFramePlaced C A ctl kit ikit x ans s0 sp rec' pt k e4 ⊢
    ∃∗ G : SessionGhost,
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.untrustedIdentity x.rem.val)) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
    (((sp + 0x5f0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
      ((sp + 0x5f4#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 0x5f8#64) ↦₆₄ ptr) ∗
      ((sp + 0x600#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
      ((sp + 0x608#64) ↦₆₄ devWord) ∗
      memRegion (sp + 0x610#64) 16) ∗
    ((((sp + 0x580#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((sp + 0x584#64) ↦₆₄ ptr) ∗
      ((sp + 0x58c#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
      ((sp + 0x594#64) ↦₆₄ devWord) ∗
      ((sp + 0x59c#64) ↦₆₄ e4)) ∗
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr x.rem.name.bytes) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
    ((wsUntrustedFixedEnvPlaced A x sp ∗ wsUntrustedFixedRestPlaced A kit ikit x s0 sp) ∗
      wsMsgCells x sp ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsUntrustedPostSpatialPlaced wsUntrustedFramePlaced wsUntrustedCommonRestPlaced wsUntrustedFixedEnvPlaced
    ac_rfl)) ?_
  rw [← wsFixed_wsEnv_untrusted_split_placed]
  have h48 := cells_48_untrusted_entails_memRegion (sp + 0x5f0#64)
    (cap.extractLsb' 0 32) (cap.extractLsb' 32 32) ptr
    (BitVec.ofNat 64 x.rem.name.bytes.length) devWord
  have hst := stagedRes_untrusted_intro A x28 w20 w21 (sp + 0x580#64)
    cap ptr devWord e4 x.rem pad hpad hw4 hx28 hw1
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h48 hst
  have hrec := sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec (sepConj_mono h48
    (sepConj_mono hst (sepConj_mono hpt
      (sepConj_mono_left (key_entails_memRegion_32 (sp + 0x2a8#64) k)))))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

attribute [local semireducible] SepWP in
theorem segUntrustedVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegUntrustedSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hyps x ans R s0 s hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, _hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  rw [← hsp] at hx26 hx19 hx22 hm
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  let R' : SepProp := decStoreExtraPlaced kit ikit st0 ist1 s0 ∗ R
  have hm_pre : s.mem ⊨
      (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
          ⌜pad.length = 7⌝ ∗
          wsUntrustedPrePlaced A x s.sp e0 e1 e3 e2 d0 pad ∗
          wsUntrustedFramePlaced C A ctl kit ikit x ans s0 s.sp rec' pt k e4) ∗ R' := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_untrustedPre_placed C A ctl kit ikit x ans s0 s.sp rec' pt k)) ?_
    simpa only [R', ist1, sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨e0, e1, e2, e3, e4, d0, pad, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hpad, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨devWord, hw4⟩ := exists_unpack64_of_length_8 (bs := x.rem.device :: pad) (by simp [hpad])
  obtain ⟨sf, hsteps, hout⟩ :=
    segUntrusted_placed_wp hyps.hooks
      (R := wsUntrustedFramePlaced C A ctl kit ikit x ans s0 s.sp rec' pt k e4 ∗ R')
      _hcrl hw4 hpc hrun hsp_align
      (wsUntrustedFramePlaced C A ctl kit ikit x ans s0 s.sp rec' pt k e4 ∗ R') hm_pre hL
  rcases hout with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨cap, ptr, hm1'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1'
    rcases hm1' with ⟨⟨hx28_1, hx20_1, hx21_1, htr1⟩, hm1'⟩
    rw [← sepConj_assoc] at hm1'
    have hmeta1 := wsMetaPlaced_of_steps hmeta hsteps hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hw1 : resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = cap.extractLsb' 0 32 := by
      rw [hx20_1, hx21_1, resWord1_lsr8]
    have hm1_post := Satisfies.mono (sepConj_mono_left
      (untrustedPost_entails_placed C A ctl kit ikit x ans s0 s.sp rec' ses hcur pt k
        (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21)
        cap ptr devWord e4 pad hpad hw4 hx28_1 hw1)) hm1'
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm1_post
    rcases hm1_post with ⟨G, hm1_post⟩
    refine ⟨sf, hsteps, Or.inl ?_⟩
    have hmod := model_of_trust_false C S x ans rec rec' pt ses k
      hload (hyps.scopeIn rec hscope.1) hdec hcur hrem htrust
    refine ⟨hpc1, hmeta1, ?_, ?_, ans, some (G, ses.state), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx26_1, hx26, hsp]
    · rw [hx28_1]; decide
    · rw [hmod.1]; exact nofun
    · intro p; rw [hmod.1]; exact nofun
    · intro r hr; rw [hload] at hr; cases hr; exact hscope
    · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
    · rw [hmod.2]; exact ⟨htrustRel, trivial⟩
    · rw [htr1, htr, hmod.2]; simp
    · have hstf : kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2 = st0 := by
        rw [hmod.2]; rfl
      have histf : ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2 = ist1 := by
        rw [hmod.2]; rfl
      rw [hmod.1, hstf, histf]
      simpa only [R', ite_true, hsp, sepConj_assoc] using hm1_post
  · have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      have hpan_m0 := hpan_post1 hm1
      rw [← sepConj_assoc] at hpan_m0
      have hpan_m1 := Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m0
      have hreord :
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R' ⊢
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
        dsimp only [R']
        rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap]
        exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))
      exact Satisfies.mono hreord hpan_m1
    exact ⟨sf, hsteps, Or.inr (panic_outcome_of_allocFailedInVPlaced ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted
