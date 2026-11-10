/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegDispatch
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchAuxPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch

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
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch hiding wsFixedRestPlaced wsFixed_eq_active_rest_placed fold_wsFixed_assoc_placed branch_err_entails_placed wsNonePassivePlaced F_clonePlaced branch_none_pre_clone_entails_placed branch_none_post_entails_placed regionCommonBodyPlaced wsRegionFrameRestPlaced branch_some_common_entails_placed regionNone_of_common_placed regionSome_of_common_placed segDispatchVPlaced_ok apiDecResultAt_store_placed_of_words stagedRes_store_err_placed apiDecResultAt_sessionNotFound_placed_of_words stagedRes_sessionNotFound_placed messageDecrypt_of_sepWP_lscro messageDecrypt_of_sepWP_done_lscro messageDecrypt_call_panic_then_wp_lscro decSeg_of_sepWP_mid_placed decSeg_of_sepWP_done_placed decSeg_of_sepWPp_placed msgDecryptStrSym satisfies_rodata_msgDecryptStr_placed ls_hook_ok_197 stringClone_placed_ok msgDecrypt_memcpy_placed_ok msgDecrypt_dealloc_placed_ok stringClone_onPanic_entails_placed loadPollPlacedOutAt_err_entails loadPollPlacedOutAt_none_entails loadPollPlacedOutAt_some_entails loadPollBranchRestPlaced loadPollPlacedOutAt_entails_common

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] extractLsb_lo_append64 extractLsb_hi_append64

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


open CryptoVerification

def wsFixedRestPlaced {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (_x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsSavedRegs s0.sp s0 ∗
  ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (b + kit.loadShimOff)) ∗
  ((b + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (b + kit.loadPollOff)) ∗
  decStoreVtableAtV kit ∗
  decSaveVtableAtV ikit ∗
  decTrustVtableAtV ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80

theorem wsFixed_eq_active_rest_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) :
    wsFixedVPlaced kit ikit x s0 sp =
      ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
      ((b + kit.loadFutVtOff) ↦₆₄ᵣ (b + kit.loadFutDropOff)) ∗
      ((b + (kit.loadFutVtOff + 8#64)) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((b + (kit.loadFutVtOff + 0x10#64)) ↦₆₄ᵣ 8#64) ∗
      wsFixedRestPlaced kit ikit x s0 sp := by
  unfold wsFixedVPlaced wsArgCellsV decVtablesAtV decLoadVtableAtV wsFixedRestPlaced
  simp only [BitVec.add_assoc]
  ac_rfl

theorem fold_wsFixed_assoc_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (R : SepProp) :
    ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
      ((b + kit.loadFutVtOff) ↦₆₄ᵣ (b + kit.loadFutDropOff)) ∗
      ((b + (kit.loadFutVtOff + 8#64)) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((b + (kit.loadFutVtOff + 0x10#64)) ↦₆₄ᵣ 8#64) ∗
      wsFixedRestPlaced kit ikit x s0 sp ∗ R =
      wsFixedVPlaced kit ikit x s0 sp ∗ R := by
  rw [wsFixed_eq_active_rest_placed]
  simp only [sepConj_assoc]

theorem branch_err_entails_placed [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 : State) (sp w2 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    (htail : tail.length = 312) :
    (w2 ↦ᵣ storeHookStr) ∗
      memRegion (sp + 0x2d0#64) 16 ∗
      stackAt sp wsCalleeStack ∗ A.pool ∗
      ((sp + 0x328#64) ↦ₛ tail) ∗ ((sp + 0x628#64) ↦ₛ tail) ∗
      ((sp + 0x5f0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((sp + 0x5f8#64) ↦₆₄ 0x800000000000001A#64) ∗
      ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
      ((sp + 0x604#64) ↦₆₄ (q0OfWords w2 10#64 1#64).extractLsb' 0 64) ∗
      ((sp + 0x60c#64) ↦₆₄ (q0OfWords w2 10#64 1#64).extractLsb' 64 64) ∗
      ((sp + 0x614#64) ↦₆₄ (q1OfWords 1#64 w5 w6).extractLsb' 0 64) ∗
      ((sp + 0x61c#64) ↦₆₄ (q1OfWords 1#64 w5 w6).extractLsb' 64 64) ∗
      ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
      ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
      ((0#64 + (kit.loadFutVtOff + 8#64)) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((0#64 + (kit.loadFutVtOff + 0x10#64)) ↦₆₄ᵣ 8#64) ∗
      wsFixedRestPlaced kit ikit x s0 sp ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      FromRecordCallees.lsLogOff ∗
      wsMsgCells x sp ∗
      memRegion sp 160 ∗
      memRegion (sp + 0x120#64) 424 ∗
      ((sp + 0x300#64) ↦₆₄ (q0OfWords w2 10#64 1#64).extractLsb' 0 64) ∗
      ((sp + 0x308#64) ↦₆₄ (q0OfWords w2 10#64 1#64).extractLsb' 64 64) ∗
      ((sp + 0x310#64) ↦₆₄ (q1OfWords 1#64 w5 w6).extractLsb' 0 64) ∗
      ((sp + 0x318#64) ↦₆₄ (q1OfWords 1#64 w5 w6).extractLsb' 64 64) ∗
      ((sp + 0x320#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      memRegion (sp + 0x324#64) 4 ∗
      ((sp + 0x460#64) ↦₆₄ (q0OfWords w2 10#64 1#64).extractLsb' 0 64) ∗
      ((sp + 0x468#64) ↦₆₄ (q0OfWords w2 10#64 1#64).extractLsb' 64 64) ∗
      ((sp + 0x470#64) ↦₆₄ (q1OfWords 1#64 w5 w6).extractLsb' 0 64) ∗
      ((sp + 0x478#64) ↦₆₄ (q1OfWords 1#64 w5 w6).extractLsb' 64 64) ∗
      ((sp + 0x480#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      memRegion (sp + 0x484#64) 44 ∗
      memRegion (sp + 0x4b0#64) 208 ∗
      ((sp + 0x580#64) ↦₆₄ (q0OfWords w2 10#64 1#64).extractLsb' 0 64) ∗
      ((sp + 0x588#64) ↦₆₄ (q0OfWords w2 10#64 1#64).extractLsb' 64 64) ∗
      ((sp + 0x590#64) ↦₆₄ (q1OfWords 1#64 w5 w6).extractLsb' 0 64) ∗
      ((sp + 0x598#64) ↦₆₄ (q1OfWords 1#64 w5 w6).extractLsb' 64 64) ∗
      ((sp + 0x5a0#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      memRegion (sp + 0x5a4#64) 76 ∗
      memRegion (sp + 0x760#64) 1696 ∗
      memRegion x.ret 48 ∗
      cliTapeAt ctl x.cur x.rest ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 ⊢
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      StagedRes A 0x800000000000001A#64
        (BitVec.zeroExtend 64
          (BitVec.truncate 32 (BitVec.zeroExtend 64 (w2.extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 (w2.extractLsb' 0 32))
        (sp + 0x300#64) (.error (.store ())) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 := by
  rw [fold_q128_pair_32 sp 0x604#64 0x60c#64 0x614#64 0x61c#64 0x624#64 rfl rfl,
      fold_q128_pair_32 sp 0x300#64 0x308#64 0x310#64 0x318#64 0x320#64 rfl rfl,
      fold_q128_pair_32 sp 0x460#64 0x468#64 0x470#64 0x478#64 0x480#64 rfl rfl,
      fold_q128_pair_32 sp 0x580#64 0x588#64 0x590#64 0x598#64 0x5a0#64 rfl rfl,
      fold_wsFixed_assoc_placed kit ikit x s0 sp]
  have hst := stagedRes_store_err_placed A (sp + 0x300#64) w2 w5 w6
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hst
  have h5f0 := fold_5f0_368 sp 0xFFFFFFFFFFFFFFFE#64 0x800000000000001A#64
    w2 10#64 1#64 w5 w6 tail htail
  have h328 := fold_328_after_recordMove sp tail htail
    (q0OfWords w2 10#64 1#64) (q1OfWords 1#64 w5 w6) (w6.extractLsb' 32 32)
  have h4b0 := fold_4b0_after_resultCopy sp
    (q0OfWords w2 10#64 1#64) (q1OfWords 1#64 w5 w6) (w6.extractLsb' 32 32)
  have htape := cliTapeAt_entails_cliTapeAfter_zero ctl x.cur x.rest
  rw [← join_324_to_adc sp]
  unfold wsEnvPlaced
  refine Entails.focus_left (by sep_focus) h4b0 ?_
  refine Entails.focus_left (by sep_focus) h328 ?_
  refine Entails.focus_left (by sep_focus) h5f0 ?_
  refine Entails.focus_left (by sep_focus) hst ?_
  refine Entails.focus_left (by sep_focus) htape ?_
  exact Entails.of_eq (by ac_rfl)

def wsNonePassivePlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  protocolAddressAt A x.loc x.locA ∗
  FromRecordCallees.lsLogOff ∗
  wsMsgCells x sp ∗
  memRegion sp 0xa0 ∗
  memRegion (sp + 0x120#64) 0x1a8 ∗
  memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x324#64) 4 ∗
  memRegion (sp + 0x328#64) 0x188 ∗
  memRegion (sp + 0x4b0#64) 0xd0 ∗
  memRegion (sp + 0x5a4#64) 0x4c ∗
  memRegion (sp + 0x620#64) 320 ∗
  memRegion (sp + 0x760#64) 0x6a0 ∗
  memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - extHookStack) ∗
  memRegion (x.remA + 0x19#64) 7 ∗
  memRegion x.ret 48 ∗
  cliTapeAt ctl x.cur x.rest ∗
  decStoreExtraPlaced kit ikit st0 ist0 s0

def F_clonePlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
  (∃∗ b0 : BitVec 8, ((sp + 0x608#64) ↦₈ b0)) ∗
  (∃∗ pad : List (BitVec 8), ⌜pad.length = 7⌝ ∗ ((sp + 0x609#64) ↦ₛ pad)) ∗
  (∃∗ d0 : BitVec 64, ((sp + 0x610#64) ↦₆₄ d0)) ∗
  (∃∗ d1 : BitVec 64, ((sp + 0x618#64) ↦₆₄ d1)) ∗
  (∃∗ q0 : BitVec 128, ((sp + 0x580#64) ↦₁₂₈ q0)) ∗
  (∃∗ q1 : BitVec 128, ((sp + 0x590#64) ↦₁₂₈ q1)) ∗
  (∃∗ w8 : BitVec 32, ((sp + 0x5a0#64) ↦₃₂ w8)) ∗
  (∃∗ q0' : BitVec 128, ((sp + 0x300#64) ↦₁₂₈ q0')) ∗
  (∃∗ q1' : BitVec 128, ((sp + 0x310#64) ↦₁₂₈ q1')) ∗
  (∃∗ w8' : BitVec 32, ((sp + 0x320#64) ↦₃₂ w8')) ∗
  wsNonePassivePlaced A ctl kit ikit st0 ist0 x s0 sp

theorem branch_none_pre_clone_entails_placed [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 : State) (sp w1 w2 w3 w4 w5 w6 : BitVec 64)
    (tail : List (BitVec 8)) (htail : tail.length = 312) :
    memRegion (sp + 0x2d0#64) 16 ∗
      stackAt sp wsCalleeStack ∗ A.pool ∗
      ((sp + 0x328#64) ↦ₛ tail) ∗ ((sp + 0x628#64) ↦ₛ tail) ∗
      ((sp + 0x5f0#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      ((sp + 0x5f8#64) ↦₆₄ w1) ∗
      ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
      ((sp + 0x604#64) ↦₆₄ (q0OfWords w2 w3 w4).extractLsb' 0 64) ∗
      ((sp + 0x60c#64) ↦₆₄ (q0OfWords w2 w3 w4).extractLsb' 64 64) ∗
      ((sp + 0x614#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 0 64) ∗
      ((sp + 0x61c#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 64 64) ∗
      ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
      ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
      ((0#64 + (kit.loadFutVtOff + 8#64)) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((0#64 + (kit.loadFutVtOff + 0x10#64)) ↦₆₄ᵣ 8#64) ∗
      wsFixedRestPlaced kit ikit x s0 sp ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      FromRecordCallees.lsLogOff ∗
      wsMsgCells x sp ∗
      memRegion sp 160 ∗
      memRegion (sp + 0x120#64) 424 ∗
      memRegion (sp + 0x300#64) 40 ∗
      ((sp + 0x460#64) ↦₆₄ (q0OfWords w2 w3 w4).extractLsb' 0 64) ∗
      ((sp + 0x468#64) ↦₆₄ (q0OfWords w2 w3 w4).extractLsb' 64 64) ∗
      ((sp + 0x470#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 0 64) ∗
      ((sp + 0x478#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 64 64) ∗
      ((sp + 0x480#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      memRegion (sp + 0x484#64) 44 ∗
      memRegion (sp + 0x4b0#64) 320 ∗
      memRegion (sp + 0x760#64) 1696 ∗
      memRegion x.ret 48 ∗
      cliTapeAt ctl x.cur x.rest ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 ⊢
      (vecGhostAt A x.rem.name x.remA ∗ memRegion (sp + 0x5f0#64) 24 ∗
        A.pool ∗ stackAt sp extHookStack) ∗
      F_clonePlaced A ctl kit ikit st0 ist0 x s0 sp := by
  rw [fold_q128_pair_32 sp 0x604#64 0x60c#64 0x614#64 0x61c#64 0x624#64 rfl rfl,
      fold_q128_pair_32 sp 0x460#64 0x468#64 0x470#64 0x478#64 0x480#64 rfl rfl,
      fold_wsFixed_assoc_placed kit ikit x s0 sp, stack_wsCallee_ext sp,
      split_300_for_resultCopy sp, split_4b0_for_resultCopy sp,
      show protocolAddressAt A x.rem x.remA =
        vecGhostAt A x.rem.name x.remA ∗ ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 from rfl]
  have h5f0 := split_5f0_for_noRecord sp 0xFFFFFFFFFFFFFFFF#64 w1 (w2.extractLsb' 0 32)
    (q0OfWords w2 w3 w4) (q1OfWords w4 w5 w6) (w6.extractLsb' 32 32) tail htail
  have h328 := fold_328_after_recordMove sp tail htail
    (q0OfWords w2 w3 w4) (q1OfWords w4 w5 w6) (w6.extractLsb' 32 32)
  unfold F_clonePlaced wsNonePassivePlaced
  simp only [sepConj_assoc]
  refine Entails.focus_left (by sep_focus) h5f0 ?_
  refine Entails.focus_left (by sep_focus) h328 ?_
  exact Entails.of_eq (by ac_rfl)

theorem branch_none_post_entails_placed [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 : State) (sp cap ptr w4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : x.rem.device :: pad = unpack64 w4) :
    ((lsmpl.ρ msgDecryptStrSym) ↦ᵣ utf8 "message_decrypt_signal") ∗
      ((sp + 0x5f8#64) ↦₃₂ ptr.extractLsb' 0 32) ∗
      ((sp + 0x5fc#64) ↦₆₄ (q0OfWords ptr (BitVec.ofNat 64 x.rem.name.bytes.length) w4).extractLsb' 0 64) ∗
      ((sp + 0x604#64) ↦₆₄ (q0OfWords ptr (BitVec.ofNat 64 x.rem.name.bytes.length) w4).extractLsb' 64 64) ∗
      ((sp + 0x60c#64) ↦₆₄ (q1OfWords w4 (lsmpl.ρ msgDecryptStrSym) 22#64).extractLsb' 0 64) ∗
      ((sp + 0x614#64) ↦₆₄ (q1OfWords w4 (lsmpl.ρ msgDecryptStrSym) 22#64).extractLsb' 64 64) ∗
      ((sp + 0x61c#64) ↦₃₂ (22#64 : BitVec 64).extractLsb' 32 32) ∗
      ((sp + 0x5f0#64) ↦₆₄ cap) ∗
      vecU8Buf A cap ptr x.rem.name.bytes ∗
      vecGhostAt A x.rem.name x.remA ∗
      A.pool ∗
      stackAt sp extHookStack ∗
      ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      ((sp + 0x580#64) ↦₆₄ (q0OfWords ptr (BitVec.ofNat 64 x.rem.name.bytes.length) w4).extractLsb' 0 64) ∗
      ((sp + 0x588#64) ↦₆₄ (q0OfWords ptr (BitVec.ofNat 64 x.rem.name.bytes.length) w4).extractLsb' 64 64) ∗
      ((sp + 0x590#64) ↦₆₄ (q1OfWords w4 (lsmpl.ρ msgDecryptStrSym) 22#64).extractLsb' 0 64) ∗
      ((sp + 0x598#64) ↦₆₄ (q1OfWords w4 (lsmpl.ρ msgDecryptStrSym) 22#64).extractLsb' 64 64) ∗
      ((sp + 0x5a0#64) ↦₃₂ 0#32) ∗
      ((sp + 0x300#64) ↦₆₄ (q0OfWords ptr (BitVec.ofNat 64 x.rem.name.bytes.length) w4).extractLsb' 0 64) ∗
      ((sp + 0x308#64) ↦₆₄ (q0OfWords ptr (BitVec.ofNat 64 x.rem.name.bytes.length) w4).extractLsb' 64 64) ∗
      ((sp + 0x310#64) ↦₆₄ (q1OfWords w4 (lsmpl.ρ msgDecryptStrSym) 22#64).extractLsb' 0 64) ∗
      ((sp + 0x318#64) ↦₆₄ (q1OfWords w4 (lsmpl.ρ msgDecryptStrSym) 22#64).extractLsb' 64 64) ∗
      ((sp + 0x320#64) ↦₃₂ 0#32) ∗
      wsNonePassivePlaced A ctl kit ikit st0 ist0 x s0 sp ⊢
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      StagedRes A cap
        (BitVec.zeroExtend 64
          (BitVec.truncate 32 (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32))
        (sp + 0x300#64) (.error (.sessionNotFound x.rem.val "message_decrypt_signal")) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 := by
  rw [fold_q128_pair_32 sp 0x5fc#64 0x604#64 0x60c#64 0x614#64 0x61c#64 rfl rfl,
      fold_q128_pair_32 sp 0x580#64 0x588#64 0x590#64 0x598#64 0x5a0#64 rfl rfl,
      fold_q128_pair_32 sp 0x300#64 0x308#64 0x310#64 0x318#64 0x320#64 rfl rfl]
  have hst := stagedRes_sessionNotFound_placed A (sp + 0x300#64) x.rem.val cap ptr
    (lsmpl.ρ msgDecryptStrSym) w4 pad hpad hw4
  have h22 : ((22#64 : BitVec 64).extractLsb' 32 32) = 0#32 := rfl
  rw [h22]
  rw [show x.rem.val.name = x.rem.name.bytes from rfl] at hst
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hst
  have h5f0 := fold_5f0_after_noRecord sp cap (ptr.extractLsb' 0 32)
    (q0OfWords ptr (BitVec.ofNat 64 x.rem.name.bytes.length) w4)
    (q1OfWords w4 (lsmpl.ρ msgDecryptStrSym) 22#64) 0#32
  have h4b0 := fold_4b0_after_resultCopy sp
    (q0OfWords ptr (BitVec.ofNat 64 x.rem.name.bytes.length) w4)
    (q1OfWords w4 (lsmpl.ρ msgDecryptStrSym) 22#64) 0#32
  have htape := cliTapeAt_entails_cliTapeAfter_zero ctl x.cur x.rest
  rw [← join_324_to_adc sp]
  unfold wsNonePassivePlaced wsEnvPlaced
  rw [show protocolAddressAt A x.rem x.remA =
    vecGhostAt A x.rem.name x.remA ∗ ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      memRegion (x.remA + 0x19#64) 7 from rfl,
    ← stack_wsCallee_ext_back sp]
  simp only [sepConj_assoc]
  refine Entails.focus_left (by sep_focus) h4b0 ?_
  refine Entails.focus_left (by sep_focus) h5f0 ?_
  refine Entails.focus_left (by sep_focus) hst ?_
  refine Entails.focus_left (by sep_focus) htape ?_
  exact Entails.of_eq (by ac_rfl)

def regionCommonBodyPlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : DecryptGhost) (sp : BitVec 64) : SepProp :=
  memRegion sp 0xa0 ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  memRegion (sp + 0x4b0#64) 0x950 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool

def wsRegionFrameRestPlaced {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗
  memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x300#64) 0x1b0 ∗
  memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
  memRegion x.ret 48 ∗
  decStoreExtraPlaced kit ikit st0 ist0 s0

theorem branch_some_common_entails_placed [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    (htail_inl : RecordTailInline g rec w4 w5 w6 tail) :
    ((sp + 0x158#64) ↦ₛ tail) ∗
      ((sp + 0x328#64) ↦ₛ tail) ∗
      memRegion (sp + 0x2d0#64) 16 ∗
      stackAt sp wsCalleeStack ∗ A.pool ∗
      ((sp + 0x628#64) ↦ₛ tail) ∗
      ((sp + 0x5f0#64) ↦₆₄ g.prevCap) ∗
      ((sp + 0x5f8#64) ↦₆₄ g.prevPtr) ∗
      ((sp + 0x600#64) ↦₃₂ 0#32) ∗
      ((sp + 0x604#64) ↦₆₄ (q0OfWords 0#64 (recordCurCap g) w4).extractLsb' 0 64) ∗
      ((sp + 0x60c#64) ↦₆₄ (q0OfWords 0#64 (recordCurCap g) w4).extractLsb' 64 64) ∗
      ((sp + 0x614#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 0 64) ∗
      ((sp + 0x61c#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 64 64) ∗
      ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      recordHeap A g rec ∗
      ((sp + 0xe8#64) ↦₆₄ x.remA) ∗
      ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
      ((0#64 + (kit.loadFutVtOff + 8#64)) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((0#64 + (kit.loadFutVtOff + 0x10#64)) ↦₆₄ᵣ 8#64) ∗
      wsFixedRestPlaced kit ikit x s0 sp ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗
      FromRecordCallees.lsLogOff ∗
      wsMsgCells x sp ∗
      memRegion sp 160 ∗
      ((sp + 0x120#64) ↦₆₄ g.prevCap) ∗
      ((sp + 0x128#64) ↦₆₄ g.prevPtr) ∗
      ((sp + 0x130#64) ↦₃₂ 0#32) ∗
      ((sp + 0x134#64) ↦₆₄ (q0OfWords 0#64 (recordCurCap g) w4).extractLsb' 0 64) ∗
      ((sp + 0x13c#64) ↦₆₄ (q0OfWords 0#64 (recordCurCap g) w4).extractLsb' 64 64) ∗
      ((sp + 0x144#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 0 64) ∗
      ((sp + 0x14c#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 64 64) ∗
      ((sp + 0x154#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      memRegion (sp + 0x290#64) 56 ∗
      memRegion (sp + 0x300#64) 40 ∗
      ((sp + 0x460#64) ↦₆₄ (q0OfWords 0#64 (recordCurCap g) w4).extractLsb' 0 64) ∗
      ((sp + 0x468#64) ↦₆₄ (q0OfWords 0#64 (recordCurCap g) w4).extractLsb' 64 64) ∗
      ((sp + 0x470#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 0 64) ∗
      ((sp + 0x478#64) ↦₆₄ (q1OfWords w4 w5 w6).extractLsb' 64 64) ∗
      ((sp + 0x480#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      memRegion (sp + 0x484#64) 44 ∗
      memRegion (sp + 0x4b0#64) 320 ∗
      memRegion (sp + 0x760#64) 1696 ∗
      memRegion x.ret 48 ∗
      cliTapeAt ctl x.cur x.rest ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 ⊢
      sessionRecordAt A (sp + 0x120#64) g rec ∗
        regionCommonBodyPlaced A ctl x sp ∗
        wsRegionFrameRestPlaced kit ikit st0 ist0 x s0 sp := by
  rw [fold_q128_pair_32 sp 0x604#64 0x60c#64 0x614#64 0x61c#64 0x624#64 rfl rfl,
      fold_q128_pair_32 sp 0x134#64 0x13c#64 0x144#64 0x14c#64 0x154#64 rfl rfl,
      fold_q128_pair_32 sp 0x460#64 0x468#64 0x470#64 0x478#64 0x480#64 rfl rfl,
      fold_wsFixed_assoc_placed kit ikit x s0 sp, stack_wsCallee_root sp]
  have h0_32 : ((0#64 : BitVec 64).extractLsb' 0 32) = 0#32 := rfl
  have hrec :
      ((sp + 0x120#64) ↦₆₄ g.prevCap) ∗ ((sp + 0x128#64) ↦₆₄ g.prevPtr) ∗
        ((sp + 0x130#64) ↦₃₂ 0#32) ∗
        ((sp + 0x134#64) ↦₁₂₈ q0OfWords 0#64 (recordCurCap g) w4) ∗
        ((sp + 0x144#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((sp + 0x154#64) ↦₃₂ w6.extractLsb' 32 32) ∗
        ((sp + 0x158#64) ↦ₛ tail) ∗ recordHeap A g rec ⊢
        sessionRecordAt A (sp + 0x120#64) g rec := by
    have h1 := fold_words56_repack (sp + 0x120#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6
    have h2 := sessionRecordAt_of_words56_sep_tail A (sp + 0x120#64) g rec htail_inl
    simp only [BitVec.add_assoc, BitVec.reduceAdd, h0_32] at h1 h2
    exact Entails.focus_left (by sep_focus) h1 h2
  have h5f0 := fold_5f0_368 sp g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 tail htail_inl.1
  simp only [h0_32] at h5f0
  have h328 := fold_328_after_recordMove sp tail htail_inl.1
    (q0OfWords 0#64 (recordCurCap g) w4) (q1OfWords w4 w5 w6) (w6.extractLsb' 32 32)
  have h300 : memRegion (sp + 0x300#64) 0x1b0 =
      memRegion (sp + 0x300#64) 40 ∗ memRegion (sp + 0x328#64) 0x188 := by
    rw [memRegion_split (sp + 0x300#64) 40 0x188 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  unfold regionCommonBodyPlaced wsRegionFrameRestPlaced wsMsgCells
  rw [h300, ← join_4b0_5f0_760 sp]
  simp only [sepConj_assoc]
  refine Entails.focus_left (by sep_focus) hrec ?_
  refine Entails.focus_left (by sep_focus) h5f0 ?_
  refine Entails.focus_left (by sep_focus) h328 ?_
  exact Entails.of_eq (by ac_rfl)

theorem regionNone_of_common_placed [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 sf : State) (sp : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hsp0 : s0.sp - 0xee0#64 = sp) (hsp : sf.sp = sp)
    (hcur : rec.currentSession = none)
    (hpure : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.spAligned = true ∧
      sf.readReg64 .x27 = x.ret ∧ sf.readReg64 .x19 = x.remA ∧
      sf.readReg64 .x23 = sp + 0x5f0#64 ∧ sf.readReg64 .x24 = sp + 0xca0#64 ∧
      rootStack ≤ sp.toNat) :
    sessionRecordAt A (sp + 0x120#64) g rec ∗
      regionCommonBodyPlaced A ctl x sp ∗
      wsRegionFrameRestPlaced kit ikit st0 ist0 x s0 sp ⊢
    regionNonePrePlaced A ctl x g.prevPtr sf ∗
      wsRegionFrameVPlaced kit ikit x s0 g.prevCap g.prevPtr ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 := by
  have hsplit := recordNone_split A (sp + 0x120#64) g rec hcur
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsplit
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  unfold regionNonePrePlaced regionCommonBodyPlaced wsRegionFrameVPlaced
    wsRegionFrameRestPlaced wsFixedVPlaced
  rw [hsp0, hsp]
  simp only [sepConj_assoc]
  apply Entails.pure_right hpure
  exact Entails.of_eq (by ac_rfl)

theorem regionSome_of_common_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (x : DecryptGhost) (s0 sf : State) (sp : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (hsp0 : s0.sp - 0xee0#64 = sp) (hsp : sf.sp = sp)
    (hscope : RecordInScope rec) (hcur : rec.currentSession = some ses)
    (hpure : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧ sf.spAligned = true ∧
      sf.readReg64 .x27 = x.ret ∧ sf.readReg64 .x19 = x.remA ∧
      sf.readReg64 .x23 = sp + 0x5f0#64 ∧ sf.readReg64 .x24 = sp + 0xca0#64 ∧
      rootStack ≤ sp.toNat) :
    sessionRecordAt A (sp + 0x120#64) g rec ∗
      regionCommonBodyPlaced A ctl x sp ∗
      wsRegionFrameRestPlaced kit ikit st0 ist0 x s0 sp ⊢
    ∃∗ G : SessionGhost,
      ⌜sessionModelRel G ses⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).pre (recGhostOf x g.prevPtr G ses.state) sf ∗
      wsRegionFrameVPlaced kit ikit x s0 g.prevCap g.prevPtr ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 := by
  have hsplit := recordSome_split A (sp + 0x120#64) g rec ses hcur
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsplit
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hw0
  apply Entails.pure_right hw0
  have hsc := hscope ses hcur
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec, recGhostOf]
  unfold regionCommonBodyPlaced wsRegionFrameVPlaced wsRegionFrameRestPlaced wsFixedVPlaced
  rw [hsp0, hsp]
  simp only [sepConj_assoc]
  apply Entails.pure_right ⟨hpure.1.1, hpure.1.2⟩
  apply Entails.pure_right ⟨hpure.2.1, hpure.2.2.1, hpure.2.2.2.1,
    hpure.2.2.2.2.1, hpure.2.2.2.2.2.1, hsc.1, hsc.2.1, hsc.2.2.1, hpure.2.2.2.2.2.2⟩
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1600000 in
theorem segDispatchVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegDispatchSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hH x ans R s0 s hLP
  dsimp only [LoadPolledStateVPlaced, wsMetaPlaced] at hLP
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, hcrl, hvregs⟩,
    hsp_le, hx19, hloadRel, htrace, hmem⟩ := hLP
  have hsp' : s0.sp - 0xee0#64 = s.sp := hsp.symm
  clear hsp
  have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
  rw [hsp'] at hx19 hmem
  simp only [← sepConj_assoc] at hmem
  have hdz0 : (0#64 + kit.loadFutDropOff == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (kit.loadFutDrop_ne_zero (by decide))
  have hdz : (kit.loadFutDropOff == 0#64) = false := by
    simpa only [BitVec.zero_add] using hdz0
  have hsz : (BitVec.ofNat 64 kit.loadBoxSize == 0#64) = false :=
    beq_eq_false_iff_ne.mpr kit.loadBoxSize_ne_zero
  simp only [wp_norm, arm64_norm] at hx29 hx27 hx19
  have hmemcpy := msgDecrypt_memcpy_placed_ok hH.hooks.memcpy
  have hdrop : subroutine_ok (lsProg_463 H) kit.loadFutDropOff
      (StoreKit.withLsCodeRoLoaded lsmpl futDropSpec) := by
    simpa only [BitVec.zero_add] using
      StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl (hH.kit.loadFutDrop (callerBlk := 463) (by decide))
  have hdealloc := msgDecrypt_dealloc_placed_ok hH.hooks.dealloc
  have hclone := stringClone_placed_ok hH.hooks
  apply decSeg_of_sepWP_mid_placed hcrl hmem (mid := (blkPl_463).base + 312#64)
  dsimp only [lsProg_463, loadPolledPCPlaced] at hpc hmemcpy hdrop hdealloc hclone ⊢
  wp_conv_pre => rw [wsFixed_eq_active_rest_placed kit ikit x s0 s.sp, split_300_for_recordMove s.sp]
  unfold wsEnvPlaced
  apply SepWP.fold (loadPollPlacedOutAt_entails_common Scope A s.sp ans.loadSession)
    (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    q0OfWords_pointsTo128, q1OfWords_pointsTo128, CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.pointsTo128_split64,
    BitVec.add_assoc, BitVec.reduceAdd]
  apply SepWP.exists_elim; intro _w8_init
  apply SepWP.exists_elim; intro _q1_init
  apply SepWP.exists_elim; intro _q0_init
  apply SepWP.exists_elim; intro box
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4
  apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro tail
  apply SepWP.pure_elim; rintro ⟨hw0_ne, htail_len⟩
  wp_simp_pre [sepConj_pure_left_comm]
  apply SepWP.pure_elim; intro hbox_ne
  apply StoreKit.sepWP_seq_lscro hcrl (mid := kit.loadFutDropOff)
  wp_steps
  wp_call hmemcpy (s.sp + 0x328#64, s.sp + 0x628#64, tail)
  wp_steps
  refine SepWP.done rfl (by wp_norm_lhs) fun ⟨hcl_d, hro_d⟩ => ?_
  wp_apply
  simp only [hsp_sf] at h_12 ⊢
  wp_steps
  apply SepWP.fold (kit.loadBoxAt_memRegion box (s0.readReg64 .x3) x.remA 1#8) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (stack_wsCallee_dealloc s.sp)) (by sep_focus)
  have hbs_toNat : (BitVec.ofNat 64 kit.loadBoxSize).toNat = kit.loadBoxSize :=
    Nat.mod_eq_of_lt kit.loadBoxSize_lt
  wp_apply
  simp only [h_12] at hsp_sf_1 ⊢
  apply SepWP.fold (Entails.of_eq (stack_wsCallee_dealloc_back s.sp)) (by sep_focus)
  apply SepWP.fold (fold_2d0 s.sp box _) (by sep_focus)
  apply SepWP.done hpc_sf_2 hrun_sf_2
  intro hcrl2 hmm2
  have hsp2 : sf_2.sp = s.sp := hsp_sf_1
  have hal2 : (sf_2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hal_s
  have htr2 : sf_2.trace = s.trace := by rw [hpost_1, h_11, hpost]
  have hx20_2 : sf_2.readReg64 (Reg.gpr 20#5) = w0 := by rw [h_24, h_14, h_1]
  have hx21_2 : sf_2.readReg64 (Reg.gpr 21#5) = BitVec.zeroExtend 64 (w2.extractLsb' 0 32) := by
    rw [h_25, h_15, h_2]
  have hx23_2 : sf_2.readReg64 (Reg.gpr 23#5) = s.sp + 1520#64 := by rw [h_27, h_17, h_4]
  have hx27_2 : sf_2.readReg64 (Reg.gpr 27#5) = x.ret := by rw [h_31, h_21, h_8, hx27]
  have hx28_2 : sf_2.readReg64 (Reg.gpr 28#5) = w1 := by rw [h_32, h_22, h_9]
  have hx29_2 : sf_2.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcs_sf_1, hpost_sf, hcs_sf, hx29]
  have hvregs2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := by
    rw [hvregs_3, hvregs_2, hvregs_1, hvregs]
  clear h_23 h_24 h_25 h_26 h_27 h_28 h_29 h_30 h_31 h_32 hcs_sf_1 hpost_1
    h_13 h_14 h_15 h_16 h_17 h_18 h_19 h_20 h_21 h_22 hpost_sf h_11
    h h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9 hcs_sf hpost hvregs_1 hvregs_2 hvregs_3
  rcases hload : ans.loadSession with ⟨⟨⟩⟩ | (_ | rec)
  · have ⟨hmod, hdraws⟩ := model_of_load_err C S x ans hload
    apply decSeg_of_sepWP_done_placed hcrl2 hmm2 (target := resultFinalPCPlaced)
    dsimp only [lsProg_463, resultFinalPCPlaced]
    wp_conv_pre => rw [hload, split_300_for_resultCopy s.sp, split_4b0_for_resultCopy s.sp]
    dsimp only [loadPollBranchRestPlaced]
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.pointsTo128_split64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_pure_left_comm]
    repeat' (apply SepWP.exists_elim; intro _)
    apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, rfl⟩
    wp_steps
    refine SepWP.done rfl hrun_sf_2 fun hcrl3 hmf3 => ?_
    have hmf3'' := Satisfies.mono
      (sepConj_mono_left (Entails.trans (Entails.of_eq (by ac_rfl))
        (branch_err_entails_placed A ctl kit ikit st0 ist0 x s0 s.sp w2 w5 w6 tail htail_len))) hmf3
    refine Or.inr (Or.inr ?_)
    dsimp only [ResultFinalStateVPlaced, wsMetaPlaced]
    refine ⟨rfl, ⟨hrun_sf_2, hsp2.trans hsp'.symm, hal0, hal2, ?_, ?_, hcrl3, hvregs2⟩,
      ans, by simp [hmod], fun r hr => by simp [hload] at hr,
      by simp only [hmod]; exact ⟨hload ▸ hloadRel, trivial⟩,
      by simp only [hmod]; trivial, ?_, ?_⟩
    · simpa [wp_norm, arm64_norm] using hx29_2
    · simpa [wp_norm, arm64_norm] using hx27_2
    · simp only [wp_norm, arm64_norm, htr2, htrace, hmod, hload,
        Identity.IdentityStoreSpec.traceOfWith_load]
    · rw [hsp', hmod, hdraws]
      dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
      simpa only [wp_norm, arm64_norm, hx28_2, hx21_2, sepConj_assoc] using hmf3''
  · have ⟨hmod, hdraws⟩ := model_of_load_none C S x ans hload
    apply decSeg_of_sepWP_mid_placed hcrl2 hmm2 (mid := lsmpl.base 623)
    dsimp only [lsProg_463]
    wp_conv_pre => rw [hload]
    dsimp only [loadPollBranchRestPlaced]
    wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
    apply SepWP.pure_elim; rintro rfl
    wp_steps
    refine SepWP.done rfl hrun_sf_2 fun hcrl3 hmm3 => ?_
    apply decSeg_of_sepWPp_placed hmm3 (target := resultFinalPCPlaced)
    dsimp only [lsProg_463, resultFinalPCPlaced]
    have h03 : s0.trace <+: sf_2.trace := by
      rw [htr2, htrace]
      exact ⟨kit.loadEvs encRecord x.rem.val ans.loadSession, rfl⟩
    refine messageDecrypt_call_panic_then_wp_lscro hclone
      (x := (x.remA, s.sp + 0x5f0#64, x.rem.name))
      (F := F_clonePlaced A ctl kit ikit st0 ist0 x s0 s.sp)
      hcrl3 rfl
      (by simpa only [wp_norm, arm64_norm] using hrun_sf_2)
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2]; exact hal_s)
      (by simp only [wp_norm, arm64_norm]; rfl)
      (fun R' hm' => ?_)
      (fun sf => stringClone_onPanic_entails_placed (by simpa only [wp_norm, arm64_norm] using h03))
      (fun _ _ => rfl)
      ?_
    · dsimp only [CryptoVerification.withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl3.1, ?_⟩
      try dsimp only [stringCloneSpec]
      rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj, ← sepConj_assoc]
      refine ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      rw [show ((((((sf_2.writeReg64 (Reg.gpr 19#5) x.remA).writeReg64 (Reg.gpr 8#5) (s.sp + 1520#64)).writeReg64
            (Reg.gpr 0#5) x.remA).writeReg64 (Reg.gpr 30#5) (blkPl_463.base + 1204#64)).setPState
            (addsPState64 18446744073709551615#64 1#64)).setPC
            (lsmpl.base 623)).sp = s.sp by
        simpa only [wp_norm, arm64_norm] using hsp2]
      have hpre_ent := branch_none_pre_clone_entails_placed A ctl kit ikit st0 ist0 x s0 s.sp w1 w2 w3 w4 w5 w6 tail htail_len
      simp only [BitVec.zero_add, wp_norm] at hpre_ent hm'
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm'
    · intro sf4 hpc4 hrun4 hsp4 hcs4
      have hsp4' : sf4.sp = s.sp := by simpa only [wp_norm, arm64_norm, hsp2] using hsp4
      have hal4 : (sf4.sp &&& 15#64 == 0#64) = true := by rw [hsp4']; exact hal_s
      have hx19_4 : sf4.readReg64 (Reg.gpr 19#5) = x.remA := by
        simpa [wp_norm, arm64_norm] using hcs4.1
      have hx23_4 : sf4.readReg64 (Reg.gpr 23#5) = s.sp + 1520#64 := by
        have h := hcs4.2.2.2.2.1
        simp only [wp_norm, arm64_norm] at h
        exact h.trans hx23_2
      have hx27_4 : sf4.readReg64 (Reg.gpr 27#5) = x.ret := by
        have h := hcs4.2.2.2.2.2.2.2.2.1
        simp only [wp_norm, arm64_norm] at h
        exact h.trans hx27_2
      have hx29_4 : sf4.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 := by
        have h := hcs4.2.2.2.2.2.2.2.2.2.2.1
        simp only [wp_norm, arm64_norm] at h
        exact h.trans hx29_2
      have hvregs4 : calleeSavedVRegs sf4 = calleeSavedVRegs s0 :=
        hcs4.2.2.2.2.2.2.2.2.2.2.2.trans hvregs2
      dsimp only [stringCloneSpec]
      wp_simp_pre [wp_norm, arm64_norm, hsp2, sepConj_assoc]
      apply SepWP.pure_elim; intro htr4
      apply SepWP.fold (vecU8_unpack_for_noRecord A s.sp x.rem.name.bytes) (by sep_focus)
      wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_elim; intro cap
      apply SepWP.exists_elim; intro ptr
      apply SepWP.pure_elim; intro hcap_ne
      have hcond_cap : (cap + 3#64 != 0#64) = true :=
        bne_iff_ne.mpr (fun h => hcap_ne (by rw [show cap = cap + 3#64 - 3#64 by bv_arith, h]; rfl))
      dsimp only [F_clonePlaced]
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.pointsTo128_split64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_pure_left_comm]
      apply SepWP.exists_elim; intro _w8_320
      apply SepWP.exists_elim; intro _q1_310
      apply SepWP.exists_elim; intro _q0_300
      apply SepWP.exists_elim; intro _w8_5a0
      apply SepWP.exists_elim; intro _q1_590
      apply SepWP.exists_elim; intro _q0_580
      apply SepWP.exists_elim; intro _d1
      apply SepWP.exists_elim; intro _d0
      apply SepWP.exists_elim; intro pad
      apply SepWP.exists_elim; intro _b0
      apply SepWP.pure_elim; intro hpad
      obtain ⟨w4_pad, hw4_pad⟩ :=
        exists_unpack64_of_length_8 (bs := x.rem.device :: pad) (by simp [hpad])
      wp_steps
      wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd, ls_blockPlacement_ρ]
      apply SepWP.fold
        (repack_after_0x3a980_split64 s.sp ptr (BitVec.ofNat 64 x.rem.name.bytes.length)
           w4_pad (lsmpl.ρ msgDecryptStrSym) 22#64 x.rem.device pad hw4_pad)
        (by sep_focus)
      wp_simp_pre [sepConj_assoc]
      wp_steps
      refine SepWP.done rfl hrun4 fun hcrl5 hmf5 => ?_
      have htr4' : sf4.trace = s.trace := htr4.trans htr2
      have hmf5' := satisfies_rodata_msgDecryptStr_placed hcrl5.2 hmf5
      rw [← sepConj_assoc] at hmf5'
      have hmf5'' := Satisfies.mono
        (sepConj_mono_left (branch_none_post_entails_placed A ctl kit ikit st0 ist0 x s0 s.sp cap ptr w4_pad pad hpad hw4_pad)) hmf5'
      refine Or.inr (Or.inr ?_)
      dsimp only [ResultFinalStateVPlaced, wsMetaPlaced]
      refine ⟨rfl, ⟨hrun4, hsp4'.trans hsp'.symm, hal0, hal4, ?_, ?_, hcrl5, hvregs4⟩,
        ans, by simp [hmod], fun r hr => by simp [hload] at hr,
        by simp only [hmod]; exact ⟨hload ▸ hloadRel, trivial⟩,
        by simp only [hmod]; trivial, ?_, ?_⟩
      · simpa [wp_norm, arm64_norm] using hx29_4
      · simpa [wp_norm, arm64_norm] using hx27_4
      · simp only [wp_norm, arm64_norm, htr4', htrace, hmod, hload,
          Identity.IdentityStoreSpec.traceOfWith_load]
      · rw [hsp', hmod, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [wp_norm, arm64_norm, sepConj_assoc] using hmf5''
  · apply decSeg_of_sepWP_done_placed hcrl2 hmm2 (target := CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced)
    dsimp only [lsProg_463, CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced]
    wp_conv_pre => rw [hload, split_120_for_some s.sp]
    dsimp only [loadPollBranchRestPlaced]
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.pointsTo128_split64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_pure_left_comm]
    apply SepWP.exists_elim; intro _w8_154
    apply SepWP.exists_elim; intro _q1_144
    apply SepWP.exists_elim; intro _q0_134
    apply SepWP.exists_elim; intro _w2_130
    apply SepWP.exists_elim; intro _w1_128
    apply SepWP.exists_elim; intro _w0_120
    apply SepWP.exists_elim; intro g
    apply SepWP.pure_elim; rintro ⟨hscope, htail_inl, hlt, rfl, rfl, rfl, rfl⟩
    have hscopeAt : kit.ScopeAt Scope st0 x.rem.val rec := ⟨hscope, hload ▸ hloadRel⟩
    have hscope_in : RecordInScope rec := hH.scopeIn rec hscope
    have ⟨hne1, hne2, _⟩ := ne_neg_tags_of_lt_two_pow_63 hlt
    have hcond2 : (g.prevCap + 2#64 != 0#64) = true :=
      bne_iff_ne.mpr (fun h => hne2 (by rw [show g.prevCap = g.prevCap + 2#64 - 2#64 by bv_arith, h]; rfl))
    have hcond1 : (g.prevCap + 1#64 == 0#64) = false :=
      beq_eq_false_iff_ne.mpr (fun h => hne1 (by rw [show g.prevCap = g.prevCap + 1#64 - 1#64 by bv_arith, h]; rfl))
    wp_steps
    wp_call hmemcpy (s.sp + 0x158#64, s.sp + 0x328#64, tail)
    refine SepWP.done hpc_sf_3 hrun_sf_3 fun hcrl3 hmf3 => ?_
    have hsp3 : sf_3.sp = s.sp := hsp_sf_2.trans hsp2
    have hal3 : sf_3.spAligned = true := by simp only [State.spAligned, hsp3]; exact hal_s
    have htr3 : sf_3.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession := by
      rw [hpost, htr2, htrace]
    have hx19_3 : sf_3.readReg64 .x19 = x.remA := h
    have hx23_3 : sf_3.readReg64 .x23 = s.sp + 0x5f0#64 := h_4.trans hx23_2
    have hx24_3 : sf_3.readReg64 .x24 = s.sp + 0xca0#64 := h_5
    have hx27_3 : sf_3.readReg64 .x27 = x.ret := h_8.trans hx27_2
    have hx29_3 : sf_3.readReg64 .x29 = s0.sp - 96#64 := hcs_sf.trans hx29_2
    have hroot : rootStack ≤ s.sp.toNat := rootStack_le_sp hsp'.symm hsp_le
    have hpure3 : StoreKit.LibsignalCodeRoLoaded lsmpl sf_3.mem ∧ sf_3.spAligned = true ∧
        sf_3.readReg64 .x27 = x.ret ∧ sf_3.readReg64 .x19 = x.remA ∧
        sf_3.readReg64 .x23 = s.sp + 0x5f0#64 ∧ sf_3.readReg64 .x24 = s.sp + 0xca0#64 ∧
        rootStack ≤ s.sp.toNat :=
      ⟨hcrl3, hal3, hx27_3, hx19_3, hx23_3, hx24_3, hroot⟩
    have hmeta3 : wsMetaPlaced x s0 sf_3 :=
      ⟨hrun_sf_3, hsp3.trans hsp'.symm, hal0, hal3, hx29_3, hx27_3, hcrl3,
        hvregs_1.trans hvregs2⟩
    have hsome_ent := branch_some_common_entails_placed A ctl kit ikit st0 ist0 x s0 s.sp g rec w4 w5 w6 tail htail_inl
    simp only [BitVec.zero_add, wp_norm] at hsome_ent hmf3
    have hmf3' := Satisfies.mono (sepConj_mono_left hsome_ent) hmf3
    cases hcur : rec.currentSession with
    | none =>
      have hmf3'' := Satisfies.mono
        (sepConj_mono_left (regionNone_of_common_placed A ctl kit ikit st0 ist0 x s0 sf_3 s.sp g rec hsp' hsp3 hcur hpure3)) hmf3'
      simp only [sepConj_assoc] at hmf3''
      exact Or.inr (Or.inl ⟨hpc_sf_3, hmeta3, rec, g.prevCap, g.prevPtr,
        hload, hscopeAt, hcur, htr3, hmf3''⟩)
    | some ses =>
      have hmf3'' := Satisfies.mono
        (sepConj_mono_left (regionSome_of_common_placed C A ctl S kit ikit st0 ist0 x s0 sf_3 s.sp g rec ses hsp' hsp3 hscope_in hcur hpure3)) hmf3'
      rw [sepExists_sepConj_left, satisfies_sepExists] at hmf3''
      obtain ⟨G, hmf3''⟩ := hmf3''
      rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hmf3''
      obtain ⟨hw0, hmf3''⟩ := hmf3''
      simp only [sepConj_assoc] at hmf3''
      exact Or.inl ⟨hpc_sf_3, hmeta3, rec, ses, G, g.prevCap, g.prevPtr,
        hload, hscopeAt, hcur, hw0, htr3, hmf3''⟩


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch
