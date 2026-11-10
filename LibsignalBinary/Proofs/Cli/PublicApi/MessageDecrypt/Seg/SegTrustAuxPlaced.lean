/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrustAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust

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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust hiding trustPollOutPlacedRel trustPollOutPlacedRel_ok_false trustPollOutPlacedRel_ok_true trustPollOutPlacedRel_err wsTrustFixedEnvPlaced wsTrustFixedRestPlaced wsFixed_wsEnv_trust_split_placed wsFixed_wsEnv_trust_join_placed wsTrustCallPrePlaced wsTrustFramePlaced keyReady_entails_trustCallPre_placed wsTrustCallPostSpatialPlaced wsTrustPostCommonRestPlaced trustCallPost_entails_common_placed trustPostCommon_ok_entails_placed trustPostCommon_err_entails_placed

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


@[reducible] def trustPollOutPlacedRel (strPtr vt o2 o3 o4 o5 : BitVec 64)
    (b0 b3 : BitVec 8) (h1 : BitVec 16) : Except Unit Bool → Prop
  | .ok false => b0 = 0#8
  | .ok true => b0 = 1#8
  | .error () =>
    let o1 := strPtr.extractLsb' 0 32
    b0 = o1.extractLsb' 0 8 ∧
    h1 = o1.extractLsb' 8 16 ∧
    b3 = o1.extractLsb' 24 8 ∧
    pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 (.error ())

@[simp] theorem trustPollOutPlacedRel_ok_false (strPtr vt o2 o3 o4 o5 : BitVec 64)
    (b3 : BitVec 8) (h1 : BitVec 16) :
    trustPollOutPlacedRel strPtr vt o2 o3 o4 o5 0#8 b3 h1 (.ok false) := rfl

@[simp] theorem trustPollOutPlacedRel_ok_true (strPtr vt o2 o3 o4 o5 : BitVec 64)
    (b3 : BitVec 8) (h1 : BitVec 16) :
    trustPollOutPlacedRel strPtr vt o2 o3 o4 o5 1#8 b3 h1 (.ok true) := rfl

@[simp] theorem trustPollOutPlacedRel_err (strPtr vt w5 : BitVec 64) :
    trustPollOutPlacedRel strPtr vt
      (10#32 ++ strPtr.extractLsb' 32 32)
      4294967296#64
      (vt.extractLsb' 0 32 ++ 0#32)
      (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
      ((strPtr.extractLsb' 0 32).extractLsb' 0 8)
      ((strPtr.extractLsb' 0 32).extractLsb' 24 8)
      ((strPtr.extractLsb' 0 32).extractLsb' 8 16)
      (.error ()) :=
  ⟨rfl, rfl, rfl, pollOutPlacedRel_err strPtr vt w5⟩

def wsTrustFixedEnvPlaced [LibsignalPlacement] (A : RustAlloc) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ ikit.trustShimOff) ∗
  (ikit.trustFutVtOff ↦₆₄ᵣ ikit.trustFutDropOff) ∗
  ((ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.trustPollOff) ∗
  ikit.identityAt (s0.readReg64 .x5) ist ∗
  FromRecordCallees.lsLogOff ∗ protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt sp (trustCallStack ikit)

def wsTrustFixedRestPlaced (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (st : kit.StoreState) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  decLoadVtableAtV kit ∗ decStoreVtableAtV kit ∗ decSaveVtableAtV ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.loc x.locA ∗
  kit.storeAt (s0.readReg64 .x3) st ∗
  memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
    (wsCalleeStackV kit ikit - trustCallStack ikit)

theorem wsFixed_wsEnv_trust_split_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64) :
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0 ⊢
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        wsTrustFixedEnvPlaced A ikit x s0 sp ist ∗ wsTrustFixedRestPlaced A kit ikit x s0 sp st := by
  subst hsp
  have hjoin := wsCalleeStack_join_extra_placed kit ikit st ist s0
  refine Entails.trans (Entails.of_eq (show
    wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗ wsEnvPlaced A x (s0.sp - 0xee0#64) ∗
      decStoreExtraPlaced kit ikit st ist s0 =
    (stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
      (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ A.pool) by
    unfold wsEnvPlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hjoin) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  have hlt := s0.sp.isLt
  have hle : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by omega
  refine Entails.pure_right hbound ?_
  unfold wsFixedVPlaced wsArgCellsV decVtablesAtV decTrustVtableAtV wsTrustFixedEnvPlaced wsTrustFixedRestPlaced
  simp only [BitVec.zero_add]
  rw [stack_wsCalleeV_trustCall kit ikit (s0.sp - 0xee0#64) hn]
  exact Entails.of_eq (by ac_rfl)

theorem wsFixed_wsEnv_trust_join_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsTrustFixedEnvPlaced A ikit x s0 sp ist ∗ wsTrustFixedRestPlaced A kit ikit x s0 sp st ⊢
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0 := by
  subst hsp
  have hlt := s0.sp.isLt
  have hle : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by omega
  have hsplit := wsCalleeStack_split_extra_placed kit ikit st ist s0 hbound
  refine Entails.trans (Entails.of_eq (show
    wsTrustFixedEnvPlaced A ikit x s0 (s0.sp - 0xee0#64) ist ∗
      wsTrustFixedRestPlaced A kit ikit x s0 (s0.sp - 0xee0#64) st =
    (kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      (memRegion ((s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - trustCallStack ikit) ∗
        stackAt (s0.sp - 0xee0#64) (trustCallStack ikit))) ∗
    (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ A.pool) by
    unfold wsTrustFixedEnvPlaced wsTrustFixedRestPlaced wsFixedVPlaced wsArgCellsV decVtablesAtV decTrustVtableAtV
    simp only [BitVec.zero_add]
    ac_rfl)) ?_
  rw [← stack_wsCalleeV_trustCall kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  unfold wsEnvPlaced
  exact Entails.of_eq (by ac_rfl)

def wsTrustCallPrePlaced [LibsignalPlacement] (A : RustAlloc) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState)
    (c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 : BitVec 64) (d5 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ ikit.trustShimOff) ∗
  (ikit.trustFutVtOff ↦₆₄ᵣ ikit.trustFutDropOff) ∗
  ((ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.trustPollOff) ∗
  ikit.identityAt (s0.readReg64 .x5) ist ∗
  ((sp + 0x2a8#64) ↦₆₄ a0) ∗ ((sp + 0x2b0#64) ↦₆₄ a1) ∗
  ((sp + 0x2b8#64) ↦₆₄ a2) ∗ ((sp + 0x2c0#64) ↦₆₄ a3) ∗
  ((sp + 0x2d0#64) ↦₆₄ c0) ∗ ((sp + 0x2d8#64) ↦₆₄ c1) ∗
  ((sp + 0x4f0#64) ↦₆₄ d0) ∗ ((sp + 0x4f8#64) ↦₆₄ d1) ∗
  ((sp + 0x500#64) ↦₆₄ d2) ∗ ((sp + 0x508#64) ↦₆₄ d3) ∗ ((sp + 0x510#64) ↦₃₂ d5) ∗
  memRegion (sp + 0x5f0#64) 48 ∗
  ((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
  ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3) ∗
  FromRecordCallees.lsLogOff ∗ protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt sp (trustCallStack ikit)

def wsTrustFramePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) : SepProp :=
  wsTrustFixedRestPlaced A kit ikit x s0 sp st ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  (memRegion (sp + 0x300#64) 0x1f0 ∗ memRegion (sp + 0x514#64) 0x6c) ∗
  memRegion (sp + 0x580#64) 0x24 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x680) ∗
  memRegion (sp + 0xcc0#64) 0x140 ∗
  memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)

theorem keyReady_entails_trustCallPre_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (k0 k1 k2 k3 : BitVec 64)
    (hsp : sp = s0.sp - 0xee0#64)
    (hk_ca0 :
      ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) =
        (((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
          ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3))) :
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0) ⊢
    ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
    ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
      wsTrustCallPrePlaced A ikit x s0 sp ist c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 d5 ∗
      wsTrustFramePlaced C A ctl kit ikit x ans s0 sp st rec' pt := by
  refine Entails.trans (Entails.of_eq (show _ =
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
    (wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (wsFixed_wsEnv_trust_split_placed A kit ikit x s0 sp st ist hsp)) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  refine Entails.pure_right hbound ?_
  rw [hk_ca0, memRegion_300_9a0_split, memRegion_300_280_trust_split, memRegion_5a4_6fc_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x4f0#64) 0x24) ∗
    (wsTrustFixedEnvPlaced A ikit x s0 sp ist ∗
      (((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
        ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3)) ∗
      memRegion (sp + 0x5f0#64) 48 ∗
      wsTrustFramePlaced C A ctl kit ikit x ans s0 sp st rec' pt) by
    unfold wsTrustFramePlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (memRegion_32_entails_cells (sp + 0x2a8#64))
    (sepConj_mono (memRegion_16_entails_cells (sp + 0x2d0#64))
      (memRegion_36_entails_cells (sp + 0x4f0#64))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d0; apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2; apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d5; apply Entails.sepExists_elim; intro c0
  apply Entails.sepExists_elim; intro c1; apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1; apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right c0 (Entails.sepExists_right c1
        (Entails.sepExists_right d0 (Entails.sepExists_right d1
          (Entails.sepExists_right d2 (Entails.sepExists_right d3
            (Entails.sepExists_right d5 ?_))))))))))
  unfold wsTrustCallPrePlaced wsTrustFixedEnvPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

def wsTrustCallPostSpatialPlaced [LibsignalPlacement] (A : RustAlloc) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState)
    (k : IdentityKey) (ans_trust : Except Unit Bool)
    (box strPtr o2 o3 o4 o5 k0 k1 k2 k3 : BitVec 64) (b0 b3 : BitVec 8) (h1 : BitVec 16)
    (o6 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ ikit.trustShimOff) ∗
  (ikit.trustFutVtOff ↦₆₄ᵣ ikit.trustFutDropOff) ∗
  ((ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
  ((ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.trustPollOff) ∗
  ikit.identityAt (s0.readReg64 .x5) (ikit.trustUpdate ist x.rem.val k .receiving ans_trust) ∗
  ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
  ((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ ikit.trustFutVtOff) ∗
  ((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
  ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗ ((sp + 0x510#64) ↦₃₂ o6) ∗
  ((sp + 0x5f0#64) ↦₆₄ trustPollTag ans_trust) ∗
  ((sp + 0x5f8#64) ↦₈ b0) ∗ ((sp + 0x5f9#64) ↦₁₆ h1) ∗ ((sp + 0x5fb#64) ↦₈ b3) ∗
  ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
  ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗ ((sp + 0x61c#64) ↦₃₂ o6) ∗
  ((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
  ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3) ∗
  (if ans_trust.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
  FromRecordCallees.lsLogOff ∗ protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt sp (trustCallStack ikit)

def wsTrustPostCommonRestPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (k : IdentityKey) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  (memRegion (sp + 0x300#64) 0x1f0 ∗ memRegion (sp + 0x514#64) 0x6c) ∗
  memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
  decStoreExtraPlaced kit ikit st ist' s0

theorem trustCallPost_entails_common_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (ans_trust : Except Unit Bool)
    (box strPtr o2 o3 o4 o5 k0 k1 k2 k3 : BitVec 64) (b0 b3 : BitVec 8) (h1 : BitVec 16)
    (o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsTrustCallPostSpatialPlaced A ikit x s0 sp ist k ans_trust box strPtr o2 o3 o4 o5 k0 k1 k2 k3 b0 b3 h1 o6 ∗
      wsTrustFramePlaced C A ctl kit ikit x ans s0 sp st rec' pt ⊢
    (((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗
      ((sp + 0x510#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    (if ans_trust.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
    wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 sp st
      (ikit.trustUpdate ist x.rem.val k .receiving ans_trust) rec' pt k := by
  let ist' := ikit.trustUpdate ist x.rem.val k .receiving ans_trust
  refine Entails.trans (Entails.of_eq (show _ =
    ((((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ ikit.trustFutVtOff)) ∗
      (((sp + 0x5f0#64) ↦₆₄ trustPollTag ans_trust) ∗
        (((sp + 0x5f8#64) ↦₈ b0) ∗ ((sp + 0x5f9#64) ↦₁₆ h1) ∗ ((sp + 0x5fb#64) ↦₈ b3)) ∗
        (((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
          ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗
          ((sp + 0x61c#64) ↦₃₂ o6))) ∗
      (((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
        ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3)) ∗
      (wsTrustFixedEnvPlaced A ikit x s0 sp ist' ∗ wsTrustFixedRestPlaced A kit ikit x s0 sp st)) ∗
    ((((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗
      ((sp + 0x510#64) ↦₃₂ o6)) ∗
      memRegion (sp + 0x580#64) 0x24 ∗
      (if ans_trust.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
      wsMsgCells x sp ∗ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗
      (memRegion (sp + 0x300#64) 0x1f0 ∗ memRegion (sp + 0x514#64) 0x6c) ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x680) ∗
      memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsTrustCallPostSpatialPlaced wsTrustFramePlaced wsTrustFixedEnvPlaced
    ac_rfl)) ?_
  have h16 := cells_16_entails_memRegion (sp + 0x2d0#64) box ikit.trustFutVtOff
  have h48 := cells_48_trust_entails_memRegion (sp + 0x5f0#64) (trustPollTag ans_trust)
    o2 o3 o4 o5 b0 b3 h1 o6
  have h32 := cells_32_entails_memRegion (sp + 0xca0#64) k0 k1 k2 k3
  have hjoin := wsFixed_wsEnv_trust_join_placed A kit ikit x s0 sp st ist' hsp hbound
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16 h48 h32
  refine Entails.trans (sepConj_mono_left
    (sepConj_mono h16 (sepConj_mono h48 (sepConj_mono h32 hjoin)))) ?_
  unfold wsTrustPostCommonRestPlaced
  rw [← memRegion_5a4_85c_merge]
  exact Entails.of_eq (by ac_rfl)

theorem trustPostCommon_ok_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) :
    (((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗
      ((sp + 0x510#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist' rec' pt k ⊢
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist' s0 := by
  have h36 := cells_36_entails_memRegion (sp + 0x4f0#64) o2 o3 o4 o5 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36
  refine Entails.trans (sepConj_mono_left h36) ?_
  unfold wsTrustPostCommonRestPlaced
  rw [memRegion_300_b00_split, memRegion_300_280_trust_split]
  exact Entails.of_eq (by ac_rfl)

theorem trustPostCommon_err_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (pt : List (BitVec 8)) (k : IdentityKey)
    (strPtr vt x28 w20 w21 o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 (.error ())) :
    (strPtr ↦ᵣ storeHookStr) ∗
    ((((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗ ((sp + 0x510#64) ↦₃₂ o6) ∗
      ((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗ ((sp + 0x5a0#64) ↦₃₂ o6)) ∗
    wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist' rec' pt k) ⊢
    ∃∗ G : SessionGhost,
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.store ())) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist' s0 := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
    ((((sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sp + 0x4f8#64) ↦₆₄ o3) ∗
      ((sp + 0x500#64) ↦₆₄ o4) ∗ ((sp + 0x508#64) ↦₆₄ o5) ∗ ((sp + 0x510#64) ↦₃₂ o6)) ∗
    ((((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗
      ((sp + 0x5a0#64) ↦₃₂ o6)) ∗ (strPtr ↦ᵣ storeHookStr)) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      (memRegion (sp + 0x300#64) 0x1f0 ∗ memRegion (sp + 0x514#64) 0x6c) ∗
      memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist' s0)) by
    unfold wsTrustPostCommonRestPlaced; ac_rfl)) ?_
  have h36 := cells_36_entails_memRegion (sp + 0x4f0#64) o2 o3 o4 o5 o6
  have hst := stagedRes_storeErr_of_pollOutPlacedRel A strPtr vt x28 w20 w21 (sp + 0x580#64)
    o2 o3 o4 o5 o1 o6 hx28 hw1 hrel
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36 hst
  have hrec := sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec (sepConj_mono h36
    (sepConj_mono hst (sepConj_mono hpt
      (sepConj_mono_left (key_entails_memRegion_32 (sp + 0x2a8#64) k)))))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_300_280_trust_split]
  exact Entails.of_eq (by ac_rfl)


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
