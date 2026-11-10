/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustStepsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable `segTrust`: `CmStateVBudget` → `SaveStateVBudget` (`+0xa70..+0xd40`)
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustPlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustStepsPlacedBudget
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (
  cliEncCommonRest cliTrustPassive encCommonPlaced_eq trustBaseActivePlaced
  seam_mem_split_placed seam_mem_to_tail_placed trustActivePlaced
  trustBaseActive_join_extra_placed trustActive_split_extra_placed trustPollPlacedOut_words
)

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust hiding alloc_onPanic_entails_placed dealloc_placed_ok_at_enc stringClone_placed_ok_at_enc trustVtablesAt_placed_intro saveVtablesAt_placed_intro storeVtablesAt_placed_intro speStaged_storeErr_placed call_nopanic_placed call_alloc_placed call_rocl_alloc_placed call_rocl_nopanic_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem cs_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x19 = s0.readReg64 .x19 := h.1
private theorem cs_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x20 = s0.readReg64 .x20 := h.2.1
private theorem cs_x21 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x21 = s0.readReg64 .x21 := h.2.2.1
private theorem cs_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x22 = s0.readReg64 .x22 := h.2.2.2.1
private theorem cs_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x23 = s0.readReg64 .x23 := h.2.2.2.2.1
private theorem cs_x24 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x24 = s0.readReg64 .x24 := h.2.2.2.2.2.1
private theorem cs_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x25 = s0.readReg64 .x25 := h.2.2.2.2.2.2.1
private theorem cs_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x26 = s0.readReg64 .x26 := h.2.2.2.2.2.2.2.1
private theorem cs_x27 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x27 = s0.readReg64 .x27 := h.2.2.2.2.2.2.2.2.1
private theorem cs_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x28 = s0.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
private theorem cs_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x29 = s0.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
private theorem cs_vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2

private theorem protocolAddressAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    {addr} (addrA : BitVec 64) :
    protocolAddressAt (A.atState lim st s) addr addrA = protocolAddressAt A.repAlloc addr addrA := rfl

private theorem trustPassive_atState [LibsignalPlacement] {M : AllocCostModel}
    (ss_vt id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) (draws : Nat) (s0 : State) :
    cliTrustPassive ss_vt id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' m draws s0 =
      cliTrustPassive ss_vt id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0 := rfl

private theorem dropRecordSlots_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (sp : BitVec 64) (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (om : Option CiphertextMessage) (poll : SepProp) :
    dropRecordSlots (A.atState lim st s) sp scratch g rec ot om poll =
      dropRecordSlots A.repAlloc sp scratch g rec ot om poll := rfl

private theorem encStoreExtraPlaced_retag {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (kit : SessionStoreSpec A.repAlloc 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
        (retagIdentityStore (A' := A.atState lim st s) ikit) ist x s0 =
      encStoreExtraPlaced kit st0 ikit ist x s0 := rfl

/-! ## 1. E9 UntrustedIdentity Path (`+0xbc4..+0xd40`) -/

theorem trust_false_to_d40_placed [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    {id_vt : BitVec 64}
    {x : WithStoresEncGhost} {st_init st : M.σ} {k : IdentityKey} {F R R0 : SepProp} {s0 s : State}
    {next : State → Prop} {w1 : BitVec 64}
    (hfit : FitsEnv M lim st (StringCloneEnv x.rem.name))
    (hpc : s.pc = encEntryPlaced + 0xbc4#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64)
    (hx21 : s.readReg64 .x21 = w1)
    (hw1 : w1.setWidth 8 = 0#8)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = s.sp + 0x9d0#64)
    (hpref0 : s0.trace <+: s.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hm : s.mem ⊨ (trustBaseActivePlaced id_vt (A.atState lim st s) s.sp x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x970#64) 24 ∗
      memRegion (s.sp + 0x9d0#64) 24) ∗ (F ∗ R))
    (hcont : ∀ sm (evs : List AllocEvent) cap ptr devWord u9e0,
      Steps (lsProg_464 Hk) s sm →
      sm.pc = encEntryPlaced + 0xd40#64 →
      sm.status = .Running → sm.sp = s.sp → sm.spAligned = true →
      sm.trace = s.trace →
      StringCloneEnv x.rem.name evs →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x27 = speWord 12 →
      sm.readReg64 .x21 = cap →
      sm.readReg64 .x23 = ptr →
      devWord.setWidth 8 = x.rem.device →
      (sm.mem ⊨ (trustBaseActivePlaced id_vt (A.atState lim (M.stepEvents evs st) sm) s.sp x k ∗
        memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗
        (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x9e0#64) ↦₆₄ u9e0)) ∗
        vecU8Body A.repAlloc cap ptr x.rem.name.bytes) ∗ (F ∗ R)) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
        x st_init R0 s0 sm next) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hm1 : s.mem ⊨ (((s.sp + 0xc0#64) ↦₆₄ x.remA) ∗ FromRecordCallees.lsLogOff) ∗
      ((((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ id_vt ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        stackAt s.sp encSubStack ∗ A.pool lim st s ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R) := by
    dsimp only [trustBaseActivePlaced, RustCliAllocBudget.atState_pool] at hm
    rw [protocolAddressAt_atState] at hm
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  refine SegExitBudget.of_sepWP hm1
    (step_bc4_ok_false_to_d18_placed hpc hrun hsp_align hx27 hx21 hw1) ?_
  rintro s1 P1 _ hsteps1 hpc1 hrun1 hm2
    ⟨hvm1, rfl, hsp1, htr1, hx0_1, hx8_1, hx21_1, hx30_1, hx19_1, hx25_1, hx26_1, hx28_1, hx29_1, hvregs_1⟩
  rw [← A.pool_transport lim st s s1 hvm1] at hm2
  have hsp1_al : s1.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp1
  have hpref1 : s0.trace <+: s1.trace := by rw [htr1]; exact hpref0
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hm3 : s1.mem ⊨ (stringCloneBudgetSpec M A lim).pre (x.remA, s.sp + 0x580#64, x.rem.name, st) s1 ∗
      (((((x.remA + 0x18#64) ↦₈ x.rem.device) ∗ memRegion (x.remA + 0x19#64) 7 ∗
        memRegion (s.sp + 0x598#64) 24 ∗
        memRegion (s.sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ id_vt ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ FromRecordCallees.lsLogOff ∗
        memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R) := by
    dsimp only [stringCloneBudgetSpec]
    rw [hsp1]
    rw [protocolAddressAt,
        show (48 : Nat) = 24 + 24 by decide,
        memRegion_split (s.sp + 0x580#64) 24 24 (by decide),
        stackAt_encSubStack_split s.sp extHookStack (by decide)] at hm2
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_1, hx8_1, hfit⟩, Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm2⟩
  refine call_rocl_alloc_placed (stringClone_placed_ok_at_enc env) (x.remA, s.sp + 0x580#64, x.rem.name, st)
    hpc1 hrun1 hsp1_al hx30_1 hpref1 hcrl1 hm3 ?_
  intro s2 hsteps2 hpc2 hrun2 hsp2 hsp2_al hcs2 _hcrl2 hm4
  dsimp only [stringCloneBudgetSpec] at hm4
  rw [hsp1] at hsp2 hm4
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨evs, ⟨htr2, hevs⟩, hm4⟩ := hm4
  set st1 := M.stepEvents evs st
  rw [vecU8_eq_exists_body] at hm4
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm4
  obtain ⟨cap, ptr, hm4⟩ := hm4
  have hm4' : s2.mem ⊨ memRegion (s.sp + 0x598#64) 24 ∗
      ((vecGhostAt A.repAlloc x.rem.name x.remA ∗ ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
        memRegion (x.remA + 0x19#64) 7 ∗
        (s.sp + 0x580#64) ↦₆₄ cap ∗ (s.sp + 0x580#64 + 8#64) ↦₆₄ ptr ∗
        (s.sp + 0x580#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length ∗
        vecU8Body A.repAlloc cap ptr x.rem.name.bytes ∗
        stackAt s.sp encSubStack ∗ A.pool lim st1 s2 ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ id_vt ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ FromRecordCallees.lsLogOff ∗
        memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R) := by
    rw [stackAt_encSubStack_split s.sp extHookStack (by decide)]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm4
  obtain ⟨b598, hm5⟩ := memRegion24_exists_byte_rest (s.sp + 0x598#64) hm4'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm5
  have hm6 : s2.mem ⊨ (((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      ((s2.sp + 0x580#64) ↦₆₄ cap) ∗ ((s2.sp + 0x588#64) ↦₆₄ ptr) ∗
      ((s2.sp + 0x598#64) ↦₈ b598)) ∗
      (((vecGhostAt A.repAlloc x.rem.name x.remA ∗ memRegion (x.remA + 0x19#64) 7 ∗
        memRegion (s.sp + 0x599#64) 7 ∗ memRegion (s.sp + 0x5a0#64) 16 ∗
        (s.sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length ∗
        vecU8Body A.repAlloc cap ptr x.rem.name.bytes ∗
        stackAt s.sp encSubStack ∗ A.pool lim st1 s2 ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ id_vt ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ FromRecordCallees.lsLogOff ∗
        memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R) := by
    rw [hsp2]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm5
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2_al
  have hx21_2 : s2.readReg64 .x21 = x.remA := (cs_x21 hcs2).trans hx21_1
  refine SegExitBudget.of_sepWP hm6 (step_d1c_to_d2c_placed hpc2 hrun2 hsp2_align hx21_2) ?_
  rintro s3 P3 _ hsteps3 hpc3 hrun3 hm7
    ⟨hvm3, rfl, hsp3, htr3, hx21_3, hx23_3, hx19_3, hx25_3, hx26_3, hx28_3, hx29_3, hvregs_3⟩
  rw [hsp2] at hsp3 hm7
  rw [← A.pool_transport lim st1 s2 s3 hvm3] at hm7
  have hm8 : s3.mem ⊨ (((s.sp + 0x598#64) ↦₈ x.rem.device) ∗ memRegion (s.sp + 0x598#64 + 1#64) 7) ∗
      (memRegion (s.sp + 0x9d0#64) 24 ∗
      ((protocolAddressAt A.repAlloc x.rem x.remA ∗
        (s.sp + 0x580#64) ↦₆₄ cap ∗ (s.sp + 0x588#64) ↦₆₄ ptr ∗
        memRegion (s.sp + 0x5a0#64) 16 ∗
        (s.sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length ∗
        vecU8Body A.repAlloc cap ptr x.rem.name.bytes ∗
        stackAt s.sp encSubStack ∗ A.pool lim st1 s3 ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ id_vt ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ FromRecordCallees.lsLogOff ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x970#64) 24) ∗ F ∗ R)) := by
    unfold protocolAddressAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7
  have hm9 := Satisfies.mono (sepConj_mono_left
    (pointsTo8_memRegion7_exists_word64 (s.sp + 0x598#64) x.rem.device)) hm8
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hm9
  obtain ⟨devWord, hdev, hm9⟩ := hm9
  have hm10 : s3.mem ⊨ memRegion (s.sp + 0x9d0#64) 24 ∗
      (((s.sp + 0x598#64) ↦₆₄ devWord ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        (s.sp + 0x580#64) ↦₆₄ cap ∗ (s.sp + 0x588#64) ↦₆₄ ptr ∗
        memRegion (s.sp + 0x5a0#64) 16 ∗
        (s.sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length ∗
        vecU8Body A.repAlloc cap ptr x.rem.name.bytes ∗
        stackAt s.sp encSubStack ∗ A.pool lim st1 s3 ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ id_vt ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ FromRecordCallees.lsLogOff ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x970#64) 24) ∗ F ∗ R) :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm9
  obtain ⟨u9d0, u9d8, u9e0, hm11⟩ := memRegion24_exists_words3 (s.sp + 0x9d0#64) hm10
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm11
  have hm12 : s3.mem ⊨ (((s3.sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
      ((s3.sp + 0x598#64) ↦₆₄ devWord) ∗
      ((s3.sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((s3.sp + 0x9d8#64) ↦₆₄ u9d8)) ∗
      ((((s.sp + 0x9e0#64) ↦₆₄ u9e0 ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        (s.sp + 0x580#64) ↦₆₄ cap ∗ (s.sp + 0x588#64) ↦₆₄ ptr ∗
        memRegion (s.sp + 0x5a0#64) 16 ∗
        vecU8Body A.repAlloc cap ptr x.rem.name.bytes ∗
        stackAt s.sp encSubStack ∗ A.pool lim st1 s3 ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ id_vt ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ FromRecordCallees.lsLogOff ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x970#64) 24) ∗ F) ∗ R) := by
    rw [hsp3]
    exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm11
  have hx25_3' : s3.readReg64 .x25 = s3.sp + 0x580#64 := by
    rw [hsp3, hx25_3, cs_x25 hcs2, hx25_1, hx25]
  have hx26_3' : s3.readReg64 .x26 = s3.sp + 0x9d0#64 := by
    rw [hsp3, hx26_3, cs_x26 hcs2, hx26_1, hx26]
  refine SegExitBudget.of_sepWP hm12 (step_d2c_to_d40_placed hpc3 hrun3 hx25_3' hx26_3') ?_
  rintro s4 P4 _ hsteps4 hpc4 hrun4 hm13
    ⟨hvm4, rfl, hsp4, htr4, hx27_4, hx19_4, hx21_4, hx23_4, hx26_4, hx28_4, hx29_4, hvregs_4⟩
  rw [hsp3] at hsp4 hm13
  rw [← A.pool_transport lim st1 s3 s4 hvm4] at hm13
  have hm14 : s4.mem ⊨
      (((s.sp + 0x580#64) ↦₆₄ cap) ∗ ((s.sp + 0x580#64 + 8#64) ↦₆₄ ptr) ∗
        ((s.sp + 0x580#64 + 16#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
        ((s.sp + 0x580#64 + 24#64) ↦₆₄ devWord) ∗ memRegion (s.sp + 0x580#64 + 32#64) 16) ∗
      (((trustBaseActivePlaced id_vt (A.atState lim st1 s4) s.sp x k ∗
        memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x970#64) 24 ∗
        (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x9e0#64) ↦₆₄ u9e0)) ∗
        vecU8Body A.repAlloc cap ptr x.rem.name.bytes) ∗ F) ∗ R) := by
    dsimp only [trustBaseActivePlaced, RustCliAllocBudget.atState_pool]
    rw [protocolAddressAt_atState]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm13
  have hm15 := Satisfies.mono (sepConj_mono_left
    (words4_memRegion16_entails_memRegion48 (s.sp + 0x580#64) cap ptr
      (BitVec.ofNat 64 x.rem.name.bytes.length) devWord)) hm14
  have hsteps_all := hsteps1.trans (hsteps2.trans (hsteps3.trans hsteps4))
  have hx29_4' : s4.readReg64 .x29 = s.readReg64 .x29 := by
    rw [hx29_4, hx29_3, cs_x29 hcs2, hx29_1]
  refine hcont s4 evs cap ptr devWord u9e0 hsteps_all hpc4 hrun4 hsp4
    (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp4) (by rw [htr4, htr3, htr2, htr1]) hevs
    (by rw [hx19_4, hx19_3, cs_x19 hcs2, hx19_1])
    (by rw [hx26_4, hx26_3, cs_x26 hcs2, hx26_1])
    (by rw [hx28_4, hx28_3, cs_x28 hcs2, hx28_1])
    hx29_4'
    (by rw [hvregs_4, hvregs_3, cs_vregs hcs2, hvregs_1])
    hx27_4
    (by rw [hx21_4, hx21_3]) (by rw [hx23_4, hx23_3]) hdev
    (Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm15)

/-! ## 2. E7 + E7r Path (`+0xa70..+0xbc4`) -/

theorem trust_to_bc4_placed [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    {x : WithStoresEncGhost} {st_init st : M.σ} {k : IdentityKey} {F R R0 : SepProp} {s0 s : State}
    {next : State → Prop}
    (hfit : FitsEnv M lim st (TrustStepEnv ikit ikitEnv ist0 x.rem.val k))
    (haddr : ikit.addrOk x.rem.val)
    (henv : ∀ s', Steps (lsProg_464 Hk) s s' → s'.trace = s.trace → ikit.envOk s'.fs.files)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hpc : s.pc = encEntryPlaced + 0xa70#64) (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true) (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hpref0 : s0.trace <+: s.trace) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hm : s.mem ⊨ (trustVtablesAt ikit ∗
      trustActivePlaced (retagIdentityStore (A' := A.atState lim st s) ikit) ist0
        s.sp (encSubStackV kit ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ (F ∗ R))
    (hcont : ∀ sm (evs : List AllocEvent) (ans : Except Unit Bool) (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      Steps (lsProg_464 Hk) s sm → sm.pc = encEntryPlaced + 0xbc4#64 →
      sm.status = .Running → sm.sp = s.sp → sm.spAligned = true →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      ikit.trustRel ist0 x.rem.val k .sending ans →
      sm.trace = s.trace ++ ikit.trustEvs x.rem.val k .sending ans →
      TrustStepEnv ikit ikitEnv ist0 x.rem.val k evs →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x27 = w0 → sm.readReg64 .x21 = w1 → sm.readReg64 .x23 = w2 →
      (match ans with
       | .ok t => w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1.setWidth 8 = (if t then 1#8 else 0#8) ∧ H = emp
       | .error () => w0 = 0x800000000000001A#64 ∧ w2 = 10#64 ∧ w3 = 1#64 ∧ H = (w1 ↦ᵣ storeHookStr)) →
      (sm.mem ⊨ (trustActivePlaced (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sm) ikit)
          (ikit.trustUpdate ist0 x.rem.val k .sending ans)
          s.sp (encSubStackV kit ikit) x k ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
        memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ (F ∗ R)) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
        x st_init R0 s0 sm next) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hm1 : s.mem ⊨ (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
      ((s.sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((s.sp + 0xe0#64) ↦₆₄ x.idA) ∗
      ((s.sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗ ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff))) ∗
      (((((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0 ∗
        stackAt s.sp (encSubStackV kit ikit) ∗ A.pool lim st s ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R) := by
    dsimp only [trustVtablesAt, trustActivePlaced, retagIdentityStore, RustCliAllocBudget.atState_pool] at hm
    rw [protocolAddressAt_atState] at hm
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  refine SegExitBudget.of_sepWP hm1 (step_a70_to_a84_placed hpc hrun hsp_align) ?_
  rintro s1 P1 _ hsteps1 hpc1 hrun1 hm2
    ⟨hvm1, rfl, hsp1, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx30_1, hx19_1, hx20_1, hx25_1, hx26_1, hx28_1, hx29_1, hvregs_1⟩
  rw [← A.pool_transport lim st s s1 hvm1] at hm2
  have hsp1_al : s1.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp1
  have hpref1 : s0.trace <+: s1.trace := by rw [htr1]; exact hpref0
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hm3 : s1.mem ⊨ (kitTrustShimBudgetSpec M A lim ikit).pre
        (⟨x.idA, x.remA, s.sp + 0x350#64⟩, directionByte .sending, st) s1 ∗
      ((((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - ikit.trustShimStack) ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitTrustShimBudgetSpec, directionByte]; rw [hsp1]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.trustShimStack
          (trustShimStack_le_encSubStackV kit ikit)] at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_1, hx1_1, hx2_1, by rw [hx3_1]; rfl, hfit.seq_left⟩,
      Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm2⟩
  refine call_rocl_alloc_placed (env.ikitOk.trustShim (by decide))
    (⟨x.idA, x.remA, s.sp + 0x350#64⟩, directionByte .sending, st)
    hpc1 hrun1 hsp1_al hx30_1 hpref1 hcrl1 hm3 ?_
  intro s2 hsteps2 hpc2 hrun2 hsp2 hsp2_al hcs2 hcrl2 hm4
  dsimp only [kitTrustShimBudgetSpec] at hm4
  rw [hsp1] at hsp2 hm4
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨evs₁, ⟨hx1_2, _, _, htr2, hevs1⟩, hm4⟩ := hm4
  set st1 := M.stepEvents evs₁ st
  set box := s2.readReg64 .x0
  have hm4' : s2.mem ⊨ memRegion (s.sp + 0x470#64) 16 ∗
      ((A.live box ikit.trustBoxSize 8 ∗
        ikit.trustBoxAt box x.idA x.remA (s.sp + 0x350#64) 0#8 (directionByte .sending) ∗
        ikit.identityAt x.idA ist0 ∗ A.pool lim st1 s2 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.trustShimStack
          (trustShimStack_le_encSubStackV kit ikit)]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm4
  obtain ⟨u470, u478, hm5⟩ := memRegion16_exists_words2 (s.sp + 0x470#64) hm4'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm5
  have hm6 : s2.mem ⊨ (((s2.sp + 0x470#64) ↦₆₄ u470) ∗ ((s2.sp + 0x478#64) ↦₆₄ u478) ∗
      ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff))) ∗
      (((A.live box ikit.trustBoxSize 8 ∗
        ikit.trustBoxAt box x.idA x.remA (s.sp + 0x350#64) 0#8 (directionByte .sending) ∗
        ikit.identityAt x.idA ist0 ∗ A.pool lim st1 s2 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R) := by
    rw [hsp2]; exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm5
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2_al
  refine SegExitBudget.of_sepWP hm6 (step_a88_to_a9c_placed hpc2 hrun2 hsp2_align rfl hx1_2) ?_
  rintro s3 P3 _ hsteps3 hpc3 hrun3 hm7
    ⟨hvm3, rfl, hsp3, htr3, hx0_3, _, hx8_3, hx30_3, hx19_3, hx20_3, hx25_3, hx26_3, hx28_3, hx29_3, hvregs_3⟩
  rw [hsp2] at hsp3 hx8_3 hm7
  rw [← A.pool_transport lim st1 s2 s3 hvm3] at hm7
  have hsp3_al : s3.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp3
  have hpref3 : s0.trace <+: s3.trace := by rw [htr3, htr2]; exact hpref1
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps3.keepsFrozen
  let pollCall : IdentityPollCall := ⟨box, s.sp + 0x580#64, ⟨x.remA, x.rem, s.sp + 0x350#64, k⟩⟩
  have hm8 : s3.mem ⊨ (kitTrustPollBudgetSpecI M A lim ikit ikitEnv).pre (pollCall, .sending, x.idA, ist0, st1) s3 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.trustFutVtOff) ∗
        A.live box ikit.trustBoxSize 8 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - ikit.trustPollStack) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitTrustPollBudgetSpecI, StoreKit.withLsLogOff, kitTrustPollBudgetSpecE,
      kitTrustPollBudgetSpec, withEnvPre, pollCall]
    rw [hsp3]; rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.trustPollStack
      (trustPollStack_le_encSubStackV kit ikit)] at hm7
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨henv s3 (hsteps1.trans (hsteps2.trans hsteps3)) (by rw [htr3, htr2, htr1]),
      ⟨hx0_3, hx8_3, haddr, (hfit.seq_right hevs1).seq_left⟩, Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7⟩
  refine call_rocl_alloc_placed (env.ikitOk.trustPoll (by decide)) (pollCall, .sending, x.idA, ist0, st1)
    hpc3 hrun3 hsp3_al hx30_3 hpref3 hcrl3 hm8 ?_
  intro s4 hsteps4 hpc4 hrun4 hsp4 hsp4_al hcs4 hcrl4 hm9
  dsimp only [kitTrustPollBudgetSpecI, StoreKit.withLsLogOff, kitTrustPollBudgetSpecE,
    kitTrustPollBudgetSpec, withEnvPre, pollCall] at hm9
  rw [hsp3] at hsp4 hm9
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm9
  obtain ⟨ans, evs₂, ⟨htrustRel, htr4, hevs2⟩, hm9⟩ := hm9
  set st2 := M.stepEvents evs₂ st1
  have hm9_poll : s4.mem ⊨ trustPollPlacedOutAt (s.sp + 0x580#64) ans ∗
      (memRegion (s.sp + 0x970#64) 24 ∗
      (((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.trustFutVtOff) ∗
        A.live box ikit.trustBoxSize 8 ∗
        ikit.trustBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 (directionByte .sending) ∗
        ikit.identityAt x.idA (ikit.trustUpdate ist0 x.rem.val k .sending ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R)) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.trustPollStack
          (trustPollStack_le_encSubStackV kit ikit)]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm9
  have hm10 := Satisfies.mono (sepConj_mono_left (trustPollPlacedOut_words (s.sp + 0x580#64) ans)) hm9_poll
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm10
  obtain ⟨w0, w1, w2, w3, w4, w5, H, ⟨hw0, hans⟩, hm10⟩ := hm10
  have hm10' : s4.mem ⊨ memRegion (s.sp + 0x970#64) 24 ∗
      (((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x580#64 + 8#64) ↦₆₄ w1 ∗
        (s.sp + 0x580#64 + 0x10#64) ↦₆₄ w2 ∗ (s.sp + 0x580#64 + 0x18#64) ↦₆₄ w3 ∗
        (s.sp + 0x580#64 + 0x20#64) ↦₆₄ w4 ∗ (s.sp + 0x580#64 + 0x28#64) ↦₆₄ w5 ∗ H ∗
        (s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.trustFutVtOff) ∗
        A.live box ikit.trustBoxSize 8 ∗
        ikit.trustBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 (directionByte .sending) ∗
        ikit.identityAt x.idA (ikit.trustUpdate ist0 x.rem.val k .sending ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R) :=
    Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm10
  obtain ⟨u970, u978, u980, hm11⟩ := memRegion24_exists_words3 (s.sp + 0x970#64) hm10'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm11
  have hm12 : s4.mem ⊨ (((s4.sp + 0x470#64) ↦₆₄ box) ∗ ((s4.sp + 0x478#64) ↦₆₄ (0#64 + ikit.trustFutVtOff)) ∗
      ((s4.sp + 0x580#64) ↦₆₄ w0) ∗ ((s4.sp + 0x588#64) ↦₆₄ w1) ∗ ((s4.sp + 0x590#64) ↦₆₄ w2) ∗
      ((s4.sp + 0x598#64) ↦₆₄ w3) ∗ ((s4.sp + 0x5a0#64) ↦₆₄ w4) ∗ ((s4.sp + 0x5a8#64) ↦₆₄ w5) ∗
      ((s4.sp + 0x970#64) ↦₆₄ u970) ∗ ((s4.sp + 0x978#64) ↦₆₄ u978) ∗ ((s4.sp + 0x980#64) ↦₆₄ u980) ∗
      ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff))) ∗
      (((A.live box ikit.trustBoxSize 8 ∗
        ikit.trustBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 (directionByte .sending) ∗
        ikit.identityAt x.idA (ikit.trustUpdate ist0 x.rem.val k .sending ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ F) ∗ R) := by
    rw [hsp4]; exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm11
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4_al
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x580#64 := by
    rw [hsp4, cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1, hx25]
  refine SegExitBudget.of_sepWP hm12
    (step_aa0_to_bac_placed (ikit.trustFutDrop_ne_zero (by decide)) hpc4 hrun4 hsp4_align hx25_4 hw0) ?_
  rintro s5 _ _ hsteps5 hpc5 hrun5 hm13
    ⟨hvm5, rfl, hsp5, htr5, hx0_5, hx21_5, hx22_5, hx23_5, hx24_5, hx27_5, hx30_5,
      hx19_5, hx20_5, hx25_5, hx26_5, hx28_5, hx29_5, hvregs_5⟩
  rw [hsp4] at hsp5 hm13
  rw [← A.pool_transport lim st2 s4 s5 hvm5] at hm13
  have hsp5_al : s5.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp5
  have hm14 : s5.mem ⊨ futDropBudgetSpec.pre () s5 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.trustFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x970#64) ↦₆₄ w3 ∗ (s.sp + 0x978#64) ↦₆₄ w4 ∗ (s.sp + 0x980#64) ↦₆₄ w5 ∗
        ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff))) ∗
      ((A.live box ikit.trustBoxSize 8 ∗
        ikit.trustBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 (directionByte .sending) ∗
        ikit.identityAt x.idA (ikit.trustUpdate ist0 x.rem.val k .sending ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s5 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ F)) ∗ R) := by
    dsimp only [futDropBudgetSpec]; rw [emp_sepConj]; exact Eq.mp (congrArg (s5.mem ⊨ ·) (by ac_rfl)) hm13
  refine call_rocl_nopanic_placed (env.ikitOk.trustFutDrop (by decide)) ()
    hpc5 hrun5 hsp5_al hx30_5 (hcrl4.of_keepsFrozen hsteps5.keepsFrozen) hm14 ?_
  intro s6 hsteps6 hpc6 hrun6 hsp6 hsp6_al hcs6 hm15
  dsimp only [futDropBudgetSpec] at hm15; rw [hsp5] at hsp6; rw [satisfies_pure_sepConj] at hm15
  obtain ⟨⟨htr6, hvm6⟩, hm15⟩ := hm15
  rw [← A.pool_transport lim st2 s5 s6 hvm6] at hm15
  have hm15_box : s6.mem ⊨
      ikit.trustBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 (directionByte .sending) ∗
      ((((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64)) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.trustFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x970#64) ↦₆₄ w3 ∗ (s.sp + 0x978#64) ↦₆₄ w4 ∗ (s.sp + 0x980#64) ↦₆₄ w5 ∗
        ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
        A.live box ikit.trustBoxSize 8 ∗
        ikit.identityAt x.idA (ikit.trustUpdate ist0 x.rem.val k .sending ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s6 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ F) ∗ R)) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15
  have hm15' := Satisfies.mono (sepConj_mono_left
    (ikit.trustBoxAt_memRegion box x.idA x.remA (s.sp + 0x350#64) 1#8 (directionByte .sending))) hm15_box
  have hm16 : s6.mem ⊨ (((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
      ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64)) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.trustFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x970#64) ↦₆₄ w3 ∗ (s.sp + 0x978#64) ↦₆₄ w4 ∗ (s.sp + 0x980#64) ↦₆₄ w5 ∗
        ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗
        memRegion box ikit.trustBoxSize ∗ A.live box ikit.trustBoxSize 8 ∗
        ikit.identityAt x.idA (ikit.trustUpdate ist0 x.rem.val k .sending ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s6 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗
        ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ F) ∗ R) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15'
  have hx22_6 : s6.readReg64 .x22 = 0#64 + ikit.trustFutVtOff := (cs_x22 hcs6).trans hx22_5
  have hx24_6 : s6.readReg64 .x24 = box := (cs_x24 hcs6).trans hx24_5
  refine SegExitBudget.of_sepWP hm16
    (step_bb0_to_bc0_placed ikit.trustBoxSize_ne_zero hpc6 hrun6 hx22_6 hx24_6) ?_
  rintro s7 P7 _ hsteps7 hpc7 hrun7 hm17
    ⟨hvm7, rfl, hsp7, htr7, hx0_7, hx1_7, hx2_7, hx30_7,
      hx19_7, hx20_7, hx21_7, hx23_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hvregs_7⟩
  rw [hsp6] at hsp7
  rw [← A.pool_transport lim st2 s6 s7 hvm7] at hm17
  have hsp7_al : s7.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp7
  have hm18 : s7.mem ⊨ (rustCliDeallocBudgetSpec M A lim).pre (box, ikit.trustBoxSize, 8, st2) s7 ∗
      (((trustVtablesAt ikit ∗
        ((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.trustFutVtOff)) ∗
        ((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
          (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5) ∗
        (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - allocHookStack) ∗
        ikit.identityAt x.idA (ikit.trustUpdate ist0 x.rem.val k .sending ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ F) ∗ R) := by
    dsimp only [rustCliDeallocBudgetSpec, trustVtablesAt]; rw [hsp7]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
          (allocHookStack_le_encSubStackV kit ikit)] at hm17
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_7, by rw [hx1_7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ikit.trustBoxSize_lt],
      by rw [hx2_7]; rfl,
      by rw [hx30_7]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 464 0xbc4#64 (by decide) (by decide)⟩,
      Eq.mp (congrArg (s7.mem ⊨ ·) (by ac_rfl)) hm17⟩
  refine call_nopanic_placed (dealloc_placed_ok_at_enc env) (box, ikit.trustBoxSize, 8, st2)
    hpc7 hrun7 hsp7_al hx30_7 hm18 ?_
  intro s8 hsteps8 hpc8 hrun8 hsp8 hsp8_al hcs8 hm19
  dsimp only [rustCliDeallocBudgetSpec] at hm19; rw [hsp7] at hsp8 hm19
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm19
  obtain ⟨⟨hpres8, _⟩, hm19⟩ := hm19
  have htr8 : s8.trace = s7.trace := hpres8.2.1
  let evs_all := evs₁ ++ (evs₂ ++ rustDeallocEvents ikit.trustBoxSize 8)
  have hevs_all : TrustStepEnv ikit ikitEnv ist0 x.rem.val k evs_all :=
    Or.inr ⟨evs₁, evs₂ ++ rustDeallocEvents ikit.trustBoxSize 8, rfl, hevs1,
      Or.inr ⟨evs₂, rustDeallocEvents ikit.trustBoxSize 8, rfl, hevs2, rfl⟩⟩
  have hst_all : M.stepEvents (rustDeallocEvents ikit.trustBoxSize 8) st2 = M.stepEvents evs_all st := by
    simp only [evs_all, M.stepEvents_append, st1, st2]
  rw [hst_all] at hm19
  have hm20 : s8.mem ⊨ trustVtablesAt ikit ∗
      ((((s.sp + 0x470#64) ↦₆₄ box) ∗ ((s.sp + 0x470#64 + 8#64) ↦₆₄ (0#64 + ikit.trustFutVtOff))) ∗
      (((s.sp + 0x580#64) ↦₆₄ w0) ∗ ((s.sp + 0x580#64 + 8#64) ↦₆₄ w1) ∗
        ((s.sp + 0x580#64 + 16#64) ↦₆₄ w2) ∗ ((s.sp + 0x580#64 + 24#64) ↦₆₄ w3) ∗
        ((s.sp + 0x580#64 + 32#64) ↦₆₄ w4) ∗ ((s.sp + 0x580#64 + 40#64) ↦₆₄ w5)) ∗
      ((trustActivePlaced (retagIdentityStore (A' := A.atState lim (M.stepEvents evs_all st) s8) ikit)
          (ikit.trustUpdate ist0 x.rem.val k .sending ans) s.sp (encSubStackV kit ikit) x k ∗
        (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
        memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ (F ∗ R))) := by
    dsimp only [trustActivePlaced, retagIdentityStore, RustCliAllocBudget.atState_pool]
    rw [protocolAddressAt_atState]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
          (allocHookStack_le_encSubStackV kit ikit)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm19
  have hm21 := Satisfies.mono (sepConj_mono
    (words2_entails_memRegion16 (s.sp + 0x470#64) box (0#64 + ikit.trustFutVtOff))
    (sepConj_mono_left (words6_entails_memRegion48 (s.sp + 0x580#64) w0 w1 w2 w3 w4 w5)))
    (Satisfies.of_sep_right hm20)
  have hsteps_tail := hsteps5.trans (hsteps6.trans (hsteps7.trans hsteps8))
  have hcrl8 : StoreKit.LibsignalCodeRoLoaded lsmpl s8.mem := hcrl4.of_keepsFrozen hsteps_tail.keepsFrozen
  have hsteps_all := hsteps1.trans (hsteps2.trans (hsteps3.trans (hsteps4.trans hsteps_tail)))
  refine hcont s8 evs_all ans w0 w1 w2 w3 w4 w5 H hsteps_all hpc8 hrun8 hsp8 hsp8_al hcrl8 htrustRel
    (by rw [htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1])
    hevs_all
    (by rw [cs_x19 hcs8, hx19_7, cs_x19 hcs6, hx19_5, cs_x19 hcs4, hx19_3, cs_x19 hcs2, hx19_1])
    (by rw [cs_x20 hcs8, hx20_7, cs_x20 hcs6, hx20_5, cs_x20 hcs4, hx20_3, cs_x20 hcs2, hx20_1])
    (by rw [cs_x25 hcs8, hx25_7, cs_x25 hcs6, hx25_5, cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1])
    (by rw [cs_x26 hcs8, hx26_7, cs_x26 hcs6, hx26_5,
            cs_x26 hcs4, hx26_3, cs_x26 hcs2, hx26_1])
    (by rw [cs_x28 hcs8, hx28_7, cs_x28 hcs6, hx28_5,
            cs_x28 hcs4, hx28_3, cs_x28 hcs2, hx28_1])
    (by rw [cs_x29 hcs8, hx29_7, cs_x29 hcs6, hx29_5,
            cs_x29 hcs4, hx29_3, cs_x29 hcs2, hx29_1])
    (by rw [cs_vregs hcs8, hvregs_7, cs_vregs hcs6, hvregs_5,
            cs_vregs hcs4, hvregs_3, cs_vregs hcs2, hvregs_1])
    (by rw [cs_x27 hcs8, hx27_7, cs_x27 hcs6, hx27_5])
    (by rw [cs_x21 hcs8, hx21_7, cs_x21 hcs6, hx21_5])
    (by rw [cs_x23 hcs8, hx23_7, cs_x23 hcs6, hx23_5])
    (by
      rcases ans with ⟨⟨⟩⟩ | t
      · exact ⟨hans.2.1, hans.2.2.1, hans.2.2.2, hans.1⟩
      · exact ⟨hans.2.1, hans.2.2, hans.1⟩)
    (Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm21)

/-! ## 3. Main Theorem: `segTrust_placed_okV` -/

theorem segTrust_placed_okV [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegTrustSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk := by
  intro env x st_init st r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s haddr hfs hcm
  obtain ⟨hbud, hcm⟩ := hcm
  let R : SepProp := kit.storeAt x.ssA st0 ∗ R0
  obtain ⟨h15, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hcm
  have h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr' := h15
  dsimp only [retagSessionStore, retagIdentityStore] at htr hm
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set F := cliTrustPassive kit.ss_vt ikit.id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hm_pre : s.mem ⊨
      (trustBaseActivePlaced ikit.id_vt (A.atState lim st s) s.sp x k ∗
        encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
          (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 x s0) ∗
      ((memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗
        memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R0) := by
    have hm1 : s.mem ⊨
        (cmSlots (A.atState lim st s) s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
          encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
          memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x draws s0) ∗
        (encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
          (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 x s0 ∗ R0) := by
      rw [hsp, encStoreExtraPlaced_retag]
      exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
    rw [seam_mem_split_placed kit.ss_vt ikit.id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp,
        trustPassive_atState] at hm1
    dsimp only [F]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_join := Satisfies.mono (sepConj_mono_left
    (trustBaseActive_join_extra_placed (retagSessionStore (A' := A.atState lim st s) kit) st0
      (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 x k s0 s.sp hsp)) hm_pre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_join
  obtain ⟨hbound, hm_join⟩ := hm_join
  dsimp only [retagSessionStore] at hbound hm_join
  have hm_split : s.mem ⊨ (trustVtablesAt ikit ∗
      trustActivePlaced (retagIdentityStore (A' := A.atState lim st s) ikit) ist0
        s.sp (encSubStackV kit ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ (F ∗ R) := by
    have hm' := trustVtablesAt_placed_intro env.idVtables hcrl.2 hm_join
    dsimp only [R]; exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm'
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  refine trust_to_bc4_placed env hbud.1.seq_left haddr
    (fun s' hst' htr' =>
      ((hfs.of_steps hst').envOk_at (htr'.trans htr) fun hq => by
        obtain ⟨⟨hl, -⟩, -⟩ := hq; simp only [hl]).2)
    hbound hpc hrun hsp_al hx25' hpref0 hcrl hm_split ?_
  intro sm evs_trust ans w0 w1 w2 w3 w4 w5 H _hsteps_bc4 hpcm hrunm hspm hspm_al hcrlm htrustRel htrm
    htrustEnv hx19m hx20m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm_act
  set st_m := M.stepEvents evs_trust st
  have hbud_m := hbud.advance htrustEnv
  let R' : SepProp := encStoreExtraPlaced kit st0 ikit (ikit.trustUpdate ist0 x.rem.val k .sending ans) x s0 ∗ R0
  have hmm : sm.mem ⊨ (trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
      memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ (F ∗ R') := by
    have hmm1 : sm.mem ⊨
        (trustActivePlaced (retagIdentityStore (A' := A.atState lim st_m sm) ikit)
            (ikit.trustUpdate ist0 x.rem.val k .sending ans) s.sp (encSubStackV kit ikit) x k ∗
          (retagSessionStore (A' := A.atState lim st_m sm) kit).storeAt x.ssA st0) ∗
        ((memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ F ∗ R0) := by
      dsimp only [R, retagSessionStore] at hmm_act ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm_act
    have hmm2 := Satisfies.mono (sepConj_mono_left
      (trustActive_split_extra_placed (retagSessionStore (A' := A.atState lim st_m sm) kit) st0
        (retagIdentityStore (A' := A.atState lim st_m sm) ikit)
        (ikit.trustUpdate ist0 x.rem.val k .sending ans) x k s0 s.sp hsp hbound)) hmm1
    rw [encStoreExtraPlaced_retag] at hmm2
    dsimp only [R', retagIdentityStore] at hmm2 ⊢
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm2
  have hspm' : sm.sp = sp := hspm.trans hsp
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++ ikit.trustEvs x.rem.val k .sending ans) := by
    rw [htrm, htr, List.append_assoc]
  have hpref_m : s0.trace <+: sm.trace := ⟨_, htrm'.symm⟩
  rcases ans with ⟨⟨⟩⟩ | (_ | _)
  ·
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ (w1 ↦ᵣ storeHookStr)) ∗ F) ∗ R') := by
      rw [emp_sepConj]; exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExitBudget.of_sepWP hmm_emp (step_bc4_err_placed hpcm hrunm hx27m) ?_
    rintro s_err _ _ hsteps_err hpc_err hrun_err hm_err
      ⟨hvm_err, rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj, ← A.atState_eq_of_vmPreserved lim st_m hvm_err] at hm_err
    have hcrl_err : StoreKit.LibsignalCodeRoLoaded lsmpl s_err.mem := hcrlm.of_keepsFrozen hsteps_err.keepsFrozen
    have hm_ro' : s_err.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_err) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ (w1 ↦ᵣ storeHookStr)) ∗
          cliTrustPassive kit.ss_vt ikit.id_vt (A.atState lim st_m s_err) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_err
      rw [trustPassive_atState]
      exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_err
    have htail_ent := seam_mem_to_tail_placed kit.ss_vt ikit.id_vt (A.atState lim st_m s_err) ctl x sess taken otr' pqCap' pqPtr' k m draws s0
      s.sp hsp
      (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5))
      (memRegion (s.sp + 0x9d0#64) 24) (pollWith s.sp 0x970 [1#64, w4, w5]) (w1 ↦ᵣ storeHookStr)
      (trustPoll_merge_970 s.sp 1#64 w4 w5)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    simp only [sepExists_sepConj_left, satisfies_sepExists, dropRecordSlots_atState] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm := StepsThroughEncrypt.tailModel_trust_err (encRecord := encRecord) (s0 := s0) (s := s_err)
      h15 htrustRel (htr_err.trans htrm')
    have hdraws : x.draws S (answersOfTrust r (.error ())) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfTrust r (.error ())) rfl
    refine SegExitBudget.of_false
      (env.tailStoreHookErr x st_init st_m R0 s0 s_err (answersOfTrust r (.error ())) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        (w1 ↦ᵣ storeHookStr) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m 0xc20 0x970 (Or.inl rfl)
        htm (speStaged_storeErr_placed A.repAlloc x.ret w1 w4 w5) ?_)
    refine ⟨hbud_m.narrow (fun _ h => Or.inl h), hpc_err,
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_err,
      by rw [hx29_err, hx29m, hx29], by rw [hx19_err, hx19m, hx19], hcrl_err,
      by rw [hvregs_err, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26], by rw [hx28_err, hx28m, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    rw [hdraws, (StepsThroughEncrypt.model_trust_err h15)]; rw [hsp] at hm_tail
    dsimp only [sp, draws, SessionStoreSpec.storeFinal, StoreKit.Identity.IdentityStoreSpec.idFinal,
      answersOfTrust, R', retagSessionStore, retagIdentityStore] at hm_tail ⊢
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_tail
  ·
    obtain ⟨rfl, hw1, rfl⟩ := hans
    have hbud_f0 := hbud_m.narrow (fun _ h => Or.inr (Or.inl h))
    have hmm_970 : sm.mem ⊨
        (((sm.sp + 0x970#64) ↦₆₄ w3) ∗ ((sm.sp + 0x970#64 + 8#64) ↦₆₄ w4) ∗ ((sm.sp + 0x970#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) sm.sp x k ∗
          memRegion (sm.sp + 0x470#64) 16 ∗ memRegion (sm.sp + 0x580#64) 48 ∗
          memRegion (sm.sp + 0x9d0#64) 24) ∗ (F ∗ R')) := by
      rw [hspm]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    have hmm_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (sm.sp + 0x970#64) w3 w4 w5)) hmm_970
    have hmm_in : sm.mem ⊨ (trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) sm.sp x k ∗
        memRegion (sm.sp + 0x470#64) 16 ∗ memRegion (sm.sp + 0x580#64) 48 ∗
        memRegion (sm.sp + 0x970#64) 24 ∗ memRegion (sm.sp + 0x9d0#64) 24) ∗ (F ∗ R') :=
      Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm_fold
    refine trust_false_to_d40_placed env hbud_f0.1.seq_left hpcm hrunm hspm_al hx27m hx21m hw1
      (by rw [hspm, hx25m, hx25']) (by rw [hspm, hx26m, hsp, hx26]) hpref_m hcrlm hmm_in ?_
    intro s_d40 evs_clone cap ptr devWord u9e0 hsteps_d40 hpc_d40 hrun_d40 hsp_d40 hsp_d40_al htr_d40
      hcloneEnv hx19_d40 hx26_d40 hx28_d40 hx29_d40 hvregs_d40 hx27_d40 hx21_d40 hx23_d40 hdev hm_d40
    set st_d40 := M.stepEvents evs_clone st_m
    have hbud_d40 := hbud_f0.advance hcloneEnv
    have hcrl_d40 : StoreKit.LibsignalCodeRoLoaded lsmpl s_d40.mem := hcrlm.of_keepsFrozen hsteps_d40.keepsFrozen
    rw [hspm] at hm_d40
    have hm_d40' : s_d40.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_d40 s_d40) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗ memRegion (s.sp + 0x970#64) 24 ∗
          (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
            ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗ ((s.sp + 0x9e0#64) ↦₆₄ u9e0)) ∗
          vecU8Body A.repAlloc cap ptr x.rem.name.bytes) ∗
          cliTrustPassive kit.ss_vt ikit.id_vt (A.atState lim st_d40 s_d40) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_d40
      rw [trustPassive_atState]
      exact Eq.mp (congrArg (s_d40.mem ⊨ ·) (by ac_rfl)) hm_d40
    have htail_ent := seam_mem_to_tail_placed kit.ss_vt ikit.id_vt (A.atState lim st_d40 s_d40) ctl x sess taken otr' pqCap' pqPtr' k m draws s0
      s.sp hsp (memRegion (s.sp + 0x970#64) 24)
      (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
        ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗ ((s.sp + 0x9e0#64) ↦₆₄ u9e0))
      (pollWith s.sp 0x9d0 [BitVec.ofNat 64 x.rem.name.bytes.length, devWord, u9e0])
      (vecU8Body A.repAlloc cap ptr x.rem.name.bytes)
      (trustPoll_merge_9d0 s.sp (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_d40'
    simp only [sepExists_sepConj_left, satisfies_sepExists, dropRecordSlots_atState] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm := StepsThroughEncrypt.tailModel_trust_false (encRecord := encRecord) (s0 := s0) (s := s_d40)
      h15 htrustRel (htr_d40.trans htrm')
    have hdraws : x.draws S (answersOfTrust r (.ok false)) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfTrust r (.ok false)) rfl
    refine SegExitBudget.of_false
      (env.tailCmDrop x st_init st_d40 R0 s0 s_d40 (answersOfTrust r (.ok false)) (.untrustedIdentity x.rem.val)
        (speWord 12) cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0
        (vecU8Body A.repAlloc cap ptr x.rem.name.bytes) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m
        htm
        (speStaged_untrusted A.repAlloc x.ret x.rem.val cap ptr
          (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0 rfl hdev) ?_)
    refine ⟨hbud_d40, hpc_d40,
      ⟨hrun_d40, hsp_d40.trans hspm', hsp0_al, hsp_d40_al,
      by rw [hx29_d40, hx29m, hx29], by rw [hx19_d40, hx19m, hx19], hcrl_d40,
      by rw [hvregs_d40, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_d40, hx26m, hx26], by rw [hx28_d40, hx28m, hx28],
       hx27_d40, hx21_d40, hx23_d40⟩,
      hstk, ?_⟩
    rw [hdraws, (StepsThroughEncrypt.model_trust_false h15)]; rw [hsp] at hm_tail
    dsimp only [sp, draws, SessionStoreSpec.storeFinal, StoreKit.Identity.IdentityStoreSpec.idFinal,
      answersOfTrust, R', retagSessionStore, retagIdentityStore] at hm_tail ⊢
    exact Eq.mp (congrArg (s_d40.mem ⊨ ·) (by ac_rfl)) hm_tail
  ·
    obtain ⟨rfl, hw1, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R') := by
      simp only [sepConj_emp, emp_sepConj] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExitBudget.of_sepWP hmm_emp (step_bc4_ok_true_placed hpcm hrunm hx27m hx21m hw1) ?_
    rintro s_ok _ _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨hvm_ok, rfl, hsp_ok, htr_ok, hx19_ok, hx20_ok, hx22_ok, hx25_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj, ← A.atState_eq_of_vmPreserved lim st_m hvm_ok] at hm_ok
    have hcrl_ok : StoreKit.LibsignalCodeRoLoaded lsmpl s_ok.mem := hcrlm.of_keepsFrozen hsteps_ok.keepsFrozen
    have hm_ok_970 : s_ok.mem ⊨
        (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x970#64 + 8#64) ↦₆₄ w4) ∗ ((s.sp + 0x970#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_ok) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R') := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s.sp + 0x970#64) w3 w4 w5)) hm_ok_970
    have hm_ok_seam : s_ok.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_ok) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗
          cliTrustPassive kit.ss_vt ikit.id_vt (A.atState lim st_m s_ok) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_ok_fold
      rw [trustPassive_atState]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_fold
    rw [← seam_mem_split_placed kit.ss_vt ikit.id_vt (A.atState lim st_m s_ok) ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm_ok_seam
    rw [hsp] at hm_ok_seam
    refine SegExitBudget.next ⟨st_m, hbud_m.narrow (fun _ h => Or.inr (Or.inr h)),
      ⟨h15, htrustRel⟩, hpc_ok,
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29], by rw [hx19_ok, hx19m, hx19], hcrl_ok,
        by rw [hvregs_ok, hvregsm, hvregs]⟩,
      htr_ok.trans htrm',
      ⟨by rw [hx20_ok, hx20m, hx20], by rw [hx22_ok, hspm'],
       by rw [hx25_ok, hx25m, hx25], by rw [hx26_ok, hx26m, hx26],
       by rw [hx28_ok, hx28m, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩
    dsimp only [sp, draws, R', retagSessionStore, retagIdentityStore] at hm_ok_seam ⊢
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_seam

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustPlacedBudget
