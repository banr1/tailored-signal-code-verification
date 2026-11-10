/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreFramePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreStepsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable CLI `SegApplyStore` Proof (`segApplyStore_placed_okV`)

Verifies the budget-threaded `SegApplyStore` segment (`ApplyStateVBudget` at `+0xd9c` →
`StoredStateVBudget` at `+0xe88` or store-error tail at `+0xf2c`) on `lsProg_464 Hk` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStorePlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreStepsPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (
  cliEncCommonRest cliTrustPassive encCommonPlaced_eq trustBaseActivePlaced
  seam_mem_split_placed seam_mem_to_tail_placed trustActivePlaced
  trustBaseActive_join_extra_placed trustActive_split_extra_placed trustPollPlacedOut_words
)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore (
  storePassivePlaced store_mem_split_placed store_mem_to_stored_placed
  store_mem_to_tail_placed storePollPlacedOut_words
)

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust hiding
  alloc_onPanic_entails_placed dealloc_placed_ok_at_enc stringClone_placed_ok_at_enc
  trustVtablesAt_placed_intro saveVtablesAt_placed_intro storeVtablesAt_placed_intro
  speStaged_storeErr_placed call_nopanic_placed call_alloc_placed call_rocl_alloc_placed
  call_rocl_nopanic_placed
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem lsLogOff_eq [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

private theorem storeBaseActive_retag {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (kit : SessionStoreSpec A.repAlloc 0#64) (st_ss : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (sp : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (rec' : SessionRecord (List (BitVec 8))) :
    storeBaseActive (retagSessionStore (A' := A.atState lim st s) kit) st_ss
      (retagIdentityStore (A' := A.atState lim st s) ikit) sp x g' rec' =
    (((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗
      ((sp + 0xd8#64) ↦₆₄ kit.ss_vt) ∗
      sessionRecordAt A.repAlloc (sp + 0x110#64) g' rec' ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      stackAt sp (encSubStackV kit ikit) ∗
      A.pool lim st s ∗ kit.storeAt x.ssA st_ss) := rfl

private theorem storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagSessionStore (A' := A') kit).storeFinal st0 ans cs = kit.storeFinal st0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact storeFinal_retag kit _ ans cs

private theorem idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs = ikit.idFinal ist0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact idFinal_retag ikit _ ans cs

private theorem encStoreExtraPlaced_final_retag [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8))))
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A') kit)
      ((retagSessionStore (A' := A') kit).storeFinal st0 ans cs)
      (retagIdentityStore (A' := A') ikit)
      ((retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs) x s0 =
    encStoreExtraPlaced kit (kit.storeFinal st0 ans cs)
      ikit (ikit.idFinal ist0 ans cs) x s0 := by
  have hs := storeFinal_retag (A' := A') kit st0 ans cs
  have hi := idFinal_retag (A' := A') ikit ist0 ans cs
  have hfn :
      ∀ (st : kit.StoreState) (ist : ikit.IdState),
        encStoreExtraPlaced (retagSessionStore (A' := A') kit) st
          (retagIdentityStore (A' := A') ikit) ist x s0 =
        encStoreExtraPlaced kit st ikit ist x s0 := fun _ _ => rfl
  exact (hfn _ _).trans (by rw [hs, hi])

private theorem encTail_mem_retag_eq [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced (retagSessionStore (A' := A') kit)
        ((retagSessionStore (A' := A') kit).storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        (retagIdentityStore (A' := A') ikit)
        ((retagIdentityStore (A' := A') ikit).idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) =
    (slotsP ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced kit
        (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        ikit
        (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) := by
  have hext := encStoreExtraPlaced_final_retag (A' := A') kit st0 ikit ist0 answers
    (x.model C S uuidTryParse answers).2 x s0
  have hvt :
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

private theorem cs_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x19 = s0.readReg64 .x19 := h.1
private theorem cs_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x20 = s0.readReg64 .x20 := h.2.1
private theorem cs_x21 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x21 = s0.readReg64 .x21 := h.2.2.1
private theorem cs_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x22 = s0.readReg64 .x22 := h.2.2.2.1
private theorem cs_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x23 = s0.readReg64 .x23 := h.2.2.2.2.1
private theorem cs_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x25 = s0.readReg64 .x25 := h.2.2.2.2.2.2.1
private theorem cs_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x26 = s0.readReg64 .x26 := h.2.2.2.2.2.2.2.1
private theorem cs_x27 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x27 = s0.readReg64 .x27 := h.2.2.2.2.2.2.2.2.1
private theorem cs_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x28 = s0.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
private theorem cs_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x29 = s0.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
private theorem cs_vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2

private theorem storeShimStack_le_encSubStackV_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.storeShimStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV; omega

private theorem storePollStack_le_encSubStackV_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.storePollStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV; omega

private theorem allocHookStack_le_encSubStackV_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    allocHookStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV encSubStack withStoresEncStack encFrameSize entryStack allocHookStack
  omega

/-! ## 1. Apply Phase (`+0xd9c..+0xde8`) -/

/-- Execute `+0xd9c..+0xde4` on `lsProg_464 Hk` (clear `[sp+0x469]`, copy 200-byte OTR from
`sp+0x288` to `sp+0x580`, and call `OTR::apply_to_session_state`), reaching `+0xde8` with
`storedRecord sess otr' taken` at `sp + 0x110` and `memRegion (sp + 0x288) 200`. -/
theorem apply_to_de8_placed [LibsignalPlacement] {M : AllocCostModel} {Scope Q C}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl S} {sendEnv : SpqrSendBudgetEnv} {encRecord Hk}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    {x : WithStoresEncGhost} {st_init st : M.σ} {sess : Session (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))} {pqCap' pqPtr' : BitVec 64}
    {k : IdentityKey} {m : CiphertextMessage} {draws : Nat} {R R0 : SepProp}
    {s0 s : State}
    {next : State → Prop}
    (hfit : FitsEnv M lim st OtrApplyEnv)
    (hpc : s.pc = encEntryPlaced + 0xd9c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xbe0#64)
    (hsp_al : s.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hpref0 : s0.trace <+: s.trace)
    (hsc_some : taken.senderChain.isSome = true)
    (hm : s.mem ⊨
      (cmSlots (A.atState lim st s) s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
        encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
        memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x draws s0) ∗ R)
    (hcont : ∀ s2 (g' : RecordGhost) (evs : List AllocEvent),
      OtrApplyEnv evs →
      Steps (lsProg_464 Hk) s s2 →
      s2.pc = encEntryPlaced + 0xde8#64 →
      s2.status = .Running →
      s2.sp = s.sp →
      s2.spAligned = true →
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
      s2.trace = s.trace →
      s2.readReg64 .x19 = s.readReg64 .x19 →
      s2.readReg64 .x20 = s.readReg64 .x20 →
      s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = s.readReg64 .x26 →
      s2.readReg64 .x28 = s.readReg64 .x28 →
      s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s →
      (s2.mem ⊨
        ((sessionRecordAt (A.atState lim (M.stepEvents evs st) s2) (s.sp + 0x110#64) g'
            (storedRecord sess otr' taken) ∗
          ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
          memRegion (s.sp + 0x288#64) 200 ∗
          ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          apiEncResultAt (A.atState lim (M.stepEvents evs st) s2) (s.sp + 0x370#64) (.ok m) ∗
          ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x469#64) ↦₈ 0#8)) ∗
        cmScratch s.sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
        memRegion (s.sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim (M.stepEvents evs st) s2) ctl x draws s0) ∗ R) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
        x st_init R0 s0 s2 next) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  let As := A.atState lim st s
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  dsimp only [cmSlots, takenSlots] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  have hm_rec : s.mem ⊨ sessionRecordAt As (s.sp + 0x110#64) g (takenRecord sess taken) ∗
      (otrAt As (s.sp + 0x288#64) pqCap' pqPtr' otr' ∗
        (((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
          ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x469#64) ↦₈ 1#8) ∗
          ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          apiEncResultAt As (s.sp + 0x370#64) (.ok m) ∗
          cmScratch s.sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
          memRegion (s.sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
          encCommonPlaced As ctl x draws s0 ∗ R)) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  obtain ⟨G, _, hpure, hm_unp⟩ := sessionRecordAt_taken_unpack As s.sp g sess taken hm_rec
  have hm_otr : s.mem ⊨ otrAt As (s.sp + 0x288#64) pqCap' pqPtr' otr' ∗
      (memRegion (s.sp + 0x580#64) 200 ∗
        (vecAt As 24 8 (fun (_ : Unit) _ => emp) (s.sp + 0x110#64) g.prevCap g.prevPtr [] ∗
          sessionStateAt As (s.sp + 0x128#64) G taken ∗
          ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
          ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x469#64) ↦₈ 1#8) ∗
          ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          apiEncResultAt As (s.sp + 0x370#64) (.ok m) ∗
          cmScratch s.sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
          (memRegion (s.sp + 0x46a#64) 0x116 ∗ memRegion (s.sp + 0x648#64) 0x538) ∗
          memRegion x.ret 248 ∗ encCommonPlaced As ctl x draws s0 ∗ R)) := by
    rw [poll46a_split_200 s.sp] at hm_unp
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_unp
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19,
    w20, w21, w22, w23, w24, H_otr, hm_w, hotr_pack⟩ :=
    otrAt_relocate As (s.sp + 0x288#64) pqCap' pqPtr' otr' hm_otr
  have hm_580 : s.mem ⊨ memRegion (s.sp + 0x580#64) 200 ∗
      (otrWords25 (s.sp + 0x288#64) pqCap' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        w17 w18 w19 w20 w21 w22 w23 w24 ∗ H_otr ∗
        vecAt As 24 8 (fun (_ : Unit) _ => emp) (s.sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateAt As (s.sp + 0x128#64) G taken ∗
        ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
        ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x469#64) ↦₈ 1#8) ∗
        ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt As (s.sp + 0x370#64) (.ok m) ∗
        cmScratch s.sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
        (memRegion (s.sp + 0x46a#64) 0x116 ∗ memRegion (s.sp + 0x648#64) 0x538) ∗
        memRegion x.ret 248 ∗ encCommonPlaced As ctl x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_w
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
    d19, d20, d21, d22, d23, d24, hm_d⟩ :=
    memRegion_200_exists_otrWords25 (s.sp + 0x580#64) hm_580
  have hm_step1 : s.mem ⊨
      (((s.sp + 0x38#64) ↦₆₄ (s.sp + 0x288#64)) ∗
        ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
        ((s.sp + 0x469#64) ↦₈ 1#8) ∗
        otrWords25 (s.sp + 0x288#64) pqCap' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        otrWords25 (s.sp + 0x580#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
          d18 d19 d20 d21 d22 d23 d24) ∗
      ((H_otr ∗
        vecAt As 24 8 (fun (_ : Unit) _ => emp) (s.sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateAt As (s.sp + 0x128#64) G taken ∗
        ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt As (s.sp + 0x370#64) (.ok m) ∗
        (memRegion s.sp 0x38 ∗ ((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
          memRegion (s.sp + 0x48#64) 8 ∗ ((s.sp + 0x50#64) ↦₆₄ (s.sp + 0x128#64))) ∗
        encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
        (memRegion (s.sp + 0x46a#64) 0x116 ∗ memRegion (s.sp + 0x648#64) 0x538) ∗
        memRegion x.ret 248 ∗ encCommonPlaced As ctl x draws s0) ∗ R) := by
    rw [cmScratch_eq_38 s.sp] at hm_d
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_d
  refine SegExitBudget.of_sepWP (R0 := R0) hm_step1 (step_d9c_to_de4_placed hpc hrun hsp_align hx25) ?_
  rintro s1 P1 _ hsteps1 hpc1 hrun1 hm1
    ⟨hvm1, rfl, hsp1, htr1, hx0_1, hx1_1, hx30_1, hx19_1, hx20_1, hx25_1, hx26_1, hx28_1, hx29_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp1
  have hpref1 : s0.trace <+: s1.trace := by rw [htr1]; exact hpref0
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hm1_pack : s1.mem ⊨
      (otrWords25 (s.sp + 0x580#64) pqCap' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        w17 w18 w19 w20 w21 w22 w23 w24 ∗ H_otr) ∗
      (otrWords25 (s.sp + 0x288#64) pqCap' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        w17 w18 w19 w20 w21 w22 w23 w24 ∗
      ((sessionStateAt As (s.sp + 0x128#64) G taken ∗
        vecAt As 24 8 (fun (_ : Unit) _ => emp) (s.sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
        ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x469#64) ↦₈ 0#8) ∗
        ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt As (s.sp + 0x370#64) (.ok m) ∗
        cmScratch s.sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
        (memRegion (s.sp + 0x46a#64) 0x116 ∗ memRegion (s.sp + 0x648#64) 0x538) ∗
        memRegion x.ret 248 ∗ encCommonPlaced As ctl x draws s0) ∗ R)) := by
    rw [cmScratch_eq_38 s.sp]
    exact Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1
  have hm1_otr := Satisfies.mono (sepConj_mono (hotr_pack (s.sp + 0x580#64))
    (sepConj_mono_left (otrWords25_entails_memRegion (s.sp + 0x288#64)
      pqCap' w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24)))
    hm1_pack
  let applyGhost : OtrApplyGhost :=
    ⟨s.sp + 0x580#64, pqCap', pqPtr', otr', s.sp + 0x128#64, G, taken⟩
  have hpool1 : As.pool = (A.atState lim st s1).pool :=
    (A.pool_transport lim st s s1 hvm1).symm
  have hm2 : s1.mem ⊨ (otrApplyBudgetSpec M A lim).pre (applyGhost, st) s1 ∗
      ((vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (s.sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗ memRegion (s.sp + 0x288#64) 200 ∗
        ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A.repAlloc (s.sp + 0x370#64) (.ok m) ∗
        ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x469#64) ↦₈ 0#8) ∗
        cmScratch s.sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
        (memRegion (s.sp + 0x46a#64) 0x116 ∗ memRegion (s.sp + 0x648#64) 0x538) ∗
        memRegion x.ret 248 ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        memRegion (s.sp - BitVec.ofNat 64 encSubStack) (encSubStack - smallRootStack) ∗
        cliEncCommonRest A.repAlloc ctl x draws s0) ∗ R) := by
    dsimp only [otrApplyBudgetSpec, OutgoingRatchet.otrApplyPlacedSpec, applyGhost]
    rw [hsp1]
    rw [encCommonPlaced_eq, lsLogOff_eq, ← hsp,
        stackAt_encSubStack_split s.sp smallRootStack (by decide), hpool1] at hm1_otr
    change s1.mem ⊨ _
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfit, ⟨hx0_1, hx1_1, hsc_some⟩, Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1_otr⟩
  refine call_rocl_alloc_placed (R0 := R0) env.calleesFull.otrApply (applyGhost, st)
    hpc1 hrun1 hsp1_al hx30_1 hpref1 hcrl1 hm2 ?_
  intro s2 hsteps2 hpc2 hrun2 hsp2 hsp2_al hcs2 hcrl2 hm3
  dsimp only [otrApplyBudgetSpec, OutgoingRatchet.otrApplyPlacedSpec, applyGhost] at hm3
  rw [hsp1] at hsp2 hm3
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hm3
  obtain ⟨evs, G', hevs, htr2, ⟨hrel, _⟩, hm3⟩ := hm3
  let A2 := A.atState lim (M.stepEvents evs st) s2
  have hm3_pre : s2.mem ⊨
      (vecAt A2 24 8 (fun (_ : Unit) _ => emp) (s.sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateAt A2 (s.sp + 0x128#64) G' (otr'.applyToSessionState taken)) ∗
      ((((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗ memRegion (s.sp + 0x288#64) 200 ∗
        ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A2 (s.sp + 0x370#64) (.ok m) ∗
        ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x469#64) ↦₈ 0#8)) ∗
      cmScratch s.sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
      memRegion (s.sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A2 ctl x draws s0 ∗ R) := by
    rw [poll46a_split_200 s.sp, encCommonPlaced_eq, lsLogOff_eq, ← hsp,
        stackAt_encSubStack_split s.sp smallRootStack (by decide)]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm3
  have hm4 := Satisfies.mono (sepConj_mono_left
    (sessionRecordAt_stored_fold A2 s.sp g sess taken otr' G G' hpure hrel)) hm3_pre
  exact hcont s2 { g with cur := some G' } evs hevs (hsteps1.trans hsteps2) hpc2 hrun2 hsp2
    hsp2_al hcrl2
    (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
    (by reg_chain) (by rw [cs_vregs hcs2, hvregs_1])
    (Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm4)

/-! ## 2. Store Phase (`+0xde8..+0xe80`) -/

/-- Execute `+0xde8..+0xe80` on `lsProg_464 Hk` (`kit.storeShim`, `kit.storePoll`,
`kit.storeFutDrop`, `__rust_dealloc`), reaching `+0xe80` with `x27 = pollTag ans` and SPE tail
words at `sp + 0x9b0..0x9c8`. -/
theorem store_to_e80_placed [LibsignalPlacement] {M : AllocCostModel} {Scope Q C}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl S} {sendEnv : SpqrSendBudgetEnv} {encRecord Hk}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    {TopEnv : List AllocEvent → Prop} {st_init st : M.σ}
    {x : WithStoresEncGhost} {g' : RecordGhost}
    {rec' : SessionRecord (List (BitVec 8))} {F R : SepProp} {s0 s : State}
    {next : State → Prop}
    (hbud : SeamBudget lim TopEnv st_init st
      (SeqEnv (BoxAllocEnv kit.storeBoxSize)
        (SeqEnv (kitEnv.storePollEnv st0 x.rem.val rec')
          (SeqEnv (· = rustDeallocEvents kit.storeBoxSize 8) FreeOnlyEvs))))
    (hrecOk : kit.RecOk rec')
    (haddr : kit.addrOk x.rem.val)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hpc : s.pc = encEntryPlaced + 0xde8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = s.sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hpref0 : s0.trace <+: s.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsCtx kit.envOk True (lsProg_464 Hk) s s)
    (hm : s.mem ⊨ (storeVtablesAt kit ∗
      storeBaseActive (retagSessionStore (A' := A.atState lim st s) kit) st0
        (retagIdentityStore (A' := A.atState lim st s) ikit) s.sp x g' rec' ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x9b0#64) 24) ∗ (F ∗ R))
    (hcont : ∀ sm (st' : M.σ) (ans : Except Unit Unit) (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      SeamBudget lim TopEnv st_init st' FreeOnlyEvs →
      Steps (lsProg_464 Hk) s sm →
      sm.pc = encEntryPlaced + 0xe80#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.spAligned = true →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace ++ kit.storeEvs encRecord x.rem.val rec' ans →
      kit.storeRel st0 x.rem.val rec' ans →
      (ans = .ok () → H = emp) →
      (ans = .error () →
        H = (w1 ↦ᵣ storeHookStr) ∧ w2 = 10#64 ∧ w3 = 1#64) →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x27 = w0 →
      sm.readReg64 .x21 = w1 →
      sm.readReg64 .x23 = w2 →
      w0 = pollTag ans →
      (sm.mem ⊨ (storeBaseActive (retagSessionStore (A' := A.atState lim st' sm) kit)
          (kit.storeUpdate st0 x.rem.val rec' ans)
          (retagIdentityStore (A' := A.atState lim st' sm) ikit) s.sp x g' rec' ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        (((s.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗ ((s.sp + 0x9c0#64) ↦₆₄ w5)) ∗
        H) ∗ (F ∗ R)) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
        x st_init R s0 sm next) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s next := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hm1 : s.mem ⊨ (((s.sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((s.sp + 0xd0#64) ↦₆₄ x.ssA) ∗
      ((s.sp + 0xd8#64) ↦₆₄ kit.ss_vt) ∗ ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff))) ∗
      (((((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff)) ∗
        sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        stackAt s.sp (encSubStackV kit ikit) ∗ A.pool lim st s ∗ kit.storeAt x.ssA st0 ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    dsimp only [storeVtablesAt] at hm
    rw [storeBaseActive_retag] at hm
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  refine SegExitBudget.of_sepWP hm1 (step_de8_to_df8_placed hpc hrun hsp_align hx20) ?_
  rintro s1 P1 _ hsteps1 hpc1 hrun1 hm2
    ⟨hvm1, rfl, hsp1, htr1, hx0_1, hx1_1, hx2_1, hx30_1, hx19_1, hx20_1, hx25_1, hx26_1, hx28_1, hx29_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp1
  have hpref1 : s0.trace <+: s1.trace := by rw [htr1]; exact hpref0
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hm3 : s1.mem ⊨ (kitStoreShimBudgetSpec M A lim kit).pre (⟨x.ssA, x.remA, s.sp + 0x110#64⟩, st) s1 ∗
      ((((s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff)) ∗
        sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        kit.storeAt x.ssA st0 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.storeShimStack) ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitStoreShimBudgetSpec]
    rw [hsp1]
    rw [← A.pool_transport lim st s s1 hvm1,
        stackAt_encSubStackV_split kit ikit hbound s.sp kit.storeShimStack
          (storeShimStack_le_encSubStackV_placed kit ikit)] at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_1, hx1_1, hx2_1, hbud.1.seq_left⟩, Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm2⟩
  refine call_rocl_alloc_placed (env.kitOk.storeShim (by decide)) (⟨x.ssA, x.remA, s.sp + 0x110#64⟩, st)
    hpc1 hrun1 hsp1_al hx30_1 hpref1 hcrl1 hm3 ?_
  intro s2 hsteps2 hpc2 hrun2 hsp2 hsp2_al hcs2 hcrl2 hm4
  dsimp only [kitStoreShimBudgetSpec] at hm4
  rw [hsp1] at hsp2 hm4
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨evs_shim, ⟨hx1_2, _, _, htr2, hevs_shim⟩, hm4⟩ := hm4
  have hbud2 := hbud.advance hevs_shim
  set st2 := M.stepEvents evs_shim st
  set box := s2.readReg64 .x0
  have hm4' : s2.mem ⊨ memRegion (s.sp + 0x470#64) 16 ∗
      ((A.live box kit.storeBoxSize 8 ∗ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 0#8 ∗ A.pool lim st2 s2 ∗
        kit.storeAt x.ssA st0 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff)) ∗
        sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        memRegion (s.sp + 0x580#64) 48 ∗ memRegion (s.sp + 0x9b0#64) 24) ∗ F ∗ R) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storeShimStack
      (storeShimStack_le_encSubStackV_placed kit ikit)]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm4
  obtain ⟨u470, u478, hm5⟩ := memRegion16_exists_words2 (s.sp + 0x470#64) hm4'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm5
  have hm6 : s2.mem ⊨ (((s2.sp + 0x470#64) ↦₆₄ u470) ∗ ((s2.sp + 0x478#64) ↦₆₄ u478) ∗
      ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗
      (((A.live box kit.storeBoxSize 8 ∗ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 0#8 ∗ A.pool lim st2 s2 ∗
        kit.storeAt x.ssA st0 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        memRegion (s.sp + 0x580#64) 48 ∗ memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    rw [hsp2]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm5
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2_al
  refine SegExitBudget.of_sepWP hm6 (step_dfc_to_e10_placed hpc2 hrun2 hsp2_align rfl hx1_2) ?_
  rintro s3 P3 _ hsteps3 hpc3 hrun3 hm7
    ⟨hvm3, rfl, hsp3, htr3, hx0_3, _, hx8_3, hx30_3, hx19_3, hx20_3, hx25_3, hx26_3, hx28_3, hx29_3, hvregs_3⟩
  rw [hsp2] at hsp3 hx8_3 hm7
  have hsp3_al : s3.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp3
  have hpref3 : s0.trace <+: s3.trace := by rw [htr3, htr2]; exact hpref1
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps3.keepsFrozen
  let pollCall : StorePollCall × BitVec 64 × kit.StoreState × M.σ :=
    (⟨box, s.sp + 0x580#64, ⟨x.remA, x.rem, s.sp + 0x110#64, g', rec'⟩⟩, x.ssA, st0, st2)
  have hm8 : s3.mem ⊨ (kitStorePollBudgetSpec M A lim kit kitEnv encRecord).pre pollCall s3 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        A.live box kit.storeBoxSize 8 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.storePollStack) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff)) ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitStorePollBudgetSpec, pollCall]
    rw [hsp3]
    rw [← A.pool_transport lim st2 s2 s3 hvm3,
        stackAt_encSubStackV_split kit ikit hbound s.sp kit.storePollStack
          (storePollStack_le_encSubStackV_placed kit ikit)] at hm7
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_3, hx8_3, hrecOk, haddr, hbud2.1.seq_left⟩, Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7⟩
  have henv3 : kit.envOk s3.fs.files :=
    (hfs.of_steps ((hsteps1.trans hsteps2).trans hsteps3)).envOk_at (evs := [])
      (by rw [htr3, htr2, htr1, List.append_nil]) (fun _ => NoFsEv.nil)
  refine call_rocl_alloc_placed (env.kitOk.storePoll (by decide)) pollCall hpc3 hrun3 hsp3_al hx30_3 hpref3 hcrl3
    (withEnvPre_pre_intro (φ := fun s => kit.envOk s.fs.files) henv3 hm8) ?_
  intro s4 hsteps4 hpc4 hrun4 hsp4 hsp4_al hcs4 hcrl4 hm9
  dsimp only [kitStorePollBudgetSpecE, withEnvPre, kitStorePollBudgetSpec, pollCall] at hm9
  rw [hsp3] at hsp4 hm9
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm9
  obtain ⟨ans, evs_poll, ⟨hstoreRel, htr4, hevs_poll⟩, hm9⟩ := hm9
  have hbud4 := hbud2.advance hevs_poll
  set st4 := M.stepEvents evs_poll st2
  have hm9_poll : s4.mem ⊨
      storePollPlacedOutAt (s.sp + 0x580#64) ans ∗
      (memRegion (s.sp + 0x9b0#64) 24 ∗
      ((kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        (s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗
        A.pool lim st4 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F ∗ R)) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storePollStack
      (storePollStack_le_encSubStackV_placed kit ikit)]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm9
  have hm10 := Satisfies.mono (sepConj_mono_left
    (storePollPlacedOut_words (s.sp + 0x580#64) ans)) hm9_poll
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm10
  obtain ⟨w0, w1, w2, w3, w4, w5, H, ⟨hw0, hans, hH, hstaged⟩, hm10⟩ := hm10
  have hm10' : s4.mem ⊨ memRegion (s.sp + 0x9b0#64) 24 ∗
      (((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x580#64 + 8#64) ↦₆₄ w1 ∗
        (s.sp + 0x580#64 + 0x10#64) ↦₆₄ w2 ∗ (s.sp + 0x580#64 + 0x18#64) ↦₆₄ w3 ∗
        (s.sp + 0x580#64 + 0x20#64) ↦₆₄ w4 ∗ (s.sp + 0x580#64 + 0x28#64) ↦₆₄ w5 ∗ H ∗
        kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        (s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗
        A.pool lim st4 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F ∗ R) :=
    Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm10
  obtain ⟨u9b0, u9b8, u9c0, hm11⟩ := memRegion24_exists_words3 (s.sp + 0x9b0#64) hm10'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm11
  have hm12 : s4.mem ⊨ (((s4.sp + 0x470#64) ↦₆₄ box) ∗ ((s4.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff)) ∗
      ((s4.sp + 0x580#64) ↦₆₄ w0) ∗ ((s4.sp + 0x588#64) ↦₆₄ w1) ∗ ((s4.sp + 0x590#64) ↦₆₄ w2) ∗
      ((s4.sp + 0x598#64) ↦₆₄ w3) ∗ ((s4.sp + 0x5a0#64) ↦₆₄ w4) ∗ ((s4.sp + 0x5a8#64) ↦₆₄ w5) ∗
      ((s4.sp + 0x9b0#64) ↦₆₄ u9b0) ∗ ((s4.sp + 0x9b8#64) ↦₆₄ u9b8) ∗ ((s4.sp + 0x9c0#64) ↦₆₄ u9c0) ∗
      ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff))) ∗
      (((H ∗ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗
        A.pool lim st4 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F) ∗ R) := by
    rw [hsp4]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm11
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4_al
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x580#64 := by
    rw [hsp4, cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1, hx25]
  refine SegExitBudget.of_sepWP hm12
    (step_e14_to_e68_placed (kit.storeFutDrop_ne_zero (by decide)) hpc4 hrun4 hsp4_align hx25_4 hw0) ?_
  rintro s5 _ _ hsteps5 hpc5 hrun5 hm13
    ⟨hvm5, rfl, hsp5, htr5, hx0_5, hx20_5, hx21_5, hx22_5, hx23_5, hx27_5, hx30_5,
      hx19_5, hx25_5, hx26_5, hx28_5, hx29_5, hvregs_5⟩
  rw [hsp4] at hsp5 hm13
  have hsp5_al : s5.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp5
  have hm14 : s5.mem ⊨ futDropBudgetSpec.pre () s5 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x9b0#64) ↦₆₄ w3 ∗ (s.sp + 0x9b8#64) ↦₆₄ w4 ∗ (s.sp + 0x9c0#64) ↦₆₄ w5 ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff))) ∗
      ((H ∗ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗
        A.pool lim st4 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F)) ∗ R) := by
    dsimp only [futDropBudgetSpec]
    rw [emp_sepConj]
    exact Eq.mp (congrArg (s5.mem ⊨ ·) (by ac_rfl)) hm13
  refine call_rocl_nopanic_placed (env.kitOk.storeFutDrop (by decide)) ()
    hpc5 hrun5 hsp5_al hx30_5 (hcrl4.of_keepsFrozen hsteps5.keepsFrozen) hm14 ?_
  intro s6 hsteps6 hpc6 hrun6 hsp6 hsp6_al hcs6 hm15
  dsimp only [futDropBudgetSpec] at hm15
  rw [hsp5] at hsp6
  rw [satisfies_pure_sepConj] at hm15
  obtain ⟨⟨htr6, hvm6⟩, hm15⟩ := hm15
  have hm15_box : s6.mem ⊨ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
      (((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
      ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x9b0#64) ↦₆₄ w3 ∗ (s.sp + 0x9b8#64) ↦₆₄ w4 ∗ (s.sp + 0x9c0#64) ↦₆₄ w5 ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗ H ∗
        A.live box kit.storeBoxSize 8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗
        A.pool lim st4 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F) ∗ R)) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15
  have hm15_mem := Satisfies.mono (sepConj_mono_left
    (kit.storeBoxAt_memRegion box x.ssA x.remA (s.sp + 0x110#64) 1#8)) hm15_box
  have hm16 : s6.mem ⊨ (((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
      ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64)) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x9b0#64) ↦₆₄ w3 ∗ (s.sp + 0x9b8#64) ↦₆₄ w4 ∗ (s.sp + 0x9c0#64) ↦₆₄ w5 ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗ H ∗
        memRegion box kit.storeBoxSize ∗ A.live box kit.storeBoxSize 8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗
        A.pool lim st4 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F) ∗ R) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15_mem
  have hx20_6 : s6.readReg64 .x20 = box := (cs_x20 hcs6).trans hx20_5
  have hx22_6 : s6.readReg64 .x22 = 0#64 + kit.storeFutVtOff := (cs_x22 hcs6).trans hx22_5
  refine SegExitBudget.of_sepWP hm16
    (step_e6c_to_e7c_placed kit.storeBoxSize_ne_zero hpc6 hrun6 hx20_6 hx22_6) ?_
  rintro s7 P7 _ hsteps7 hpc7 hrun7 hm17
    ⟨hvm7, rfl, hsp7, htr7, hx0_7, hx1_7, hx2_7, hx30_7,
      hx19_7, hx20_7, hx21_7, hx23_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hvregs_7⟩
  rw [hsp6] at hsp7
  have hsp7_al : s7.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp7
  have hvm47 : VmPreserved s4 s7 := hvm5.trans (hvm6.trans hvm7)
  have hm18 : s7.mem ⊨ (rustCliDeallocBudgetSpec M A lim).pre (box, kit.storeBoxSize, 8, st4) s7 ∗
      (((storeVtablesAt kit ∗
        ((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff)) ∗
        ((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
          (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5) ∗
        (((s.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗ ((s.sp + 0x9c0#64) ↦₆₄ w5)) ∗
        H ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - allocHookStack) ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ sessionRecordAt A.repAlloc (s.sp + 0x110#64) g' rec' ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt) ∗ F) ∗ R) := by
    dsimp only [rustCliDeallocBudgetSpec, storeVtablesAt]
    rw [hsp7]
    rw [← A.pool_transport lim st4 s4 s7 hvm47,
        stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
          (allocHookStack_le_encSubStackV_placed kit ikit)] at hm17
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_7, by rw [hx1_7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kit.storeBoxSize_lt],
      by rw [hx2_7]; rfl,
      by rw [hx30_7]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 464 0xe80#64 (by decide) (by decide)⟩,
      Eq.mp (congrArg (s7.mem ⊨ ·) (by ac_rfl)) hm17⟩
  refine call_nopanic_placed (dealloc_placed_ok_at_enc env.toEncEnvBudget) (box, kit.storeBoxSize, 8, st4)
    hpc7 hrun7 hsp7_al hx30_7 hm18 ?_
  intro s8 hsteps8 hpc8 hrun8 hsp8 hsp8_al hcs8 hm19
  dsimp only [rustCliDeallocBudgetSpec] at hm19
  rw [hsp7] at hsp8 hm19
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm19
  obtain ⟨⟨hacp8, _⟩, hm19⟩ := hm19
  have htr8 : s8.trace = s7.trace := hacp8.2.1
  have hbud8 := hbud4.advance rfl
  set st8 := M.stepEvents (rustDeallocEvents kit.storeBoxSize 8) st4
  have hm20 : s8.mem ⊨ storeVtablesAt kit ∗
      ((((s.sp + 0x470#64) ↦₆₄ box) ∗ ((s.sp + 0x470#64 + 8#64) ↦₆₄ (0#64 + kit.storeFutVtOff))) ∗
      (((s.sp + 0x580#64) ↦₆₄ w0) ∗ ((s.sp + 0x580#64 + 8#64) ↦₆₄ w1) ∗
        ((s.sp + 0x580#64 + 16#64) ↦₆₄ w2) ∗ ((s.sp + 0x580#64 + 24#64) ↦₆₄ w3) ∗
        ((s.sp + 0x580#64 + 32#64) ↦₆₄ w4) ∗ ((s.sp + 0x580#64 + 40#64) ↦₆₄ w5)) ∗
      ((storeBaseActive (retagSessionStore (A' := A.atState lim st8 s8) kit)
          (kit.storeUpdate st0 x.rem.val rec' ans)
          (retagIdentityStore (A' := A.atState lim st8 s8) ikit) s.sp x g' rec' ∗
        (((s.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗ ((s.sp + 0x9c0#64) ↦₆₄ w5)) ∗
        H) ∗ (F ∗ R))) := by
    rw [storeBaseActive_retag,
        stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
          (allocHookStack_le_encSubStackV_placed kit ikit)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm19
  have hm21 := Satisfies.mono (sepConj_mono
    (words2_entails_memRegion16 (s.sp + 0x470#64) box (0#64 + kit.storeFutVtOff))
    (sepConj_mono_left
      (words6_entails_memRegion48 (s.sp + 0x580#64) w0 w1 w2 w3 w4 w5)))
    (Satisfies.of_sep_right hm20)
  have hsteps_tail := hsteps5.trans (hsteps6.trans (hsteps7.trans hsteps8))
  have hcrl8 : StoreKit.LibsignalCodeRoLoaded lsmpl s8.mem := hcrl4.of_keepsFrozen hsteps_tail.keepsFrozen
  have hsteps_all := hsteps1.trans (hsteps2.trans (hsteps3.trans (hsteps4.trans hsteps_tail)))
  refine hcont s8 st8 ans w0 w1 w2 w3 w4 w5 H hbud8 hsteps_all hpc8 hrun8 hsp8 hsp8_al hcrl8
    (by rw [htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1])
    hstoreRel hH hstaged
    (by rw [cs_x19 hcs8, hx19_7, cs_x19 hcs6, hx19_5, cs_x19 hcs4, hx19_3, cs_x19 hcs2, hx19_1])
    (by rw [cs_x25 hcs8, hx25_7, cs_x25 hcs6, hx25_5, cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1])
    (by rw [cs_x26 hcs8, hx26_7, cs_x26 hcs6, hx26_5, cs_x26 hcs4, hx26_3, cs_x26 hcs2, hx26_1])
    (by rw [cs_x28 hcs8, hx28_7, cs_x28 hcs6, hx28_5, cs_x28 hcs4, hx28_3, cs_x28 hcs2, hx28_1])
    (by rw [cs_x29 hcs8, hx29_7, cs_x29 hcs6, hx29_5, cs_x29 hcs4, hx29_3, cs_x29 hcs2, hx29_1])
    (by rw [cs_vregs hcs8, hvregs_7, cs_vregs hcs6, hvregs_5,
            cs_vregs hcs4, hvregs_3, cs_vregs hcs2, hvregs_1])
    (by rw [cs_x27 hcs8, hx27_7, cs_x27 hcs6, hx27_5])
    (by rw [cs_x21 hcs8, hx21_7, cs_x21 hcs6, hx21_5])
    (by rw [cs_x23 hcs8, hx23_7, cs_x23 hcs6, hx23_5])
    hans
    (Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm21)

/-! ## 3. Main Theorem: `segApplyStore_placed_okV` -/

theorem segApplyStore_placed_okV [LibsignalPlacement]
    {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegApplyStoreSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk := by
  intro env x st_init st r sess otr taken k m otr' pqCap' pqPtr' c R s0 s haddr hfs ⟨hbud0, hap⟩
  obtain ⟨⟨h15_raw, htrust, hsave⟩, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hap
  have h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr' :=
    h15_raw
  clear h15_raw
  dsimp only [retagSessionStore, retagIdentityStore] at htrust hsave htr
  rw [show (retagSessionStore (A' := A.atState lim st s) kit).ss_vt = kit.ss_vt from rfl,
      show (retagIdentityStore (A' := A.atState lim st s) ikit).id_vt = ikit.id_vt from rfl,
      show encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
            (retagIdentityStore (A' := A.atState lim st s) ikit)
            ((retagIdentityStore (A' := A.atState lim st s) ikit).saveUpdate
              ((retagIdentityStore (A' := A.atState lim st s) ikit).trustUpdate ist0 x.rem.val k
                .sending (.ok true)) x.rem.val k (.ok c)) x s0 =
          encStoreExtraPlaced kit st0 ikit
            (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true))
              x.rem.val k (.ok c)) x s0 from rfl] at hm
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set rec' := storedRecord sess otr' taken
  set ist2 := ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c)
  have hsc_some : taken.senderChain.isSome = true :=
    fromSessionState_senderChain_isSome h15.2.2.1
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  have hm_in : s.mem ⊨
      (cmSlots (A.atState lim st s) s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
        encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
        memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x draws s0) ∗
      (encStoreExtraPlaced kit st0 ikit ist2 x s0 ∗ R) := by
    rw [hsp]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  refine apply_to_de8_placed (R0 := R) env hbud0.1.seq_left
    hpc hrun hsp hsp_al hcrl hx25' hpref0 hsc_some hm_in ?_
  intro s_de8 g' evs_apply hevs_apply hsteps_de8 hpc_de8 hrun_de8 hsp_de8 hsp_de8_al hcrl_de8 htr_de8
    hx19_de8 hx20_de8 hx25_de8 hx26_de8 hx28_de8 hx29_de8 hvregs_de8 hm_de8
  have hbud_de8 := hbud0.advance hevs_apply
  set st_de8 := M.stepEvents evs_apply st
  have hsp_de8' : s_de8.sp = sp := hsp_de8.trans hsp
  have hsp_de8_s0 : s_de8.sp = s0.sp - 0xbe0#64 := hsp_de8'
  have hpref_de8 : s0.trace <+: s_de8.trace := by rw [htr_de8]; exact hpref0
  set F := storePassivePlaced kit ikit ist2 ctl x k m draws s0
  let kit_de8 := retagSessionStore (A' := A.atState lim st_de8 s_de8) kit
  let ikit_de8 := retagIdentityStore (A' := A.atState lim st_de8 s_de8) ikit
  have hm_de8' : s_de8.mem ⊨
      (((sessionRecordAt (A.atState lim st_de8 s_de8) (s.sp + 0x110#64) g' rec' ∗
        ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗ memRegion (s.sp + 0x288#64) 200 ∗
        ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt (A.atState lim st_de8 s_de8) (s.sp + 0x370#64) (.ok m) ∗
        ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x469#64) ↦₈ 0#8)) ∗
      cmScratch s.sp ∗ encSpillsAtV kit_de8.ss_vt ikit_de8.id_vt s.sp x ∗
      memRegion (s.sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st_de8 s_de8) ctl x draws s0) ∗
      encStoreExtraPlaced kit_de8 st0 ikit_de8 ist2 x s0) ∗ R :=
    Eq.mp (congrArg (s_de8.mem ⊨ ·) (by ac_rfl)) hm_de8
  have hm_split := Satisfies.mono
    (sepConj_mono_left (store_mem_split_placed kit_de8 st0 ikit_de8 ist2 ctl x g' rec' k m draws s0 s.sp hsp))
    hm_de8'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_split
  rcases hm_split with ⟨hbound, hm_split⟩
  have hm_store_in : s_de8.mem ⊨ (storeVtablesAt kit ∗
      storeBaseActive kit_de8 st0 ikit_de8 s_de8.sp x g' rec' ∗
      memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
      memRegion (s_de8.sp + 0x9b0#64) 24) ∗ (F ∗ R) := by
    rw [hsp_de8]
    have hm_vt := storeVtablesAt_placed_intro env.vtables hcrl_de8.2 hm_split
    dsimp only [F, kit_de8, ikit_de8]
    exact Eq.mp (congrArg (s_de8.mem ⊨ ·) (by ac_rfl)) hm_vt
  have hx20_de8' : s_de8.readReg64 .x20 = s_de8.sp + 0x58#64 := by
    rw [hx20_de8, hsp_de8, hsp, hx20]
  have hx25_de8' : s_de8.readReg64 .x25 = s_de8.sp + 0x580#64 := by
    rw [hx25_de8, hsp_de8, hx25']
  have hrecOk : kit.RecOk rec' := env.recOk h15
  have hfs_de8 : FsCtx kit.envOk True (lsProg_464 Hk) s_de8 s_de8 :=
    ((hfs.of_steps hsteps_de8).rebase (by rw [htr_de8, htr])
      (fun hQ => by
        obtain ⟨⟨hl, -⟩, ht, hs⟩ := hQ
        simp only [NoFsEv.append_iff, hl, ht, hs, and_self])).mono
      (fun _ h => h.1) (fun _ => trivial)
  refine store_to_e80_placed env hbud_de8 hrecOk haddr hbound hpc_de8 hrun_de8 hsp_de8_al
    hx20_de8' hx25_de8' hpref_de8 hcrl_de8 hfs_de8 hm_store_in ?_
  intro sm st_m ans w0 w1 w2 w3 w4 w5 H hbudm _hsteps_e80 hpcm hrunm hspm hspm_al hcrlm htrm
    hstoreRel hH hstaged hx19m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm
  have hspm' : sm.sp = sp := hspm.trans hsp_de8'
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        (ikit.trustEvs x.rem.val k .sending (.ok true) ++
          ikit.saveEvs x.rem.val k (.ok c)) ++
        kit.storeEvs encRecord x.rem.val rec' ans) := by
    rw [htrm, htr_de8, htr]
    simp only [List.append_assoc]; rfl
  rcases ans with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  ·
    dsimp only [pollTag] at hans
    subst hans
    obtain ⟨rfl, rfl, rfl⟩ := hstaged rfl
    have hmm_emp : sm.mem ⊨ emp ∗
        (((storeBaseActive (retagSessionStore (A' := A.atState lim st_m sm) kit)
            (kit.storeUpdate st0 x.rem.val rec' (.error ()))
            (retagIdentityStore (A' := A.atState lim st_m sm) ikit) s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
          (((s_de8.sp + 0x9b0#64) ↦₆₄ 1#64) ∗ ((s_de8.sp + 0x9b8#64) ↦₆₄ w4) ∗
            ((s_de8.sp + 0x9c0#64) ↦₆₄ w5)) ∗
          (w1 ↦ᵣ storeHookStr)) ∗ F) ∗ R) := by
      rw [emp_sepConj, sepConj_assoc]
      exact hmm
    refine SegExitBudget.of_sepWP hmm_emp (step_e80_err_placed hpcm hrunm hx27m) ?_
    rintro s_err _ _ hsteps_err hpc_err hrun_err hm_err
      ⟨hvm_err, rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err,
        hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj] at hm_err
    have hcrl_err : StoreKit.LibsignalCodeRoLoaded lsmpl s_err.mem := hcrlm.of_keepsFrozen hsteps_err.keepsFrozen
    let kit_err := retagSessionStore (A' := A.atState lim st_m s_err) kit
    let ikit_err := retagIdentityStore (A' := A.atState lim st_m s_err) ikit
    have hm_ro' : s_err.mem ⊨
        ((storeBaseActive kit_err (kit.storeUpdate st0 x.rem.val rec' (.error ()))
            ikit_err s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
          (((s_de8.sp + 0x9b0#64) ↦₆₄ 1#64) ∗ ((s_de8.sp + 0x9b8#64) ↦₆₄ w4) ∗
            ((s_de8.sp + 0x9c0#64) ↦₆₄ w5)) ∗
          (w1 ↦ᵣ storeHookStr)) ∗
        storePassivePlaced kit_err ikit_err ist2 ctl x k m draws s0) ∗ R := by
      rw [← A.atState_eq_of_vmPreserved lim st_m hvm_err] at hm_err
      rw [show storePassivePlaced kit_err ikit_err ist2 ctl x k m draws s0 = F from rfl]
      exact hm_err
    have htail_ent := store_mem_to_tail_placed kit_err (kit.storeUpdate st0 x.rem.val rec' (.error ()))
      ikit_err ist2 ctl x g' rec' k m draws s0 s_de8.sp hsp_de8' hbound 1#64 w4 w5
      (w1 ↦ᵣ storeHookStr)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    have htm :=
      StepsThroughEncrypt.tailModel_store_err c (encRecord := encRecord) (s0 := s0) (s := s_err)
        h15 htrust hsave hstoreRel (htr_err.trans htrm')
    have hdraws : x.draws S (answersOfStoreErr r c) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfStoreErr r c) rfl
    have hfinal :
        kit.storeFinal st0 (answersOfStoreErr r c) (x.model C S uuidTryParse (answersOfStoreErr r c)).2 =
          kit.storeUpdate st0 x.rem.val rec' (.error ()) := by
      rw [StepsThroughEncrypt.model_store_err c h15]; rfl
    have hid_final :
        ikit.idFinal ist0 (answersOfStoreErr r c) (x.model C S uuidTryParse (answersOfStoreErr r c)).2 =
          ist2 := by
      rw [StepsThroughEncrypt.model_store_err c h15]; rfl
    refine SegExitBudget.of_false
      (env.tailStoreHookErr x st_init st_m R s0 s_err (answersOfStoreErr r c) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        (w1 ↦ᵣ storeHookStr) cmScratch (Or.inr rfl)
        g' rec' none m 0xf2c 0x9b0 (Or.inr (Or.inr rfl))
        htm (speStaged_storeErr_placed A.repAlloc x.ret w1 w4 w5) ⟨hbudm, ?_⟩)
    refine ⟨hpc_err,
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_err,
       by rw [hx29_err, hx29m, hx29_de8, hx29],
       by rw [hx19_err, hx19m, hx19_de8, hx19], hcrl_err,
       by rw [hvregs_err, hvregsm, hvregs_de8, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26_de8, hx26], by rw [hx28_err, hx28m, hx28_de8, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    rw [encTail_mem_retag_eq, hdraws, hfinal, hid_final, ← hsp_de8_s0]
    dsimp only [kit_err, ikit_err, encStoreExtraPlaced, retagSessionStore, retagIdentityStore] at hm_tail ⊢
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by sep_ac_rfl)) hm_tail
  ·
    dsimp only [pollTag] at hans
    subst hans
    rw [hH rfl, sepConj_emp] at hmm
    have hmm_emp : sm.mem ⊨ emp ∗
        (((storeBaseActive (retagSessionStore (A' := A.atState lim st_m sm) kit)
            (kit.storeUpdate st0 x.rem.val rec' (.ok ()))
            (retagIdentityStore (A' := A.atState lim st_m sm) ikit) s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
          (((s_de8.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s_de8.sp + 0x9b8#64) ↦₆₄ w4) ∗
            ((s_de8.sp + 0x9c0#64) ↦₆₄ w5))) ∗ F) ∗ R) := by
      rw [emp_sepConj, sepConj_assoc]
      exact hmm
    refine SegExitBudget.of_sepWP hmm_emp (step_e80_ok_placed hpcm hrunm hx27m) ?_
    rintro s_ok _ _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨hvm_ok, rfl, hsp_ok, htr_ok, hx19_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj] at hm_ok
    have hcrl_ok : StoreKit.LibsignalCodeRoLoaded lsmpl s_ok.mem := hcrlm.of_keepsFrozen hsteps_ok.keepsFrozen
    let kit_ok := retagSessionStore (A' := A.atState lim st_m s_ok) kit
    let ikit_ok := retagIdentityStore (A' := A.atState lim st_m s_ok) ikit
    have hm_ok_9b0 : s_ok.mem ⊨
        (((s_de8.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s_de8.sp + 0x9b0#64 + 8#64) ↦₆₄ w4) ∗
          ((s_de8.sp + 0x9b0#64 + 16#64) ↦₆₄ w5)) ∗
        ((storeBaseActive kit_ok (kit.storeUpdate st0 x.rem.val rec' (.ok ()))
            ikit_ok s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48) ∗ F ∗ R) := by
      rw [← A.atState_eq_of_vmPreserved lim st_m hvm_ok] at hm_ok
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s_de8.sp + 0x9b0#64) w3 w4 w5)) hm_ok_9b0
    have hm_ok_pre : s_ok.mem ⊨
        ((storeBaseActive kit_ok (kit.storeUpdate st0 x.rem.val rec' (.ok ()))
            ikit_ok s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
          memRegion (s_de8.sp + 0x9b0#64) 24) ∗
          storePassivePlaced kit_ok ikit_ok ist2 ctl x k m draws s0) ∗ R := by
      rw [show storePassivePlaced kit_ok ikit_ok ist2 ctl x k m draws s0 = F from rfl]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_fold
    have hm_ok_stored := Satisfies.mono (sepConj_mono_left
      (store_mem_to_stored_placed kit_ok (kit.storeUpdate st0 x.rem.val rec' (.ok ()))
        ikit_ok ist2 ctl x g' rec' k m draws s0 s_de8.sp hsp_de8' hbound)) hm_ok_pre
    refine SegExitBudget.next ⟨st_m, hbudm, ⟨h15, htrust, hsave, hstoreRel⟩, hpc_ok,
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29_de8, hx29],
        by rw [hx19_ok, hx19m, hx19_de8, hx19], hcrl_ok,
        by rw [hvregs_ok, hvregsm, hvregs_de8, hvregs]⟩,
      by dsimp only [retagSessionStore, retagIdentityStore]; rw [htr_ok, htrm']; simp only [List.append_assoc]; rfl,
      ⟨by rw [hx26_ok, hx26m, hx26_de8, hx26],
       by rw [hx28_ok, hx28m, hx28_de8, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩
    dsimp only [kit_ok, ikit_ok, rec', draws, ist2, encStoreExtraPlaced,
      retagSessionStore, retagIdentityStore] at hm_ok_stored ⊢
    rw [← hsp_de8_s0]
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by sep_ac_rfl)) hm_ok_stored

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStorePlacedBudget
