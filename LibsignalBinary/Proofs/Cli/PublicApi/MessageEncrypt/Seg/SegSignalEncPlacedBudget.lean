/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalUnackPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalEnc
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `segSignal` Setup Before `OTR::encrypt` (`+0x348..+0x3a0`)

Defines `SegSignalEncStateVPlaced` and proves `segSignal_placed_ack_to_enc` (`+0x348..+0x3a0`) on
Block `464` (`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncPlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalUnackPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOkPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalMemPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
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
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- **Enc** (`OTR::encrypt`'s entry, `lr = +0x3a4`) under `[LibsignalPlacement]`:
`segSignal_placed_step_enc` done. -/
def SegSignalEncStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
    (FromKeyEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k) ∧
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
  taken.remoteIdentity = some k ∧ sess.pendingPreKey = none ∧
  s.pc = libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName ∧
  s.readReg64 Reg.lr = encEntryPlaced + 0x3a4#64 ∧ encMidMetaPlaced x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
  s.readReg64 .x2 = x.ptA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length ∧
  s.readReg64 .x4 = 0#64 ∧ s.readReg64 .x5 = x.remA ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧
  s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
  s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  (s.mem ⊨
    (takenSlots (A.atState lim st s) sp sess taken ∗
      otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
      memRegion (sp + 0x5f8#64) 0x588) ∗
    memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x 0 s0 ∗
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0))

set_option maxHeartbeats 1600000 in
/-- **Ack → Enc** (`+0x348..+0x3a0`) under `[LibsignalPlacement]`: `segSignal_placed_step_enc`. -/
theorem segSignal_placed_ack_to_enc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (_env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State)
    (hs : SegSignalAckStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord x st_init st r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R0 s0 s
      (fun s' => SegSignalEncStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord x st_init st r sess otr taken pqCap pqPtr k
        R0 s0 s') := by
  obtain ⟨hbud, hcur, hsc, hfrom, hrem, hnone, hs_pc, ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx20, hx23, hx25, hx26, hx27, hx28, hpt, hrest, hloc, hnow, hstk, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  change s.mem ⊨
    (takenSlots (A.atState lim st s) sp sess taken ∗
      otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    curScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
    memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x 0 s0 ∗
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) at hm
  unfold curScratch encSpillsAtV at hm
  have hscr : memRegion sp 0x50 =
      memRegion sp 0x38 ∗ memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8 ∗
        memRegion (sp + 0x48#64) 8 := by
    rw [segSignal_memRegion_cut sp (sp + 0x38#64) 0x50 0x38 0x18 rfl rfl (by decide),
      segSignal_memRegion_cut (sp + 0x38#64) (sp + 0x40#64) 0x18 8 0x10 (by bv_omega) rfl (by decide),
      segSignal_memRegion_cut (sp + 0x40#64) (sp + 0x48#64) 0x10 8 8 (by bv_omega) rfl (by decide)]
  have h584 : memRegion (sp + 0x584#64) 84 =
      memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗ memRegion (sp + 0x590#64) 8 ∗
        memRegion (sp + 0x598#64) 4 ∗ memRegion (sp + 0x59c#64) 8 ∗
        memRegion (sp + 0x5a4#64) 8 ∗ memRegion (sp + 0x5ac#64) 8 ∗
        memRegion (sp + 0x5b4#64) 8 ∗ memRegion (sp + 0x5bc#64) 4 ∗
        memRegion (sp + 0x5c0#64) 24 := by
    rw [show (84 : Nat) = 4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + 24)))))))) from rfl,
      show sp + 0x584#64 = sp + BitVec.ofNat 64 0x584 from rfl,
      mr_cut_add sp 0x584 4 _ (by decide),
      mr_cut_add sp (0x584 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  have h5d8 : memRegion (sp + 0x5d8#64) 0x5a8 =
      memRegion (sp + 0x5d8#64) 32 ∗ memRegion (sp + 0x5f8#64) 0x278 ∗
        memRegion (sp + 0x870#64) 8 ∗ memRegion (sp + 0x878#64) 8 ∗
        memRegion (sp + 0x880#64) 8 ∗ memRegion (sp + 0x888#64) 8 ∗
        memRegion (sp + 0x890#64) 4 ∗ memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x5a8 : Nat) = 32 + (0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec)))))) from rfl,
      show sp + 0x5d8#64 = sp + BitVec.ofNat 64 0x5d8 from rfl,
      mr_cut_add sp 0x5d8 32 _ (by decide),
      mr_cut_add sp (0x5d8 + 32) 0x278 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  rw [hscr, h584, h5d8] at hm
  obtain ⟨u38, hm⟩ := segSignal_peel8 (sp + 0x38#64) (by sep_focus) hm
  obtain ⟨u40, hm⟩ := segSignal_peel8 (sp + 0x40#64) (by sep_focus) hm
  obtain ⟨u48, hm⟩ := segSignal_peel8 (sp + 0x48#64) (by sep_focus) hm
  obtain ⟨a0, hm⟩ := segSignal_peel4 (sp + 0x584#64) (by sep_focus) hm
  obtain ⟨a1, hm⟩ := segSignal_peel8 (sp + 0x588#64) (by sep_focus) hm
  obtain ⟨a2, hm⟩ := segSignal_peel8 (sp + 0x590#64) (by sep_focus) hm
  obtain ⟨a3, hm⟩ := segSignal_peel4 (sp + 0x598#64) (by sep_focus) hm
  obtain ⟨c0, hm⟩ := segSignal_peel8 (sp + 0x59c#64) (by sep_focus) hm
  obtain ⟨c1, hm⟩ := segSignal_peel8 (sp + 0x5a4#64) (by sep_focus) hm
  obtain ⟨c2, hm⟩ := segSignal_peel8 (sp + 0x5ac#64) (by sep_focus) hm
  obtain ⟨c3, hm⟩ := segSignal_peel8 (sp + 0x5b4#64) (by sep_focus) hm
  obtain ⟨c4, hm⟩ := segSignal_peel4 (sp + 0x5bc#64) (by sep_focus) hm
  obtain ⟨e0, hm⟩ := segSignal_peel8 (sp + 0x870#64) (by sep_focus) hm
  obtain ⟨e1, hm⟩ := segSignal_peel8 (sp + 0x878#64) (by sep_focus) hm
  obtain ⟨e2, hm⟩ := segSignal_peel8 (sp + 0x880#64) (by sep_focus) hm
  obtain ⟨e3, hm⟩ := segSignal_peel8 (sp + 0x888#64) (by sep_focus) hm
  obtain ⟨e4, hm⟩ := segSignal_peel4 (sp + 0x890#64) (by sep_focus) hm
  have hm4 := segSignal_focusR' (T := ((sp + 0x38#64) ↦₆₄ u38) ∗ ((sp + 0x40#64) ↦₆₄ u40) ∗
        ((sp + 0x48#64) ↦₆₄ u48) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
        ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
        ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
        ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
        ((sp + 0x5bc#64) ↦₃₂ c4) ∗
        ((sp + 0x870#64) ↦₆₄ e0) ∗ ((sp + 0x878#64) ↦₆₄ e1) ∗ ((sp + 0x880#64) ↦₆₄ e2) ∗
        ((sp + 0x888#64) ↦₆₄ e3) ∗ ((sp + 0x890#64) ↦₃₂ e4))
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm
  refine SegExitBudget.of_sepWP hm4 (segSignal_placed_step_enc hs_pc hrun hsp hal hx23 hx25 hx27) ?_
  intro s3 Pm3 _hL hsteps hs3_pc hs3_run hm5
    ⟨hvm03, hs3_sp, hs3_tr, hx0, hx1, hx2, hx3, hx4, hx5, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28,
      hs3_x29, hs3_vregs, hlr, hPm3⟩
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hPost := Entails.trans hPm3
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _) (sepConj_mono
    (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo32_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (pointsTo32_entails_memRegion _ _)))))))))))))))))))))
  have hm7 := Satisfies.mono (sepConj_mono_left hPost) hm5
  rw [(A.atState_eq_of_vmPreserved lim st hvm03).symm] at hm7
  refine SegExitBudget.next ?_
  unfold SegSignalEncStateVPlaced
  refine ⟨hbud, hcur, hsc, hfrom, hrem, hnone, hs3_pc, hlr,
    ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19, hcrl3,
      hs3_vregs.trans hvregs⟩,
    hs3_tr.trans htr, hx0, hx1, hx2, hx3, hx4, hx5, hs3_x20.trans hx20, hs3_x25.trans hx25,
    hs3_x26.trans hx26, hs3_x28.trans hx28, hpt, hrest, hloc, hnow, hstk, ?_⟩
  rw [← hsp0]
  have h580g : memRegion (sp + 0x580#64) 120 =
      memRegion (sp + 0x580#64) 4 ∗ memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗
        memRegion (sp + 0x590#64) 8 ∗ memRegion (sp + 0x598#64) 4 ∗
        memRegion (sp + 0x59c#64) 8 ∗ memRegion (sp + 0x5a4#64) 8 ∗
        memRegion (sp + 0x5ac#64) 8 ∗ memRegion (sp + 0x5b4#64) 8 ∗
        memRegion (sp + 0x5bc#64) 4 ∗ memRegion (sp + 0x5c0#64) 24 ∗
        memRegion (sp + 0x5d8#64) 32 := by
    rw [show (120 : Nat) = 4 + (4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + (24 + 32))))))))))
        from rfl,
      show sp + 0x580#64 = sp + BitVec.ofNat 64 0x580 from rfl,
      mr_cut_add sp 0x580 4 _ (by decide),
      mr_cut_add sp (0x580 + 4) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8 + 4) 24 _ (by decide)]
  have h5f8g : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x278 ∗ memRegion (sp + 0x870#64) 8 ∗
        memRegion (sp + 0x878#64) 8 ∗ memRegion (sp + 0x880#64) 8 ∗
        memRegion (sp + 0x888#64) 8 ∗ memRegion (sp + 0x890#64) 4 ∗
        memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x588 : Nat) = 0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec))))) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x278 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  rw [h580g, h5f8g]
  unfold cmScratch encSpillsAtV
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm7

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncPlacedBudget
