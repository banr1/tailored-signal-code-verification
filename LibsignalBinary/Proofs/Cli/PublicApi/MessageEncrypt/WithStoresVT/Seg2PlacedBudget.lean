/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSavePlacedBudget
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSave
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Part 2): `SegFinish` and `SegSave`

Re-exports `h45_segFinish_placed_okVT` from `Seg2PlacedBudgetAux` and proves
`h45_segSave_placed_okVT_of_tails` and `h45_segSave_placed_okVT` on Block `464` (`lsProg_464 Hk`)
under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto IdentityKey OutgoingTripleRatchet SessionState)
open CryptoGames.LibsignalSessionApi
  (CiphertextMessage IdentityChange Session SessionRecord StoreAnswers StoreCall)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
  (EncFsCtxPlaced encCommonPlaced encEntryPlaced encStoreExtraPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSave
  (cliSavePassive save_seam_mem_split_placed save_seam_mem_to_tail_placed)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
  (saveVtablesAt_placed_intro speStaged_storeErr_placed trustActivePlaced
   trustActive_split_extra_placed trustBaseActivePlaced trustBaseActive_join_extra_placed)
open CryptoVerification.LibsignalPublicApi (EncryptGhost)
open CryptoVerification.LibsignalPublicApiRepr
  (AddrVal RecordGhost storeHookStr)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (StepsThroughEncrypt WithStoresEncGhost cmScratch cmSlots
   encSpillsAtV encSubStackV takenRecord withStoresEncStackV)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
  (spAligned_of_sp_eq)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSave
  (savePoll_merge_990)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
  (answersOfSaveErr saveVtablesAt words3_entails_memRegion24)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
  (dropRecordSlots pollWith)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded NoFsEv SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
  (ApplyStateVPlaced EncTailsVPlaced SaveStateVPlaced SegExitPlaced toTempTwinsIkitEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
  (segExit_placed_of_sepWP)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (SaveStepEnv SegExitBudget SpqrSendBudgetEnv retagIdentityStore retagSessionStore)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSavePlacedBudget
  (save_to_d94_placed step_d94_err_placed step_d94_ok_placed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
  (EncEnvTPlaced EncTailsVTPlaced h45_envF_placed h45_kitEnvF h45_kitF_placed
   h45_segExit_of_tempTwins_kitF_scope)

export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudgetAux
  (h45_segFinish_placed_okVT_of_tails h45_segFinish_placed_okVT)

section SegSave

private theorem savePassive_atState [LibsignalPlacement] {M : AllocCostModel}
    (ss_vt id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) (draws : Nat) (s0 : State) :
    cliSavePassive ss_vt id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' m draws s0 =
      cliSavePassive ss_vt id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0 := rfl

private theorem dropRecordSlots_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (sp : BitVec 64) (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (om : Option CiphertextMessage) (poll : SepProp) :
    dropRecordSlots (A.atState lim st s) sp scratch g rec ot om poll =
      dropRecordSlots A.repAlloc sp scratch g rec ot om poll := rfl

private theorem encStoreExtraPlaced_retag [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (kit : SessionStoreSpec A.repAlloc 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
        (retagIdentityStore (A' := A.atState lim st s) ikit) ist x s0 =
      encStoreExtraPlaced kit st0 ikit ist x s0 := rfl

private theorem storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs,
      (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).storeFinal st0 ans cs =
      kit.storeFinal st0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact storeFinal_retag kit _ ans cs

private theorem idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs,
      (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs =
      ikit.idFinal ist0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact idFinal_retag ikit _ ans cs

private theorem encStoreExtraPlaced_final_retag [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8))))
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced
      (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit)
      ((LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).storeFinal st0 ans cs)
      (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit)
      ((LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs)
      x s0 =
    encStoreExtraPlaced kit (kit.storeFinal st0 ans cs)
      ikit (ikit.idFinal ist0 ans cs) x s0 := by
  have hs := storeFinal_retag (A' := A') kit st0 ans cs
  have hi := idFinal_retag (A' := A') ikit ist0 ans cs
  have hfn :
      ∀ (st : kit.StoreState) (ist : ikit.IdState),
        encStoreExtraPlaced
          (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit) st
          (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit) ist
          x s0 =
        encStoreExtraPlaced kit st ikit ist x s0 := fun _ _ => rfl
  exact (hfn _ _).trans (by rw [hs, hi])

private theorem encTail_mem_retag_eq [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV
        (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).ss_vt
        (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).id_vt
        (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced
        (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit)
        ((LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).storeFinal
          st0 answers (x.model C S uuidTryParse answers).2)
        (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit)
        ((LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).idFinal
          ist0 answers (x.model C S uuidTryParse answers).2)
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
      encSpillsAtV
        (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore (A' := A') kit).ss_vt
        (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

theorem h45_segSave_placed_okVT_of_tails [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTailsF : EncTailsVPlaced A lim (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0 ikit ikitEnv ist0
      (fun _ => False) C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s)
    (hsave : SaveStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ st' c,
        ApplyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' c R0 s0 s') := by
  let envF := (h45_envF_placed hEnv).toTempTwins hTailsF
  obtain ⟨hbud, hsave⟩ := hsave
  let R : SepProp := kit.storeAt x.ssA st0 ∗ R0
  obtain ⟨⟨h15, htrustRel⟩, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx22, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hsave
  have h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr' := h15
  have htrustRel : ikit.trustRel ist0 x.rem.val k .sending (.ok true) := htrustRel
  dsimp only [retagSessionStore, retagIdentityStore,
    LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore,
    LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore] at htr hm
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set ist1 := ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)
  set F := cliSavePassive kit.ss_vt ikit.id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hm_pre : s.mem ⊨
      (trustBaseActivePlaced ikit.id_vt (A.atState lim st s) s.sp x k ∗
        encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
          (retagIdentityStore (A' := A.atState lim st s) ikit) ist1 x s0) ∗
      ((memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F ∗ R0) := by
    have hm1 : s.mem ⊨
        (cmSlots (A.atState lim st s) s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
          encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
          memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x draws s0) ∗
        (encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
          (retagIdentityStore (A' := A.atState lim st s) ikit) ist1 x s0 ∗ R0) := by
      rw [hsp, encStoreExtraPlaced_retag]
      exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm
    rw [save_seam_mem_split_placed kit.ss_vt ikit.id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp,
        savePassive_atState] at hm1
    dsimp only [F]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm_join := Satisfies.mono (sepConj_mono_left
    (trustBaseActive_join_extra_placed (retagSessionStore (A' := A.atState lim st s) kit) st0
      (retagIdentityStore (A' := A.atState lim st s) ikit) ist1 x k s0 s.sp hsp)) hm_pre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_join
  obtain ⟨hbound, hm_join⟩ := hm_join
  dsimp only [retagSessionStore] at hbound hm_join
  have hm_split : s.mem ⊨ (saveVtablesAt ikit ∗
      trustActivePlaced (retagIdentityStore (A' := A.atState lim st s) ikit) ist1
        s.sp (encSubStackV (h45_kitF_placed kit) ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x990#64) 24) ∗ (F ∗ R) := by
    have hm' := saveVtablesAt_placed_intro envF.idVtables hcrl.2 hm_join
    dsimp only [R, encSubStackV, h45_kitF_placed]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm'
  have hx22' : s.readReg64 .x22 = s.sp + 0x8b8#64 := by rw [hsp]; exact hx22
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  refine h45_segExit_of_tempTwins_kitF_scope (Scope' := fun _ => False)
    (mid := fun sm =>
      ∃ (evs_save : List AllocEvent) (ans : Except Unit IdentityChange)
        (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
        sm.pc = encEntryPlaced + 0xd94#64 ∧
        sm.status = .Running ∧ sm.sp = s.sp ∧ sm.spAligned = true ∧
        LibsignalCodeRoLoaded lsmpl sm.mem ∧
        ikit.saveRel ist1 x.rem.val k ans ∧
        sm.trace = s.trace ++ ikit.saveEvs x.rem.val k ans ∧
        SaveStepEnv ikit (toTempTwinsIkitEnv ikitEnv) ist1 x.rem.val k evs_save ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x27 = w0 ∧ sm.readReg64 .x21 = w1 ∧ sm.readReg64 .x23 = w2 ∧
        (match ans with
         | .ok c => w0 = 0xFFFFFFFFFFFFFFFE#64 ∧
             w1.setWidth 32 = (if c == .replacedExisting then 1#32 else 0#32) ∧ H = emp
         | .error () => w0 = 0x800000000000001A#64 ∧ w2 = 10#64 ∧ w3 = 1#64 ∧ H = (w1 ↦ᵣ storeHookStr)) ∧
        (sm.mem ⊨ (trustActivePlaced (retagIdentityStore (A' := A.atState lim (M.stepEvents evs_save st) sm) ikit)
            (ikit.saveUpdate ist1 x.rem.val k ans) s.sp (encSubStackV (h45_kitF_placed kit) ikit) x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ w3) ∗ ((s.sp + 0x998#64) ↦₆₄ w4) ∗ ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ (F ∗ R)))
    (fun _ => False.elim)
    (save_to_d94_placed envF hbud.1.seq_left haddr
      (fun s' hst' htr' =>
        ((hfs.of_steps hst').envOk_at (htr'.trans htr) fun hq => by
          obtain ⟨⟨hl, -⟩, ht, -⟩ := hq
          simp only [NoFsEv.append_iff, hl, ht, and_self]).2)
      hbound hpc hrun hsp_al hx22' hx25' hpref0 hcrl hm_split
      (fun sm evs_save ans w0 w1 w2 w3 w4 w5 H _hsteps_d94 hpcm hrunm hspm hspm_al hcrlm hsaveRel htrm
        hsaveEnv hx19m hx20m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm_act =>
        SegExitBudget.next
          ⟨evs_save, ans, w0, w1, w2, w3, w4, w5, H,
           hpcm, hrunm, hspm, hspm_al, hcrlm, hsaveRel, htrm, hsaveEnv,
           hx19m, hx20m, hx25m, hx26m, hx28m, hx29m, hvregsm, hx27m, hx21m, hx23m, hans, hmm_act⟩))
    ?_
  rintro sm _hsteps_d94
    ⟨evs_save, ans, w0, w1, w2, w3, w4, w5, H,
     hpcm, hrunm, hspm, hspm_al, hcrlm, hsaveRel, htrm, hsaveEnv,
     hx19m, hx20m, hx25m, hx26m, hx28m, hx29m, hvregsm, hx27m, hx21m, hx23m, hans, hmm_act⟩
  set st_m := M.stepEvents evs_save st
  have hbud_m := hbud.advance hsaveEnv
  let R' : SepProp := encStoreExtraPlaced kit st0 ikit (ikit.saveUpdate ist1 x.rem.val k ans) x s0 ∗ R0
  have hmm : sm.mem ⊨ (trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      (((s.sp + 0x990#64) ↦₆₄ w3) ∗
        ((s.sp + 0x998#64) ↦₆₄ w4) ∗
        ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ (F ∗ R') := by
    have hmm1 : sm.mem ⊨
        (trustActivePlaced (retagIdentityStore (A' := A.atState lim st_m sm) ikit)
            (ikit.saveUpdate ist1 x.rem.val k ans) s.sp (encSubStackV kit ikit) x k ∗
          (retagSessionStore (A' := A.atState lim st_m sm) kit).storeAt x.ssA st0) ∗
        ((memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ w3) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ F ∗ R0) := by
      dsimp only [R, encSubStackV, h45_kitF_placed, retagSessionStore] at hmm_act ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm_act
    have hmm2 := Satisfies.mono (sepConj_mono_left
      (trustActive_split_extra_placed (retagSessionStore (A' := A.atState lim st_m sm) kit) st0
        (retagIdentityStore (A' := A.atState lim st_m sm) ikit)
        (ikit.saveUpdate ist1 x.rem.val k ans) x k s0 s.sp hsp hbound)) hmm1
    rw [encStoreExtraPlaced_retag] at hmm2
    dsimp only [R']
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm2
  have hspm' : sm.sp = sp := hspm.trans hsp
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        (ikit.trustEvs x.rem.val k .sending (.ok true) ++
          ikit.saveEvs x.rem.val k ans)) := by
    rw [htrm, htr, List.append_assoc, List.append_assoc]
  rcases ans with ⟨⟨⟩⟩ | c
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
          (w1 ↦ᵣ storeHookStr)) ∗ F) ∗ R') := by
      rw [emp_sepConj]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm
    refine segExit_placed_of_sepWP hmm_emp (step_d94_err_placed hpcm hrunm hx27m) ?_
    rintro s_err _ hsteps_err hpc_err hrun_err hm_err
      ⟨hvm_err, rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj, ← A.atState_eq_of_vmPreserved lim st_m hvm_err] at hm_err
    have hcrl_err : LibsignalCodeRoLoaded lsmpl s_err.mem := hcrlm.of_keepsFrozen hsteps_err.keepsFrozen
    have hm_ro' : s_err.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_err) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
          (w1 ↦ᵣ storeHookStr)) ∗
          cliSavePassive kit.ss_vt ikit.id_vt (A.atState lim st_m s_err) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_err
      rw [savePassive_atState]
      exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by sep_ac_rfl)) hm_err
    have htail_ent := save_seam_mem_to_tail_placed kit.ss_vt ikit.id_vt (A.atState lim st_m s_err) ctl x sess taken otr' pqCap' pqPtr' k m draws s0
      s.sp hsp
      (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
        ((s.sp + 0x998#64) ↦₆₄ w4) ∗
        ((s.sp + 0x9a0#64) ↦₆₄ w5))
      (pollWith s.sp 0x990 [1#64, w4, w5])
      (w1 ↦ᵣ storeHookStr)
      (savePoll_merge_990 s.sp 1#64 w4 w5)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    simp only [sepExists_sepConj_left, satisfies_sepExists, dropRecordSlots_atState] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm :=
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.StepsThroughEncrypt.tailModel_save_err
        (encRecord := encRecord) (s0 := s0) (s := s_err) h15 htrustRel hsaveRel (htr_err.trans htrm')
    have hdraws : x.draws S (answersOfSaveErr r) = draws :=
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.StepsThroughEncrypt.draws_eq
        h15 (answersOfSaveErr r) rfl
    refine SegExitPlaced.of_false
      (hTails.tailStoreHookErr x st_init st_m R0 s0 s_err (answersOfSaveErr r) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        (w1 ↦ᵣ storeHookStr) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m 0xe28 0x990 (Or.inr (Or.inl rfl))
        htm (speStaged_storeErr_placed A.repAlloc x.ret w1 w4 w5) ?_)
    refine ⟨hbud_m.narrow (fun _ h => Or.inl h), hpc_err,
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al,
      spAligned_of_sp_eq hspm_al hsp_err,
      by rw [hx29_err, hx29m, hx29], by rw [hx19_err, hx19m, hx19], hcrl_err,
      by rw [hvregs_err, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26], by rw [hx28_err, hx28m, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    rw [encTail_mem_retag_eq (A' := A.atState lim st_m s_err) kit st0 ikit ist0 C ctl S x
      (answersOfSaveErr r) _ R0 s0]
    rw [hdraws,
      (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.StepsThroughEncrypt.model_save_err h15)]
    rw [hsp] at hm_tail
    dsimp only [sp, draws, ist1, SessionStoreSpec.storeFinal, IdentityStoreSpec.idFinal,
      answersOfSaveErr, R'] at hm_tail ⊢
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by sep_ac_rfl)) hm_tail
  · obtain ⟨rfl, _, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ w3) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5))) ∗ F) ∗ R') := by
      simp only [sepConj_emp, emp_sepConj] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmm
    refine segExit_placed_of_sepWP hmm_emp (step_d94_ok_placed hpcm hrunm hx27m) ?_
    rintro s_ok _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨hvm_ok, rfl, hsp_ok, htr_ok, hx19_ok, hx20_ok, hx25_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj, ← A.atState_eq_of_vmPreserved lim st_m hvm_ok] at hm_ok
    have hcrl_ok : LibsignalCodeRoLoaded lsmpl s_ok.mem := hcrlm.of_keepsFrozen hsteps_ok.keepsFrozen
    have hm_ok_990 : s_ok.mem ⊨
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗
          ((s.sp + 0x990#64 + 8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x990#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_ok) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48) ∗ F ∗ R') := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by sep_ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s.sp + 0x990#64) w3 w4 w5)) hm_ok_990
    have hm_ok_seam : s_ok.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_ok) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x990#64) 24) ∗
          cliSavePassive kit.ss_vt ikit.id_vt (A.atState lim st_m s_ok) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_ok_fold
      rw [savePassive_atState]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by sep_ac_rfl)) hm_ok_fold
    rw [← save_seam_mem_split_placed kit.ss_vt ikit.id_vt (A.atState lim st_m s_ok) ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm_ok_seam
    rw [hsp] at hm_ok_seam
    refine SegExitPlaced.next ⟨st_m, c, hbud_m.narrow (fun _ h => Or.inr h),
      ⟨h15, htrustRel, hsaveRel⟩, hpc_ok,
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al, spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29], by rw [hx19_ok, hx19m, hx19], hcrl_ok,
        by rw [hvregs_ok, hvregsm, hvregs]⟩,
      by rw [htr_ok, htrm']; simp only [List.append_assoc],
      ⟨by rw [hx20_ok, hx20m, hx20],
       by rw [hx25_ok, hx25m, hx25], by rw [hx26_ok, hx26m, hx26],
       by rw [hx28_ok, hx28m, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩
    dsimp only [sp, draws, ist1, R', retagSessionStore, retagIdentityStore,
      LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore,
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore] at hm_ok_seam ⊢
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by sep_ac_rfl)) hm_ok_seam

theorem h45_segSave_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (hTails : EncTailsVTPlaced A lim ikit ikitEnv ist0 C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s)
    (hsave : SaveStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ st' c,
        ApplyStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r sess otr taken k m otr' pqCap' pqPtr' c R0 s0 s') :=
  h45_segSave_placed_okVT_of_tails hEnv
    (@hTails (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0 (fun _ => False))
    (@hTails kit kitEnv st0 Scope)
    x st_init st r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s haddr hfs hsave

end SegSave

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2PlacedBudget
