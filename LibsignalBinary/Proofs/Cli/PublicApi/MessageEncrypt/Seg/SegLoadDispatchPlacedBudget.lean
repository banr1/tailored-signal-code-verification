/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs -- shake: keep

/-!
# Budget-Threaded Relocatable CLI `SegLoad` Dispatch: `.error ()` & `.ok none` Branches

Proves the budget-threaded `ans = .error ()` and `ans = .ok none` dispatch branches of `SegLoad`
on `lsProg_464 Hk` (`blkPl_464`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchPlacedBudget

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

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
open CryptoVerification.LibsignalTripleRatchet hiding
  LibsignalCodeRoLoaded withLsCodeRoLoaded sepWP_seq_lscro sepWPp_seq_lscro
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlacedBudget
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cs_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x19 = s0.readReg64 .x19 := h.1
private theorem cs_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x22 = s0.readReg64 .x22 := h.2.2.2.1
private theorem cs_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x26 = s0.readReg64 .x26 := h.2.2.2.2.2.2.2.1
private theorem cs_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x28 = s0.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
private theorem cs_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x29 = s0.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
private theorem cs_vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2

/-! ## 1. Branch 1: `ans = .error ()` (`+0x160..+0x174` → `+0x5b4` `env.tailWriteErr`) -/

theorem segLoad_dispatch_err_budget_wp_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {sp w4 w5 w6 : BitVec 64} {F : SepProp}
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hps : s.pstate = addsPState64 0xFFFFFFFFFFFFFFFE#64 2#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x5b4#64) s
      (((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        P_f = (((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x848#64) 0x188 ∗
          ((sp + 0x9d0#64) ↦₆₄ w4) ∗ ((sp + 0x9d8#64) ↦₆₄ w5) ∗ ((sp + 0x9e0#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx25 hx26
  by_vm_steps (
    wp_conv_pre => rw [memRegion_0x848_split_0x9d0 s.sp]
    wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hx26, hal_norm, true_and])

set_option maxHeartbeats 800000 in
theorem segLoad_dispatch_err_budget [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st3 : M.σ) (R : SepProp) (s0 s : State)
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hbud3 : SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
      st_init st3 (LoadRemEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 Scope x))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hmeta : encMidMetaPlaced x s0 s)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.error ()))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.error ()))
    (hx27 : s.readReg64 .x27 = w1) (hx21 : s.readReg64 .x21 = w2) (hx23 : s.readReg64 .x23 = w3)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc (.error ()) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st3 s ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s
      (fun s' => ∃ st' r g sess,
        CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩
  have hbud_free : SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
      st_init st3 FreeOnlyEvs :=
    hbud3.narrow fun _ h => Or.inl h
  have hm_drop : s.mem ⊨
      LoadOutResPlaced Scope A.repAlloc (.error ()) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st3 s ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  clear hm
  rw [loadOutResPlaced_err_eq] at hm_drop
  obtain ⟨strPtr, hm_drop1⟩ := satisfies_sepExists_left hm_drop
  obtain ⟨vt, hm_drop2⟩ := satisfies_sepExists_left hm_drop1
  clear hm_drop hm_drop1
  rw [sepConj_assoc] at hm_drop2
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hm_drop'⟩ := satisfies_pure_left hm_drop2
  let strPtr := w2; let vt := w5
  clear hm_drop2
  rw [← sepConj_assoc] at hm_drop'
  have hm_tail : s.mem ⊨
      (((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
        ((strPtr ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          memRegion (s0.sp - 0xbe0#64) 0x58 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
          encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st3 s) ctl x 0 s0 ∗
          encStoreExtraPlaced kit st0 ikit ist0 x s0)) ∗ R := by
    refine Satisfies.mono ?_ hm_drop'
    refine sepConj_mono_left ?_
    have hfr := dispatchFramePlaced_tail_entails
      (retagSessionStore (A' := A.atState lim st3 s) kit) st0
      (retagIdentityStore (A' := A.atState lim st3 s) ikit) ist0 ctl x s0 v50
    have hperm1 :
        (strPtr ↦ᵣ storeHookStr) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          A.pool lim st3 s ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) =
        (protocolAddressAt (A.atState lim st3 s) x.rem x.remA ∗
          (A.atState lim st3 s).pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          dispatchFramePlaced (retagSessionStore (A' := A.atState lim st3 s) kit) st0
            (retagIdentityStore (A' := A.atState lim st3 s) ikit) ist0 ctl x s0 v50) ∗
        ((strPtr ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6)) := by
      change _ = (protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st3 s ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ _
      sep_ac_rfl
    rw [hperm1]
    refine Entails.trans (sepConj_mono_left hfr) ?_
    change (memRegion (s0.sp - 0xbe0#64) 0x58 ∗ memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗ memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
        encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st3 s) ctl x 0 s0 ∗
        encStoreExtraPlaced kit st0 ikit ist0 x s0) ∗ _ ⊢ _
    exact Entails.of_eq (by sep_ac_rfl)
  have hwp := segLoad_dispatch_err_budget_wp_vm (Hk := Hk)
    (w4 := 1#64) (w5 := vt) (w6 := w6)
    (F := (strPtr ↦ᵣ storeHookStr) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
      ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
      memRegion (s0.sp - 0xbe0#64) 0x58 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st3 s) ctl x 0 s0 ∗
      encStoreExtraPlaced kit st0 ikit ist0 x s0)
    hpc hrun hsp hal hx25 hx26 hps
  refine segExit_budget_of_sepWP_frozen hcrl hm_tail hwp ?_
  intro sf P_f hpcf hrunf hpostf hcrlf hm_f
  rcases hpostf with ⟨hvmf, hspf, half, htrf, hx19f, hx29f, hvregsf, hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
  have hcomm_eq : encCommonPlaced (A.atState lim st3 s) ctl x 0 s0 =
      encCommonPlaced (A.atState lim st3 sf) ctl x 0 s0 := by
    rw [A.atState_eq_of_vmPreserved lim st3 hvmf]
  rw [hcomm_eq] at hm_f
  refine segExit_budget_of_false (env.tailWriteErr x st_init st3 R s0 sf
    (answersOfLoad (.error ())) (.store ())
    0x800000000000001A#64 strPtr 10#64 1#64 vt w6
    (strPtr ↦ᵣ storeHookStr)
    (tailModel_load_err hl (htrf.trans htr))
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.speStaged_storeErr_placed
      A.repAlloc x.ret strPtr vt w6)
    ⟨hbud_free, hpcf,
      ⟨hrunf, hspf, hal0, half, hx29f.trans hx29, hx19f.trans hx19, hcrlf, hvregsf.trans hvregs⟩,
      ⟨hx26f, hx28f.trans hx28, hx27f.trans hx27, hx21f.trans hx21, hx23f.trans hx23⟩,
      enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
  dsimp only [EncTailVPlaced, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailVPlaced]
  rw [segLoad_encTail_mem_retag_eq (A' := A.atState lim st3 sf) kit st0 ikit ist0 C ctl S x
    (answersOfLoad (.error ())) _ R s0]
  rw [draws_answersOfLoad_err]
  change sf.mem ⊨ _ ∗ _ ∗ _ ∗ _ ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)
  refine Satisfies.mono ?_ hm_f
  have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
    1#64 vt w6 1#64 vt w6 tail htail
  have hperm2 :
      ((((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
        ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
        ((strPtr ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          memRegion (s0.sp - 0xbe0#64) 0x58 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
          encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st3 sf) ctl x 0 s0 ∗
          encStoreExtraPlaced kit st0 ikit ist0 x s0)) ∗ R) =
      ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188) ∗
      (((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ w6)) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198) ∗
      (memRegion (s0.sp - 0xbe0#64) 0x58 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
        (strPtr ↦ᵣ storeHookStr) ∗
        encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
        memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st3 sf) ctl x 0 s0 ∗
        (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)) := by
    sep_ac_rfl
  rw [hperm2]
  refine Entails.trans (sepConj_mono_left hpoll) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. Branch 2: `ans = .ok none` (`+0x160`, `+0x178..+0x180`, `+0x41c..+0x458` → `+0x5b4`) -/

theorem segLoad_dispatch_none_pre_budget_wp_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {sp remA : BitVec 64} {F : SepProp}
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = 0xFFFFFFFFFFFFFFFF#64)
    (hps : s.pstate = addsPState64 0xFFFFFFFFFFFFFFFF#64 2#64) :
    SepWP (lsProg_464 Hk) (lsmpl.base 623) s
      (((sp + 0x108#64) ↦₆₄ remA) ∗ F)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = remA ∧
        sf.readReg64 .x8 = sp + 0x580#64 ∧
        sf.readReg64 .x22 = remA ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x428#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        P_f = (((sp + 0x108#64) ↦₆₄ remA) ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx24
  by_vm_steps (
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hal_norm, true_and])

theorem sepWP_trans_budget {P : Program} {mid tgt : BitVec 64} {s0 : State}
    {Pre : SepProp} {Post1 Post2 : State → SepProp → Prop}
    (h1 : SepWP P mid s0 Pre Post1)
    (h2 : ∀ sa Pa, sa.pc = mid → sa.status = .Running → Post1 sa Pa → SepWP P tgt sa Pa Post2) :
    SepWP P tgt s0 Pre Post2 := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sa, hs1, ⟨hpc1, hrun1, Pa, hma, hp1⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h1 hm hL
  · obtain ⟨sb, hs2, hout2⟩ :=
      SepWP.to_reaches_pc (h2 sa Pa hpc1 hrun1 hp1) hma (hs1.codeLoaded hL)
    exact ⟨sb, hs1.trans hs2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem sepWP_shift_vmPreserved {P : Program} {tgt : BitVec 64} {s0 s1 : State}
    {Pre : SepProp} {rest : State → SepProp → Prop}
    (h01 : VmPreserved s0 s1)
    (hwp : SepWP P tgt s1 Pre (fun sf Pf => VmPreserved s1 sf ∧ rest sf Pf)) :
    SepWP P tgt s1 Pre (fun sf Pf => VmPreserved s0 sf ∧ rest sf Pf) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sf, hs, ⟨hpc, hrun, Pf, hmf, h1f, hr⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc hwp hm hL
  · exact ⟨sf, hs, Or.inl ⟨hpc, hrun, Pf, hmf, h01.trans h1f, hr⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

set_option maxHeartbeats 800000 in
theorem segLoad_dispatch_none_post_budget_wp_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {sp remA cap ptr len : BitVec 64} {dev : BitVec 8} {F : SepProp}
    (hpc : s.pc = encEntryPlaced + 0x428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = remA)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x5b4#64) s
      (((remA + 0x18#64) ↦₈ dev) ∗
        ((sp + 0x580#64) ↦₆₄ cap) ∗ ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ len) ∗
        memRegion (sp + 0x598#64) 344 ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        VmPreserved s sf ∧
        ∃ w3 : BitVec 64, DevWord dev w3 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          sf.readReg64 .x26 = sp + 0x9d0#64 ∧
          sf.readReg64 .x28 = sp + 0x4a0#64 ∧
          sf.readReg64 .x27 = cap ∧
          sf.readReg64 .x21 = ptr ∧
          sf.readReg64 .x23 = len ∧
          P_f = (((remA + 0x18#64) ↦₈ dev) ∗
            memRegion (sp + 0x580#64) 368 ∗
            memRegion (sp + 0x848#64) 0x188 ∗
            ((sp + 0x9d0#64) ↦₆₄ w3) ∗
            ((sp + 0x9d8#64) ↦₆₄ (lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.122")) ∗
            ((sp + 0x9e0#64) ↦₆₄ 15#64) ∗
            memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx22 hx26 hx28
  refine sepWP_trans_budget (mid := blkPl_464.base + 1084#64)
    (Post1 := fun sa Pa =>
      VmPreserved s sa ∧
      ∃ w3 v5a0 : BitVec 64, DevWord dev w3 ∧
        sa.sp = s.sp ∧ sa.spAligned = true ∧ sa.trace = s.trace ∧
        sa.readReg64 .x19 = s.readReg64 .x19 ∧
        sa.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sa = calleeSavedVRegs s ∧
        sa.readReg64 .x26 = s.sp + 0x9d0#64 ∧
        sa.readReg64 .x28 = s.sp + 0x4a0#64 ∧
        sa.readReg64 .x27 = cap ∧
        sa.readReg64 .x21 = ptr ∧
        sa.readReg64 .x23 = len ∧
        Pa = (((remA + 0x18#64) ↦₈ dev) ∗
          ((s.sp + 0x580#64) ↦₆₄ cap) ∗ ((s.sp + 0x588#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x590#64) ↦₆₄ len) ∗ ((s.sp + 0x598#64) ↦₆₄ w3) ∗
          ((s.sp + 0x5a0#64) ↦₆₄ v5a0) ∗ memRegion (s.sp + 0x5a8#64) 328 ∗
          memRegion (s.sp + 0x848#64) 0x338 ∗ F)) ?_ ?_
  · by_vm_steps (
      wp_conv_pre => rw [memRegion_0x598_split s.sp]
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v5a0
      apply SepWP.exists_elim; intro _
      wp_steps
      apply SepWP.fold (devWord_of_pointsTo8_memRegion7_1432 s.sp dev) (by sep_focus)
      wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_elim; intro w3
      apply SepWP.pure_elim; intro hdev
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨?_, w3, v5a0, hdev, ?_⟩
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm, hx26, hx28, hal_norm, true_and]
        sep_ac_rfl)
  · rintro sa Pa hpca hruna ⟨hvm1, w3, v5a0, hdev, hspa, _hala, htra,
      hx19a, hx29a, hvregsa, hx26a, hx28a, hx27a, hx21a, hx23a, rfl⟩
    simp only [wp_norm, arm64_norm] at hspa hx19a hx29a hx26a hx28a hx27a hx21a hx23a
    wp_step
    apply sepWP_shift_vmPreserved (hvm1.trans (by simp only [wp_norm, arm64_norm]))
    by_vm_steps (
      wp_conv_pre => rw [memRegion_0x848_split_0x9d0 s.sp]
      wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
      repeat (apply SepWP.exists_elim; intro _)
      wp_steps
      apply SepWP.fold (memRegion_0x580_368_fold s.sp cap ptr len w3 _) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨?_, w3, hdev, ?_⟩
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm, hspa, htra, hx19a, hx29a, hvregsa,
          hx26a, hx28a, hx27a, hx21a, hx23a, hal_norm, true_and]
        sep_ac_rfl)

set_option maxHeartbeats 1200000 in
theorem segLoad_dispatch_none_budget [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st3 : M.σ) (R : SepProp) (s0 s : State)
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hbud3 : SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
      st_init st3 (LoadRemEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 Scope x))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hmeta : encMidMetaPlaced x s0 s)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.ok none))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok none))
    (hx24 : s.readReg64 .x24 = w0)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc (.ok none) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st3 s ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s
      (fun s' => ∃ st' r g sess,
        CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩
  have hbud_clone : SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
      st_init st3 (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs) :=
    hbud3.narrow fun _ h => Or.inr (Or.inl h)
  have hm_drop : s.mem ⊨
      LoadOutResPlaced Scope A.repAlloc (.ok none) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
        (vecGhostAt A.repAlloc x.rem.name x.remA ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          A.pool lim st3 s ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          stackAt (s0.sp - 0xbe0#64) extHookStack ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50))) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    refine Satisfies.mono ?_ hm
    rw [protocolAddressAt, memRegion_0x580_split_24 (s0.sp - 0xbe0#64),
        stack_encSub_extHook (s0.sp - 0xbe0#64),
        dispatchFramePlaced_eq_108_848_sep kit st0 ikit ist0 ctl x s0 v50]
    exact Entails.of_eq (by sep_ac_rfl)
  clear hm
  rw [loadOutResPlaced_none_eq] at hm_drop
  obtain ⟨rfl, hm_drop'⟩ := satisfies_pure_left hm_drop
  clear hm_drop
  let F_pre : SepProp :=
    vecGhostAt A.repAlloc x.rem.name x.remA ∗
      ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      memRegion (x.remA + 0x19#64) 7 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
      A.pool lim st3 s ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
      stackAt (s0.sp - 0xbe0#64) extHookStack ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50)
  have hm_pre : s.mem ⊨ (((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗ emp) ∗ (F_pre ∗ R) := by
    dsimp only [F_pre]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_drop'
  refine SegExitBudget.of_sepWP (R0 := R) hm_pre
    (segLoad_dispatch_none_pre_budget_wp_vm (remA := x.remA) (F := emp)
      hpc hrun hsp hal hx24 hps) ?_
  rintro sm P_m _ hsteps_pre hpcm hrunm hmm
    ⟨hvm_pre, hspm, halm, htrm, hx0m, hx8m, hx22m, hx30m, hx19m, hx29m, hvregsm, hx26m, hx28m, rfl⟩
  have hcrlm : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem := hcrl.of_keepsFrozen hsteps_pre.keepsFrozen
  have hprefm : s0.trace <+: sm.trace := by
    rw [htrm, htr]
    exact ⟨kit.loadEvs encRecord x.rem.val (.ok none), rfl⟩
  let F_clone : SepProp :=
    ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
      ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      memRegion (x.remA + 0x19#64) 7 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50)
  have hm_clone : sm.mem ⊨
      (stringCloneBudgetSpec M A lim).pre (x.remA, s0.sp - 0xbe0#64 + 0x580#64, x.rem.name, st3) sm ∗
      (F_clone ∗ R) := by
    dsimp only [stringCloneBudgetSpec, F_clone, F_pre] at hmm ⊢
    rw [← A.pool_transport lim st3 s sm hvm_pre] at hmm
    rw [hspm, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0m, hx8m, hbud_clone.1.seq_left⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmm⟩
  refine call_rocl_alloc_placed (R0 := R) (stringClone_budget_ok env.toEncEnvBudget)
    (x.remA, s0.sp - 0xbe0#64 + 0x580#64, x.rem.name, st3)
    hpcm hrunm halm hx30m hprefm hcrlm hm_clone ?_
  intro sf1 hsteps_clone hpc1 hrun1 hsp1 hal1 hcs1 hcrl1 hm1
  dsimp only [stringCloneBudgetSpec] at hm1
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm1
  obtain ⟨evs_clone, ⟨htr1, hevs_clone⟩, hm1⟩ := hm1
  have hbud4 := hbud_clone.advance hevs_clone
  set st4 := M.stepEvents evs_clone st3
  have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
  have hx22_1 : sf1.readReg64 .x22 = x.remA := by rw [cs_x22 hcs1, hx22m]
  have hx26_1 : sf1.readReg64 .x26 = s0.sp - 0xbe0#64 + 0x9d0#64 := by rw [cs_x26 hcs1, hx26m, hx26]
  have hx28_1 : sf1.readReg64 .x28 = s0.sp - 0xbe0#64 + 0x4a0#64 := by rw [cs_x28 hcs1, hx28m, hx28]
  have hm1_vec : sf1.mem ⊨
      vecU8 A.repAlloc (s0.sp - 0xbe0#64 + 0x580#64) x.rem.name.bytes ∗
      ((vecGhostAt A.repAlloc x.rem.name x.remA ∗
        A.pool lim st4 sf1 ∗ stackAt sm.sp extHookStack ∗ F_clone) ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
  rw [vecU8_eq_words3_sep_buf] at hm1_vec
  simp only [sepExists_sepConj_left, satisfies_sepExists, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc] at hm1_vec
  obtain ⟨cap, ptr, hm1_vec⟩ := hm1_vec
  let F_post : SepProp :=
    vecGhostAt A.repAlloc x.rem.name x.remA ∗
      memRegion (x.remA + 0x19#64) 7 ∗
      vecU8Buf A.repAlloc cap ptr x.rem.name.bytes ∗
      A.pool lim st4 sf1 ∗
      stackAt (s0.sp - 0xbe0#64) encSubStack ∗
      ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50)
  have hm_post : sf1.mem ⊨
      (((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
        ((s0.sp - 0xbe0#64 + 0x580#64) ↦₆₄ cap) ∗
        ((s0.sp - 0xbe0#64 + 0x588#64) ↦₆₄ ptr) ∗
        ((s0.sp - 0xbe0#64 + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗ F_post) ∗ R := by
    dsimp only [F_post, F_clone] at hm1_vec ⊢
    rw [hspm] at hm1_vec
    refine Satisfies.mono ?_ hm1_vec
    rw [← stack_encSub_extHook_back (s0.sp - 0xbe0#64)]
    exact Entails.of_eq (by sep_ac_rfl)
  refine segExit_budget_of_sepWP_frozen hcrl1 hm_post
    (segLoad_dispatch_none_post_budget_wp_vm hpc1 hrun1 hsp1' hal1 hx22_1 hx26_1 hx28_1) ?_
  intro sf P_f hpcf hrunf hpostf hcrlf hm_f
  rcases hpostf with ⟨hvm_post, w3', hdev, hspf, half, htrf, hx19f, hx29f, hvregsf,
    hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
  have hm_rod := rodata_message_encrypt_placed_intro hcrlf.2 hm_f
  let msgPtr := lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.122"
  refine segExit_budget_of_false (env.tailWriteErr x st_init st4 R s0 sf
    (answersOfLoad (.ok none))
    (.sessionNotFound x.rem.val "message_encrypt")
    cap ptr (BitVec.ofNat 64 x.rem.val.name.length) w3' msgPtr 15#64
    (vecU8Buf A.repAlloc cap ptr x.rem.val.name ∗ (msgPtr ↦ᵣ utf8 "message_encrypt"))
    (tailModel_load_none hl (by rw [htrf, htr1, htrm, htr]))
    (speStaged_sessionNotFound_devWord_placed A.repAlloc x.ret cap ptr w3' msgPtr x.rem.val hdev)
    ⟨hbud4, hpcf,
      ⟨hrunf, hspf, hal0, half,
        by rw [hx29f, cs_x29 hcs1, hx29m, hx29],
        by rw [hx19f, cs_x19 hcs1, hx19m, hx19], hcrlf,
        by rw [hvregsf, cs_vregs hcs1, hvregsm, hvregs]⟩,
      ⟨hx26f, hx28f, hx27f, hx21f, hx23f⟩,
      enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
  dsimp only [EncTailVPlaced, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailVPlaced]
  rw [segLoad_encTail_mem_retag_eq (A' := A.atState lim st4 sf) kit st0 ikit ist0 C ctl S x
    (answersOfLoad (.ok none)) _ R s0]
  rw [draws_answersOfLoad_none]
  change sf.mem ⊨ _ ∗ _ ∗ _ ∗ _ ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)
  dsimp only [F_post] at hm_rod
  rw [← A.pool_transport lim st4 sf1 sf hvm_post] at hm_rod
  refine Satisfies.mono ?_ hm_rod
  have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
    w3' msgPtr 15#64 w4 w5 w6 tail htail
  have hperm_end :
      (msgPtr ↦ᵣ utf8 "message_encrypt") ∗
      ((((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
        ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
        ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ msgPtr) ∗
        ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
        (vecGhostAt A.repAlloc x.rem.name x.remA ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          vecU8Buf A.repAlloc cap ptr x.rem.name.bytes ∗
          A.pool lim st4 sf ∗
          stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50))) ∗ R) =
      (memRegion (s0.sp - 0xbe0#64) 0x50 ∗ ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50)) ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
        ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8)) ∗
      ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188) ∗
      (((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
        ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ msgPtr) ∗
        ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64)) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198) ∗
      (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
      ((vecU8Buf A.repAlloc cap ptr x.rem.val.name ∗ (msgPtr ↦ᵣ utf8 "message_encrypt")) ∗
        memRegion x.ret 248 ∗
        encCommonPlaced (A.atState lim st4 sf) ctl x 0 s0 ∗
        (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)) := by
    dsimp only [dispatchFrameNo108848Placed, encCommonPlaced, protocolAddressAt, AddrGhost.val]
    change _ = _ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗
      ((x.ptA ↦ₛ x.ptext) ∗
        (vecGhostAt A.repAlloc x.rem.name x.remA ∗ ((x.remA + 24#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 25#64) 7) ∗
        (vecGhostAt A.repAlloc x.loc.name x.locA ∗ ((x.locA + 24#64) ↦₈ x.loc.device) ∗
          memRegion (x.locA + 25#64) 7) ∗
        nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
        stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st4 sf) ∗ _)))))
    sep_ac_rfl
  rw [hperm_end]
  refine Entails.trans (sepConj_mono (fold_sp58 _ _)
    (sepConj_mono (memRegion_0x110_0x35a_fold _ _ _)
      (sepConj_mono hpoll
        (sepConj_mono_left (encSpillsAt_fold _ _ _ _))))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchPlacedBudget
