/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegUntrustedPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchAuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegUntrustedPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync LibsignalBinary.Proofs.Placed.BudgetVmSteps
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (wsMetaPlaced_of_steps)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted hiding segUntrusted_placed_wp wsUntrustedFixedEnvPlaced wsUntrustedFixedRestPlaced wsFixed_wsEnv_untrusted_split_placed wsUntrustedPrePlaced wsUntrustedCommonRestPlaced wsUntrustedFramePlaced trusted_entails_untrustedPre_placed wsUntrustedPostSpatialPlaced untrustedPost_entails_placed segUntrustedVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted (
  wsUntrustedPrePlaced wsUntrustedFramePlaced wsUntrustedPostSpatialPlaced
  trusted_entails_untrustedPre_placed untrustedPost_entails_placed)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] protocolAddressAt vecGhostAt

attribute [local semireducible] protocolAddressAt vecGhostAt in
set_option maxHeartbeats 1600000 in
theorem segUntrusted_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {st : M.σ}
    (hclone : subroutine_ok (lsProg_463 H) (lsmpl.base 623)
      (StoreKit.withLsCodeRoLoaded lsmpl (stringCloneBudgetSpec M A lim)))
    {s : State} {R : SepProp}
    {addrA e0 e1 e3 devWord : BitVec 64} {e2 : BitVec 32} {d0 : BitVec 8} {pad : List (BitVec 8)}
    {addr : AddrGhost}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfits : FitsEnv M lim st (StringCloneEnv addr.name))
    (hw4 : addr.device :: pad = unpack64 devWord)
    (hpc : s.pc = untrustedPCPlaced)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (lsProg_463 H) (errJoinPCPlaced true) s
      (FromRecordCallees.lsLogOff ∗
        ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
        vecGhostAt A.repAlloc addr.name addrA ∗
        ((addrA + 0x18#64) ↦₈ addr.device) ∗
        memRegion (s.sp + 0x5f0#64) 24 ∗
        ((s.sp + 0x608#64) ↦₈ d0) ∗ ((s.sp + 0x609#64) ↦ₛ pad) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₃₂ e2) ∗ ((s.sp + 0x594#64) ↦₆₄ e3) ∗
        A.pool lim st s ∗ stackAt s.sp extHookStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ evs : List AllocEvent, ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
          ⌜sf.readReg64 .x28 = 0x800000000000000c#64 ∧
            sf.readReg64 .x20 = ((cap.extractLsb' 0 32) >>> 8#32).zeroExtend 64 ∧
            sf.readReg64 .x21 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
            sf.trace = s.trace ∧
            StringCloneEnv addr.name evs⌝ ∗
          FromRecordCallees.lsLogOff ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
          vecGhostAt A.repAlloc addr.name addrA ∗
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
          CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A.repAlloc cap ptr addr.name.bytes ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s.sp extHookStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold untrustedPCPlaced at hpc
  unfold errJoinPCPlaced FromRecordCallees.lsLogOff lsLogFilterAddr
  dsimp only [lsProg_463, ite_true] at hclone ⊢
  apply StoreKit.sepWP_seq_lscro hcrl (mid := lsmpl.base 623)
  wp_steps
  refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_call, hro_call⟩ => ?_
  refine SepWP.transport_budgetPool (s1 := s) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
  wp_call hclone (addrA, s.sp + 1520#64, addr.name, st)
  apply SepWP.fold (vecU8_unpack_5f0 A.repAlloc s.sp addr.name.bytes) (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro (cap : BitVec 64)
  apply SepWP.exists_elim; intro (ptr : BitVec 64)
  by_vm_open (
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
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm2 hm_final
    let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2
    have hpool2 := A.pool_transport lim (M.stepEvents w st) sf s_end hvm2
    rw [← hpool2] at hm_final
    have hcap_ubfx :
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.extractLsb' 0 32 cap) >>> 8)) =
          BitVec.setWidth 64 (BitVec.extractLsb' 0 32 cap) >>> 8 := by bv_omega
    refine ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right w
      (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_))
    refine Entails.pure_right (by simp_all) (Entails.of_eq (by sep_ac_rfl)))

attribute [local semireducible] protocolAddressAt vecGhostAt in
private theorem rep_decStoreExtra_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    decStoreExtraPlaced (retagSessionStore (A' := { pool := P, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P, live := A.live }) ikit) st ist s0 =
    decStoreExtraPlaced kit ikit st ist s0 := rfl

attribute [local semireducible] protocolAddressAt vecGhostAt in
private theorem rep_vecGhostAt_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp) (v : VecGhost) (a : BitVec 64) :
    vecGhostAt ({ pool := P, live := A.live } : RustAlloc) v a =
    vecGhostAt A.repAlloc v a := rfl

attribute [local semireducible] protocolAddressAt vecGhostAt in
private theorem rep_vecU8Buf_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf
      ({ pool := P, live := A.live } : RustAlloc) cap ptr bs =
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf
      A.repAlloc cap ptr bs := rfl

attribute [local semireducible] protocolAddressAt vecGhostAt in
private theorem rep_wsUntrustedFrame_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (P1 P2 : SepProp) (ctl : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (k : IdentityKey) (e4 : BitVec 64) :
    wsUntrustedFramePlaced C ({ pool := P1, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P1, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P1, live := A.live }) ikit)
      x ans s0 sp rec' pt k e4 =
    wsUntrustedFramePlaced C ({ pool := P2, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P2, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P2, live := A.live }) ikit)
      x ans s0 sp rec' pt k e4 := rfl

attribute [local semireducible] SepWP protocolAddressAt vecGhostAt in
theorem segUntrustedVPlaced_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegUntrustedSpecVBudget C A lim ctl uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope := by
  intro hyps x st_init ans R s0 s hstB hL
  rcases hstB with ⟨st, hsb_all, hst⟩
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hsb : SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse Scope x) st_init st
      (FromTrustedFalseEnv x) :=
    hsb_all rec rec' pt ses k hload hdec hcur hrem
  have hfits : FitsEnv M lim st (StringCloneEnv x.rem.name) := hsb.1.seq_left
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, _hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  let A0 := A.atState lim st s
  let kit0 := retagSessionStore (A' := A0) kit
  let ikit0 := retagIdentityStore (A' := A0) ikit
  rw [← hsp] at hx26 hx19 hx22 hm
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  let R' : SepProp := decStoreExtraPlaced kit ikit st0 ist1 s0 ∗ R
  have hm_pre : s.mem ⊨
      (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
          ⌜pad.length = 7⌝ ∗
          wsUntrustedPrePlaced A0 x s.sp e0 e1 e3 e2 d0 pad ∗
          wsUntrustedFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp rec' pt k e4) ∗ R' := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_untrustedPre_placed C A0 ctl kit0 ikit0 x ans s0 s.sp rec' pt k)) ?_
    dsimp only [A0, kit0, ikit0, R', ist1, RustCliAllocBudget.atState] at hm ⊢
    simpa only [rep_decStoreExtra_eq, sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨e0, e1, e2, e3, e4, d0, pad, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hpad, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨devWord, hw4⟩ := exists_unpack64_of_length_8 (bs := x.rem.device :: pad) (by simp [hpad])
  obtain ⟨sf, hsteps, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ :=
    segUntrusted_placed_wp (SegDispatchAuxPlacedBudget.stringClone_placed_rocl_ok hyps.hooks)
      (R := wsUntrustedFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp rec' pt k e4 ∗ R')
      _hcrl hfits hw4 hpc hrun hsp_align
      (wsUntrustedFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp rec' pt k e4 ∗ R') hm_pre hL
  rotate_left
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨hm1', hsp1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
  rcases hm1' with ⟨evs_cl, cap, ptr, hm1'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm1'
  rcases hm1' with ⟨⟨hx28_1, hx20_1, hx21_1, htr1, hevs_cl⟩, hm1'⟩
  have hsb1 := hsb.advance hevs_cl
  let st1 := M.stepEvents evs_cl st
  let A1 := A.atState lim st1 sf
  let kit1 := retagSessionStore (A' := A1) kit
  let ikit1 := retagIdentityStore (A' := A1) ikit
  rw [← sepConj_assoc] at hm1'
  have hmeta1 := wsMetaPlaced_of_steps hmeta hsteps hrun1 hsp1 hx29_1 hx27_1 hvregs_1
  have hw1 : resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = cap.extractLsb' 0 32 := by
    rw [hx20_1, hx21_1, resWord1_lsr8]
  have hm1_a1 : sf.mem ⊨
      (wsUntrustedPostSpatialPlaced A1 x s.sp cap ptr devWord ∗
        wsUntrustedFramePlaced C A1 ctl kit1 ikit1 x ans s0 s.sp rec' pt k e4) ∗ R' := by
    unfold wsUntrustedPostSpatialPlaced
    dsimp only [A0, A1, kit0, ikit0, kit1, ikit1, RustCliAllocBudget.atState] at hm1' ⊢
    rw [rep_wsUntrustedFrame_eq (P1 := A.pool lim st s) (P2 := A.pool lim st1 sf)] at hm1'
    simpa only [rep_vecGhostAt_eq, rep_vecU8Buf_eq, sepConj_assoc] using hm1'
  have hm1_post := Satisfies.mono (sepConj_mono_left
    (untrustedPost_entails_placed C A1 ctl kit1 ikit1 x ans s0 s.sp rec' ses hcur pt k
      (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21)
      cap ptr devWord e4 pad hpad hw4 hx28_1 hw1)) hm1_a1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1_post
  rcases hm1_post with ⟨G, hm1_post⟩
  refine ⟨sf, hsteps, Or.inl ⟨st1, hsb1, ?_⟩⟩
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
  · have hstf : kit1.storeFinal st0 ans (x.model C S uuidTryParse ans).2 = st0 := by
      rw [hmod.2]; rfl
    have histf : ikit1.idFinal ist0 ans (x.model C S uuidTryParse ans).2 = ist1 := by
      rw [hmod.2]; rfl
    rw [hmod.1, hstf, histf]
    dsimp only [A1, kit1, ikit1, R', ist1, RustCliAllocBudget.atState] at hm1_post ⊢
    simpa only [rep_decStoreExtra_eq, ite_true, hsp, sepConj_assoc] using hm1_post

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegUntrustedPlacedBudget
