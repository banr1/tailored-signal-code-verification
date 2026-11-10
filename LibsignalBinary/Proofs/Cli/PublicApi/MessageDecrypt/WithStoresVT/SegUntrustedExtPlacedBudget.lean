/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegUntrustedPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtPlaced
public import LibsignalBinary.Proofs.Common.StringClonePlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `SegUntrusted` (`+0x21b0 → +0x2294`)

Proves budget-threaded (`RustCliAllocBudget M`) relocatable `segUntrustedVX_placed_ok` on
`lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord StoreAnswers)
open CryptoVerification.LibsignalSessionRepr (vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (resWord1)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (resWord1_lsr8)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (decStoreExtraPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (wsMetaPlaced_of_steps)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted
  (trusted_entails_untrustedPre_placed untrustedPost_entails_placed
   wsUntrustedFramePlaced wsUntrustedPostSpatialPlaced wsUntrustedPrePlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget TryDecryptEnvArgs)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromTrustedEnv FromTrustedFalseEnv WithStoresDecEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (ErrJoinStateVPlaced TrustedStateVPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (DecSegVXPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegUntrustedPlacedBudget
  (segUntrusted_placed_wp)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
  (DecHypsExtPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtBudget
  (model_of_trust_false_noScope rep_callsRel_eq rep_decStoreExtra_eq rep_idCallsRel_eq
   rep_idFinal_eq rep_storeFinal_eq rep_traceOfWith_eq rep_vecGhostAt_eq rep_vecU8Buf_eq
   rep_wsUntrustedFrame_eq)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] protocolAddressAt vecGhostAt

set_option maxHeartbeats 800000 in
attribute [local semireducible] SepWP protocolAddressAt vecGhostAt in
/-- Budget-threaded relocatable `segUntrustedVX_placed_ok` on `lsProg_463 H`. -/
theorem segUntrustedVX_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State)
    (hstB : TrustedStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans false R s0 s) :
    DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H
      kit kitEnv ikit ikitEnv st0 ist0 Scope Extra x st_init R s0 s
      (ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0) := by
  intro hL
  rcases hstB with ⟨st, hsb_all, hst⟩
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hsb : SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x)
      st_init st (FromTrustedFalseEnv x) := by
    simpa only [FromTrustedEnv, Bool.false_eq_true, ↓reduceIte] using
      hsb_all rec rec' pt ses k hload hdec hcur hrem
  have hfits : FitsEnv M lim st (StringCloneEnv x.rem.name) := by
    dsimp only [FromTrustedFalseEnv] at hsb
    exact hsb.1.seq_left
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hcrl, _hvregs⟩
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
  have hclone_rocl : subroutine_ok (CryptoVerification.CliRatchet.DecPlaced.lsProg_463 H)
      (CryptoVerification.lsmpl.base 623)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded CryptoVerification.lsmpl
        (LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins.stringCloneBudgetSpec
          M A lim)) :=
    CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl
      (CryptoVerification.LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_plain
        (callerProg := CryptoVerification.CliRatchet.DecPlaced.lsProg_463 H) (i := 463)
        (LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchAuxPlacedBudget.stringCloneSeg_blk623_ok
          hyps.hooks.shim hyps.hooks.alloc hyps.hooks.memcpy))
  obtain ⟨sf, hsteps, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ :=
    segUntrusted_placed_wp hclone_rocl
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
  have hsb1 : SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x)
      st_init (M.stepEvents evs_cl st) FreeOnlyEvs := by
    dsimp only [FromTrustedFalseEnv] at hsb
    exact hsb.step (fun _ _ => SeqEnv.append) hevs_cl
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
  have hmod := model_of_trust_false_noScope C S x ans rec rec' pt ses k
    hload hdec hcur hrem htrust
  refine ⟨hpc1, hmeta1, ?_, ?_, ans, some (G, ses.state), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx26_1, hx26, hsp]
  · rw [hx28_1]; decide
  · rw [hmod.1]; exact nofun
  · intro p; rw [hmod.1]; exact nofun
  · intro r hr; rw [hload] at hr; cases hr; exact hscope
  · rw [rep_callsRel_eq, hmod.2]
    exact ⟨hload ▸ hscope.2, trivial⟩
  · rw [rep_idCallsRel_eq, hmod.2]
    exact ⟨htrustRel, trivial⟩
  · dsimp only [kit0, ikit0, retagSessionStore, retagIdentityStore] at htr ⊢
    rw [rep_traceOfWith_eq, htr1, htr, hmod.2]; simp
  · have hstf : kit1.storeFinal st0 ans (x.model C S uuidTryParse ans).2 = st0 := by
      dsimp only [A1, kit1, RustCliAllocBudget.atState]
      rw [rep_storeFinal_eq, hmod.2]
      rfl
    have histf : ikit1.idFinal ist0 ans (x.model C S uuidTryParse ans).2 = ist1 := by
      dsimp only [A1, ikit1, RustCliAllocBudget.atState]
      rw [rep_idFinal_eq, hmod.2]
      rfl
    rw [hmod.1, hstf, histf]
    dsimp only [A1, kit1, ikit1, R', ist1, RustCliAllocBudget.atState] at hm1_post ⊢
    simpa only [rep_decStoreExtra_eq, ite_true, hsp, sepConj_assoc] using hm1_post

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExtPlacedBudget
