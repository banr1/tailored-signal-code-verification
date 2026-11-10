/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegRegionSome
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome hiding post_meta_extract_placed segRegionSomeVPlaced_ok

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem post_meta_extract_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {x_rg : RecordDecryptGhost} {s sf : State} {F : SepProp}
    (hm : sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).post x_rg s sf ∗ F) :
    sf.sp = s.sp ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x27 = x_rg.sret := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨_, _, hsp, hx29, hx27, _, _⟩, _⟩
  exact ⟨hsp, hx29, hx27⟩

theorem segRegionSomeVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegRegionSomeSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro _hHyps Q hreg hQ x ans R s0 s hRS hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hcrl, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg := wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
    decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R
  have hmem_rg : s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.pre x_rg s ∗ R_rg := by
    dsimp only [x_rg, R_rg, Spec.withVRegs]
    simpa only [sepConj_assoc] using hmem
  have hmemQ : s.mem ⊨
      ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre (Q ·.st.pqRatchetState)).pre
        x_rg s ∗ R_rg :=
    Spec.satisfies_restrictPre.mpr ⟨hQ x.rem.val rec ses hscope hcur, hmem_rg⟩
  obtain ⟨sf, hsteps, hout⟩ := hreg x_rg R_rg s hpc hrun hmemQ hL
  try dsimp only [Spec.restrictPre] at hout
  rcases hout with ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.withVRegs] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ := post_meta_extract_placed hmf
    have hcrl_sf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    have hal_sf : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      exact hal
    have hmeta_sf : wsMetaPlaced x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29,
        hx27_sf, hcrl_sf, hvregs_sf.trans hvregs⟩
    refine ⟨hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr, hsp, htrace,
      hload, hscope, hcur, hw0, ?_⟩
    dsimp only [x_rg, R_rg] at hmf
    simpa only [sepConj_assoc] using hmf
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.withVRegs, CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec, withStoresDecPlacedSpecV,
      StoreKit.withLsCodeRoLoaded, R_rg] at hmf ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    rcases hmf with ⟨⟨hdisj, hpref⟩, hmf⟩
    have hload_pref : s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: sf.trace := by
      rwa [← htrace]
    have hs0_pref : s0.trace <+: sf.trace :=
      (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
    have hpan_pure :
        s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidTryParse answers).1 = .error .panic ∨ x.recvPanics S answers)) := by
      refine ⟨hs0_pref, ?_⟩
      rcases hdisj with hmod_pan | hrecv_pan | halloc
      · exact Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl
          (model_panic_of_region_panic C S x ans rec ses G prevPtr hload hcur hmod_pan)⟩
      · exact Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inr
          (recvPanics_of_region_recvPanics S x ans rec ses G prevPtr hload hcur hrecv_pan)⟩
      · exact Or.inl (allocFailedIn_of_load_prefix htrace hpref halloc)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpan_pure, ?_⟩
    have h_any : anyHeap ∗ (wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗
        decStoreExtraPlaced kit ikit st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome
