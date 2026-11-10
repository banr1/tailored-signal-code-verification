/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs

/-!
# `MessageDecrypt` Active-Session Region Segment (`SegRegionSome`)

Instantiates `recordDecryptSpec` restricted to a PQ-state predicate `Q` (`ScopePq`) at
`recGhostOf x prevPtr G ses.state`, lifting the region exit to `PostSomeState` and region panics to
`withStoresDecSpec.onPanic`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

theorem serializeAddrVals_eq_serializeAddresses (parse : ServiceIdParser) (s r : AddrGhost) :
    serializeAddrVals parse s.val r.val = serializeAddresses parse s r :=
  rfl

theorem api_run_storeCall_ok {Addr PQ E α β : Type} (c : StoreCall Addr PQ) (a : α)
    (k : α → Api Addr PQ E β) :
    Api.run (storeCall c (.ok a) >>= k) = (ExceptT.run (k a)).run [c] :=
  rfl

theorem exceptT_run_liftProtocol_error {Addr PQ E α β : Type} (e : SignalProtocolError)
    (k : α → Api Addr PQ E β) (s : List (StoreCall Addr PQ)) :
    (ExceptT.run (liftProtocol (.error e) >>= k)).run s = (.error (ApiError.ofProtocol e), s) :=
  rfl

theorem model_panic_of_region_panic (C : Crypto) (S : SpqrModel)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (G : SessionGhost) (prevPtr : BitVec 64)
    (hload : ans.loadSession = .ok (some rec))
    (hcur : rec.currentSession = some ses)
    (hpan : ((recGhostOf x prevPtr G ses.state).model C S uuidTryParse).1 = .error .panic) :
    (x.model C S uuidTryParse ans).1 = .error .panic := by
  unfold DecryptGhost.model messageDecryptSignal
  rw [hload, api_run_storeCall_ok]
  dsimp only [SessionRecord.tryDecryptFromRecord]
  rw [hcur, serializeAddrVals_eq_serializeAddresses]
  unfold RecordDecryptGhost.model recGhostOf at hpan
  dsimp only at hpan
  generalize hres :
    SessionState.tryDecryptFromRecord C S.spqr
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc) x.msg .whisper
      (coinsOf x.rest) ses.state = res at hpan ⊢
  rcases res with ⟨r1, r2⟩
  dsimp only at hpan
  subst hpan
  dsimp only
  rw [hres]
  dsimp only
  rw [exceptT_run_liftProtocol_error]
  rfl

theorem recvPanics_of_region_recvPanics (S : SpqrModel) (x : DecryptGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (G : SessionGhost) (prevPtr : BitVec 64)
    (hload : ans.loadSession = .ok (some rec))
    (hcur : rec.currentSession = some ses)
    (hpan : (recGhostOf x prevPtr G ses.state).st.version.toNat =
        (recGhostOf x prevPtr G ses.state).msg.messageVersion.toNat ∧
      S.recvPanics (recGhostOf x prevPtr G ses.state).st.pqRatchetState
        (recGhostOf x prevPtr G ses.state).msg.pqRatchet) :
    x.recvPanics S ans := by
  unfold DecryptGhost.recvPanics loadedSession
  rw [hload]
  dsimp only
  rw [hcur]
  exact hpan

theorem allocFailedIn_of_load_prefix {s0 s sf : State} {evs : List TraceEvent}
    (htr : s.trace = s0.trace ++ evs) (hpref : s.trace <+: sf.trace)
    (halloc : allocFailedIn s sf) :
    allocFailedIn s0 sf := by
  rcases hpref with ⟨tail, hsf⟩
  unfold allocFailedIn at halloc ⊢
  rw [← hsf, List.drop_left] at halloc
  rw [← hsf, htr, List.append_assoc, List.drop_left]
  exact List.mem_append_right _ halloc

theorem post_meta_extract {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image} {x_rg : RecordDecryptGhost} {s sf : State} {F : SepProp}
    (hm : sf.mem ⊨ (recordDecryptSpec C A ctl uuidTryParse S img).post x_rg s sf ∗ F) :
    sf.sp = s.sp ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x27 = x_rg.sret := by
  dsimp only [recordDecryptSpec, Spec.inImage] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨_, _, hsp, hx29, hx27, _, _⟩, _⟩
  exact ⟨hsp, hx29, hx27⟩

theorem segRegionSomeV_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegRegionSomeSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope := by
  intro _hHyps Q hreg hQ x ans R s0 s hRS hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, _hx27, hfrozen, hsym, hvregs⟩,
    rec, ses, G, prevCap, prevPtr, hload, hscope, hcur, hw0, htrace, hmem⟩ := hRS
  let x_rg := recGhostOf x prevPtr G ses.state
  let R_rg := wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
    decStoreExtra kit ikit st0 ist0 s0 ∗ R
  have hmem_rg : s.mem ⊨ (recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.pre x_rg s ∗ R_rg := by
    dsimp only [x_rg, R_rg, Spec.withVRegs]
    simpa only [sepConj_assoc] using hmem
  have hmemQ : s.mem ⊨
      ((recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)).pre
        x_rg s ∗ R_rg :=
    Spec.satisfies_restrictPre.mpr ⟨hQ x.rem.val rec ses hscope hcur, hmem_rg⟩
  obtain ⟨sf, hsteps, hout⟩ := hreg x_rg R_rg s hpc hrun hmemQ hL
  try dsimp only [Spec.restrictPre] at hout
  rcases hout with ⟨hpc_sf, hrun_sf, hmf⟩ | ⟨hpan_sf, hmf⟩
  · refine ⟨sf, hsteps, Or.inl ?_⟩
    dsimp only [Spec.withVRegs] at hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf
    obtain ⟨hvregs_sf, hmf⟩ := hmf
    obtain ⟨hsp_sf, hx29_sf, hx27_sf⟩ := post_meta_extract hmf
    have hfrozen_sf : img.FrozenLoaded sf := hfrozen.of_keepsFrozen hsteps.keepsFrozen
    have hsym_sf : sf.symtab = img.symtab := hsteps.symtab_eq.trans hsym
    have hal_sf : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      exact hal
    have hmeta_sf : wsMeta img x s0 sf :=
      ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf.trans hx29,
        hx27_sf, hfrozen_sf, hsym_sf, hvregs_sf.trans hvregs⟩
    refine ⟨hpc_sf, hmeta_sf, s, rec, ses, G, prevCap, prevPtr, hsp, htrace,
      hload, hscope, hcur, hw0, ?_⟩
    dsimp only [x_rg, R_rg] at hmf
    simpa only [sepConj_assoc] using hmf
  · refine ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan_sf, ?_⟩))⟩
    dsimp only [Spec.withVRegs, recordDecryptSpec, withStoresDecSpecV, Spec.inImage, R_rg] at hmf ⊢
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
    have h_any : anyHeap ∗ (wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗
        decStoreExtra kit ikit st0 ist0 s0) ⊢ anyHeap :=
      entails_anyHeap _
    rw [← sepConj_assoc, ← sepConj_assoc] at hmf
    rw [sepConj_assoc anyHeap] at hmf
    exact Satisfies.mono (sepConj_mono_left h_any) hmf

theorem segRegionSome_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegRegionSomeSpec img C A ctl uuidTryParse S encRecord abs :=
  segRegionSomeV_ok

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

theorem post_meta_extract_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {x_rg : RecordDecryptGhost} {s sf : State} {F : SepProp}
    (hm : sf.mem ⊨ (Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).post x_rg s sf ∗ F) :
    sf.sp = s.sp ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧ sf.readReg64 .x27 = x_rg.sret := by
  dsimp only [Record.recordDecryptPlacedSpec] at hm
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
  have hmem_rg : s.mem ⊨ (Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.pre x_rg s ∗ R_rg := by
    dsimp only [x_rg, R_rg, Spec.withVRegs]
    simpa only [sepConj_assoc] using hmem
  have hmemQ : s.mem ⊨
      ((Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre (Q ·.st.pqRatchetState)).pre
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
    dsimp only [Spec.withVRegs, Record.recordDecryptPlacedSpec, withStoresDecPlacedSpecV,
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

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome
