/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptRecordStorePeak
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PqValid
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow

/-!
# End-to-End `WithStoresDecEnv` and CLI W2 `message_decrypt` Slot Peak Bounds

Composes the `Scope`-guarded `WithStoresDecEnv`, post-`decryptRecord` session and SPQR growth bounds
(`decryptRecord_post_caps_of_scopeIn`), and CLI W2 (`StoresGhost.opened`) store-kit bridges into
`PhaseCreditSpec` and `PhaseGroupSpec` slot theorems.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak

open CryptoGames.LibsignalSession (Crypto IdentityKey SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E.Record (bytesField encSession encodeRecord msgField)
open CryptoVerification.E2E.RecordX
  (DeserializeScopeBounded bytesField_length_le' encodeRecord_length_lt_21_of_bounded
   lenField_length_ge' lenField_length_le' sessionScopeBounded_of_sessionScopeP)
open CryptoVerification.E2E.V1 (tryDecryptFromRecord_ok_props_gen)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost serializeAddrVals)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost UuidParser coinsOf serviceIdParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.Slots
  (FilesOkPeer cliSess_scopeIn_of_opened decryptRecord_recOk_of_scopeIn scopeIn scopeKit)
open CryptoVerification.SignalSession.Cli.Slots.PqValid (PqInV1 stripPq)
open CryptoVerification.SpqrV1.Top.StateSize (spqrV1_recv_validState_length_le)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSmallStorePollEnv
   sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
   sessLoadPoll_phaseCredit
   sessStorePollDeltaCum sessStorePollDeltaLive sessStorePollDeltaPeak sessStorePollMaxReq
   sessStorePoll_phaseCredit
   smallStorePollDeltaCum smallStorePollDeltaLive smallStorePollDeltaPeak smallStorePollMaxReq
   smallStorePoll_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (PeerSpqrTightValidAt ValidChainParams ValidEncoderPtsAt
   peerSpqrTightValidAt_of_cliSessionStoreSpec)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid SessionCloneDom recordDecrypt_dom_phaseCredit sessStorePoll_dom_phaseCredit
   sessionCloneDom_of_scopeKit_pq)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptRecordStorePeak
  (phaseCreditSpec_exists_guarded phaseCreditSpec_fromRegionNoneEnv
   phaseCreditSpec_loadPollStep_smallBox phaseCreditSpec_saveStep_smallBox
   phaseCreditSpec_seq_freeOnly phaseCreditSpec_storeStep_smallBox
   phaseCreditSpec_stringClone_small phaseCreditSpec_trustStep_smallBox)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromPostSomeEnv FromRegionSomeEnv FromStoreCallEnv
   FromTrustedFalseEnv FromTrustedTrueEnv SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (RecordDecryptEnv TryDecryptEnvArgs recordTryDecryptEnvArgs)

/-! ## 1. Small-Box and Small-Name `WithStoresDecEnv` Composers -/

/-- Small-box / small-name `PhaseCreditSpec` for `FromKeyReadyEnv`. -/
theorem fromKeyReady_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} (hM : ModelHyps M)
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {x : DecryptGhost} {rec' : SessionRecord (List (BitVec 8))} {k : IdentityKey}
    {nameCap c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hBoxTr : ikit.trustBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSv : ikit.saveBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSt : kit.storeBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : x.rem.name.bytes.length ≤ nameCap)
    (hNameSm : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hTrust : PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 x.rem.val k .receiving)
      c_tr l_tr p_tr r_tr)
    (hSave : PhaseCreditSpec M
      (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true)) x.rem.val k)
      c_sv l_sv p_sv r_sv)
    (hStore : PhaseCreditSpec M (kitEnv.storePollEnv st0 x.rem.val rec')
      c_st l_st p_st r_st) :
    let c_tr_step := 2 * ikit.trustBoxSize + 9539 + c_tr
    let c_sv_step := 2 * ikit.saveBoxSize + 9539 + c_sv
    let c_st_step := 2 * kit.storeBoxSize + 9539 + c_st
    let c_sc := 2 * nameCap + 9539
    PhaseCreditSpec M (FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)
      (c_tr_step + max c_sc (c_sv_step + c_st_step))
      (l_tr + (l_sv + l_st))
      (max p_tr (l_tr + max p_sv (l_sv + p_st)))
      (max (max ikit.trustBoxSize r_tr)
        (max nameCap (max (max ikit.saveBoxSize r_sv) (max kit.storeBoxSize r_st)))) := by
  intro c_tr_step c_sv_step c_st_step c_sc
  have hTrStep := phaseCreditSpec_trustStep_smallBox hM hBoxTr hTrust
  have hSvStep := phaseCreditSpec_saveStep_smallBox hM hBoxSv hSave
  have hStStep := phaseCreditSpec_storeStep_smallBox hM hBoxSt hStore
  have hStoreCall : PhaseCreditSpec M (FromStoreCallEnv kit kitEnv st0 x.rem.val rec')
      c_st_step l_st p_st (max kit.storeBoxSize r_st) :=
    phaseCreditSpec_seq_freeOnly hM hStStep (fun _ h => h)
  have hNameSm' : x.rem.name.bytes.length ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans hName hNameSm
  have hFalse : PhaseCreditSpec M (FromTrustedFalseEnv x) c_sc 0 0 nameCap :=
    (PhaseCreditSpec.seq (phaseCreditSpec_stringClone_small hM x.rem.name hNameSm')
      (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
      (by omega) (by omega) (by omega) (by omega)
  have hTrueTail := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM) hStoreCall
  have hTrue : PhaseCreditSpec M
      (FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)
      (c_sv_step + c_st_step) (l_sv + l_st) (max p_sv (l_sv + p_st))
      (max (max ikit.saveBoxSize r_sv) (max kit.storeBoxSize r_st)) :=
    (PhaseCreditSpec.seq hSvStep hTrueTail).mono
      (by omega) (by omega) (by omega) (by omega)
  have hCont := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM)
    (PhaseCreditSpec.or hFalse hTrue)
  exact (PhaseCreditSpec.seq hTrStep hCont).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem withStoresDec_finish {M : AllocCostModel} [HasFineReallocCredit M]
    {P : List AllocEvent → Prop}
    {boxLd nameCap c_ld_step l_ld p_ld r_ld c_sc c_rd l_rd p_rd r_rd c_kr l_kr p_kr r_kr : Nat}
    (h : PhaseCreditSpec M P
      (c_ld_step + (0 + max 0 (max c_sc (max 9573 (c_rd + c_kr)))))
      (l_ld + (0 + max 0 (max 0 (max 0 (l_rd + l_kr)))))
      (max p_ld (l_ld + max 0 (0 + max 0 (max 0 (max 0 (max p_rd (l_rd + p_kr)))))))
      (max (max boxLd r_ld) (max 0 (max 0 (max nameCap (max 17 (max r_rd r_kr))))))) :
    PhaseCreditSpec M P
      (c_ld_step + max (max c_sc 9573) (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max boxLd r_ld) (max (max nameCap 17) (max r_rd r_kr))) :=
  h.mono (by omega) (by omega) (by omega) (by omega)

/-- Small-box / small-name `PhaseCreditSpec` for the `Scope`-guarded `WithStoresDecEnv`. -/
theorem withStoresDec_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} (hM : ModelHyps M)
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    {nameCap c_ld l_ld p_ld r_ld c_rd l_rd p_rd r_rd c_tr l_tr p_tr r_tr
     c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hsmall17 : 17 ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxLd : kit.loadBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxTr : ikit.trustBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSv : ikit.saveBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSt : kit.storeBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : x.rem.name.bytes.length ≤ nameCap)
    (hNameSm : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hLoad : PhaseCreditSpec M (kitEnv.loadPollEnv st0 x.rem.val) c_ld l_ld p_ld r_ld)
    (hRecDec : ∀ rec ses G,
      kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      PhaseCreditSpec M (RecordDecryptEnv tdEnv (recGhostOf x 0#64 G ses.state))
        c_rd l_rd p_rd r_rd)
    (hTrust : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 x.rem.val k .receiving)
        c_tr l_tr p_tr r_tr)
    (hSave : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec M
        (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true))
          x.rem.val k)
        c_sv l_sv p_sv r_sv)
    (hStore : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec M (kitEnv.storePollEnv st0 x.rem.val rec')
        c_st l_st p_st r_st) :
    let c_ld_step := 2 * kit.loadBoxSize + 9539 + c_ld
    let c_tr_step := 2 * ikit.trustBoxSize + 9539 + c_tr
    let c_sv_step := 2 * ikit.saveBoxSize + 9539 + c_sv
    let c_st_step := 2 * kit.storeBoxSize + 9539 + c_st
    let c_sc := 2 * nameCap + 9539
    let c_kr := c_tr_step + max c_sc (c_sv_step + c_st_step)
    let l_kr := l_tr + (l_sv + l_st)
    let p_kr := max p_tr (l_tr + max p_sv (l_sv + p_st))
    let r_kr := max (max ikit.trustBoxSize r_tr)
      (max nameCap (max (max ikit.saveBoxSize r_sv) (max kit.storeBoxSize r_st)))
    PhaseCreditSpec M
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      (c_ld_step + max (max c_sc 9573) (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max kit.loadBoxSize r_ld) (max (max nameCap 17) (max r_rd r_kr))) := by
  intro c_ld_step c_tr_step c_sv_step c_st_step c_sc c_kr l_kr p_kr r_kr
  have hLdStep := phaseCreditSpec_loadPollStep_smallBox hM hBoxLd hLoad
  have hNameSm' : x.rem.name.bytes.length ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans hName hNameSm
  have hArm2 : PhaseCreditSpec M (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs)
      c_sc 0 0 nameCap :=
    (PhaseCreditSpec.seq (phaseCreditSpec_stringClone_small hM x.rem.name hNameSm')
      (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hName) 9539)
      (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.max_le.2 ⟨hName, Nat.zero_le _⟩)
  have hArm3 := phaseCreditSpec_fromRegionNoneEnv hM hsmall17
  have hArm4 : PhaseCreditSpec M
      (fun evs => ∃ rec ses G,
        kit.ScopeAt Scope st0 x.rem.val rec ∧
        rec.currentSession = some ses ∧
        SessionGhostValid G ses ∧
        FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 x rec G ses.state evs)
      (c_rd + c_kr) (l_rd + l_kr) (max p_rd (l_rd + p_kr)) (max r_rd r_kr) := by
    have hEx : PhaseCreditSpec M
        (fun evs =>
          ∃ p : SessionRecord (List (BitVec 8)) × Session (List (BitVec 8)) × SessionGhost,
            (kit.ScopeAt Scope st0 x.rem.val p.1 ∧
              p.1.currentSession = some p.2.1 ∧
              SessionGhostValid p.2.2 p.2.1) ∧
            FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0
              x p.1 p.2.2 p.2.1.state evs)
        (c_rd + c_kr) (l_rd + l_kr) (max p_rd (l_rd + p_kr)) (max r_rd r_kr) := by
      refine phaseCreditSpec_exists_guarded fun ⟨rec, ses, G⟩ ⟨hsc, hcur, hgv⟩ => ?_
      have hexKrTuple : PhaseCreditSpec M
          (fun evs' =>
            ∃ q : List (BitVec 8) × SessionRecord (List (BitVec 8)) ×
                Session (List (BitVec 8)) × IdentityKey,
              (decryptRecord C S parse x rec = .ok (q.1, q.2.1) ∧
                q.2.1.currentSession = some q.2.2.1 ∧
                q.2.2.1.state.remoteIdentity = some q.2.2.2) ∧
              FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x q.2.1 q.2.2.2 evs')
          c_kr l_kr p_kr r_kr :=
        phaseCreditSpec_exists_guarded fun ⟨pt, rec', ses', k⟩ ⟨hdec, hc', hk⟩ =>
          fromKeyReady_creditSpec_small hM hBoxTr hBoxSv hBoxSt hName hNameSm
            (hTrust rec pt rec' ses' k hsc hdec hc' hk)
            (hSave rec pt rec' ses' k hsc hdec hc' hk)
            (hStore rec pt rec' ses' k hsc hdec hc' hk)
      have hexKr : PhaseCreditSpec M
          (fun evs' => ∃ pt rec' ses' k,
            decryptRecord C S parse x rec = .ok (pt, rec') ∧
            rec'.currentSession = some ses' ∧
            ses'.state.remoteIdentity = some k ∧
            FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs')
          c_kr l_kr p_kr r_kr :=
        PhaseCreditSpec.of_imp
          (fun _ ⟨pt, rec', ses', k, hdec, hc', hk, hfe⟩ =>
            ⟨(pt, rec', ses', k), ⟨hdec, hc', hk⟩, hfe⟩)
          hexKrTuple
      have hPostSome : PhaseCreditSpec M
          (FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec)
          c_kr l_kr p_kr r_kr :=
        (PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM) hexKr).mono
          (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
          (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
      exact PhaseCreditSpec.seq (hRecDec rec ses G hsc hcur hgv) hPostSome
    exact PhaseCreditSpec.of_imp
      (fun _ ⟨rec, ses, G, hsc, hcur, hgv, hf⟩ => ⟨(rec, ses, G), ⟨hsc, hcur, hgv⟩, hf⟩)
      hEx
  have hBranches := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM)
    (PhaseCreditSpec.or hArm2 (PhaseCreditSpec.or hArm3 hArm4))
  have hFromLoad := PhaseCreditSpec.seq
    (PhaseCreditSpec.rustDealloc_align16 M (req := kit.loadBoxSize) (al := 8) (by decide)) hBranches
  exact withStoresDec_finish (PhaseCreditSpec.seq hLdStep hFromLoad)

/-- `l_st ≤ p_st` on the trailing `Store` step implies `Δlive ≤ Δpeak` for `withStoresDec_creditSpec_small`.
-/
theorem withStoresDec_small_live_le_peak
    {l_ld p_ld l_rd p_rd l_tr p_tr l_sv p_sv l_st p_st : Nat}
    (hSt : l_st ≤ p_st) :
    l_ld + (l_rd + (l_tr + (l_sv + l_st))) ≤
      max p_ld (l_ld + max p_rd (l_rd + max p_tr (l_tr + max p_sv (l_sv + p_st)))) := by
  omega

/-! ## 2. CLI W2 (`StoresGhost.opened`) Domain and Post-Decrypt Growth Bounds -/

theorem pqRatchetState_length_le_encodeRecord
    {r : SessionRecord (List (BitVec 8))} {ses : Session (List (BitVec 8))}
    (hCur : r.currentSession = some ses) :
    ses.state.pqRatchetState.length ≤ (encodeRecord r).length := by
  have h1 : ses.state.pqRatchetState.length ≤
      (bytesField 15 ses.state.pqRatchetState).length := by
    unfold bytesField
    split_ifs with h
    · simp [h]
    · exact lenField_length_ge' 15 ses.state.pqRatchetState
  have h2 : (bytesField 15 ses.state.pqRatchetState).length ≤ (encSession ses).length := by
    unfold encSession
    simp only [List.length_append]
    omega
  have h3 : (encSession ses).length ≤ (encodeRecord r).length := by
    unfold encodeRecord msgField
    rw [hCur]
    dsimp only [Option.map_some]
    exact lenField_length_ge' 1 (encSession ses)
  omega

private theorem encSession_stripPq_length_eq (s : Session (List (BitVec 8))) :
    (encSession s).length =
      (encSession (stripPq s)).length +
        (bytesField 15 s.state.pqRatchetState).length := by
  have hb0 : bytesField 15 ([] : List (BitVec 8)) = [] := rfl
  simp only [encSession, stripPq, hb0, List.length_nil, List.length_append]
  omega

/-- Bounds `(encodeRecord r).length ≤ pqCap + 2,097,192` on any `scopeKit` record with `pqRatchetState.length ≤ pqCap`.
-/
theorem encodeRecord_length_le_of_scopeKit {pqCap : Nat}
    {r : SessionRecord (List (BitVec 8))}
    (hKit : scopeKit r)
    (hPq : ∀ ses, r.currentSession = some ses → ses.state.pqRatchetState.length ≤ pqCap) :
    (encodeRecord r).length ≤ pqCap + 2097192 := by
  obtain ⟨⟨hInP, _, hRep⟩, ses, hCur, hScP⟩ := hKit
  have hPqSes : ses.state.pqRatchetState.length ≤ pqCap := hPq ses hCur
  obtain ⟨hSeeds, hRcLt, hKyLt⟩ := hInP ses hCur
  obtain ⟨hRep1, hRep2, hWf, hAbk⟩ := hRep ses hCur
  have hScP_strip : CryptoVerification.E2E.RecordX.SessionScopeP (stripPq ses) :=
    ⟨hScP.1, hScP.2.1, hScP.2.2.1, hScP.2.2.2⟩
  have hBdd : DeserializeScopeBounded ⟨some (stripPq ses)⟩ := by
    refine ⟨⟨?_, ?_, ?_⟩, stripPq ses, rfl,
      sessionScopeBounded_of_sessionScopeP hScP_strip⟩
    · intro t ht; injection ht with ht; subst ht
      exact ⟨hSeeds, hRcLt, hKyLt⟩
    · intro t ht; injection ht with ht; subst ht
      rfl
    · intro t ht; injection ht with ht; subst ht
      exact ⟨hRep1, hRep2, hWf, hAbk⟩
  have h21 : (encodeRecord ⟨some (stripPq ses)⟩).length < 2 ^ 21 :=
    encodeRecord_length_lt_21_of_bounded hBdd
  have hge : (encSession (stripPq ses)).length ≤
      (encodeRecord ⟨some (stripPq ses)⟩).length := by
    unfold encodeRecord msgField
    dsimp only [Option.map_some]
    exact lenField_length_ge' 1 (encSession (stripPq ses))
  have hle : (encodeRecord r).length ≤ (encSession ses).length + 20 := by
    unfold encodeRecord msgField
    rw [hCur]
    dsimp only [Option.map_some]
    exact lenField_length_le' 1 (encSession ses)
  have heq := encSession_stripPq_length_eq ses
  have hb15 : (bytesField 15 ses.state.pqRatchetState).length ≤
      ses.state.pqRatchetState.length + 20 :=
    bytesField_length_le' 15 ses.state.pqRatchetState
  omega

/-- Any record `r` loaded via `cliSessionStoreSpec.ScopeAt` on `StoresGhost.opened.sessions` satisfies `(encodeRecord r).length ≤ fileCap`.
-/
theorem opened_scopeAt_encodeRecord_le {A : RustAlloc} {b : BitVec 64}
    {F : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 fileCap : Nat} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))}
    (hrem : rem = peer.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hScAt : (cliSessionStoreSpec A b cliIo.rd F pathOk Scope peer s1 s2 s3 s4).ScopeAt
      Scope StoresGhost.opened.sessions rem r) :
    (encodeRecord r).length ≤ fileCap := by
  subst hrem
  obtain ⟨_, bs, hget, hans⟩ := hScAt
  have hgetRd : cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) =
      .ok bs := hget
  have hbs := hSessFileCap bs hgetRd
  cases bs with
  | nil => cases hans
  | cons b₀ bs' =>
    obtain ⟨r', hr', henc, _⟩ := hans
    injection hr' with hr'
    injection hr' with hr'
    subst hr'
    rw [henc]
    exact hbs

theorem opened_scopeAt_sessionCloneDom {A : RustAlloc} {b : BitVec 64}
    {F : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 fileCap : Nat} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {ses : Session (List (BitVec 8))}
    (hrem : rem = peer.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hScAt : (cliSessionStoreSpec A b cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r)
    (hCur : r.currentSession = some ses) :
    ses.state.pqRatchetState.length ≤ fileCap ∧ SessionCloneDom fileCap ses := by
  have hEnc := opened_scopeAt_encodeRecord_le hrem hSessFileCap hScAt
  have hPq : ses.state.pqRatchetState.length ≤ fileCap :=
    Nat.le_trans (pqRatchetState_length_le_encodeRecord hCur) hEnc
  exact ⟨hPq, sessionCloneDom_of_scopeKit_pq hScAt.1 hCur hPq⟩

/-- Post-`decryptRecord` growth bound from `scopeIn rec` and `(encodeRecord rec).length ≤ fileCap`:
establishes `scopeKit rec'`, `SessionCloneDom (fileCap + 1,128,000) ses'`, and
`(encodeRecord rec').length ≤ fileCap + 3,225,192`. -/
theorem decryptRecord_post_caps_of_scopeIn {C : Crypto} {K : MlKem}
    {parse : UuidParser} {x : DecryptGhost} {fileCap : Nat}
    {rec rec' : SessionRecord (List (BitVec 8))} {pt : List (BitVec 8)}
    (hIn : scopeIn rec)
    (hEncPre : (encodeRecord rec).length ≤ fileCap)
    (hDec : decryptRecord C (spqrV1 C.F K) parse x rec = .ok (pt, rec')) :
    scopeKit rec' ∧
      (∀ ses', rec'.currentSession = some ses' →
        ses'.state.pqRatchetState.length ≤ fileCap + 1128000 ∧
          SessionCloneDom (fileCap + 1128000) ses') ∧
      (encodeRecord rec').length ≤ fileCap + 3225192 := by
  have hKit' : scopeKit rec' := (decryptRecord_recOk_of_scopeIn hIn hDec).1
  have hPostPq : ∀ ses', rec'.currentSession = some ses' →
      ses'.state.pqRatchetState.length ≤ fileCap + 1128000 := by
    obtain ⟨⟨hInP, hPqIn, _⟩, ses, hCur, hSessSc⟩ := hIn
    have hPqFile : ses.state.pqRatchetState.length ≤ fileCap :=
      Nat.le_trans (pqRatchetState_length_le_encodeRecord hCur) hEncPre
    unfold decryptRecord SessionRecord.tryDecryptFromRecord at hDec
    rw [hCur] at hDec
    dsimp only at hDec
    rcases hTry : SessionState.tryDecryptFromRecord C (spqrV1 C.F K).spqr
        (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
        x.msg .whisper (coinsOf x.rest) ses.state with ⟨e | ptext, st'⟩
    · rw [hTry] at hDec; cases hDec
    · rw [hTry] at hDec
      simp only [Except.ok.injEq, Prod.mk.injEq] at hDec
      rcases hDec with ⟨rfl, rfl⟩
      obtain ⟨hSeeds, _, _⟩ := hInP ses hCur
      have hPqSes : PqInV1 ses.state.pqRatchetState := hPqIn ses hCur
      have hPqLt31 : ses.state.pqRatchetState.length < 2 ^ 31 := hPqSes.2
      obtain ⟨_, _, _, _, key, hRecv⟩ :=
        tryDecryptFromRecord_ok_props_gen C (spqrV1 C.F K).spqr
          (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
          x.msg .whisper (coinsOf x.rest) ses.state st' ptext hSeeds hSessSc.1 hTry
      have hGrow : st'.pqRatchetState.length ≤ ses.state.pqRatchetState.length + 1128000 :=
        (spqrV1_recv_validState_length_le C.F K ses.state.pqRatchetState x.msg.pqRatchet
          st'.pqRatchetState key hPqSes.1 (by omega) hRecv).2
      intro ses' hCur'
      injection hCur' with hEq
      subst hEq
      dsimp only
      omega
  have hEncPost : (encodeRecord rec').length ≤ (fileCap + 1128000) + 2097192 :=
    encodeRecord_length_le_of_scopeKit hKit' hPostPq
  refine ⟨hKit', ?_, by omega⟩
  intro ses' hCur'
  have hpq' := hPostPq ses' hCur'
  exact ⟨hpq', sessionCloneDom_of_scopeKit_pq hKit' hCur' hpq'⟩

theorem cliSessStorePoll_exists_capped {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dir : DirGhost} {peer : AddrGhost}
    {r : SessionRecord (List (BitVec 8))} {P : RecordGhost → Prop}
    {maxDir maxEntries maxVal c_st l_st p_st r_st : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hCum : ∀ g, P g → sessStorePollDeltaCum (recordSerializeCum g r) maxEntries ≤ c_st)
    (hLive : ∀ g, P g → sessStorePollDeltaLive (recordSerializeOutLarge M g r) maxEntries ≤ l_st)
    (hPeak : ∀ g, P g → sessStorePollDeltaPeak (recordSerializePeak M g r) maxEntries ≤ p_st)
    (hReq : ∀ g, P g → sessStorePollMaxReq (recordSerializeMaxReq g r) maxEntries ≤ r_st) :
    PhaseCreditSpec M
      (fun evs => ∃ g : RecordGhost, P g ∧ CliSessStorePollEnv dir peer g r evs)
      c_st l_st p_st r_st :=
  phaseCreditSpec_exists_guarded fun g hg =>
    (sessStorePoll_phaseCredit hM hdc hpeer).mono
      (hCum g hg) (hLive g hg) (hPeak g hg) (hReq g hg)

theorem cliSessStorePoll_exists_dom_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {dir : DirGhost} {peer : AddrGhost} {r : SessionRecord (List (BitVec 8))}
    {maxDir maxEntries maxVal pqCap encCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hDom : ∀ ses, r.currentSession = some ses → SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    PhaseCreditSpec M
      (fun evs => ∃ g : RecordGhost, RecordGhostValid g r ∧ CliSessStorePollEnv dir peer g r evs)
      (sessStorePollDeltaCum (98372903 + 2 * pqCap + 2 * encCap) maxEntries)
      (sessStorePollDeltaLive (encCap + 8195) maxEntries)
      (sessStorePollDeltaPeak (1097365 + pqCap + encCap) maxEntries)
      (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries) := by
  refine phaseCreditSpec_exists_guarded fun g hgv => ?_
  refine sessStorePoll_dom_phaseCredit hM hsmall hdc hpeer (fun G ses hg hr => ?_) hEnc
  unfold RecordGhostValid at hgv
  rw [hg, hr] at hgv
  exact ⟨hgv, hDom ses hr⟩

/-! ## 3. Concrete CLI W2 (`StoresGhost.opened`) `WithStoresDecEnv` Slot Theorems -/

/-- CLI W2 (`StoresGhost.opened`) `PhaseCreditSpec` for `WithStoresDecEnv` on `cliSessionStoreSpec` and `cliIdentityStoreSpec`.
-/
theorem w2CliDecryptSlot_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (C : Crypto) (K : MlKem) (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {Kspqr fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td c_st l_st p_st r_st : Nat}
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec M
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td)
    (hStore : ∀ rec pt rec' ses' k,
      scopeIn rec →
      decryptRecord C (spqrV1 C.F K) parse x rec = .ok (pt, rec') →
      scopeKit rec' →
      rec'.currentSession = some ses' →
      ses'.state.remoteIdentity = some k →
      ses'.state.pqRatchetState.length ≤ fileCap + 1128000 →
      SessionCloneDom (fileCap + 1128000) ses' →
      (encodeRecord rec').length ≤ fileCap + 3225192 →
      PhaseCreditSpec M (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec')
        c_st l_st p_st r_st) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    let c_ld := sessLoadPollDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollMaxReq (max 0 fileCap) deserMaxReq
    let c_rd := 98382860 + 2 * fileCap + c_td
    let l_rd := 1089170 + fileCap + l_td
    let p_rd := 1089170 + fileCap + max p_td l_td
    let r_rd := max (max 208000 fileCap) (max r_td 192)
    let c_id := smallStorePollDeltaCum (max 0 idFileCap) 0
    let l_id := smallStorePollDeltaLive (max 0 idFileCap) 0
    let p_id := smallStorePollDeltaPeak (max 0 idFileCap) 0
    let r_id := smallStorePollMaxReq (max 0 idFileCap) 0
    let c_ld_step := 2 * 24 + 9539 + c_ld
    let c_id_step := 2 * 32 + 9539 + c_id
    let c_st_step := 2 * 32 + 9539 + c_st
    let c_sc := 2 * 40 + 9539
    let c_kr := c_id_step + max c_sc (c_id_step + c_st_step)
    let l_kr := l_id + (l_id + l_st)
    let p_kr := max p_id (l_id + max p_id (l_id + p_st))
    let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
    PhaseCreditSpec M
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (c_ld_step + max (max c_sc 9573) (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))) := by
  intro kit ikit c_ld l_ld p_ld r_ld c_rd l_rd p_rd r_rd c_id l_id p_id r_id
    c_ld_step c_id_step c_st_step c_sc c_kr l_kr p_kr r_kr
  have hle17 : 17 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have hle24 : 24 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have hle40 : 40 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hsmall
  have hLoadPoll : PhaseCreditSpec M
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val) c_ld l_ld p_ld r_ld :=
    PhaseCreditSpec.of_imp hLoadEq
      (sessLoadPoll_phaseCredit hM dirDomainCaps_opened_sess (by decide) hpeer hSessFileCap hDeser)
  have hSmallId : PhaseCreditSpec M
      (CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName)
      c_id l_id p_id r_id :=
    smallStorePoll_phaseCredit hM dirDomainCaps_opened_peers (by decide) hidKeyLen hIdFileCap
  exact withStoresDec_creditSpec_small hM
    (kit := kit) (kitEnv := kitEnv) (st0 := StoresGhost.opened.sessions)
    (ikit := ikit) (ikitEnv := ikitEnv) (ist0 := StoresGhost.opened.identity)
    (nameCap := 40)
    hle17 hle24 hle32 hle32 hle32 hremName hle40
    hLoadPoll
    (fun rec ses G hsc hcur hgv => by
      have hIn : scopeIn rec :=
        (cliSess_scopeIn_of_opened (fun _ h => h) hFilesOk hrem hsc).2
      obtain ⟨hPqFile, hDom⟩ := opened_scopeAt_sessionCloneDom hrem hSessFileCap hsc hcur
      obtain ⟨hVe, hVcp, hPqLt31⟩ :=
        peerSpqrTightValidAt_of_cliSessionStoreSpec hsc hcur rfl hValid
      exact recordDecrypt_dom_phaseCredit hM hsmall
        (x := recGhostOf x 0#64 G ses.state) (ses := ses) rfl hgv hDom
        (fun G₁ hRel => hTd rec ses G G₁ hIn hcur hgv hDom hRel hVe hVcp hPqLt31 hPqFile))
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hTrustEq k) hSmallId)
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hSaveEq k) hSmallId)
    (fun rec pt rec' ses' k hsc hdec hc' hk => by
      have hIn : scopeIn rec :=
        (cliSess_scopeIn_of_opened (fun _ h => h) hFilesOk hrem hsc).2
      have hEncPre : (encodeRecord rec).length ≤ fileCap :=
        opened_scopeAt_encodeRecord_le hrem hSessFileCap hsc
      obtain ⟨hKit', hPostDom, hEncPost⟩ := decryptRecord_post_caps_of_scopeIn hIn hEncPre hdec
      obtain ⟨hPqPost, hDomPost⟩ := hPostDom ses' hc'
      exact hStore rec pt rec' ses' k hIn hdec hKit' hc' hk hPqPost hDomPost hEncPost)

/-- Closed-poll specialization of `w2CliDecryptSlot_creditSpec_small` discharging `StorePoll` at `pqCap' = fileCap + 1,128,000` and `encCap' = fileCap + 3,225,192`.
-/
theorem w2CliDecryptSlot_polls_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (C : Crypto) (K : MlKem) (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {Kspqr fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td : Nat}
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hStoreEq : ∀ rec' evs,
      scopeKit rec' →
      kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec' evs →
      ∃ g : RecordGhost, RecordGhostValid g rec' ∧
        CliSessStorePollEnv StoresGhost.opened.sessions peer g rec' evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec M
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    let pqCap' := fileCap + 1128000
    let encCap' := fileCap + 3225192
    let c_ld := sessLoadPollDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollMaxReq (max 0 fileCap) deserMaxReq
    let c_rd := 98382860 + 2 * fileCap + c_td
    let l_rd := 1089170 + fileCap + l_td
    let p_rd := 1089170 + fileCap + max p_td l_td
    let r_rd := max (max 208000 fileCap) (max r_td 192)
    let c_id := smallStorePollDeltaCum (max 0 idFileCap) 0
    let l_id := smallStorePollDeltaLive (max 0 idFileCap) 0
    let p_id := smallStorePollDeltaPeak (max 0 idFileCap) 0
    let r_id := smallStorePollMaxReq (max 0 idFileCap) 0
    let c_st := sessStorePollDeltaCum (98372903 + 2 * pqCap' + 2 * encCap') 0
    let l_st := sessStorePollDeltaLive (encCap' + 8195) 0
    let p_st := sessStorePollDeltaPeak (1097365 + pqCap' + encCap') 0
    let r_st := sessStorePollMaxReq (max (max 208000 pqCap') encCap') 0
    let c_ld_step := 2 * 24 + 9539 + c_ld
    let c_id_step := 2 * 32 + 9539 + c_id
    let c_st_step := 2 * 32 + 9539 + c_st
    let c_sc := 2 * 40 + 9539
    let c_kr := c_id_step + max c_sc (c_id_step + c_st_step)
    let l_kr := l_id + (l_id + l_st)
    let p_kr := max p_id (l_id + max p_id (l_id + p_st))
    let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
    PhaseCreditSpec M
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (c_ld_step + max (max c_sc 9573) (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))) := by
  intro kit ikit pqCap' encCap' c_ld l_ld p_ld r_ld c_rd l_rd p_rd r_rd
    c_id l_id p_id r_id c_st l_st p_st r_st
    c_ld_step c_id_step c_st_step c_sc c_kr l_kr p_kr r_kr
  exact w2CliDecryptSlot_creditSpec_small hM hsmall F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
    C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hpeer hremName hidKeyLen hFilesOk hValid hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hTd
    (fun _ _ rec' ses' _ _ _ hKit' hc' _ _ hDomPost hEncPost =>
      PhaseCreditSpec.of_imp (fun evs h => hStoreEq rec' evs hKit' h)
        (cliSessStorePoll_exists_dom_phaseCredit hM hsmall dirDomainCaps_opened_sess hpeer
          (fun s hs => by rw [hc'] at hs; injection hs with hs; subst hs; exact hDomPost)
          hEncPost))

/-! ## 4. Tight `fineCostModel` and `PhaseGroupSpec` CLI W2 Slot Bounds -/

section TightCliW2Slot

open CryptoGames.LibsignalSessionApi (Direction)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.SignalSession.Cli (ReadRule)
open LibsignalBinary.Heap (rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_smallMaxReq_eq smallAllocCost_le_488_of_le_28)
open LibsignalBinary.Heap.SpecBudget
  (allocBytes1Events cliIoCapIdx cliIoCapsEvents cliIoReadScheduleCaps)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (CliDecimalEnv CliDirGetEnv CliDirPutEnv CliDirPutStrEnv CliPathEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec nonFreeCount
   nonFreeCount_append nonFreeCount_nil nonFreeCount_rustAllocEvents
   nonFreeCount_rustDeallocEvents nonFreeCount_rustReallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (boxAlloc_phaseCredit_tight optLargeCost optLargeCost_fine_of_le
   sessLoadPollTightDeltaCum sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak
   sessLoadPollTightMaxReq sessLoadPoll_phaseCredit_tight
   sessStorePollTightDeltaCum sessStorePollTightDeltaLive sessStorePollTightDeltaPeak
   smallStorePollTightDeltaCum smallStorePollTightDeltaLive smallStorePollTightDeltaPeak
   smallStorePollTightMaxReq smallStorePoll_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (rustAllocTightCum rustAllocTightCum_fine_24 rustAllocTightCum_fine_32
   rustAllocTightCum_fine_le_738 tryCloneSmallDelta)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (PeerSpqrTightValid640 ValidEncoderPts640)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (addrText_phaseGroup dirPut_phaseGroup recordDecrypt_dom_phaseCredit_tight
   recordDecrypt_dom_phaseGroup sessStorePoll_dom_phaseCredit_tight sessStorePoll_dom_phaseGroup)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromRegionNoneEnv LoadPollStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (SaveStepEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (StoreStepEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

/-! ### 4.1 Tight `fineCostModel` Step and `WithStoresDecEnv` Composers -/

theorem boxAlloc24_fine_tight :
    PhaseCreditSpec fineCostModel (BoxAllocEnv 24) 488 0 0 24 := by
  have h := boxAlloc_phaseCredit_tight fineCostModel_modelHyps 24
  have hc : tryCloneSmallDelta fineCostModel 24 = 488 := by
    unfold tryCloneSmallDelta
    simp [rustAllocTightCum_fine_24]
  have hl : optLargeCost fineCostModel 24 = 0 := optLargeCost_fine_of_le (by decide)
  rw [hc, hl] at h
  exact h

theorem boxAlloc32_fine_tight :
    PhaseCreditSpec fineCostModel (BoxAllocEnv 32) 738 0 0 32 := by
  have h := boxAlloc_phaseCredit_tight fineCostModel_modelHyps 32
  have hc : tryCloneSmallDelta fineCostModel 32 = 738 := by
    unfold tryCloneSmallDelta
    simp [rustAllocTightCum_fine_32]
  have hl : optLargeCost fineCostModel 32 = 0 := optLargeCost_fine_of_le (by decide)
  rw [hc, hl] at h
  exact h

theorem stringClone44_fine_tight {g : VecGhost} {nameCap : Nat}
    (hName : g.bytes.length ≤ nameCap) (h44 : nameCap ≤ 44) :
    PhaseCreditSpec fineCostModel (StringCloneEnv g) 738 0 0 nameCap := by
  have hlen44 : g.bytes.length ≤ 44 := Nat.le_trans hName h44
  have hall := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight fineCostModel_modelHyps
    (req := g.bytes.length) (al := 1) (by decide)
  have hc : rustAllocTightCum fineCostModel g.bytes.length ≤ 738 :=
    rustAllocTightCum_fine_le_738 hlen44
  have hl : optLargeCost fineCostModel g.bytes.length = 0 :=
    optLargeCost_fine_of_le (Nat.le_trans hlen44 (by decide))
  rw [hl] at hall
  refine (PhaseCreditSpec.or_of_imp ?_ (PhaseCreditSpec.nil fineCostModel)
    (hall.mono hc (Nat.le_refl 0) (Nat.le_refl 0) hName)).mono
    (Nat.le_of_eq (Nat.zero_max 738)) (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.le_of_eq (Nat.zero_max nameCap))
  rintro evs (⟨_, rfl⟩ | ⟨_, h2⟩)
  · exact Or.inl rfl
  · exact Or.inr h2

theorem fromRegionNone_fine_tight :
    PhaseCreditSpec fineCostModel FromRegionNoneEnv 488 0 0 17 := by
  have hall := SessionCloneCredit.PhaseCreditSpec.rustAlloc_tight fineCostModel_modelHyps
    (req := 17) (al := 1) (by decide)
  have hc : rustAllocTightCum fineCostModel 17 ≤ 488 := by
    unfold rustAllocTightCum
    rw [fineCostModel_smallMaxReq_eq]
    simp only [show 17 ≤ 135167 by decide, ↓reduceIte]
    exact smallAllocCost_le_488_of_le_28 (by decide)
  have hl : optLargeCost fineCostModel 17 = 0 := optLargeCost_fine_of_le (by decide)
  rw [hl] at hall
  exact ((hall.mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 17)).seq
    (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc)).mono
    (by decide) (by decide) (by decide) (by decide)

theorem loadPollStep24_fine_tight {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState} {rem : AddrVal} {c_p l_p p_p r_p : Nat}
    (hBox : kit.loadBoxSize = 24)
    (hpoll : PhaseCreditSpec fineCostModel (kitEnv.loadPollEnv st0 rem) c_p l_p p_p r_p) :
    PhaseCreditSpec fineCostModel (LoadPollStepEnv kit kitEnv st0 rem)
      (488 + c_p) l_p p_p (max 24 r_p) := by
  unfold LoadPollStepEnv
  rw [hBox]
  exact (boxAlloc24_fine_tight.seq hpoll).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add l_p))
    (Nat.max_le.mpr ⟨Nat.zero_le p_p, Nat.le_of_eq (Nat.zero_add p_p)⟩)
    (Nat.le_refl _)

private theorem rustDealloc_eq_freeOnly (sz al : Nat) :
    ∀ evs, evs = rustDeallocEvents sz al → FreeOnlyEvs evs := by
  rintro _ rfl ev hev
  unfold rustDeallocEvents at hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨al, sz, rfl⟩

theorem trustStep32_fine_tight {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState} {rem : AddrVal} {key : IdentityKey}
    {d : Direction} {c_p l_p p_p r_p : Nat}
    (hBox : ikit.trustBoxSize = 32)
    (hpoll : PhaseCreditSpec fineCostModel (ikitEnv.trustPollEnv ist0 rem key d) c_p l_p p_p r_p) :
    PhaseCreditSpec fineCostModel (TrustStepEnv ikit ikitEnv ist0 rem key d)
      (738 + c_p) l_p p_p (max 32 r_p) := by
  unfold TrustStepEnv
  rw [hBox]
  have htail := phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hpoll
    (rustDealloc_eq_freeOnly 32 8)
  exact (boxAlloc32_fine_tight.seq htail).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add l_p))
    (Nat.max_le.mpr ⟨Nat.zero_le p_p, Nat.le_of_eq (Nat.zero_add p_p)⟩)
    (Nat.le_refl _)

theorem saveStep32_fine_tight {A : RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState} {rem : AddrVal} {key : IdentityKey} {c_p l_p p_p r_p : Nat}
    (hBox : ikit.saveBoxSize = 32)
    (hpoll : PhaseCreditSpec fineCostModel (ikitEnv.savePollEnv ist0 rem key) c_p l_p p_p r_p) :
    PhaseCreditSpec fineCostModel (SaveStepEnv ikit ikitEnv ist0 rem key)
      (738 + c_p) l_p p_p (max 32 r_p) := by
  unfold SaveStepEnv
  rw [hBox]
  have htail := phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hpoll
    (rustDealloc_eq_freeOnly 32 8)
  exact (boxAlloc32_fine_tight.seq htail).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add l_p))
    (Nat.max_le.mpr ⟨Nat.zero_le p_p, Nat.le_of_eq (Nat.zero_add p_p)⟩)
    (Nat.le_refl _)

theorem storeStep32_fine_tight {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState} {rem : AddrVal} {rec' : SessionRecord (List (BitVec 8))}
    {c_p l_p p_p r_p : Nat}
    (hBox : kit.storeBoxSize = 32)
    (hpoll : PhaseCreditSpec fineCostModel (kitEnv.storePollEnv st0 rem rec') c_p l_p p_p r_p) :
    PhaseCreditSpec fineCostModel (StoreStepEnv kit kitEnv st0 rem rec')
      (738 + c_p) l_p p_p (max 32 r_p) := by
  unfold StoreStepEnv
  rw [hBox]
  have htail := phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hpoll
    (rustDealloc_eq_freeOnly 32 8)
  exact (boxAlloc32_fine_tight.seq htail).mono
    (Nat.le_refl _)
    (Nat.le_of_eq (Nat.zero_add l_p))
    (Nat.max_le.mpr ⟨Nat.zero_le p_p, Nat.le_of_eq (Nat.zero_add p_p)⟩)
    (Nat.le_refl _)

private theorem fromKeyReady_tight_finish
    {P : List AllocEvent → Prop}
    {nameCap c_tr_step l_tr p_tr r_tr c_sv_step l_sv p_sv r_sv c_st_step l_st p_st r_st : Nat}
    (h : PhaseCreditSpec fineCostModel P
      (c_tr_step + max 0 (max 738 (c_sv_step + c_st_step)))
      (l_tr + max 0 (max 0 (l_sv + l_st)))
      (max p_tr (l_tr + max 0 (max 0 (max p_sv (l_sv + p_st)))))
      (max (max 32 r_tr) (max 0 (max nameCap (max (max 32 r_sv) (max 32 r_st)))))) :
    PhaseCreditSpec fineCostModel P
      (c_tr_step + max 738 (c_sv_step + c_st_step))
      (l_tr + (l_sv + l_st))
      (max p_tr (l_tr + max p_sv (l_sv + p_st)))
      (max (max 32 r_tr) (max nameCap (max (max 32 r_sv) (max 32 r_st)))) :=
  h.mono (by omega) (by omega) (by omega) (by omega)

theorem fromKeyReady_fine_creditSpec_tight {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {x : DecryptGhost} {rec' : SessionRecord (List (BitVec 8))} {k : IdentityKey}
    {nameCap c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hBoxTr : ikit.trustBoxSize = 32)
    (hBoxSv : ikit.saveBoxSize = 32)
    (hBoxSt : kit.storeBoxSize = 32)
    (hName : x.rem.name.bytes.length ≤ nameCap)
    (hName44 : nameCap ≤ 44)
    (hTrust : PhaseCreditSpec fineCostModel (ikitEnv.trustPollEnv ist0 x.rem.val k .receiving)
      c_tr l_tr p_tr r_tr)
    (hSave : PhaseCreditSpec fineCostModel
      (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true)) x.rem.val k)
      c_sv l_sv p_sv r_sv)
    (hStore : PhaseCreditSpec fineCostModel (kitEnv.storePollEnv st0 x.rem.val rec')
      c_st l_st p_st r_st) :
    let c_tr_step := 738 + c_tr
    let c_sv_step := 738 + c_sv
    let c_st_step := 738 + c_st
    PhaseCreditSpec fineCostModel (FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)
      (c_tr_step + max 738 (c_sv_step + c_st_step))
      (l_tr + (l_sv + l_st))
      (max p_tr (l_tr + max p_sv (l_sv + p_st)))
      (max (max 32 r_tr) (max nameCap (max (max 32 r_sv) (max 32 r_st)))) := by
  intro c_tr_step c_sv_step c_st_step
  have hTrStep := trustStep32_fine_tight hBoxTr hTrust
  have hSvStep := saveStep32_fine_tight hBoxSv hSave
  have hStStep := storeStep32_fine_tight hBoxSt hStore
  have hStoreCall : PhaseCreditSpec fineCostModel (FromStoreCallEnv kit kitEnv st0 x.rem.val rec')
      c_st_step l_st p_st (max 32 r_st) :=
    phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hStStep (fun _ h => h)
  have hFalse : PhaseCreditSpec fineCostModel (FromTrustedFalseEnv x) 738 0 0 nameCap :=
    ((stringClone44_fine_tight hName hName44).seq
      (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc)).mono
      (by decide) (by decide) (by decide) (Nat.le_of_eq (Nat.max_zero nameCap))
  have hTrueTail : PhaseCreditSpec fineCostModel
      (fun evs => FreeOnlyEvs evs ∨ FromStoreCallEnv kit kitEnv st0 x.rem.val rec' evs)
      c_st_step l_st p_st (max 32 r_st) :=
    ((PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).or hStoreCall).mono
      (Nat.le_of_eq (Nat.zero_max _))
      (Nat.le_of_eq (Nat.zero_max _))
      (Nat.le_of_eq (Nat.zero_max _))
      (Nat.le_of_eq (Nat.zero_max _))
  have hTrue : PhaseCreditSpec fineCostModel
      (FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)
      (c_sv_step + c_st_step) (l_sv + l_st) (max p_sv (l_sv + p_st))
      (max (max 32 r_sv) (max 32 r_st)) :=
    hSvStep.seq hTrueTail
  have hCont := (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).or (hFalse.or hTrue)
  exact fromKeyReady_tight_finish (hTrStep.seq hCont)

private theorem withStoresDec_tight_finish
    {P : List AllocEvent → Prop}
    {nameCap c_ld_step l_ld p_ld r_ld c_rd l_rd p_rd r_rd c_kr l_kr p_kr r_kr : Nat}
    (h : PhaseCreditSpec fineCostModel P
      (c_ld_step + (0 + max 0 (max 738 (max 488 (c_rd + c_kr)))))
      (l_ld + (0 + max 0 (max 0 (max 0 (l_rd + l_kr)))))
      (max p_ld (l_ld + max 0 (0 + max 0 (max 0 (max 0 (max p_rd (l_rd + p_kr)))))))
      (max (max 24 r_ld) (max 0 (max 0 (max nameCap (max 17 (max r_rd r_kr))))))) :
    PhaseCreditSpec fineCostModel P
      (c_ld_step + max 738 (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max nameCap 17) (max r_rd r_kr))) :=
  h.mono (by omega) (by omega) (by omega) (by omega)

theorem withStoresDec_fine_creditSpec_tight {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    {nameCap c_ld l_ld p_ld r_ld c_rd l_rd p_rd r_rd c_tr l_tr p_tr r_tr
     c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hBoxLd : kit.loadBoxSize = 24)
    (hBoxTr : ikit.trustBoxSize = 32)
    (hBoxSv : ikit.saveBoxSize = 32)
    (hBoxSt : kit.storeBoxSize = 32)
    (hName : x.rem.name.bytes.length ≤ nameCap)
    (hName44 : nameCap ≤ 44)
    (hLoad : PhaseCreditSpec fineCostModel (kitEnv.loadPollEnv st0 x.rem.val) c_ld l_ld p_ld r_ld)
    (hRecDec : ∀ rec ses G,
      kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      PhaseCreditSpec fineCostModel (RecordDecryptEnv tdEnv (recGhostOf x 0#64 G ses.state))
        c_rd l_rd p_rd r_rd)
    (hTrust : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec fineCostModel (ikitEnv.trustPollEnv ist0 x.rem.val k .receiving)
        c_tr l_tr p_tr r_tr)
    (hSave : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec fineCostModel
        (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true))
          x.rem.val k)
        c_sv l_sv p_sv r_sv)
    (hStore : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec fineCostModel (kitEnv.storePollEnv st0 x.rem.val rec')
        c_st l_st p_st r_st) :
    let c_ld_step := 488 + c_ld
    let c_tr_step := 738 + c_tr
    let c_sv_step := 738 + c_sv
    let c_st_step := 738 + c_st
    let c_kr := c_tr_step + max 738 (c_sv_step + c_st_step)
    let l_kr := l_tr + (l_sv + l_st)
    let p_kr := max p_tr (l_tr + max p_sv (l_sv + p_st))
    let r_kr := max (max 32 r_tr) (max nameCap (max (max 32 r_sv) (max 32 r_st)))
    PhaseCreditSpec fineCostModel
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      (c_ld_step + max 738 (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max nameCap 17) (max r_rd r_kr))) := by
  intro c_ld_step c_tr_step c_sv_step c_st_step c_kr l_kr p_kr r_kr
  have hLdStep := loadPollStep24_fine_tight hBoxLd hLoad
  have hArm2 : PhaseCreditSpec fineCostModel (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs)
      738 0 0 nameCap :=
    ((stringClone44_fine_tight hName hName44).seq
      (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc)).mono
      (by decide) (by decide) (by decide) (Nat.le_of_eq (Nat.max_zero nameCap))
  have hArm3 := fromRegionNone_fine_tight
  have hArm4 : PhaseCreditSpec fineCostModel
      (fun evs => ∃ rec ses G,
        kit.ScopeAt Scope st0 x.rem.val rec ∧
        rec.currentSession = some ses ∧
        SessionGhostValid G ses ∧
        FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 x rec G ses.state evs)
      (c_rd + c_kr) (l_rd + l_kr) (max p_rd (l_rd + p_kr)) (max r_rd r_kr) := by
    have hEx : PhaseCreditSpec fineCostModel
        (fun evs =>
          ∃ p : SessionRecord (List (BitVec 8)) × Session (List (BitVec 8)) × SessionGhost,
            (kit.ScopeAt Scope st0 x.rem.val p.1 ∧
              p.1.currentSession = some p.2.1 ∧
              SessionGhostValid p.2.2 p.2.1) ∧
            FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0
              x p.1 p.2.2 p.2.1.state evs)
        (c_rd + c_kr) (l_rd + l_kr) (max p_rd (l_rd + p_kr)) (max r_rd r_kr) := by
      refine phaseCreditSpec_exists_guarded fun ⟨rec, ses, G⟩ ⟨hsc, hcur, hgv⟩ => ?_
      have hexKrTuple : PhaseCreditSpec fineCostModel
          (fun evs' =>
            ∃ q : List (BitVec 8) × SessionRecord (List (BitVec 8)) ×
                Session (List (BitVec 8)) × IdentityKey,
              (decryptRecord C S parse x rec = .ok (q.1, q.2.1) ∧
                q.2.1.currentSession = some q.2.2.1 ∧
                q.2.2.1.state.remoteIdentity = some q.2.2.2) ∧
              FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x q.2.1 q.2.2.2 evs')
          c_kr l_kr p_kr r_kr :=
        phaseCreditSpec_exists_guarded fun ⟨pt, rec', ses', k⟩ ⟨hdec, hc', hk⟩ =>
          fromKeyReady_fine_creditSpec_tight hBoxTr hBoxSv hBoxSt hName hName44
            (hTrust rec pt rec' ses' k hsc hdec hc' hk)
            (hSave rec pt rec' ses' k hsc hdec hc' hk)
            (hStore rec pt rec' ses' k hsc hdec hc' hk)
      have hexKr : PhaseCreditSpec fineCostModel
          (fun evs' => ∃ pt rec' ses' k,
            decryptRecord C S parse x rec = .ok (pt, rec') ∧
            rec'.currentSession = some ses' ∧
            ses'.state.remoteIdentity = some k ∧
            FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs')
          c_kr l_kr p_kr r_kr :=
        PhaseCreditSpec.of_imp
          (fun _ ⟨pt, rec', ses', k, hdec, hc', hk, hfe⟩ =>
            ⟨(pt, rec', ses', k), ⟨hdec, hc', hk⟩, hfe⟩)
          hexKrTuple
      have hPostSome : PhaseCreditSpec fineCostModel
          (FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec)
          c_kr l_kr p_kr r_kr :=
        ((PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).or hexKr).mono
          (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
          (Nat.le_of_eq (Nat.zero_max _)) (Nat.le_of_eq (Nat.zero_max _))
      exact (hRecDec rec ses G hsc hcur hgv).seq hPostSome
    exact PhaseCreditSpec.of_imp
      (fun _ ⟨rec, ses, G, hsc, hcur, hgv, hf⟩ => ⟨(rec, ses, G), ⟨hsc, hcur, hgv⟩, hf⟩)
      hEx
  have hBranches := (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).or
    (hArm2.or (hArm3.or hArm4))
  have hDealloc24 : PhaseCreditSpec fineCostModel
      (· = rustDeallocEvents kit.loadBoxSize 8) 0 0 0 0 := by
    rw [hBoxLd]
    exact PhaseCreditSpec.rustDealloc_align16 fineCostModel (req := 24) (al := 8) (by decide)
  have hFromLoad := hDealloc24.seq hBranches
  exact withStoresDec_tight_finish (hLdStep.seq hFromLoad)

/-! ### 4.2 Tight `fineCostModel` CLI W2 Slot Credit Specs -/

theorem cliSessStorePoll_exists_dom_phaseCredit_tight
    {dir : DirGhost} {peer : AddrGhost} {r : SessionRecord (List (BitVec 8))}
    {maxDir maxEntries maxVal pqCap encCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hDom : ∀ ses, r.currentSession = some ses → SessionCloneDom pqCap ses)
    (hEnc : (encodeRecord r).length ≤ encCap) :
    PhaseCreditSpec fineCostModel
      (fun evs => ∃ g : RecordGhost, RecordGhostValid g r ∧ CliSessStorePollEnv dir peer g r evs)
      (sessStorePollTightDeltaCum 8420940 maxEntries)
      (sessStorePollTightDeltaLive (optLargeCost fineCostModel encCap) maxEntries)
      (sessStorePollTightDeltaPeak
        (1080975 + optLargeCost fineCostModel pqCap + optLargeCost fineCostModel encCap) maxEntries)
      (sessStorePollMaxReq (max (max 208000 pqCap) encCap) maxEntries) := by
  refine phaseCreditSpec_exists_guarded fun g hgv => ?_
  refine sessStorePoll_dom_phaseCredit_tight hdc hpeer (fun G ses hg hr => ?_) hEnc
  unfold RecordGhostValid at hgv
  rw [hg, hr] at hgv
  exact ⟨hgv, hDom ses hr⟩

/-- Tight `fineCostModel` CLI W2 (`StoresGhost.opened`) `PhaseCreditSpec` for `WithStoresDecEnv`. -/
theorem w2CliDecryptSlot_tight_fine_creditSpec {A : RustAlloc}
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (C : Crypto) (K : MlKem) (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {Kspqr fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td c_st l_st p_st r_st : Nat}
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td)
    (hStore : ∀ rec pt rec' ses' k,
      scopeIn rec →
      decryptRecord C (spqrV1 C.F K) parse x rec = .ok (pt, rec') →
      scopeKit rec' →
      rec'.currentSession = some ses' →
      ses'.state.remoteIdentity = some k →
      ses'.state.pqRatchetState.length ≤ fileCap + 1128000 →
      SessionCloneDom (fileCap + 1128000) ses' →
      (encodeRecord rec').length ≤ fileCap + 3225192 →
      PhaseCreditSpec fineCostModel (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec')
        c_st l_st p_st r_st) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    let c_ld := sessLoadPollTightDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollTightDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollTightDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollTightMaxReq (max 0 fileCap) deserMaxReq
    let c_rd := 8286380 + c_td
    let l_rd := 1080975 + optLargeCost fineCostModel fileCap + l_td
    let p_rd := 1080975 + optLargeCost fineCostModel fileCap + max p_td l_td
    let r_rd := max (max 208000 fileCap) (max r_td 192)
    let c_id := smallStorePollTightDeltaCum (max 0 idFileCap) 0
    let l_id := smallStorePollTightDeltaLive (max 0 idFileCap) 0
    let p_id := smallStorePollTightDeltaPeak (max 0 idFileCap) 0
    let r_id := smallStorePollTightMaxReq (max 0 idFileCap) 0
    let c_ld_step := 488 + c_ld
    let c_id_step := 738 + c_id
    let c_st_step := 738 + c_st
    let c_kr := c_id_step + max 738 (c_id_step + c_st_step)
    let l_kr := l_id + (l_id + l_st)
    let p_kr := max p_id (l_id + max p_id (l_id + p_st))
    let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
    PhaseCreditSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (c_ld_step + max 738 (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))) := by
  intro kit ikit c_ld l_ld p_ld r_ld c_rd l_rd p_rd r_rd c_id l_id p_id r_id
    c_ld_step c_id_step c_st_step c_kr l_kr p_kr r_kr
  have hLoadPoll : PhaseCreditSpec fineCostModel
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val) c_ld l_ld p_ld r_ld :=
    PhaseCreditSpec.of_imp hLoadEq
      (sessLoadPoll_phaseCredit_tight dirDomainCaps_opened_sess (by decide) hpeer hSessFileCap hDeser)
  have hSmallId : PhaseCreditSpec fineCostModel
      (CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName)
      c_id l_id p_id r_id :=
    smallStorePoll_phaseCredit_tight dirDomainCaps_opened_peers (by decide) hidKeyLen hIdFileCap
  exact withStoresDec_fine_creditSpec_tight
    (kit := kit) (kitEnv := kitEnv) (st0 := StoresGhost.opened.sessions)
    (ikit := ikit) (ikitEnv := ikitEnv) (ist0 := StoresGhost.opened.identity)
    (nameCap := 40)
    rfl rfl rfl rfl hremName (by decide)
    hLoadPoll
    (fun rec ses G hsc hcur hgv => by
      have hIn : scopeIn rec :=
        (cliSess_scopeIn_of_opened (fun _ h => h) hFilesOk hrem hsc).2
      obtain ⟨hPqFile, hDom⟩ := opened_scopeAt_sessionCloneDom hrem hSessFileCap hsc hcur
      obtain ⟨hVe, hVcp, hPqLt31⟩ :=
        peerSpqrTightValidAt_of_cliSessionStoreSpec hsc hcur rfl hValid
      exact recordDecrypt_dom_phaseCredit_tight
        (x := recGhostOf x 0#64 G ses.state) (ses := ses) rfl hgv hDom
        (fun G₁ hRel => hTd rec ses G G₁ hIn hcur hgv hDom hRel hVe hVcp hPqLt31 hPqFile))
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hTrustEq k) hSmallId)
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hSaveEq k) hSmallId)
    (fun rec pt rec' ses' k hsc hdec hc' hk => by
      have hIn : scopeIn rec :=
        (cliSess_scopeIn_of_opened (fun _ h => h) hFilesOk hrem hsc).2
      have hEncPre : (encodeRecord rec).length ≤ fileCap :=
        opened_scopeAt_encodeRecord_le hrem hSessFileCap hsc
      obtain ⟨hKit', hPostDom, hEncPost⟩ := decryptRecord_post_caps_of_scopeIn hIn hEncPre hdec
      obtain ⟨hPqPost, hDomPost⟩ := hPostDom ses' hc'
      exact hStore rec pt rec' ses' k hIn hdec hKit' hc' hk hPqPost hDomPost hEncPost)

/-- Closed-poll specialization of `w2CliDecryptSlot_tight_fine_creditSpec`. -/
theorem w2CliDecryptSlot_polls_tight_fine_creditSpec {A : RustAlloc}
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (C : Crypto) (K : MlKem) (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {Kspqr fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td : Nat}
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hStoreEq : ∀ rec' evs,
      scopeKit rec' →
      kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec' evs →
      ∃ g : RecordGhost, RecordGhostValid g rec' ∧
        CliSessStorePollEnv StoresGhost.opened.sessions peer g rec' evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    let pqCap' := fileCap + 1128000
    let encCap' := fileCap + 3225192
    let c_ld := sessLoadPollTightDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollTightDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollTightDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollTightMaxReq (max 0 fileCap) deserMaxReq
    let c_rd := 8286380 + c_td
    let l_rd := 1080975 + optLargeCost fineCostModel fileCap + l_td
    let p_rd := 1080975 + optLargeCost fineCostModel fileCap + max p_td l_td
    let r_rd := max (max 208000 fileCap) (max r_td 192)
    let c_id := smallStorePollTightDeltaCum (max 0 idFileCap) 0
    let l_id := smallStorePollTightDeltaLive (max 0 idFileCap) 0
    let p_id := smallStorePollTightDeltaPeak (max 0 idFileCap) 0
    let r_id := smallStorePollTightMaxReq (max 0 idFileCap) 0
    let c_st := sessStorePollTightDeltaCum 8420940 0
    let l_st := sessStorePollTightDeltaLive (optLargeCost fineCostModel encCap') 0
    let p_st := sessStorePollTightDeltaPeak
      (1080975 + optLargeCost fineCostModel pqCap' + optLargeCost fineCostModel encCap') 0
    let r_st := sessStorePollMaxReq (max (max 208000 pqCap') encCap') 0
    let c_ld_step := 488 + c_ld
    let c_id_step := 738 + c_id
    let c_st_step := 738 + c_st
    let c_kr := c_id_step + max 738 (c_id_step + c_st_step)
    let l_kr := l_id + (l_id + l_st)
    let p_kr := max p_id (l_id + max p_id (l_id + p_st))
    let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
    PhaseCreditSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (c_ld_step + max 738 (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))) := by
  intro kit ikit pqCap' encCap' c_ld l_ld p_ld r_ld c_rd l_rd p_rd r_rd
    c_id l_id p_id r_id c_st l_st p_st r_st
    c_ld_step c_id_step c_st_step c_kr l_kr p_kr r_kr
  exact w2CliDecryptSlot_tight_fine_creditSpec F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
    C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hpeer hremName hidKeyLen hFilesOk hValid hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hTd
    (fun _ _ rec' ses' _ _ _ hKit' hc' _ _ hDomPost hEncPost =>
      PhaseCreditSpec.of_imp (fun evs h => hStoreEq rec' evs hKit' h)
        (cliSessStorePoll_exists_dom_phaseCredit_tight dirDomainCaps_opened_sess hpeer
          (fun s hs => by rw [hc'] at hs; injection hs with hs; subst hs; exact hDomPost)
          hEncPost))

/-- `PeerSpqrTightValid640` (`Kspqr = 640`) instantiation of `w2CliDecryptSlot_tight_fine_creditSpec`.
-/
theorem w2CliDecryptSlot_tight640_fine_creditSpec {A : RustAlloc}
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (C : Crypto) (K : MlKem) (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td c_st l_st p_st r_st : Nat}
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValid640 F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPts640 ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td)
    (hStore : ∀ rec pt rec' ses' k,
      scopeIn rec →
      decryptRecord C (spqrV1 C.F K) parse x rec = .ok (pt, rec') →
      scopeKit rec' →
      rec'.currentSession = some ses' →
      ses'.state.remoteIdentity = some k →
      ses'.state.pqRatchetState.length ≤ fileCap + 1128000 →
      SessionCloneDom (fileCap + 1128000) ses' →
      (encodeRecord rec').length ≤ fileCap + 3225192 →
      PhaseCreditSpec fineCostModel (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec')
        c_st l_st p_st r_st) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    let c_ld := sessLoadPollTightDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollTightDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollTightDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollTightMaxReq (max 0 fileCap) deserMaxReq
    let c_rd := 8286380 + c_td
    let l_rd := 1080975 + optLargeCost fineCostModel fileCap + l_td
    let p_rd := 1080975 + optLargeCost fineCostModel fileCap + max p_td l_td
    let r_rd := max (max 208000 fileCap) (max r_td 192)
    let c_id := smallStorePollTightDeltaCum (max 0 idFileCap) 0
    let l_id := smallStorePollTightDeltaLive (max 0 idFileCap) 0
    let p_id := smallStorePollTightDeltaPeak (max 0 idFileCap) 0
    let r_id := smallStorePollTightMaxReq (max 0 idFileCap) 0
    let c_ld_step := 488 + c_ld
    let c_id_step := 738 + c_id
    let c_st_step := 738 + c_st
    let c_kr := c_id_step + max 738 (c_id_step + c_st_step)
    let l_kr := l_id + (l_id + l_st)
    let p_kr := max p_id (l_id + max p_id (l_id + p_st))
    let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
    PhaseCreditSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (c_ld_step + max 738 (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))) :=
  w2CliDecryptSlot_tight_fine_creditSpec F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
    C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hpeer hremName hidKeyLen hFilesOk hValid hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hTd hStore

theorem w2CliDecryptSlot_polls_tight640_fine_creditSpec {A : RustAlloc}
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (C : Crypto) (K : MlKem) (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td : Nat}
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValid640 F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hStoreEq : ∀ rec' evs,
      scopeKit rec' →
      kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec' evs →
      ∃ g : RecordGhost, RecordGhostValid g rec' ∧
        CliSessStorePollEnv StoresGhost.opened.sessions peer g rec' evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPts640 ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    let pqCap' := fileCap + 1128000
    let encCap' := fileCap + 3225192
    let c_ld := sessLoadPollTightDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollTightDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollTightDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollTightMaxReq (max 0 fileCap) deserMaxReq
    let c_rd := 8286380 + c_td
    let l_rd := 1080975 + optLargeCost fineCostModel fileCap + l_td
    let p_rd := 1080975 + optLargeCost fineCostModel fileCap + max p_td l_td
    let r_rd := max (max 208000 fileCap) (max r_td 192)
    let c_id := smallStorePollTightDeltaCum (max 0 idFileCap) 0
    let l_id := smallStorePollTightDeltaLive (max 0 idFileCap) 0
    let p_id := smallStorePollTightDeltaPeak (max 0 idFileCap) 0
    let r_id := smallStorePollTightMaxReq (max 0 idFileCap) 0
    let c_st := sessStorePollTightDeltaCum 8420940 0
    let l_st := sessStorePollTightDeltaLive (optLargeCost fineCostModel encCap') 0
    let p_st := sessStorePollTightDeltaPeak
      (1080975 + optLargeCost fineCostModel pqCap' + optLargeCost fineCostModel encCap') 0
    let r_st := sessStorePollMaxReq (max (max 208000 pqCap') encCap') 0
    let c_ld_step := 488 + c_ld
    let c_id_step := 738 + c_id
    let c_st_step := 738 + c_st
    let c_kr := c_id_step + max 738 (c_id_step + c_st_step)
    let l_kr := l_id + (l_id + l_st)
    let p_kr := max p_id (l_id + max p_id (l_id + p_st))
    let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
    PhaseCreditSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (c_ld_step + max 738 (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))) :=
  w2CliDecryptSlot_polls_tight_fine_creditSpec F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
    C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hpeer hremName hidKeyLen hFilesOk hValid hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hStoreEq hTd

/-! ### 4.3 `PhaseGroupSpec fineCostModel` CLI W2 Slot Bounds -/

theorem phaseGroupSpec_exists_guarded {α : Sort _} {M : AllocCostModel} [HasFineGroupCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, P a → PhaseGroupSpec M (E a) g) :
    PhaseGroupSpec M (fun evs => ∃ a, P a ∧ E a evs) g where
  groups_le st0 {_} := fun ⟨a, ha, hevs⟩ => (h a ha).groups_le st0 hevs

private theorem nonFreeCount_le_length : ∀ (evs : List AllocEvent), nonFreeCount evs ≤ evs.length
  | [] => Nat.le_refl 0
  | ev :: tl => by
    have ih := nonFreeCount_le_length tl
    cases ev <;> simp only [nonFreeCount, List.length_cons] <;> omega

private theorem boxAlloc_phaseGroup (sz : Nat) :
    PhaseGroupSpec fineCostModel (BoxAllocEnv sz) 196608 := by
  refine (((PhaseGroupSpec.nil fineCostModel).or
    (PhaseGroupSpec.rustAlloc_any fineCostModel sz 8)).of_imp ?_).mono (by decide)
  rintro evs (⟨_, h1⟩ | ⟨_, h2⟩)
  · exact Or.inl h1
  · exact Or.inr h2

private theorem stringClone_phaseGroup (g : VecGhost) :
    PhaseGroupSpec fineCostModel (StringCloneEnv g) 196608 := by
  refine (((PhaseGroupSpec.nil fineCostModel).or
    (PhaseGroupSpec.rustAlloc_any fineCostModel g.bytes.length 1)).of_imp ?_).mono (by decide)
  rintro evs (⟨_, h1⟩ | ⟨_, h2⟩)
  · exact Or.inl h1
  · exact Or.inr h2

private theorem fromRegionNone_phaseGroup :
    PhaseGroupSpec fineCostModel FromRegionNoneEnv 196608 :=
  ((PhaseGroupSpec.rustAlloc_any fineCostModel 17 1).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (by decide)

private theorem allocBytes1_phaseGroup (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (· = allocBytes1Events bs) 196608 := by
  unfold allocBytes1Events
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (by decide)
  · exact (PhaseGroupSpec.rustAlloc_any fineCostModel bs.length 1).mono (by decide)

private theorem cliIoCapIdx_le_local : ∀ (K r : Nat), cliIoCapIdx K r ≤ K
  | 0, _ => Nat.le_refl 0
  | K + 1, r => by
    unfold cliIoCapIdx
    split
    · exact Nat.le_trans (cliIoCapIdx_le_local K r) (Nat.le_succ K)
    · exact Nat.le_refl (K + 1)

private theorem cliIoCapsEvents_nonFreeCount :
    ∀ (prev : Nat) (cs : List Nat), nonFreeCount (cliIoCapsEvents prev cs) ≤ cs.length
  | 0, [] => by simp only [cliIoCapsEvents, nonFreeCount_nil]; exact Nat.zero_le 0
  | _ + 1, [] => by simp only [cliIoCapsEvents, nonFreeCount_nil]; exact Nat.zero_le 0
  | 0, c :: rest => by
    simp only [cliIoCapsEvents, nonFreeCount_append, List.length_cons]
    have h1 := nonFreeCount_rustAllocEvents c 1
    have ih := cliIoCapsEvents_nonFreeCount c rest
    omega
  | prev + 1, c :: rest => by
    simp only [cliIoCapsEvents, nonFreeCount_append, List.length_cons]
    have h1 := nonFreeCount_rustReallocEvents (prev + 1) c 1
    have ih := cliIoCapsEvents_nonFreeCount c rest
    omega

private theorem cliIoReadSchedule9_nonFreeCount (r : Nat) :
    nonFreeCount (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 r)) ≤ 10 := by
  have h1 := cliIoCapsEvents_nonFreeCount 0 (cliIoReadScheduleCaps 9 r)
  have h2 : (cliIoReadScheduleCaps 9 r).length ≤ 10 := by
    unfold cliIoReadScheduleCaps
    split
    · exact Nat.zero_le 10
    · simp only [List.length_map, List.length_range]
      have hidx := cliIoCapIdx_le_local 9 r
      omega
  exact Nat.le_trans h1 h2

private theorem readFile_rule_nonFreeBound (rd : ReadRule) (files : FsFiles)
    (path : List (BitVec 8)) :
    NonFreeBound (ReadFileRuleEnv rd files path) 10 := by
  intro evs h
  unfold ReadFileRuleEnv at h
  cases hres : rd files path with
  | error u =>
    rw [hres] at h
    dsimp only at h
    subst h
    rw [nonFreeCount_nil]
    exact Nat.zero_le 10
  | ok bs =>
    rw [hres] at h
    dsimp only at h
    rcases h with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · unfold allocBytes1Events
      split
      · rw [nonFreeCount_nil]; exact Nat.zero_le 10
      · rw [nonFreeCount_rustAllocEvents]; decide
    · rw [nonFreeCount_nil]; exact Nat.zero_le 10
    · exact cliIoReadSchedule9_nonFreeCount bs.length
    · rw [nonFreeCount_append, nonFreeCount_rustDeallocEvents, Nat.add_zero]
      exact cliIoReadSchedule9_nonFreeCount 2097152

private theorem readFile_rule_phaseGroup (rd : ReadRule) (files : FsFiles)
    (path : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (ReadFileRuleEnv rd files path) 1966080 :=
  (PhaseGroupSpec.of_nonFreeBound fineCostModel
    (readFile_rule_nonFreeBound rd files path)).mono (by decide)

private theorem decimal_phaseGroup (n : BitVec 32) :
    PhaseGroupSpec fineCostModel (CliDecimalEnv n) 196608 := by
  have hex : PhaseGroupSpec fineCostModel
      (fun evs => ∃ cap : Nat, (CryptoVerification.SignalSession.Cli.decimalText n.toNat).length ≤ cap ∧
        cap ≤ 32 ∧ SeqEnv (· = rustAllocEvents cap 1) FreeOnlyEvs evs) 196608 :=
    { groups_le := fun st0 {_} ⟨cap, _, _, hs⟩ =>
        (((PhaseGroupSpec.rustAlloc_any fineCostModel cap 1).seq
          (PhaseGroupSpec.freeOnly fineCostModel)).mono (by decide)).groups_le st0 hs }
  exact ((PhaseGroupSpec.nil fineCostModel).or hex).mono (by decide)

private theorem path_else_phaseGroup (cap0 cap1 capFinal : Nat) (need2 : Bool) :
    PhaseGroupSpec fineCostModel
      (ConcatEnv
        (ConcatEnv (· = rustAllocEvents cap0 1) (· = rustReallocEvents cap0 cap1 1))
        (if need2 then (· = rustReallocEvents cap1 capFinal 1) else (· = [])))
      589824 := by
  have s0 := PhaseGroupSpec.rustAlloc_any fineCostModel cap0 1
  have s1 := PhaseGroupSpec.rustRealloc_any fineCostModel cap0 cap1 1
  have s2 : PhaseGroupSpec fineCostModel
      (if need2 then (· = rustReallocEvents cap1 capFinal 1) else (· = [])) 196608 := by
    cases need2
    · exact (PhaseGroupSpec.nil fineCostModel).mono (by decide)
    · exact (PhaseGroupSpec.rustRealloc_any fineCostModel cap1 capFinal 1).mono (by decide)
  exact ((s0.concat s1).concat s2).mono (by decide)

private theorem path_phaseGroup (dir name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (CliPathEnv dir name) 589824 := by
  by_cases hdir : dir = []
  · exact ((allocBytes1_phaseGroup name).mono (by decide)).of_imp fun _ h => by
      simpa only [CliPathEnv, hdir, ↓reduceIte] using h
  · let cap0 := dir.length
    let cap1 := CryptoVerification.LibsignalTripleRatchet.reserveCap cap0 cap0 1
    let need2 := decide (cap1 - (cap0 + 1) < name.length)
    let capFinal := if need2 then
        CryptoVerification.LibsignalTripleRatchet.reserveCap cap1 (cap0 + 1) name.length
      else cap1
    exact (path_else_phaseGroup cap0 cap1 capFinal need2).of_imp fun _ h => by
      simpa only [CliPathEnv, hdir, ↓reduceIte] using h

private theorem dirGet_rule_phaseGroup (rd : ReadRule) (files : FsFiles)
    (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (CliDirGetEnv (ReadFileRuleEnv rd) files dir name) 2555904 := by
  have hhit : PhaseGroupSpec fineCostModel
      (fun evs => ∃ k v, (k, v) ∈ dir.changed ∧ k = name ∧ evs = allocBytes1Events v) 2555904 :=
    { groups_le := fun st0 {_} ⟨_, v, _, _, heq⟩ =>
        ((allocBytes1_phaseGroup v).mono (by decide)).groups_le st0 heq }
  have hmiss : PhaseGroupSpec fineCostModel
      (SeqEnv (CliPathEnv dir.path name)
        (SeqEnv (ReadFileRuleEnv rd files (pathOf dir.path name)) FreeOnlyEvs)) 2555904 :=
    ((path_phaseGroup dir.path name).seq
      ((readFile_rule_phaseGroup rd files (pathOf dir.path name)).seq
        (PhaseGroupSpec.freeOnly fineCostModel))).mono (by decide)
  exact (hhit.or hmiss).mono (by decide)

private theorem dirPutStr_phaseGroup (dir : DirGhost) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (CliDirPutStrEnv dir name bytes) 393216 :=
  ((allocBytes1_phaseGroup name).seq (dirPut_phaseGroup dir name bytes)).mono (by decide)

private theorem boundedRustEvs32_phaseGroup :
    PhaseGroupSpec fineCostModel (BoundedRustEvs 32 8192) 6291456 := by
  have hnf : NonFreeBound (BoundedRustEvs 32 8192) 32 :=
    fun evs h => Nat.le_trans (nonFreeCount_le_length evs) h.1
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by decide)

theorem cliSessLoadPoll_phaseGroupSpec
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {dir : DirGhost} {peer : AddrGhost} {g_deser : Nat}
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser) :
    PhaseGroupSpec fineCostModel (CliSessLoadPollEnv rd DeserEnv files dir peer)
      (2752512 + g_deser) := by
  unfold CliSessLoadPollEnv
  have h1 := addrText_phaseGroup peer
  have h2 := dirGet_rule_phaseGroup rd files dir (addressText peer.val)
  have h3_ex : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ bs : List (BitVec 8), bs.length ≤ 2097152 ∧ DeserEnv bs evs') g_deser :=
    phaseGroupSpec_exists_guarded hDeser
  have h3 : PhaseGroupSpec fineCostModel
      (fun evs' => evs' = [] ∨ ∃ bs : List (BitVec 8), bs.length ≤ 2097152 ∧ DeserEnv bs evs')
      g_deser :=
    ((PhaseGroupSpec.nil fineCostModel).or h3_ex).mono (Nat.le_of_eq (Nat.zero_max g_deser))
  have h3f := (h3.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero g_deser))
  refine (h1.seq (h2.seq h3f)).mono ?_
  rw [← Nat.add_assoc 196608 2555904 g_deser, show 196608 + 2555904 = 2752512 by decide]

theorem cliSmallStorePoll_phaseGroupSpec
    (rd : ReadRule) (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (CliSmallStorePollEnv rd files dir name) 9437184 := by
  unfold CliSmallStorePollEnv
  have h1 := decimal_phaseGroup 0#32
  have h2 := dirGet_rule_phaseGroup rd files dir name
  have h3 := boundedRustEvs32_phaseGroup
  have h4 := (dirPutStr_phaseGroup dir name []).seq (PhaseGroupSpec.freeOnly fineCostModel)
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by decide)

theorem cliSessStorePoll_exists_dom_phaseGroupSpec
    {dir : DirGhost} {peer : AddrGhost} {r : SessionRecord (List (BitVec 8))} {pqCap : Nat}
    (hDom : ∀ ses, r.currentSession = some ses → SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel
      (fun evs => ∃ g : RecordGhost, RecordGhostValid g r ∧ CliSessStorePollEnv dir peer g r evs)
      173471280 := by
  refine phaseGroupSpec_exists_guarded fun g hgv => ?_
  refine sessStorePoll_dom_phaseGroup (pqCap := pqCap) fun G ses hg hr => ?_
  unfold RecordGhostValid at hgv
  rw [hg, hr] at hgv
  exact ⟨hgv, hDom ses hr⟩

theorem fromKeyReady_phaseGroupSpec {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {x : DecryptGhost} {rec' : SessionRecord (List (BitVec 8))} {k : IdentityKey}
    {g_tr g_sv g_st : Nat}
    (hTrust : PhaseGroupSpec fineCostModel (ikitEnv.trustPollEnv ist0 x.rem.val k .receiving) g_tr)
    (hSave : PhaseGroupSpec fineCostModel
      (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true)) x.rem.val k)
      g_sv)
    (hStore : PhaseGroupSpec fineCostModel (kitEnv.storePollEnv st0 x.rem.val rec') g_st) :
    let g_tr_step := 196608 + g_tr
    let g_sv_step := 196608 + g_sv
    let g_st_step := 196608 + g_st
    PhaseGroupSpec fineCostModel (FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)
      (g_tr_step + max 196608 (g_sv_step + g_st_step)) := by
  intro g_tr_step g_sv_step g_st_step
  have hTrStep : PhaseGroupSpec fineCostModel
      (TrustStepEnv ikit ikitEnv ist0 x.rem.val k .receiving) g_tr_step :=
    (boxAlloc_phaseGroup ikit.trustBoxSize).seq
      ((hTrust.seq (PhaseGroupSpec.rustDealloc fineCostModel ikit.trustBoxSize 8)).mono
        (Nat.le_of_eq (Nat.add_zero g_tr)))
  have hSvStep : PhaseGroupSpec fineCostModel
      (SaveStepEnv ikit ikitEnv
        (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true)) x.rem.val k) g_sv_step :=
    (boxAlloc_phaseGroup ikit.saveBoxSize).seq
      ((hSave.seq (PhaseGroupSpec.rustDealloc fineCostModel ikit.saveBoxSize 8)).mono
        (Nat.le_of_eq (Nat.add_zero g_sv)))
  have hStStep : PhaseGroupSpec fineCostModel
      (StoreStepEnv kit kitEnv st0 x.rem.val rec') g_st_step :=
    (boxAlloc_phaseGroup kit.storeBoxSize).seq
      ((hStore.seq (PhaseGroupSpec.rustDealloc fineCostModel kit.storeBoxSize 8)).mono
        (Nat.le_of_eq (Nat.add_zero g_st)))
  have hStoreCall : PhaseGroupSpec fineCostModel
      (FromStoreCallEnv kit kitEnv st0 x.rem.val rec') g_st_step :=
    (hStStep.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (Nat.le_of_eq (Nat.add_zero g_st_step))
  have hFalse : PhaseGroupSpec fineCostModel (FromTrustedFalseEnv x) 196608 :=
    ((stringClone_phaseGroup x.rem.name).seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (by decide)
  have hTrueTail : PhaseGroupSpec fineCostModel
      (fun evs => FreeOnlyEvs evs ∨ FromStoreCallEnv kit kitEnv st0 x.rem.val rec' evs)
      g_st_step :=
    ((PhaseGroupSpec.freeOnly fineCostModel).or hStoreCall).mono
      (Nat.le_of_eq (Nat.zero_max g_st_step))
  have hTrue := hSvStep.seq hTrueTail
  have hCont : PhaseGroupSpec fineCostModel
      (fun evs => FreeOnlyEvs evs ∨ FromTrustedFalseEnv x evs ∨
        FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs)
      (max 196608 (g_sv_step + g_st_step)) :=
    ((PhaseGroupSpec.freeOnly fineCostModel).or (hFalse.or hTrue)).mono
      (Nat.le_of_eq (Nat.zero_max _))
  exact hTrStep.seq hCont

private theorem withStoresDec_group_finish
    {P : List AllocEvent → Prop} {g_ld_step g_rd g_kr : Nat}
    (h : PhaseGroupSpec fineCostModel P
      (g_ld_step + (0 + max 0 (max 196608 (max 196608 (g_rd + g_kr)))))) :
    PhaseGroupSpec fineCostModel P (g_ld_step + max 196608 (g_rd + g_kr)) := by
  refine h.mono ?_
  rw [Nat.zero_add, Nat.zero_max, ← Nat.max_assoc 196608 196608 (g_rd + g_kr), Nat.max_self 196608]

theorem withStoresDec_phaseGroupSpec {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    {g_ld g_rd g_tr g_sv g_st : Nat}
    (hLoad : PhaseGroupSpec fineCostModel (kitEnv.loadPollEnv st0 x.rem.val) g_ld)
    (hRecDec : ∀ rec ses G,
      kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      PhaseGroupSpec fineCostModel (RecordDecryptEnv tdEnv (recGhostOf x 0#64 G ses.state)) g_rd)
    (hTrust : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseGroupSpec fineCostModel (ikitEnv.trustPollEnv ist0 x.rem.val k .receiving) g_tr)
    (hSave : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseGroupSpec fineCostModel
        (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true))
          x.rem.val k) g_sv)
    (hStore : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseGroupSpec fineCostModel (kitEnv.storePollEnv st0 x.rem.val rec') g_st) :
    let g_ld_step := 196608 + g_ld
    let g_tr_step := 196608 + g_tr
    let g_sv_step := 196608 + g_sv
    let g_st_step := 196608 + g_st
    let g_kr := g_tr_step + max 196608 (g_sv_step + g_st_step)
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      (g_ld_step + max 196608 (g_rd + g_kr)) := by
  intro g_ld_step g_tr_step g_sv_step g_st_step g_kr
  have hLdStep : PhaseGroupSpec fineCostModel (LoadPollStepEnv kit kitEnv st0 x.rem.val)
      g_ld_step :=
    (boxAlloc_phaseGroup kit.loadBoxSize).seq hLoad
  have hArm2 : PhaseGroupSpec fineCostModel (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs)
      196608 :=
    ((stringClone_phaseGroup x.rem.name).seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (by decide)
  have hArm3 := fromRegionNone_phaseGroup
  have hArm4 : PhaseGroupSpec fineCostModel
      (fun evs => ∃ rec ses G,
        kit.ScopeAt Scope st0 x.rem.val rec ∧
        rec.currentSession = some ses ∧
        SessionGhostValid G ses ∧
        FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 x rec G ses.state evs)
      (g_rd + g_kr) := by
    have hEx : PhaseGroupSpec fineCostModel
        (fun evs =>
          ∃ p : SessionRecord (List (BitVec 8)) × Session (List (BitVec 8)) × SessionGhost,
            (kit.ScopeAt Scope st0 x.rem.val p.1 ∧
              p.1.currentSession = some p.2.1 ∧
              SessionGhostValid p.2.2 p.2.1) ∧
            FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0
              x p.1 p.2.2 p.2.1.state evs)
        (g_rd + g_kr) := by
      refine phaseGroupSpec_exists_guarded fun ⟨rec, ses, G⟩ ⟨hsc, hcur, hgv⟩ => ?_
      have hexKrTuple : PhaseGroupSpec fineCostModel
          (fun evs' =>
            ∃ q : List (BitVec 8) × SessionRecord (List (BitVec 8)) ×
                Session (List (BitVec 8)) × IdentityKey,
              (decryptRecord C S parse x rec = .ok (q.1, q.2.1) ∧
                q.2.1.currentSession = some q.2.2.1 ∧
                q.2.2.1.state.remoteIdentity = some q.2.2.2) ∧
              FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x q.2.1 q.2.2.2 evs')
          g_kr :=
        phaseGroupSpec_exists_guarded fun ⟨pt, rec', ses', k⟩ ⟨hdec, hc', hk⟩ =>
          fromKeyReady_phaseGroupSpec
            (hTrust rec pt rec' ses' k hsc hdec hc' hk)
            (hSave rec pt rec' ses' k hsc hdec hc' hk)
            (hStore rec pt rec' ses' k hsc hdec hc' hk)
      have hexKr : PhaseGroupSpec fineCostModel
          (fun evs' => ∃ pt rec' ses' k,
            decryptRecord C S parse x rec = .ok (pt, rec') ∧
            rec'.currentSession = some ses' ∧
            ses'.state.remoteIdentity = some k ∧
            FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs')
          g_kr :=
        hexKrTuple.of_imp
          (fun _ ⟨pt, rec', ses', k, hdec, hc', hk, hfe⟩ =>
            ⟨(pt, rec', ses', k), ⟨hdec, hc', hk⟩, hfe⟩)
      have hPostSome : PhaseGroupSpec fineCostModel
          (FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec) g_kr :=
        ((PhaseGroupSpec.freeOnly fineCostModel).or hexKr).mono
          (Nat.le_of_eq (Nat.zero_max g_kr))
      exact (hRecDec rec ses G hsc hcur hgv).seq hPostSome
    exact hEx.of_imp
      (fun _ ⟨rec, ses, G, hsc, hcur, hgv, hf⟩ => ⟨(rec, ses, G), ⟨hsc, hcur, hgv⟩, hf⟩)
  have hBranches := (PhaseGroupSpec.freeOnly fineCostModel).or
    (hArm2.or (hArm3.or hArm4))
  have hFromLoad := (PhaseGroupSpec.rustDealloc fineCostModel kit.loadBoxSize 8).seq hBranches
  exact withStoresDec_group_finish (hLdStep.seq hFromLoad)

private theorem cliSlot_group_bound {g_deser g_td : Nat} :
    (196608 + (2752512 + g_deser)) +
      max 196608 ((173274672 + g_td) +
        ((196608 + 9437184) + max 196608 ((196608 + 9437184) + (196608 + 173471280)))) ≤
      369159264 + g_deser + g_td := by
  have hkr : (196608 + 9437184) + max 196608 ((196608 + 9437184) + (196608 + 173471280)) =
      192935472 := by decide
  rw [hkr]
  have hld : 196608 + (2752512 + g_deser) = 2949120 + g_deser := by
    rw [← Nat.add_assoc 196608 2752512 g_deser, show 196608 + 2752512 = 2949120 by decide]
  rw [hld]
  have hrd : (173274672 + g_td) + 192935472 = 366210144 + g_td := by
    rw [Nat.add_assoc 173274672 g_td 192935472,
        Nat.add_comm g_td 192935472,
        ← Nat.add_assoc 173274672 192935472 g_td,
        show 173274672 + 192935472 = 366210144 by decide]
  rw [hrd]
  have hmax : max 196608 (366210144 + g_td) = 366210144 + g_td :=
    Nat.max_eq_right (Nat.le_trans (by decide : 196608 ≤ 366210144) (Nat.le_add_right _ g_td))
  rw [hmax]
  have htot : (2949120 + g_deser) + (366210144 + g_td) = 369159264 + g_deser + g_td := by
    rw [Nat.add_assoc 2949120 g_deser (366210144 + g_td),
        ← Nat.add_assoc g_deser 366210144 g_td,
        Nat.add_comm g_deser 366210144,
        Nat.add_assoc 366210144 g_deser g_td,
        ← Nat.add_assoc 2949120 366210144 (g_deser + g_td),
        show 2949120 + 366210144 = 369159264 by decide,
        ← Nat.add_assoc 369159264 g_deser g_td]
  exact Nat.le_of_eq htot

/-- `PhaseGroupSpec fineCostModel` for CLI W2 (`StoresGhost.opened`) `WithStoresDecEnv`. -/
theorem w2CliDecryptSlot_polls_phaseGroupSpec {A : RustAlloc}
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (C : Crypto) (K : MlKem) (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {Kspqr fileCap g_deser g_td : Nat}
    (hrem : x.rem.val = peer.val)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hStoreEq : ∀ rec' evs,
      scopeKit rec' →
      kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec' evs →
      ∃ g : RecordGhost, RecordGhostValid g rec' ∧
        CliSessStorePollEnv StoresGhost.opened.sessions peer g rec' evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseGroupSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        g_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (369159264 + g_deser + g_td) := by
  intro kit ikit
  have hLoadPoll : PhaseGroupSpec fineCostModel
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val) (2752512 + g_deser) :=
    (cliSessLoadPoll_phaseGroupSpec hDeser).of_imp hLoadEq
  have hSmallId : PhaseGroupSpec fineCostModel
      (CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName)
      9437184 :=
    cliSmallStorePoll_phaseGroupSpec cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName
  refine (withStoresDec_phaseGroupSpec
    (kit := kit) (kitEnv := kitEnv) (st0 := StoresGhost.opened.sessions)
    (ikit := ikit) (ikitEnv := ikitEnv) (ist0 := StoresGhost.opened.identity)
    hLoadPoll
    (fun rec ses G hsc hcur hgv => by
      have hIn : scopeIn rec :=
        (cliSess_scopeIn_of_opened (fun _ h => h) hFilesOk hrem hsc).2
      obtain ⟨hPqFile, hDom⟩ := opened_scopeAt_sessionCloneDom hrem hSessFileCap hsc hcur
      obtain ⟨hVe, hVcp, hPqLt31⟩ :=
        peerSpqrTightValidAt_of_cliSessionStoreSpec hsc hcur rfl hValid
      exact recordDecrypt_dom_phaseGroup
        (x := recGhostOf x 0#64 G ses.state) (ses := ses) rfl hgv hDom
        (fun G₁ hRel => hTd rec ses G G₁ hIn hcur hgv hDom hRel hVe hVcp hPqLt31 hPqFile))
    (fun _ _ _ _ k _ _ _ _ => hSmallId.of_imp (hTrustEq k))
    (fun _ _ _ _ k _ _ _ _ => hSmallId.of_imp (hSaveEq k))
    (fun rec _ rec' ses' _ hsc hdec hc' _ => by
      have hIn : scopeIn rec :=
        (cliSess_scopeIn_of_opened (fun _ h => h) hFilesOk hrem hsc).2
      have hEncPre : (encodeRecord rec).length ≤ fileCap :=
        opened_scopeAt_encodeRecord_le hrem hSessFileCap hsc
      obtain ⟨hKit', hPostDom, _⟩ := decryptRecord_post_caps_of_scopeIn hIn hEncPre hdec
      obtain ⟨_, hDomPost⟩ := hPostDom ses' hc'
      exact (cliSessStorePoll_exists_dom_phaseGroupSpec
        (pqCap := fileCap + 1128000)
        (fun s hs => by rw [hc'] at hs; injection hs with hs; subst hs; exact hDomPost)).of_imp
        (fun evs h => hStoreEq rec' evs hKit' h))).mono cliSlot_group_bound

theorem w2CliDecryptSlot_polls_tight640_phaseGroupSpec {A : RustAlloc}
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (C : Crypto) (K : MlKem) (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {fileCap g_deser g_td : Nat}
    (hrem : x.rem.val = peer.val)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValid640 F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hStoreEq : ∀ rec' evs,
      scopeKit rec' →
      kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec' evs →
      ∃ g : RecordGhost, RecordGhostValid g rec' ∧
        CliSessStorePollEnv StoresGhost.opened.sessions peer g rec' evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPts640 ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseGroupSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        g_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (369159264 + g_deser + g_td) :=
  w2CliDecryptSlot_polls_phaseGroupSpec F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
    C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hFilesOk hValid hSessFileCap hDeser hLoadEq hTrustEq hSaveEq hStoreEq hTd

end TightCliW2Slot

end LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
