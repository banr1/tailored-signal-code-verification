/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhE
import VCVio.EvalDist.Monad.Basic

@[expose] public section

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh

open _root_.SignalPqxdh.Security.FgGapDh

theorem fgStepCoupling_dh3_acceptOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.acceptOPK k j o hdr)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.acceptOPK k j o hdr) st >>= k2] {true} := by
  let R := FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hTakePrin : st.base.principals.take S.N_dh = hst.base.principals := by
    rw [hBaseEq]; exact List.take_of_length_le hLengths.1
  have hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk := by
    rw [hBaseEq]
    exact koskSenderOkTake_eq_koskSenderOk S P hst.base.principals st.advKeyPows
      hst.base.advKeys hdr.ikAPk hLengths.1 hAdvEq.2.1
  refine fgAcceptOPK_coupling R hP (fun _ e => e) (eraseSpkBundleEntryFg S bIdx)
    hCache hFgLen hValidEc hAdvEq hPrins hOpks
    (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl) hKoskEq
    (by rw [hBaseEq, option_map_prod_id]; rfl)
    (by rw [hBaseEq]; exact find?_idx_eraseSpkBundlesFg S bIdx (k.val, j.val) hst.base.spkBundles)
    (fun _ _ => rfl) (eraseSpkBundleEntryFg_pqspkSk S bIdx)
    (eraseSpkBundleEntryFg_spkPk S bIdx) (eraseSpkBundleEntryFg_pqspkPk S bIdx)
    (by rw [hTakePrin])
    (fun rInit => by
      rw [hBaseEq]; exact choosePartnerDrKeyRandPure_eraseSessionsFg P sIdx hst.base.sessions rInit)
    (fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont)
    (fun k0 kEntry kb0 bEntry hkMem hbMem hIkOnCurve hEkOnCurve => ?_)
    (fun r rEntry roCache' fgL' hValidEc' hOpks' hCache' hFgLen' => ?_)
  · refine ⟨computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
        hdr.ikAPk (hSpks (kb0, bEntry) hbMem) hIkOnCurve, ?_,
      computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
        hdr.ekAPk (hSpks (kb0, bEntry) hbMem) hEkOnCurve⟩
    rw [computeTwoSideOrPairPosPure_nil_right_len32 P kEntry.secIKA0 hdr.ekAPk
      kEntry.ikAPk (hPrins (k0, kEntry) hkMem).1]
    exact R.sec2 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
  · apply hCont r
    · rw [deadDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl]; exact hDead
    · exact ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache', hFgLen', by dsimp; omega,
        hValidEc', hSpkV, hPrins, hSpks, hOpks', hSess⟩


theorem checkBundleProvenanceTake_eq_checkBundleProvenance (S : Setup) (P : Primitives)
    (bIdx : ℕ) (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput)
    (hP : principals.length ≤ S.N_dh)
    (hS : spkBundles.length ≤ S.N_dh)
    (hO : opkEntries.length ≤ S.N_dh) :
    checkBundleProvenanceTake S P principals (eraseSpkBundlesFg S bIdx spkBundles) opkEntries bundle
      =
      checkBundleProvenance P principals spkBundles opkEntries bundle := by
  have hS' : (eraseSpkBundlesFg S bIdx spkBundles).length ≤ S.N_dh := by
    rw [eraseSpkBundlesFg_length]; exact hS
  unfold checkBundleProvenanceTake
  rw [List.take_of_length_le hP, List.take_of_length_le hS', List.take_of_length_le hO]
  exact checkBundleProvenance_eraseSpkBundlesFg P S bIdx principals spkBundles opkEntries bundle

theorem computeOptPosPure_left_len32_fgOptLeftRep (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (uSk ekASk ekAPk : Bytes) (hLen : ekASk.length = 32)
    (opkB? : Option (UInt32 × Bytes)) :
    FgOptLeftRep P uSk
      (computeOptPosPure P ekASk ekAPk (opkB?.map (fun (_, opkPk) => ([], opkPk))))
      (opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
  cases opkB? with
  | none => trivial
  | some p =>
    rcases p with ⟨opkId, opkPk⟩
    dsimp only [Option.map, computeOptPosPure]
    rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk opkPk hLen]
    exact ⟨hWF.x25519_len ekASk opkPk, Or.inl rfl⟩

theorem computeOptPosPure_nil_uSk_fgOptLeftRep (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (uSk : Bytes) (opkB? : Option (UInt32 × Bytes))
    (hopk : match opkB? with | none => True | some (_, opkPk) => onCurveKeyLocal P opkPk) :
    FgOptLeftRep P uSk
      (computeOptPosPure P [] (P.x25519Base uSk) (opkB?.map (fun (_, opkPk) => ([], opkPk))))
      (opkB?.map (fun (_, opkPk) => P.x25519 uSk opkPk)) := by
  cases opkB? with
  | none => trivial
  | some p =>
    rcases p with ⟨opkId, opkPk⟩
    dsimp only [Option.map, computeOptPosPure, computeTwoSideOrPairPosPure_nil_nil]
    exact fgPosLeftRep_mkPair_left P hWF uSk opkPk hopk

theorem fgStepCoupling_dh3_initiate (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (hSend : IsSendSessionId S sid)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadCont : ∀ r hst', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(do
        let x ← (fgPreInitiate false sIdx (some uSk) S P sid u bundle).run hst.base
        k1 (x.1, { base := x.2, advRoLog := hst.advRoLog }))] {true} ≤
      𝒟[fgRunInitiatePure P P.isValidDhTriple false sIdx S b.q_total
          (P.x25519Base uSk) sid u bundle st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hRespLen := validKeyIndEc_resp_length_le_fg S hst.base hValidEc
  have hAnyEq : st.base.sessions.any (fun e => e.sid == sid) =
      hst.base.sessions.any (fun e => e.sid == sid) := by
    rw [hBaseEq]; exact any_sid_eraseSessionsFg sIdx sid hst.base.sessions
  have hPrinEq : st.base.principals = hst.base.principals := by rw [hBaseEq]; rfl
  have hSpkEq : st.base.spkBundles = eraseSpkBundlesFg S bIdx hst.base.spkBundles :=
    by rw [hBaseEq]; rfl
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := by rw [hBaseEq]; rfl
  have hRespEq : st.base.respSessions = hst.base.respSessions := by rw [hBaseEq]; rfl
  have hTakePrin : hst.base.principals.take S.N_dh = hst.base.principals :=
    List.take_of_length_le hLengths.1
  have hKoskEq : koskBundleOkTake S P hst.base.principals (eraseSpkBundlesFg S bIdx
      hst.base.spkBundles)
      hst.base.opkEntries st.advKeyPows bundle =
      koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries hst.base.advKeys
        bundle :=
    koskBundleOkTake_eraseSpk_eq S P bIdx hst.base.principals hst.base.spkBundles
      hst.base.opkEntries
      st.advKeyPows hst.base.advKeys bundle hLengths.1 hLengths.2.1 hLengths.2.2.1 hAdvEq.2.1
  have hProvEq : checkBundleProvenanceTake S P hst.base.principals (eraseSpkBundlesFg S bIdx
      hst.base.spkBundles) hst.base.opkEntries bundle =
      checkBundleProvenance P hst.base.principals hst.base.spkBundles hst.base.opkEntries bundle :=
    checkBundleProvenanceTake_eq_checkBundleProvenance S P bIdx
      hst.base.principals hst.base.spkBundles hst.base.opkEntries bundle
      hLengths.1 hLengths.2.1 hLengths.2.2.1
  unfold fgPreInitiate fgRunInitiatePure
  simp only [StateT.run_bind, StateT.run_get, hAnyEq, hPrinEq, hSpkEq, hOpkEq, hRespEq, hTakePrin,
    hKoskEq,
    Bool.not_false, Bool.true_and, pure_bind]
  cases hAny : hst.base.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hAnyMap : ((sessPksKeyInd S hst.base).map Prod.fst).any (fun s => s == sid) = false := by
      simp [sessPksKeyInd, List.any_map, Function.comp_def, hAny]
    have hValidSess' : ValidSessionIds S (sid :: (sessPksKeyInd S hst.base).map Prod.fst) :=
      (validSessionIds_cons S sid ((sessPksKeyInd S hst.base).map Prod.fst) hSend hValidEc.2.2.2.1
        hAnyMap).1
    cases hFU : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
        .noneResp k1 k2 hCont
    | some pu =>
      rcases pu with ⟨u0, uEntry⟩
      dsimp only
      have huMem := List.mem_of_find?_eq_some hFU
      rcases hPrins (u0, uEntry) huMem with ⟨huSkLen, huPk⟩
      by_cases hKosk : (!koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
        hst.base.advKeys bundle) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]
        exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
          hInv0 .noneResp k1 k2 hCont
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        by_cases hTgt : (initSessionSlotIdx sid == sIdx) = true
        · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
            bind_assoc, pure_bind, evalDist_sampleScalar32_const]
          refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun kemCoins _ => ?_)
          by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC
               bundle.spkB) bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                 bundle.pqspkSig)) = true
          · simp only [hSig, ↓reduceIte, StateT.run_pure, pure_bind]
            exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
              hInv0 .noneResp k1 k2 hCont
          · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
            cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              simp only [StateT.run_pure, pure_bind]
              exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              dsimp only
              by_cases hPowV : (P.pow8 bundle.spkB == P.pow8 (P.x25519Base vSk)) = true
              · have hPowEq : P.pow8 bundle.spkB = P.pow8 (P.x25519Base vSk) := beq_iff_eq.mp hPowV
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 uSk bundle.ikB
                let dh3 := P.x25519 uSk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 uSk opkPk)
                let spkSk :=
                  lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx hst.base.spkBundles) st.advKeyPows
                  bundle.spkB
                let pos1 :=
                  computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB
                let pos2 := computeTwoSideOrPairPosPure P [] [] (P.x25519Base uSk) bundle.ikB
                let pos3 := computeTwoSideOrPairPosPure P [] [] (P.x25519Base uSk) bundle.spkB
                let pos4? := computeOptPosPure P [] (P.x25519Base uSk) (bundle.opkB?.map (fun (_,
                  opkPk) => ([], opkPk)))
                have hPos1 : FgPosRightRep P vSk pos1 dh1 := by
                  dsimp only [pos1, dh1]
                  rw [computeTwoSideOrPairPosPure_left_len32 P uEntry.secIKA0 spkSk uEntry.ikAPk
                    bundle.spkB huSkLen]
                  exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec1 _
                    (hP.toWellFormedPrimitivesδ.x25519_len _ _)
                have hBundleOnCurve :=
                  onCurveKeyLocal_of_koskBundleOk P hst.base.principals hst.base.spkBundles
                    hst.base.opkEntries hst.base.advKeys bundle
                    hPrins hOpks hAdvEq.2.2 hKosk
                have hPos2 : FgPosLeftRep P uSk pos2 dh2 := by
                  dsimp only [pos2, dh2, computeTwoSideOrPairPosPure_nil_nil]
                  exact fgPosLeftRep_mkPair_left P hP.toWellFormedPrimitivesδ uSk bundle.ikB
                    hBundleOnCurve.1
                have hPos3 : FgPosRightRep P vSk pos3 dh3 := by
                  dsimp only [pos3, dh3, computeTwoSideOrPairPosPure_nil_nil]
                  exact fgPosRightRep_mkPair_left_of_pow8 P hP.toWellFormedPrimitivesδ uSk vSk
                    bundle.spkB huSk hvSk (hP.pow8_base_len bundle.spkB vSk hPowEq) hPowEq
                have hPos4 : FgOptLeftRep P uSk pos4? dh4? :=
                  computeOptPosPure_nil_uSk_fgOptLeftRep P hP.toWellFormedPrimitivesδ uSk
                    bundle.opkB? hBundleOnCurve.2
                have hSsLen : ss.length = 32 :=
                  (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _ hEnc).1
                have hTup : FgTupleRel (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk) pos1 pos2 pos3
                  pos4? dh1 dh2 dh3 dh4? ss :=
                  ⟨hPos1, hPos2, hPos3, hPos4, hSsLen⟩
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  bind_assoc, pure_bind]
                refine fgPatchPure_bind_le (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk) hCache hFgLen hTup
                  (fun drKeyReal roCache' fgL' hCache' hFgLen' => ?_)
                rw [chooseInitPartnerDrKeyRand_eq_pure P hst.base.respSessions _ _ hRespLen]
                refine evalDist_bind_true_mono_of_support (chooseInitPartnerDrKeyRandPure P
                  hst.base.respSessions _) _ _ (fun drKeyRand _ => ?_)
                cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
                  simp only [Option.map, StateT.run_pure, pure_bind]
                all_goals
                  apply hCont
                  · unfold deadDh3; unfold spkTargetIsV at hSpkV ⊢
                    simp [hTgt, hPowEq]
                  · refine ⟨?_, hAdvEq, hCache', hFgLen', by dsimp; omega,
                      ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess', hValidEc.2.2.2.2⟩,
                      hSpkV, hPrins, hSpks, hOpks, ?_⟩
                    · rw [hBaseEq]; simp [eraseStateFg, eraseSessionsFg, eraseSessionEntryFg,
                        beq_iff_eq.mp hTgt, hProvEq]
                    · intro s hs
                      rcases List.mem_cons.mp hs with rfl | hMem
                      · exact ⟨huSk, rfl, fun _ => rfl⟩
                      · exact hSess s hMem
              ·
                have hPowNe : (P.pow8 bundle.spkB != P.pow8 (P.x25519Base vSk)) = true := by
                  simpa [bne] using hPowV
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  bind_assoc, pure_bind]
                refine le_trans (le_of_eq ?_) zero_le
                refine evalDist_bind_true_eq_zero_of_support _ _ (fun ⟨drKeyReal, roCache'⟩ _ => ?_)
                refine evalDist_bind_true_eq_zero_of_support _ _ (fun drKeyRand _ => ?_)
                cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
                  simp only [Option.map, StateT.run_pure, pure_bind]
                all_goals
                  apply hDeadCont
                  unfold deadDh3; unfold spkTargetIsV at hSpkV ⊢
                  simp [hSpkV, hTgt, hPowNe]
        ·
          have hTgtF : (initSessionSlotIdx sid == sIdx) = false := Bool.eq_false_iff.mpr hTgt
          simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_self, bind_assoc, pure_bind]
          refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ekASk hEk => ?_)
          have hEkLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32 hEk
          refine evalDist_bind_true_mono_of_support sampleCoins32 _ _ (fun kemCoins _ => ?_)
          by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC
               bundle.spkB) bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                 bundle.pqspkSig)) = true
          · simp only [hSig, ↓reduceIte, StateT.run_pure, pure_bind]
            exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
              hInv0 .noneResp k1 k2 hCont
          · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
            cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              simp only [StateT.run_pure, pure_bind]
              exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st
                hDead hInv0 .noneResp k1 k2 hCont
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              dsimp only
              let ekAPk := P.x25519Base ekASk
              let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
              let dh2 := P.x25519 ekASk bundle.ikB
              let dh3 := P.x25519 ekASk bundle.spkB
              let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
              let spkSk :=
                lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx hst.base.spkBundles) st.advKeyPows
                bundle.spkB
              let pos1 :=
                computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB
              let pos2 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.ikB
              let pos3 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.spkB
              let pos4? := computeOptPosPure P ekASk ekAPk (bundle.opkB?.map (fun (_, opkPk) => ([],
                opkPk)))
              have hPos1 : FgPosRightRep P vSk pos1 dh1 := by
                dsimp only [pos1, dh1]
                rw [computeTwoSideOrPairPosPure_left_len32 P uEntry.secIKA0 spkSk uEntry.ikAPk
                  bundle.spkB huSkLen]
                exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec1 _
                  (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos2 : FgPosLeftRep P uSk pos2 dh2 := by
                dsimp only [pos2, dh2]
                rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk bundle.ikB hEkLen]
                exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec2 _
                  (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos3 : FgPosRightRep P vSk pos3 dh3 := by
                dsimp only [pos3, dh3]
                rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk bundle.spkB hEkLen]
                exact (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk).sec3 _
                  (hP.toWellFormedPrimitivesδ.x25519_len _ _)
              have hPos4 : FgOptLeftRep P uSk pos4? dh4? :=
                computeOptPosPure_left_len32_fgOptLeftRep P hP.toWellFormedPrimitivesδ uSk ekASk
                  ekAPk hEkLen bundle.opkB?
              have hSsLen : ss.length = 32 :=
                (hP.toWellFormedPrimitivesδ.kemEncaps_len _ _ _ _ hEnc).1
              have hTup : FgTupleRel (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk) pos1 pos2 pos3 pos4?
                dh1 dh2 dh3 dh4? ss :=
                ⟨hPos1, hPos2, hPos3, hPos4, hSsLen⟩
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                bind_assoc, pure_bind]
              refine fgPatchPure_bind_le (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk) hCache hFgLen hTup
                (fun drKeyReal roCache' fgL' hCache' hFgLen' => ?_)
              rw [chooseInitPartnerDrKeyRand_eq_pure P hst.base.respSessions _ _ hRespLen]
              refine evalDist_bind_true_mono_of_support (chooseInitPartnerDrKeyRandPure P
                hst.base.respSessions _) _ _ (fun drKeyRand _ => ?_)
              cases findHonestPrincipal P hst.base.principals bundle.ikB <;>
                simp only [Option.map, StateT.run_pure, pure_bind]
              all_goals
                apply hCont
                · unfold deadDh3 spkTargetIsV
                  dsimp only [List.find?]
                  rw [hTgtF]
                  exact hDead
                · refine ⟨?_, hAdvEq, hCache', hFgLen', by dsimp; omega,
                    ⟨hValidEc.1, hValidEc.2.1, hValidEc.2.2.1, hValidSess', hValidEc.2.2.2.2⟩,
                    hSpkV, hPrins, hSpks, hOpks, ?_⟩
                  · rw [hBaseEq]; simp [eraseStateFg, eraseSessionsFg, eraseSessionEntryFg,
                      beq_eq_false_iff_ne.mp hTgtF, hProvEq]
                  · intro s hs
                    rcases List.mem_cons.mp hs with rfl | hMem
                    · exact ⟨hEkLen, rfl, fun h => by rw [hTgtF] at h; cases h⟩
                    · exact hSess s hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh3 (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDeadFull : deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hContFull : ∀ r hst' st', deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true})
    (hDeadContFull : ∀ r hst', deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P q).run hst >>= k1] {true} ≤
      𝒟[(fgKeyIndSimImpl P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) q).run st >>= k2] {true} := by
  have hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false :=
    (Bool.or_eq_false_iff.mp hDeadFull).1
  have hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true} := by
    intro r hst' st' hD3 hInv'
    by_cases hRev : spkTargetRevealed bIdx hst' = true
    · rw [hDeadContFull r hst' (by unfold deadDh3Full; simp [hRev])]
      exact zero_le
    · exact hContFull r hst' st' (by unfold deadDh3Full; simp [hD3,
      Bool.eq_false_iff.mpr hRev]) hInv'
  have hDeadCont : ∀ r hst', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0 := by
    intro r hst' hD3
    exact hDeadContFull r hst' (by unfold deadDh3Full; simp [hD3])
  have hRhs : (fgKeyIndSimImpl P P.isValidDhTriple false sIdx bIdx S b.q_total
      (P.x25519Base uSk) (P.x25519Base vSk) q).run st =
      fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) q st := by
    unfold fgKeyIndSimImpl
    simp
  rw [hRhs]
  cases q with
  | initPrin u =>
    exact fgStepCoupling_dh3_initPrin S b P hP sIdx bIdx uSk vSk huSk hvSk u rem hst st hDead hInv
      k1 k2 hCont
  | corruptIK u =>
    exact fgStepCoupling_dh3_corruptIK S b P hP sIdx bIdx uSk vSk huSk hvSk u rem hst st hDead hInv
      k1 k2 hCont
  | genSPK u j =>
    exact fgStepCoupling_dh3_genSPK S b P hP sIdx bIdx uSk vSk huSk hvSk u j rem hst st hDead hInv
      k1 k2 hCont
  | genOPK u j o =>
    exact fgStepCoupling_dh3_genOPK S b P hP sIdx bIdx uSk vSk huSk hvSk u j o rem hst st hDead hInv
      k1 k2 hCont
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl liftFgBase fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgStepCoupling_dh3_initiate S b P hP sIdx bIdx uSk vSk huSk hvSk (.sendOPK u i) trivial
        u bundle rem hst st hDead hInv k1 k2 hCont hDeadCont
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv
        .noneResp k1 k2 hCont
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl liftFgBase fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact fgStepCoupling_dh3_initiate S b P hP sIdx bIdx uSk vSk huSk hvSk (.sendNoOPK u i)
        trivial u bundle rem hst st hDead hInv k1 k2 hCont hDeadCont
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv
        .noneResp k1 k2 hCont
  | acceptOPK k j o hdr =>
    exact fgStepCoupling_dh3_acceptOPK S b P hP sIdx bIdx uSk vSk huSk hvSk k j o hdr rem hst st
      hDead hInv k1 k2 hCont
  | acceptNoOPK k j l hdr =>
    exact fgStepCoupling_dh3_acceptNoOPK S b P hP sIdx bIdx uSk vSk huSk hvSk k j l hdr rem hst st
      hDead hInv k1 k2 hCont
  | testSession sid =>
    exact fgStepCoupling_dh3_testSession S b P hP sIdx bIdx uSk vSk huSk hvSk sid rem hst st hDead
      hInv k1 k2 hCont
  | revealSessionKey sid =>
    exact fgStepCoupling_dh3_revealSessionKey S b P hP sIdx bIdx uSk vSk huSk hvSk sid rem hst st
      hDead hInv k1 k2 hCont
  | roQuery secrets =>
    exact fgStepCoupling_dh3_roQuery S b P hP sIdx bIdx uSk vSk huSk hvSk secrets rem hst st hDead
      hInv k1 k2 hCont
  | revealDhSecrets =>
    exact fgStepCoupling_dh3_revealDhSecrets S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead
      hInv k1 k2 hCont
  | registerKey sk =>
    have hInv0 := hInv
    rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks,
      hOpks, hSess⟩
    refine fgRegisterKey_coupling
      (fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
        .noneResp k1 k2 hCont)
      (fun hSkLen32 => ?_)
    apply hCont (.pkResp (P.x25519Base sk))
    · rw [deadDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl]; exact hDead
    · exact ⟨by rw [hBaseEq]; rfl, fgAdvEq_registerKey hSkLen32 hAdvEq,
        hCache, by dsimp; omega, by dsimp; omega,
        validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hSpkV, hPrins, hSpks, hOpks, hSess⟩
  | revealSpkSk u j =>
    have hInv0 := hInv
    rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks,
      hOpks, hSess⟩
    have hSpkFind : st.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) =
        (hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val))).map
          (fun (idx, b) => (idx, eraseSpkBundleEntryFg S bIdx idx b)) := by
      rw [hBaseEq]; exact find?_idx_eraseSpkBundlesFg S bIdx (u.val, j.val) hst.base.spkBundles
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkFind, bind_assoc, pure_bind]
    cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      dsimp only [Option.map]
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
        .noneResp k1 k2 hCont
    | some kb =>
      rcases kb with ⟨k0, bEntry⟩
      dsimp only [Option.map]
      by_cases hTgt : (spkBundleFlatIdx S u j == bIdx) = true
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        have hRevTrue :=
          spkTargetRevealed_map_revealed_of_eq bIdx u j hTgt hst hValidEc.2.1 k0 bEntry hFB
        rw [hDeadContFull (.spkSkResp bEntry.spkSk) _ (Bool.or_eq_true_iff.mpr (Or.inr hRevTrue))]
        exact zero_le
      · have hTgtF : (spkBundleFlatIdx S u j == bIdx) = false := Bool.eq_false_iff.mpr hTgt
        have hk0 : (k0 == (u.val, j.val)) = true :=
          List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) => x.1 == (u.val, j.val)) hFB
        rw [eraseSpkBundleEntryFg_eq_self_of_ne S bIdx u j hTgtF k0 bEntry hk0]
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        apply hCont (.spkSkResp bEntry.spkSk)
        · unfold deadDh3
          rw [spkTargetIsV_map_revealed]
          exact hDead
        · refine ⟨?_, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
            ⟨hValidEc.1, (validSpkBundles_map_revealed S P (u.val,
              j.val) hst.base.spkBundles hValidEc.2.1).1, hValidEc.2.2⟩,
            by rw [spkTargetIsV_map_revealed]; exact hSpkV, hPrins, ?_, hOpks, hSess⟩
          · rw [hBaseEq]
            dsimp only [eraseStateFg]
            rw [eraseSpkBundlesFg_map_revealed]
          · intro kv hkv
            rcases List.mem_map.mp hkv with ⟨⟨idx, b0⟩, hMem0, hEq0⟩
            have h0 := hSpks (idx, b0) hMem0
            split_ifs at hEq0 <;> subst hEq0 <;> exact h0

/-- Bounds the Case C (`DH3 = CDH(ek_U*, spk_V*)`) bad-event probability at `(sIdx, bIdx)` by the
    `GapDH` advantage of `fgKeyIndGapDhAdvAt false sIdx bIdx S b A`. -/
theorem prob_badKeyIndFgDh3At_le_gapDh (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b)
    (sIdx : ℕ) (hsIdx : sIdx ∈ Finset.range S.N_send_tot)
    (bIdx : ℕ) (_hbIdx : bIdx ∈ Finset.range S.N_spk_tot) :
    (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
        pure (badKeyIndFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdvAt false sIdx bIdx S b A) := by
  have hsLt : sIdx < S.N_send_tot := Finset.mem_range.mp hsIdx
  unfold GapDH
  refine ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim_eq_preSample_dh3 sIdx bIdx P A.1
    (fun x => pure (badKeyIndFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog))]
  rw [gapDhExp_fgKeyIndGapDhAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    QueryBounded.keyInd_total A.2
  exact evalDist_simulateQ_le_of_step_or_dead
    (deadDh3Full P sIdx bIdx (P.x25519Base vSk))
    (FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huLen hvLen)
    (pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P)
    (fgKeyIndSimImpl P P.isValidDhTriple false sIdx bIdx S b.q_total (P.x25519Base uSk)
      (P.x25519Base vSk))
    (fun q s1 hD x hx =>
      pqxdhKeyIndFgPreImpl_preserves_deadDh3Full P sIdx bIdx hsLt uSk vSk q s1 hD x hx)
    (fun q rem s1 s2 hDF hInv k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh3 S b P hP sIdx bIdx uSk vSk huLen hvLen q rem s1 s2 hDF hInv k1 k2 hCont
        hDeadCont)
    (fun x => pure (badKeyIndFgDh3At P b.q_ro sIdx bIdx x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdhFromAdvRoLog P.isValidDhTriple false b.q_total
        (P.x25519Base uSk) (P.x25519Base vSk) x.2.advRoLog) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun a s1 hD =>
      by simp [badKeyIndFgDh3At_eq_false_of_deadDh3Full P b.q_ro sIdx bIdx (P.x25519Base vSk) s1
      hD])
    (fun a rem s1 s2 hDF hInv =>
      fgSimInvDh3_terminal_le S b P hP b.q_ro sIdx bIdx uSk vSk huLen hvLen a rem s1 s2 hDF hInv)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyIndSimState.empty S secb)
    (fgSimInvDh3_empty S b P hP sIdx bIdx uSk vSk huLen hvLen secb)

/-! ## Case A (`DH1`) invariant, step coupling, and union bound -/

def FgSlotReps.ofDh1 (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) : FgSlotReps P where
  Rep1 := FgPosRightRep P vSk
  Rep2 := FgPosRightRep P uSk
  Rep3 := FgPosRightRep P vSk
  Rep4 := FgOptRightRep P vSk
  len1 _ _ h := h.1
  len2 _ _ h := h.1
  len3 _ _ h := h.1
  len4 pos4? dh4? h d hd := by
    subst hd
    cases pos4? with
    | none => exact False.elim h
    | some _ => exact h.1
  eq1 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosRightRep P hP hvSk h1 h2
  eq2 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosRightRep P hP huSk h1 h2
  eq3 _ _ _ _ h1 h2 := ddhEqPure_of_fgPosRightRep P hP hvSk h1 h2
  eq4 _ _ _ _ h1 h2 := ddhEqOptPure_of_fgOptRightRep P hP hvSk h1 h2
  sec1 d hd := ⟨hd, Or.inl rfl⟩
  sec2 d hd := ⟨hd, Or.inl rfl⟩
  sec3 d hd := ⟨hd, Or.inl rfl⟩
  sec4 d? hd := by
    cases d? with
    | none => trivial
    | some d => exact ⟨hd d rfl, Or.inl rfl⟩

theorem computeTwoSideOrPairPosPure_erasePrin_fgPosRightRep
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (uIdx : ℕ)
    (uSk : Bytes) (k : Nat) (kEntry : PrincipalEntry) (pk : Bytes)
    (hk : kEntry.secIKA0.length = 32 ∧ kEntry.ikAPk = P.x25519Base kEntry.secIKA0 ∧
      ((k == uIdx) = true → kEntry.secIKA0 = uSk))
    (hpk : onCurveKeyLocal P pk) :
    FgPosRightRep P uSk
      (computeTwoSideOrPairPosPure P [] (erasePrincipalEntryFg uIdx k kEntry).secIKA0 pk
        kEntry.ikAPk)
      (P.x25519 kEntry.secIKA0 pk) := by
  dsimp only [erasePrincipalEntryFg]
  by_cases hIdx : (k == uIdx) = true
  · have hSk : kEntry.secIKA0 = uSk := hk.2.2 hIdx
    have hPk : kEntry.ikAPk = P.x25519Base uSk := by rw [hk.2.1, hSk]
    simp only [hIdx, ↓reduceIte, computeTwoSideOrPairPosPure_nil_nil, hPk, hSk]
    exact fgPosRightRep_mkPair_right P hP.toWellFormedPrimitivesδ uSk pk hpk
  · have hIdxF : (k == uIdx) = false := Bool.eq_false_iff.mpr hIdx
    simp only [hIdxF, Bool.false_eq_true, ↓reduceIte,
      computeTwoSideOrPairPosPure_nil_right_len32 P kEntry.secIKA0 pk kEntry.ikAPk hk.1]
    exact fgPosRightRep_mkSecret P uSk _ (hP.x25519_len _ _)

theorem checkBundleProvenanceTake_erasePrin_eraseSpk_eq (S : Setup) (P : Primitives)
    (uIdx bIdx : ℕ) (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput)
    (hP : principals.length ≤ S.N_dh)
    (hS : spkBundles.length ≤ S.N_dh)
    (hO : opkEntries.length ≤ S.N_dh) :
    checkBundleProvenanceTake S P (erasePrincipalsFg uIdx principals)
      (eraseSpkBundlesFg S bIdx spkBundles) opkEntries bundle =
      checkBundleProvenance P principals spkBundles opkEntries bundle := by
  rw [checkBundleProvenanceTake_eq_of_le S P _ _ _ _
    (by rw [erasePrincipalsFg_length]; exact hP)
    (by rw [eraseSpkBundlesFg_length]; exact hS) hO]
  rw [checkBundleProvenance_erasePrincipalsFg, checkBundleProvenance_eraseSpkBundlesFg]

def deadDh1 {S : Setup} (uIdx : ℕ) (hst : KeyIndFgCutoffState S) : Bool :=
  match hst.base.principals.find? (fun (u, _) => u == uIdx) with
  | some (_, uEntry) => uEntry.corrupted
  | none => false

theorem badKeyIndFgDh1At_eq_false_of_deadDh1 {S : Setup} (P : Primitives)
    (maxLen uIdx bIdx : ℕ) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh1 uIdx hst = true) :
    badKeyIndFgDh1At P maxLen uIdx bIdx hst.base hst.advRoLog = false := by
  unfold deadDh1 at hDead
  unfold badKeyIndFgDh1At
  cases hF1 : hst.base.principals.find? (fun (u, _) => u == uIdx) with
  | none => rw [hF1] at hDead
  | some ue =>
    rcases ue with ⟨_, uEntry⟩
    rw [hF1] at hDead
    dsimp only at hDead ⊢
    cases hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
    | none => rfl
    | some kb =>
      rcases kb with ⟨_, bEntry⟩
      simp [hDead]

theorem deadDh1_eq_of_principals {S : Setup} (uIdx : ℕ)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hPrin : hst2.base.principals = hst1.base.principals) :
    deadDh1 uIdx hst2 = deadDh1 uIdx hst1 := by
  unfold deadDh1
  rw [hPrin]

theorem deadDh1_map_corrupted_of_ne {S : Setup} (uIdx u : ℕ) (hNe : (u == uIdx) = false)
    (hst : KeyIndFgCutoffState S) :
    deadDh1 uIdx { hst with base := { hst.base with
      principals := hst.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)) } } =
      deadDh1 uIdx hst := by
  unfold deadDh1
  have hMapFind :
      (List.map (fun ((idx, e) : Nat × PrincipalEntry) =>
          if idx == u then (idx, { e with corrupted := true }) else (idx, e))
        hst.base.principals).find? (fun (idx, _) => idx == uIdx) =
      (hst.base.principals.find? (fun (idx, _) => idx == uIdx)).map
        (fun (idx, e) => if idx == u then (idx, { e with corrupted := true }) else (idx, e)) := by
    have hPred : (fun (x : Nat × PrincipalEntry) => x.1 == uIdx) ∘
        (fun ((idx, e) : Nat × PrincipalEntry) =>
          if idx == u then (idx, { e with corrupted := true }) else (idx, e)) =
        (fun (x : Nat × PrincipalEntry) => x.1 == uIdx) := by
      funext ⟨idx, e⟩; dsimp; split_ifs <;> rfl
    rw [List.find?_map, hPred]
  dsimp only
  rw [hMapFind]
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == uIdx) with
  | none => rfl
  | some p =>
    rcases p with ⟨u0, uEntry⟩
    have hu0 : u0 = uIdx := beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) =>
      x.1 == uIdx) hF)
    subst hu0
    have hNeSymm : (u0 == u) = false := by
      rw [beq_eq_false_iff_ne] at hNe ⊢
      exact Ne.symm hNe
    dsimp only [Option.map]
    rw [hNeSymm]
    rfl

theorem deadDh1_map_corrupted_eq_true_of_eq {S : Setup} (uIdx u : ℕ) (hEq : (u == uIdx) = true)
    (hst : KeyIndFgCutoffState S) (u0 : ℕ) (uEntry : PrincipalEntry)
    (hF : hst.base.principals.find? (fun (idx, _) => idx == u) = some (u0, uEntry)) :
    deadDh1 uIdx { hst with base := { hst.base with
      principals := hst.base.principals.map (fun (idx, e) =>
        if idx == u then (idx, { e with corrupted := true }) else (idx, e)) } } = true := by
  have huEq : u = uIdx := beq_iff_eq.mp hEq
  subst huEq
  unfold deadDh1
  have hMapFind :
      (List.map (fun ((idx, e) : Nat × PrincipalEntry) =>
          if idx == u then (idx, { e with corrupted := true }) else (idx, e))
        hst.base.principals).find? (fun (idx, _) => idx == u) =
      (hst.base.principals.find? (fun (idx, _) => idx == u)).map
        (fun (idx, e) => if idx == u then (idx, { e with corrupted := true }) else (idx, e)) := by
    have hPred : (fun (x : Nat × PrincipalEntry) => x.1 == u) ∘
        (fun ((idx, e) : Nat × PrincipalEntry) =>
          if idx == u then (idx, { e with corrupted := true }) else (idx, e)) =
        (fun (x : Nat × PrincipalEntry) => x.1 == u) := by
      funext ⟨idx, e⟩; dsimp; split_ifs <;> rfl
    rw [List.find?_map, hPred]
  dsimp only
  rw [hMapFind, hF]
  have hu0 : (u0 == u) = true := List.find?_some (p := fun (x : Nat × PrincipalEntry) =>
    x.1 == u) hF
  dsimp only [Option.map]
  rw [hu0]
  rfl

theorem pqxdhKeyIndFgPreImpl_preserves_deadDh1 {S : Setup} (P : Primitives)
    (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh1 uIdx hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadDh1 uIdx x.2 = true := by
  have hUnchanged : ∀ x : KeyIndResponse × KeyIndFgCutoffState S,
      x.2.base.principals = hst.base.principals →
      deadDh1 uIdx x.2 = true := by
    intro x hPrin
    rw [deadDh1_eq_of_principals uIdx hPrin]
    exact hDead
  unfold deadDh1 at hDead
  cases hFP : hst.base.principals.find? (fun (u, _) => u == uIdx) with
  | none => rw [hFP] at hDead; cases hDead
  | some p0 =>
    rcases p0 with ⟨u0, uEntry0⟩
    rw [hFP] at hDead
    dsimp only at hDead
    have hu0Mem : (u0, uEntry0) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
    have hu0Eq : u0 = uIdx := beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) =>
      x.1 == uIdx) hFP)
    subst hu0Eq
    intro x hx
    refine mem_support_pqxdhKeyIndFgPreImpl_elim true u0 bIdx (some uSk) (some vSk) P q hst x hx
      (fun hP _ _ _ => hUnchanged x hP)
      (fun u e _ hAny hB => ?_)
      (fun u u1 entry1 _ hFU hB => ?_)
      (fun _ _ _ _ _ _ _ hB => hUnchanged x (by rw [hB]))
      (fun _ _ _ _ _ _ _ hB => hUnchanged x (by rw [hB]))
      (fun _ _ _ hB => hUnchanged x (by rw [hB]))
      (fun _ _ _ hP _ _ _ => hUnchanged x hP)
      (fun _ _ _ _ _ hP _ _ _ => hUnchanged x hP)
      (fun _ _ hB => hUnchanged x (by rw [hB]))
    · have hNe : (u.val == u0) = false := by
        cases hEqB : (u.val == u0)
        · rfl
        · have hT : (u0 == u.val) = true := by
            rw [beq_iff_eq] at hEqB ⊢; exact hEqB.symm
          have hAnyT : hst.base.principals.any (fun (idx, _) => idx == u.val) = true :=
            List.any_eq_true.mpr ⟨(u0, uEntry0), hu0Mem, hT⟩
          rw [hAny] at hAnyT; cases hAnyT
      unfold deadDh1; rw [hB]; dsimp only [List.find?]; rw [hNe, hFP]; exact hDead
    · have hPrinX : x.2.base.principals =
          hst.base.principals.map (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) := by
        rw [hB]
      rw [deadDh1_eq_of_principals u0 (hst1 := { hst with base := { hst.base with
          principals := hst.base.principals.map (fun (idx, e) =>
            if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) } }) hPrinX]
      by_cases hEqU : (u.val == u0) = true
      · exact deadDh1_map_corrupted_eq_true_of_eq u0 u.val hEqU hst u1 entry1 hFU
      · have hNeU : (u.val == u0) = false := Bool.eq_false_iff.mpr hEqU
        rw [deadDh1_map_corrupted_of_ne u0 u.val hNeU hst]
        unfold deadDh1; rw [hFP]; exact hDead

noncomputable def deadDh1Full {S : Setup} (uIdx bIdx : ℕ)
    (hst : KeyIndFgCutoffState S) : Bool :=
  deadDh1 uIdx hst || spkTargetRevealed bIdx hst

theorem badKeyIndFgDh1At_eq_false_of_deadDh1Full {S : Setup} (P : Primitives)
    (maxLen uIdx bIdx : ℕ) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh1Full uIdx bIdx hst = true) :
    badKeyIndFgDh1At P maxLen uIdx bIdx hst.base hst.advRoLog = false := by
  rcases Bool.or_eq_true_iff.mp hDead with hD | hR
  · exact badKeyIndFgDh1At_eq_false_of_deadDh1 P maxLen uIdx bIdx hst hD
  · exact badKeyIndFgDh1At_eq_false_of_spkTargetRevealed P maxLen uIdx bIdx hst hR

theorem pqxdhKeyIndFgPreImpl_preserves_deadDh1Full {S : Setup} (P : Primitives)
    (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh1Full uIdx bIdx hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadDh1Full uIdx bIdx x.2 = true := by
  intro x hx
  unfold deadDh1Full at hDead ⊢
  rcases Bool.or_eq_true_iff.mp hDead with hD | hR
  · exact Bool.or_eq_true_iff.mpr (Or.inl
      (pqxdhKeyIndFgPreImpl_preserves_deadDh1 P uIdx bIdx uSk vSk q hst hD x hx))
  · exact Bool.or_eq_true_iff.mpr (Or.inr
      (pqxdhKeyIndFgPreImpl_preserves_spkTargetRevealed true uIdx bIdx (some uSk) (some vSk) P q hst
        hR x hx))

def FgSimInvDh1 (S : Setup) (b : QueryBudget) (P : Primitives) (R : FgSlotReps P)
    (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S) : Prop :=
  st.base = eraseStateFg true uIdx bIdx hst.base ∧
  FgAdvEq P st.advRoLog hst.advRoLog st.advKeyPows hst.base.advKeys ∧
  FgCacheRel R b.q_total st.fgL st.rawRoCache hst.base.roCache ∧
  st.fgL.length + rem ≤ b.q_total ∧
  hst.advRoLog.length + rem ≤ b.q_total ∧
  ValidKeyIndEcFg S hst.base ∧
  spkTargetIsV bIdx (P.x25519Base vSk) hst = true ∧
  (∀ kv ∈ hst.base.principals,
    kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0 ∧
    ((kv.1 == uIdx) = true → kv.2.secIKA0 = uSk)) ∧
  (∀ kv ∈ hst.base.spkBundles,
    kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
    ((spkBundleFlatIdxVal S kv.1 == bIdx) = true → kv.2.spkSk = vSk)) ∧
  (∀ kv ∈ hst.base.opkEntries, kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk) ∧
  (∀ s ∈ hst.base.sessions, s.ekASk.length = 32 ∧ s.hdr.ekAPk = P.x25519Base s.ekASk)

theorem fgSimInvDh1_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (secb : Bool) :
    FgSimInvDh1 S b P R uIdx bIdx uSk vSk b.q_total
      (KeyIndFgCutoffState.empty S secb) (FgKeyIndSimState.empty S secb) := by
  refine ⟨rfl, ⟨rfl, rfl, fun _ h => False.elim (List.not_mem_nil h)⟩,
    ⟨Nat.zero_le _, rfl, List.Forall₂.nil⟩,
    by change 0 + b.q_total ≤ b.q_total; omega, by simp [KeyIndFgCutoffState.empty],
    validKeyIndEcFg_empty S secb, rfl, ?_, ?_, ?_, ?_⟩
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)

theorem fgSimInvDh1_terminal_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (R : FgSlotReps P) (maxLen uIdx bIdx : ℕ)
    (uSk vSk : Bytes)
    (_a : Bool) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (_hDead : deadDh1Full uIdx bIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst st) :
    𝒟[(pure (badKeyIndFgDh1At P maxLen uIdx bIdx hst.base hst.advRoLog) : ProbComp Bool)] {true} ≤
      𝒟[(pure (P.pow8 (pureExtractCdhFromSimState S P P.isValidDhTriple true b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) st) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true} := by
  by_cases hBad : badKeyIndFgDh1At P maxLen uIdx bIdx hst.base hst.advRoLog = true
  · rcases hInv with ⟨hBaseEq, hAdvEq, _, _, hAdvLen, _, _, hPrins, hSpks, _, _⟩
    have hBad' := hBad
    unfold badKeyIndFgDh1At at hBad'
    cases hFP : hst.base.principals.find? (fun (u, _) => u == uIdx) with
    | none => rw [hFP] at hBad'; cases hBad'
    | some up =>
      rcases up with ⟨u0, uEntry⟩
      rw [hFP] at hBad'
      cases hFB : hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
      | none => rw [hFB] at hBad'; cases hBad'
      | some kb =>
        rcases kb with ⟨k, bEntry⟩
        rw [hFB] at hBad'
        dsimp only at hBad'
        rcases Bool.and_eq_true_iff.mp hBad' with ⟨_, hAny⟩
        have huMem : (u0, uEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
        have huIdx : (u0 == uIdx) = true :=
          List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == uIdx) hFP
        have hbMem : (k, bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hFB
        have hbIdx : (spkBundleFlatIdxVal S k == bIdx) = true :=
          List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) =>
            spkBundleFlatIdxVal S x.1 == bIdx) hFB
        have huEq : uEntry.secIKA0 = uSk := (hPrins (u0, uEntry) huMem).2.2 huIdx
        have hbSkEq : bEntry.spkSk = vSk := (hSpks (k, bEntry) hbMem).2.2 hbIdx
        have hbPkEq : bEntry.spkPk = P.x25519Base vSk := by
          rw [(hSpks (k, bEntry) hbMem).2.1, hbSkEq]
        rw [huEq, hbPkEq] at hAny
        have hSpkEq : st.base.spkBundles = eraseSpkBundlesFg S bIdx hst.base.spkBundles := by
          rw [hBaseEq]; rfl
        have hSessEq : st.base.sessions = hst.base.sessions := by
          rw [hBaseEq]; rfl
        have hRespEq : st.base.respSessions = hst.base.respSessions := by
          rw [hBaseEq]; rfl
        have hMemDisj :
            P.x25519 uSk (P.x25519Base vSk) ∈ (st.advRoLog.take b.q_total).map extractDh1 ∨
            P.x25519 uSk (P.x25519Base vSk) ∈
              (st.base.sessions.take S.N_dh).map (initDh1Cand S P st.base.spkBundles st.advKeyPows)
                ∨
            P.x25519 uSk (P.x25519Base vSk) ∈
              (st.base.respSessions.take S.N_sess_tot).map (respDh1Cand S P st.base.spkBundles) :=
                by
          rcases Bool.or_eq_true_iff.mp hAny with hAny12 | hAny3
          · rcases Bool.or_eq_true_iff.mp hAny12 with hAny1 | hAny2
            · rcases List.any_eq_true.mp hAny1 with ⟨sec, hSecTake, hSecEq⟩
              have hSecMem : sec ∈ hst.advRoLog := List.mem_of_mem_take hSecTake
              have hSecMemTake : sec ∈ st.advRoLog.take b.q_total := by
                rw [hAdvEq.1, List.take_of_length_le (by omega)]
                exact hSecMem
              exact Or.inl (by rw [← beq_iff_eq.mp hSecEq]; exact List.mem_map_of_mem hSecMemTake)
            · rcases List.any_eq_true.mp hAny2 with ⟨s, hsTake, hsEq⟩
              refine Or.inr (Or.inl ?_)
              rw [hSessEq, hSpkEq, hAdvEq.2.1, ← beq_iff_eq.mp hsEq]
              exact List.mem_map_of_mem hsTake
          · rcases List.any_eq_true.mp hAny3 with ⟨r, hrTake, hrEq⟩
            refine Or.inr (Or.inr ?_)
            rw [hRespEq, hSpkEq, ← beq_iff_eq.mp hrEq]
            exact List.mem_map_of_mem hrTake
        have hWin := pureExtractCdhFromSimState_dh1_wins_of_mem S P hP.toWellFormedPrimitivesδ
          b.q_total uSk vSk st hMemDisj
        rw [hBad, hWin]
  · have hBadF : badKeyIndFgDh1At P maxLen uIdx bIdx hst.base hst.advRoLog = false :=
      Bool.eq_false_iff.mpr hBad
    rw [hBadF]
    simp

theorem fgStepCoupling_dh1_unchanged (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ) (uSk vSk : Bytes)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (r : KeyIndResponse)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[k1 (r, hst)] {true} ≤ 𝒟[k2 (r, st)] {true} := by
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact hCont r hst st hDead ⟨h1, h2, h3, by omega, by omega, h6, h7, h8, h9, h10, h11⟩

theorem fgStepCoupling_dh1_initPrin (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh1 uIdx hst = false)
    (hInv : FgSimInvDh1 S b P R uIdx bIdx uSk vSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh1 uIdx hst' = false →
      FgSimInvDh1 S b P R uIdx bIdx uSk vSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl true uIdx bIdx (some uSk) (some vSk) S P (.initPrin u)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple true uIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hPrinAnyEq : st.base.principals.any (fun (idx, _) => idx == u.val) =
      hst.base.principals.any (fun (idx, _) => idx == u.val) := by
    rw [hBaseEq]; exact any_idx_erasePrincipalsFg uIdx u.val hst.base.principals
  unfold pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.true_and,
    hPrinAnyEq, bind_assoc, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hTgt : (u.val == uIdx) = true
    · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        evalDist_sampleScalar32_const]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKAsign _ => ?_)
      let entry1 : PrincipalEntry := {
        secIKA0 := uSk, ikAPk := P.x25519Base uSk,
        secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false }
      apply hCont (.initPrinResp entry1.ikAPk entry1.ikSignPk)
      · unfold deadDh1
        dsimp only [List.find?]
        rw [hTgt]
      · refine ⟨?_, hAdvEq, hCache,
        by dsimp; omega, by dsimp; omega, ?_, hSpkV, ?_, hSpks, hOpks, hSess⟩
        · rw [hBaseEq]
          simp [eraseStateFg, erasePrincipalsFg, erasePrincipalEntryFg, beq_iff_eq.mp hTgt]
        · exact ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
            hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨huSk, rfl, fun _ => rfl⟩
          · exact hPrins kv hMem
    · have hTgtF : (u.val == uIdx) = false := Bool.eq_false_iff.mpr hTgt
      simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKA0 hSec0 => ?_)
      have hLen0 : secIKA0.length = 32 := length_of_mem_support_sampleScalar32 hSec0
      refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKAsign _ => ?_)
      let entry1 : PrincipalEntry := {
        secIKA0 := secIKA0, ikAPk := P.x25519Base secIKA0,
        secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false }
      apply hCont (.initPrinResp entry1.ikAPk entry1.ikSignPk)
      · unfold deadDh1 at hDead ⊢
        dsimp only [List.find?]
        rw [hTgtF]
        exact hDead
      · refine ⟨?_, hAdvEq, hCache,
        by dsimp; omega, by dsimp; omega, ?_, hSpkV, ?_, hSpks, hOpks, hSess⟩
        · rw [hBaseEq]
          simp [eraseStateFg, erasePrincipalsFg, erasePrincipalEntryFg,
            beq_eq_false_iff_ne.mp hTgtF]
        · exact ⟨(validPrincipals_cons S u entry1 hst.base.principals hValidEc.1 hAny).1,
            hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hMem
          · exact ⟨hLen0, rfl, fun h => by rw [hTgtF] at h; cases h⟩
          · exact hPrins kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh1_unchanged S b P R uIdx bIdx uSk vSk rem hst st hDead hInv0 .noneResp k1
      k2 hCont


end Proofs.SignalPqxdh.Security.FgGapDh
