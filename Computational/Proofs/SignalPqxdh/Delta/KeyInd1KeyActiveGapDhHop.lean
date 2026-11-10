/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyCoupling -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre -- proof-setup: allow-public-import
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure
import VCVio.CryptoFoundations.SecExp.Measure

/-!
# Active Creation-Order One-Key `GapDhWithSign` `DH1` and `DH3` Bounds

Proves creation-order per-ordinal `GapDhWithSign` bounds for `DH1` and `DH3` in one-key `KeyInd`,
the four-way flat-index decomposition of `fgKeyInd1KeyGapDhActiveAdv4`, and `KI1KeyActiveG3BoundStmt`
transfer combiners.
-/

set_option autoImplicit false

open scoped ENNReal BigOperators
open MeasureTheory (measure_ne_top)
open OracleSpec OracleComp
open SignalPqxdh (
  Setup Bytes PrincipalEntry SpkBundleEntry OpkEntry PreKeyBundleInput
  HandshakeHdr SessionId KeyIndQuery KeyIndResponse KeyIndState
  KeyIndInitiatorEntry KeyIndAdversary keyIndSpec QueryBudget BoundedAdv
  isGameQuery isKeyIndOnlineQuery QueryBounded
  Primitives CryptoWellFormedPrimitivesδ KemDeltaCorrectReal
  GapDhWithSignAdv GapDhWithSign gapDhWithSignExp GapDhWithSignReal
  gapDhOracleSpec sampleScalar32 sampleCoins32 sampleRandom64
  encodeEC encodeKEM findHonestPrincipal resolveSigPk isHonestUncorruptedPeer
  koskBundleOk isKeyIndSessionTestable registerAdvKey pqxdhKeyIndImpl
  activeIdCount activeSpkCount activeOpkCount activeSendCount activeSendOpkCount
)
open SignalPqxdh.Model (acceptKeys)
open SignalPqxdh.Security (
  kemDecapsFailureTermReal keyInd1KeyAllTestedClean
  embedPrim isHonestUncorruptedPeerPrim checkBundleProvenancePrim findHonestPrincipalPrim
  IsSendSessionId ValidPrincipals ValidSpkBundles ValidOpkEntries ValidSessionIds
  validPrincipals_cons validSpkBundles_cons validPrincipals_corrupt
  spkSlotFlatIdx spkSlotFlatIdx_lt spkSlotFlatIdx_inj
  bundleSignedMessages
)
open SignalPqxdh.Security.RoKem (sampleIndexRange)
open SignalPqxdh.Security.FgGapDh (
  GdhSimSpec unifGdh primGdhQ FgKeyIndSimState
  spkBundleFlatIdx initSessionSlotIdx
  koskBundleOkPrim resolveSigPkPrim lookupSpkSkPrim
  fgRunAcceptOPKGdh fgKeyIndStep extractCdhFromSimState
  computeTwoSideOrPairPos computeOptPos fgPatch chooseInitPartnerDrKeyRandGdh
)
open SignalPqxdh.Security.FgGapDh.Ik (extractCdh2FromAdvRoLog)
open SignalPqxdh.Security.FgGapDh.Opk (fgRunAcceptOPKGdhOpk extractCdh4FromAdvRoLog)
open SignalPqxdh.Security.FgGapDh1Key (
  GdhSignSimSpec liftGdhToSign unifGdhSign primGdhSignQ sigChalQ
  FgKeyInd1KeySimState runWithGdhSignStep
)
open Proofs.SignalPqxdh.Security (
  keyInd1KeyAdvG3 keyIndAdvG3_1Key keyInd1KeyExpG3 keyIndExpG3_1Key
  pqxdhKeyInd1KeyShCrImpl pqxdhKeyIndShCrImpl1Key
  runKeyInd1KeyShCrSim runKeyIndShCrSim1Key
  finalizeKeyIndG3 badKeyIndFgAny4
  keyIndAdvG3_1Key_le_prob_badKeyIndFgAny4_add_corr_1Key
  mul_toReal_sampleIndexRange_bind_eq_sum sum_range_mul_div_mod
)
open Proofs.SignalPqxdh.Security.FgGapDh (
  KeyIndFgCutoffState spkBundleFlatIdxVal badKeyIndFgDh1At badKeyIndFgDh3At
  hasFiredSpk hasFiredPrin hasFiredSess
  spkBundles_any_of_hasFiredSpk sessions_any_of_hasFiredSess
  initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt
  spkBundleFlatIdx_inj StateT_run_mk liftFgBase pqxdhKeyIndFgImpl
  fgPreInitPrin fgPreGenSPK fgPreInitiate pqxdhKeyIndFgPreImpl
  mem_support_liftFgBase mem_support_recordKeyIndResp
  mem_support_fgPreInitiate_elim mem_support_pqxdhKeyIndFgPreImpl_elim
  evalDist_simulateQ_preSample_slot_eq
  evalDist_bind_true_eq_zero_of_support evalDist_bind_true_mono_of_support
  simulateQ_run_query_inl simulateQ_run_query_inr
  ValidKeyIndEcFg eraseStateFg erasePrincipalsFg eraseSpkBundlesFg eraseSessionsFg
  erasePrincipalEntryFg eraseSpkBundleEntryFg eraseSessionEntryFg
  erasePrincipalsFg_length eraseSpkBundlesFg_length
  any_idx_erasePrincipalsFg any_idx_eraseSpkBundlesFg any_sid_eraseSessionsFg
  FgSlotReps FgAdvEq FgCacheRel
  spkTargetIsV spkTargetIsV_map_revealed_base spkTargetRevealed
  deadDh3 deadDh3Full deadDh1 deadDh1Full deadDh1_eq_of_principals
  pqxdhKeyIndFgPreImpl_preserves_hasFired
  badKeyIndFgDh1At_eq_false_of_deadDh1Full badKeyIndFgDh3At_eq_false_of_deadDh3Full
  FgSimInvDh1 FgSimInvDh3 fgSimInvDh1_empty fgSimInvDh3_empty
  fgSimInvDh3_terminal_le fgStepCoupling_dh1 fgStepCoupling_dh3
  length_of_mem_support_sampleScalar32
  gapDhFullImpl koskBundleOkTake lookupSpkSkTake checkBundleProvenanceTake
  computeTwoSideOrPairPosPure computeOptPosPure fgPatchPure
  chooseInitPartnerDrKeyRandPure fgRunInitiatePure fgRunAcceptOPKPure fgKeyIndStepPure
  pureExtractCdhFromSimState pureExtractCdhFromAdvRoLog
  simulateQ_gapDhFullImpl_embedPrim simulateQ_gapDhFullImpl_unifGdh
  simulateQ_gapDhFullImpl_primGdhQ_x25519Base simulateQ_gapDhFullImpl_primGdhQ_sigSign
  simulateQ_gapDhFullImpl_primGdhQ_sigVerify simulateQ_gapDhFullImpl_primGdhQ_kemKeyGen
  simulateQ_gapDhFullImpl_primGdhQ_kemEncaps simulateQ_gapDhFullImpl_computeTwoSideOrPairPos
  simulateQ_gapDhFullImpl_computeOptPos simulateQ_gapDhFullImpl_fgPatch
  simulateQ_gapDhFullImpl_chooseInitPartnerDrKeyRandGdh
  simulateQ_primBaseImpl_koskBundleOkPrim simulateQ_primBaseImpl_resolveSigPkPrim
  simulateQ_primBaseImpl_lookupSpkSkPrim simulateQ_primBaseImpl_isHonestUncorruptedPeerPrim
  simulateQ_primBaseImpl_checkBundleProvenancePrim simulateQ_primBaseImpl_findHonestPrincipalPrim
  simulateQ_gapDhFullImpl_fgRunAcceptOPKGdh simulateQ_gapDhFullImpl_fgKeyIndStep
  simulateQ_gapDhFullImpl_extractCdhFromSimState
)
open Proofs.SignalPqxdh.Security.FgGapDh.Ik (
  pureExtractCdh2FromAdvRoLog simulateQ_gapDhFullImpl_extractCdh2FromAdvRoLog
)
open Proofs.SignalPqxdh.Security.FgGapDh.Opk (
  fgRunAcceptOPKPureOpk pureExtractCdh4FromAdvRoLog
  simulateQ_gapDhFullImpl_fgRunAcceptOPKGdhOpk
  simulateQ_gapDhFullImpl_extractCdh4FromAdvRoLog
)
open Proofs.SignalPqxdh.Security.FgGapDh1Key (
  pqxdhKeyIndFgImpl1Key runKeyIndFgSim1Key gapDhWithSignFullImpl
  fgInitPrin1KeyPure fgGenSPK1KeyPure fgKeyInd1KeyStepPure fgKeyInd1KeySimImpl
  fgPreInitPrin1Key fgPreInitPrin1Key_false_eq pqxdhKeyIndFgPreImpl1Key
  pqxdhKeyIndFgPreImpl1Key_none_none_eq pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin
  clearTargetPrinSecSign clearTargetSecIKAsignBase clearTargetSecIKAsign
  any_idx_map_clearTargetPrinSecSign
  clearTargetSecIKAsign_base_principals clearTargetSecIKAsign_base_spkBundles
  clearTargetSecIKAsign_base_sessions spkTargetRevealed_eq_of_spkBundles_eq
  FgSimInvDh1_1Key fgSimInvDh1_1Key_empty fgSimInvDh1_1Key_terminal_le fgStepCoupling_dh1_1Key
  FgSimInvDh3_1Key fgSimInvDh3_1Key_empty fgStepCoupling_dh3_1Key
  simulateQ_gapDhWithSignFullImpl_liftGdhToSign
  simulateQ_gapDhWithSignFullImpl_unifGdhSign
  simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base
  simulateQ_gapDhWithSignFullImpl_primGdhSignQ_kemKeyGen
  simulateQ_gapDhWithSignFullImpl_sigChalQ
  simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep
)
open Proofs.SignalPqxdh.Security.PqxdhDelta (KI1KeyActiveG3BoundStmt prob_hasBadKemCorrRecords_1Key_le)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (activeSigBudget fgActiveTotalIndexCount)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (
  FgActiveParams activeParamsDh1 activeParamsDh3 activeParamsDh2 activeParamsDh4
  activeParamsZero activeParamsFlat FgKeyInd1KeyActiveSimState
  liftSimStep1KeyActive fgInitPrin1KeyActiveGdh fgGenSpkActiveGdh fgGenSPK1KeyActiveGdh
  fgGenOPKActiveGdh fgRunInitiateActiveGdh fgInitiateActiveGdh
  fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveFinish fgKeyInd1KeyActiveRunWithParams
  fgKeyInd1KeyGapDhActiveAdvAt fgKeyInd1KeyGapDhActiveAdvAtIk fgKeyInd1KeyGapDhActiveAdvAtOpk
  fgKeyInd1KeyGapDhActiveRunAtFlat fgKeyInd1KeyGapDhActiveAdvAtFlat fgKeyInd1KeyGapDhActiveAdv4
  fgKeyInd1KeyGapDhActiveAdvAtFlat_dh1 fgKeyInd1KeyGapDhActiveAdvAtFlat_dh3
  fgKeyInd1KeyGapDhActiveAdvAtFlat_dh2 fgKeyInd1KeyGapDhActiveAdvAtFlat_dh4
  optNatMatches
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre (
  prinSlotAtOrd spkSlotAtOrd sessSlotAtOrd
  badKeyIndFgDh1OrdAt badKeyIndFgDh3OrdAt
  evalDist_preSample_sessOrd_1Key
)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhHop

public section
theorem keyInd1KeyAdvG3_eq_keyIndAdvG3_1Key (S : Setup) (P : Primitives)
    (A : KeyIndAdversary S) :
    keyInd1KeyAdvG3 S P A = keyIndAdvG3_1Key S P A := by
  have hImpl : pqxdhKeyInd1KeyShCrImpl false S P = pqxdhKeyIndShCrImpl1Key false S P := by
    funext q; cases q <;> rfl
  have hRun : runKeyInd1KeyShCrSim S P A = runKeyIndShCrSim1Key S P A := by
    unfold runKeyInd1KeyShCrSim runKeyIndShCrSim1Key
    rw [hImpl]
  unfold keyInd1KeyAdvG3 keyIndAdvG3_1Key keyInd1KeyExpG3 keyIndExpG3_1Key
    finalizeKeyIndG3 keyInd1KeyAllTestedClean
  rw [hRun]

theorem ki1KeyActiveGapDh_of_evalEq (S : Setup)
    (gdh0 gdh : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapDhWithSignAdv)
    (h0 : KI1KeyActiveG3BoundStmt S gdh0)
    (hEq : ∀ P b A,
      GapDhWithSign P P.isValidDhTriple P.pow8 (gdh b A) =
      GapDhWithSign P P.isValidDhTriple P.pow8 (gdh0 b A)) :
    KI1KeyActiveG3BoundStmt S gdh := by
  intro P hP δ hδ b A
  have hReal :
      GapDhWithSignReal P P.isValidDhTriple P.pow8 (gdh b A) =
      GapDhWithSignReal P P.isValidDhTriple P.pow8 (gdh0 b A) :=
    congrArg ENNReal.toReal (hEq P b A)
  have hBound := h0 P hP δ hδ b A
  dsimp only at hBound ⊢
  rw [hReal]
  exact hBound

/-- Transfers `KI1KeyActiveG3BoundStmt S` along `GapDhWithSignReal` equality under
    `CryptoWellFormedPrimitivesδ P`. -/
theorem ki1KeyActiveGapDh_of_realEq (S : Setup)
    (gdh0 gdh : (b : QueryBudget) → BoundedAdv (KeyIndAdversary S) b → GapDhWithSignAdv)
    (h0 : KI1KeyActiveG3BoundStmt S gdh0)
    (hEq : ∀ P, CryptoWellFormedPrimitivesδ P → ∀ b A,
      GapDhWithSignReal P P.isValidDhTriple P.pow8 (gdh b A) =
      GapDhWithSignReal P P.isValidDhTriple P.pow8 (gdh0 b A)) :
    KI1KeyActiveG3BoundStmt S gdh := by
  intro P hP δ hδ b A
  have hBound := h0 P hP δ hδ b A
  dsimp only at hBound ⊢
  rw [hEq P hP b A]
  exact hBound

/-! ## Flat-index averaging decomposition -/

private theorem evalDist_gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdv4_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdv4 S b A)] =
    𝒟[sampleIndexRange (fgActiveTotalIndexCount S b.q_on) >>= fun idx =>
        gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A)] := by
  have hStep1 :
      gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdv4 S b A) =
      (do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let idx ← sampleIndexRange (fgActiveTotalIndexCount S b.q_on)
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) := by
    unfold gapDhWithSignExp fgKeyInd1KeyGapDhActiveAdv4
    congr 1; ext u; congr 1; ext v
    change (simulateQ (gapDhWithSignFullImpl P u ddh)
        (unifGdhSign (sampleIndexRange (fgActiveTotalIndexCount S b.q_on)) >>= fun idx =>
          fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v)) >>=
      fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
    rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign, bind_assoc]
  rw [hStep1]
  have hSwap1 :
      𝒟[do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let idx ← sampleIndexRange (fgActiveTotalIndexCount S b.q_on)
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] =
      𝒟[do
        let u ← sampleScalar32
        let idx ← sampleIndexRange (fgActiveTotalIndexCount S b.q_on)
        let v ← sampleScalar32
        let Z ← simulateQ (gapDhWithSignFullImpl P u ddh)
          (fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] := by
    refine OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun u _ => ?_)
    exact OracleComp.evalDist_bind_bind_swap sampleScalar32
      (sampleIndexRange (fgActiveTotalIndexCount S b.q_on)) _
  rw [hSwap1, OracleComp.evalDist_bind_bind_swap sampleScalar32
    (sampleIndexRange (fgActiveTotalIndexCount S b.q_on))]
  rfl

/-- Decomposes `GapDhWithSignReal` of `fgKeyInd1KeyGapDhActiveAdv4` into the four active
    creation-order sub-rectangles (`DH1`, `DH3`, `DH2`, `DH4`). -/
theorem sum_gapDhWithSign_fgKeyInd1KeyGapDhActiveAdv4_eq
    (S : Setup) (P : Primitives) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    let n_id := activeIdCount S b.q_on
    let n_spk := activeSpkCount S b.q_on
    let n_opk := activeOpkCount S b.q_on
    let n_send := activeSendCount S b.q_on
    let n_send_opk := activeSendOpkCount S b.q_on
    (∑ p ∈ Finset.range n_id, ∑ spk ∈ Finset.range n_spk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt true p spk S b A)) +
    (∑ s ∈ Finset.range n_send, ∑ spk ∈ Finset.range n_spk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt false s spk S b A)) +
    (∑ s ∈ Finset.range n_send, ∑ p ∈ Finset.range n_id,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtIk s p S b A)) +
    (∑ sOpk ∈ Finset.range n_send_opk, ∑ opk ∈ Finset.range n_opk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtOpk sOpk opk S b A)) =
    (fgActiveTotalIndexCount S b.q_on : ℝ) *
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdv4 S b A) := by
  dsimp only
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let n_send_opk := activeSendOpkCount S b.q_on
  have hExp := evalDist_gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdv4_eq
    P P.isValidDhTriple P.pow8 S b A
  have hSum := mul_toReal_sampleIndexRange_bind_eq_sum (fgActiveTotalIndexCount S b.q_on)
    (fun idx => gapDhWithSignExp P P.isValidDhTriple P.pow8
      (fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A))
  have hRhs :
      (fgActiveTotalIndexCount S b.q_on : ℝ) *
        GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhActiveAdv4 S b A) =
      ∑ idx ∈ Finset.range (fgActiveTotalIndexCount S b.q_on),
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A) := by
    unfold GapDhWithSignReal GapDhWithSign
    rw [hExp]
    exact hSum
  rw [hRhs]
  have hTotEq : fgActiveTotalIndexCount S b.q_on =
      n_id * n_spk + n_send * n_spk + n_send * n_id + n_send_opk * n_opk := rfl
  rw [hTotEq, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range (n_id * n_spk),
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtFlat x S b A) =
      ∑ p ∈ Finset.range n_id, ∑ spk ∈ Finset.range n_spk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt true p spk S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [fgKeyInd1KeyGapDhActiveAdvAtFlat_dh1 S b A x (Finset.mem_range.mp hx)]
  have h2 : ∑ x ∈ Finset.range (n_send * n_spk),
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtFlat (n_id * n_spk + x) S b A) =
      ∑ s ∈ Finset.range n_send, ∑ spk ∈ Finset.range n_spk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAt false s spk S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxLt : x < n_send * n_spk := Finset.mem_range.mp hx
    have hEq := fgKeyInd1KeyGapDhActiveAdvAtFlat_dh3 S b A (n_id * n_spk + x)
      (by dsimp only [n_id, n_spk]; omega)
      (by dsimp only [n_id, n_spk, n_send] at hxLt ⊢; omega)
    dsimp only at hEq
    rw [hEq, Nat.add_sub_cancel_left]
  have h3 : ∑ x ∈ Finset.range (n_send * n_id),
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtFlat (n_id * n_spk + n_send * n_spk + x) S b A) =
      ∑ s ∈ Finset.range n_send, ∑ p ∈ Finset.range n_id,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtIk s p S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxLt : x < n_send * n_id := Finset.mem_range.mp hx
    have hEq := fgKeyInd1KeyGapDhActiveAdvAtFlat_dh2 S b A
      (n_id * n_spk + n_send * n_spk + x)
      (by dsimp only [n_id, n_spk, n_send]; omega)
      (by dsimp only [n_id, n_spk, n_send] at hxLt ⊢; omega)
    dsimp only at hEq
    rw [hEq, Nat.add_sub_cancel_left]
  have h4 : ∑ x ∈ Finset.range (n_send_opk * n_opk),
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtFlat
          (n_id * n_spk + n_send * n_spk + n_send * n_id + x) S b A) =
      ∑ sOpk ∈ Finset.range n_send_opk, ∑ opk ∈ Finset.range n_opk,
        GapDhWithSignReal P P.isValidDhTriple P.pow8
          (fgKeyInd1KeyGapDhActiveAdvAtOpk sOpk opk S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxLt : x < n_send_opk * n_opk := Finset.mem_range.mp hx
    have hEq := fgKeyInd1KeyGapDhActiveAdvAtFlat_dh4 S b A
      (n_id * n_spk + n_send * n_spk + n_send * n_id + x)
      (by dsimp only [n_id, n_spk, n_send]; omega)
      (by rw [hTotEq]; omega)
    dsimp only at hEq
    rw [hEq, Nat.add_sub_cancel_left]
  rw [h1, h2, h3, h4]

/-! ## Pure step counterparts -/

private noncomputable def fgInitPrin1KeyActivePure {S : Setup} (P : Primitives)
    (prinFlag : Bool) (prinIdx : Nat) (Up : Bytes)
    (u : Fin S.N_id) (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if stA.st1.sim.base.principals.any (fun (idx, _) => idx == u.val) then
    return (.noneResp, stA)
  let isTargetPrin : Bool := prinFlag && (stA.st1.sim.base.principals.length == prinIdx)
  let sk0 ← sampleScalar32
  let pk0 := P.x25519Base sk0
  let sec0 := if isTargetPrin then [] else sk0
  let ikPk := if isTargetPrin then Up else pk0
  let entry : PrincipalEntry :=
    { secIKA0 := sec0, ikAPk := ikPk, secIKAsign := sec0, ikSignPk := ikPk, corrupted := false }
  let base' :=
    { stA.st1.sim.base with principals := (u.val, entry) :: stA.st1.sim.base.principals }
  let tp' := if isTargetPrin then some u.val else stA.resolvedPrin?
  return (.initPrinResp ikPk ikPk,
    { stA with st1 := { stA.st1 with sim := { stA.st1.sim with base := base' } },
               resolvedPrin? := tp' })

private noncomputable def fgGenSpkActivePure {S : Setup} (P : Primitives)
    (spkIdx : Nat) (V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgKeyIndSimState S) : ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  if st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then return (.noneResp, st)
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, st)
  let isTargetSpk : Bool := st.base.spkBundles.length == spkIdx
  let spkSkRaw ← sampleScalar32
  let spkSk := if isTargetSpk then [] else spkSkRaw
  let spkPk := if isTargetSpk then V else P.x25519Base spkSkRaw
  let rSpk ← sampleRandom64
  let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
  let seedKem ← sampleRandom64
  let (pqspkPk, pqspkSk) := P.kemKeyGen seedKem
  let rPq ← sampleRandom64
  let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
  let bEntry : SpkBundleEntry :=
    { spkSk, spkPk, spkSig, pqspkSk, pqspkPk, pqspkSig }
  let base' := { st.base with spkBundles := ((u.val, j.val), bEntry) :: st.base.spkBundles }
  let bundleOut : PreKeyBundleInput :=
    { ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig,
      opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig }
  return (.bundleResp bundleOut, { st with base := base' })

private noncomputable def fgGenSPK1KeyActivePure {S : Setup} (P : Primitives) (uSk : Bytes)
    (spkIdx : Nat) (V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if optNatMatches stA.resolvedPrin? u.val then
    if stA.st1.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, stA)
    let some (_, uEntry) := stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, stA)
    if stA.st1.sigBudget == 0 then return (.noneResp, stA)
    let isTargetSpk : Bool := stA.st1.sim.base.spkBundles.length == spkIdx
    let spkSkRaw ← sampleScalar32
    let spkSk := if isTargetSpk then [] else spkSkRaw
    let spkPk := if isTargetSpk then V else P.x25519Base spkSkRaw
    let rSpk ← sampleRandom64
    let spkSig := P.sigSign uSk (encodeEC spkPk) rSpk
    let seedKem ← sampleRandom64
    let (pqspkPk, pqspkSk) := P.kemKeyGen seedKem
    let rPq ← sampleRandom64
    let pqspkSig := P.sigSign uSk (encodeKEM pqspkPk) rPq
    let bEntry : SpkBundleEntry :=
      { spkSk, spkPk, spkSig, pqspkSk, pqspkPk, pqspkSig }
    let base' :=
      { stA.st1.sim.base with spkBundles := ((u.val, j.val), bEntry) :: stA.st1.sim.base.spkBundles }
    let bundleOut : PreKeyBundleInput :=
      { ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig,
        opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig }
    return (.bundleResp bundleOut,
      { stA with st1 := { sim := { stA.st1.sim with base := base' }
                          sigBudget := stA.st1.sigBudget - 1 } })
  else
    let (resp, sim') ← fgGenSpkActivePure P spkIdx V u j stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })

private noncomputable def fgGenOPKActivePure {S : Setup} (P : Primitives)
    (opkMode : Bool) (opkIdx : Nat) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if stA.st1.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
    return (.noneResp, stA)
  let isTargetOpk : Bool := opkMode && (stA.st1.sim.base.opkEntries.length == opkIdx)
  let opkSkRaw ← sampleScalar32
  let oEntry : OpkEntry :=
    { opkSk := if isTargetOpk then [] else opkSkRaw,
      opkPk := if isTargetOpk then V else P.x25519Base opkSkRaw, consumed := false }
  let base' :=
    { stA.st1.sim.base with opkEntries := ((u.val, j.val, o.val), oEntry) :: stA.st1.sim.base.opkEntries }
  return (.pkResp oEntry.opkPk,
    { stA with st1 := { stA.st1 with sim := { stA.st1.sim with base := base' } } })

private noncomputable def fgRunInitiateActivePure (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (dhFlag opkMode : Bool) (ephIdx : Nat)
    (S : Setup) (maxLen : Nat) (U : Bytes) (hasOpk : Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (st : FgKeyIndSimState S) (sendOpkCnt : Nat) :
    ProbComp (KeyIndResponse × (FgKeyIndSimState S × Nat)) := do
  let guardOk : Bool := if hasOpk then bundle.opkB?.isSome else !bundle.opkB?.isSome
  if !guardOk then return (.noneResp, (st, sendOpkCnt))
  if st.base.sessions.any (fun e => e.sid == sid) then return (.noneResp, (st, sendOpkCnt))
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, (st, sendOpkCnt))
  if !koskBundleOkTake S P st.base.principals st.base.spkBundles st.base.opkEntries
    st.advKeyPows bundle then
    return (.noneResp, (st, sendOpkCnt))
  let isTargetEph : Bool :=
    if hasOpk then
      (!dhFlag) && ((if opkMode then sendOpkCnt else st.base.sessions.length) == ephIdx)
    else
      (!dhFlag) && ((!opkMode) && (st.base.sessions.length == ephIdx))
  let ekASkRaw ← sampleScalar32
  let kemCoins ← sampleCoins32
  let sigPkB := resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return (.noneResp, (st, sendOpkCnt))
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return (.noneResp, (st, sendOpkCnt))
  let ekASk := if isTargetEph then [] else ekASkRaw
  let ekAPk := if isTargetEph then U else P.x25519Base ekASkRaw
  let spkSk := lookupSpkSkTake S P st.base.spkBundles st.advKeyPows bundle.spkB
  let pos1 := computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB
  let pos2 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.ikB
  let pos3 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.spkB
  let pos4? := computeOptPosPure P ekASk ekAPk (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk)))
  let (drKeyReal, fgL') ← fgPatchPure ddh maxLen pos1 pos2 pos3 pos4? ss st.fgL
  let hdr : HandshakeHdr :=
    { ikAPk := uEntry.ikAPk, ekAPk, spkId := bundle.spkId, opkId? := bundle.opkB?.map Prod.fst,
      pqspkId := bundle.pqspkId, kemCt }
  let honestPeer := isHonestUncorruptedPeer P (st.base.principals.take S.N_dh) bundle.ikB
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenanceTake S P st.base.principals st.base.spkBundles st.base.opkEntries bundle
  let sessEntry : KeyIndInitiatorEntry S :=
    { sid, honestPeer, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
      peerOpkPk? := bundle.opkB?.map Prod.snd, peerPqspkPk := bundle.pqspkB,
      spkHonest := spkHon, opkHonest := opkHon, pqspkHonest := pqspkHon,
      ekASk, fresh := honestPeer.isSome, drKeyReal, drKeyRand := drKeyReal, hdr, tested := false }
  let drKeyRand ← chooseInitPartnerDrKeyRandPure P st.base.respSessions sessEntry
  let base' : KeyIndState S :=
    { st.base with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.base.sessions }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  let cnt' : Nat := if hasOpk then sendOpkCnt + 1 else sendOpkCnt
  match findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB with
  | some _ => return (.hdrResp hdr, (st', cnt'))
  | none   => return (.initUnfreshResp drKeyReal hdr, (st', cnt'))

private noncomputable def fgInitiateActivePure (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (dhFlag opkMode : Bool) (ephIdx : Nat)
    (S : Setup) (maxLen : Nat) (U : Bytes) (hasOpk : Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  let (resp, (sim', cnt')) ←
    fgRunInitiateActivePure P ddh dhFlag opkMode ephIdx S maxLen U hasOpk sid u bundle
      stA.st1.sim stA.sendOpkCnt
  return (resp, { stA with st1 := { stA.st1 with sim := sim' }, sendOpkCnt := cnt' })

private noncomputable def fgKeyInd1KeyActiveStepPure (pa : FgActiveParams)
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (maxLen : Nat) (q : KeyIndQuery S)
    (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) :=
  match q with
  | .initPrin u => fgInitPrin1KeyActivePure P pa.prinFlag pa.prinIdx pa.Up u stA
  | .genSPK u j => fgGenSPK1KeyActivePure P uSk pa.spkIdx pa.V u j stA
  | .genOPK u j o => fgGenOPKActivePure P pa.opkMode pa.opkIdx pa.V u j o stA
  | .initiateOPK u i bundle =>
    fgInitiateActivePure P ddh pa.dhFlag pa.opkMode pa.ephIdx S maxLen pa.U true (.sendOPK u i) u
      bundle stA
  | .initiateNoOPK u i bundle =>
    fgInitiateActivePure P ddh pa.dhFlag pa.opkMode pa.ephIdx S maxLen pa.U false (.sendNoOPK u i) u
      bundle stA
  | .acceptOPK k j o hdr => do
    let (resp, sim') ←
      if pa.opkMode then fgRunAcceptOPKPureOpk P ddh S maxLen k j o hdr stA.st1.sim
      else fgRunAcceptOPKPure P ddh S maxLen k j o hdr stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })
  | q_other => do
    let (resp, sim') ←
      fgKeyIndStepPure P ddh pa.dhFlag pa.ephIdx pa.spkIdx S maxLen pa.U pa.V q_other stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })

private noncomputable def fgKeyInd1KeyActiveSimImpl (pa : FgActiveParams)
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (maxLen : Nat) :
    QueryImpl (keyIndSpec S) (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) :=
  fun q => StateT.mk (fgKeyInd1KeyActiveStepPure pa P uSk ddh S maxLen q)

private noncomputable def fgKeyInd1KeyActiveFinishPure (pa : FgActiveParams)
    (S : Setup) (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : Nat)
    (stA : FgKeyInd1KeyActiveSimState S) : Bytes :=
  if pa.mode == 0 then
    pureExtractCdhFromSimState S P ddh true maxLen pa.U pa.V stA.st1.sim
  else if pa.mode == 1 then
    pureExtractCdhFromSimState S P ddh false maxLen pa.U pa.V stA.st1.sim
  else if pa.mode == 2 then
    pureExtractCdh2FromAdvRoLog ddh maxLen pa.U pa.V stA.st1.sim.advRoLog
  else
    pureExtractCdh4FromAdvRoLog ddh maxLen pa.U pa.V stA.st1.sim.advRoLog

private theorem security_embedPrim_eq :
    @SignalPqxdh.Security.embedPrim = @SignalPqxdh.Security.FgGapDh.embedPrim := rfl

private theorem security_primQ_eq :
    @SignalPqxdh.Security.primQ = @SignalPqxdh.Security.FgGapDh.primQ := rfl

private theorem security_findMPrim_eq {α : Type}
    (p : α → OracleComp SignalPqxdh.PrimBaseSpec Bool) (L : List α) :
    SignalPqxdh.Security.findMPrim p L = SignalPqxdh.Security.FgGapDh.findMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    unfold SignalPqxdh.Security.findMPrim SignalPqxdh.Security.FgGapDh.findMPrim
    rw [ih]

private theorem security_anyMPrim_eq {α : Type}
    (p : α → OracleComp SignalPqxdh.PrimBaseSpec Bool) (L : List α) :
    SignalPqxdh.Security.anyMPrim p L = SignalPqxdh.Security.FgGapDh.anyMPrim p L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    unfold SignalPqxdh.Security.anyMPrim SignalPqxdh.Security.FgGapDh.anyMPrim
    rw [ih]

private theorem security_findHonestPrincipalPrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    SignalPqxdh.Security.findHonestPrincipalPrim S principals ikB =
      SignalPqxdh.Security.FgGapDh.findHonestPrincipalPrim S principals ikB := by
  unfold SignalPqxdh.Security.findHonestPrincipalPrim
    SignalPqxdh.Security.FgGapDh.findHonestPrincipalPrim
  simp only [security_primQ_eq, security_findMPrim_eq]

private theorem security_isHonestUncorruptedPeerPrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    SignalPqxdh.Security.isHonestUncorruptedPeerPrim S principals ikB =
      SignalPqxdh.Security.FgGapDh.isHonestUncorruptedPeerPrim S principals ikB := by
  unfold SignalPqxdh.Security.isHonestUncorruptedPeerPrim
    SignalPqxdh.Security.FgGapDh.isHonestUncorruptedPeerPrim
  rw [security_findHonestPrincipalPrim_eq]
  rfl

private theorem security_checkBundleProvenancePrim_eq (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (bundle : PreKeyBundleInput) :
    SignalPqxdh.Security.checkBundleProvenancePrim S principals spkBundles opkEntries bundle =
      SignalPqxdh.Security.FgGapDh.checkBundleProvenancePrim S principals spkBundles opkEntries
        bundle := by
  unfold SignalPqxdh.Security.checkBundleProvenancePrim
    SignalPqxdh.Security.FgGapDh.checkBundleProvenancePrim
  simp only [security_primQ_eq, security_findHonestPrincipalPrim_eq, security_anyMPrim_eq]
  rfl

private theorem simulateQ_gapDhFullImpl_fgGenSpkActiveGdh {S : Setup}
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (spkIdx : Nat) (V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgGenSpkActiveGdh spkIdx V u j st) =
      fgGenSpkActivePure P spkIdx V u j st := by
  unfold fgGenSpkActiveGdh fgGenSpkActivePure
  dsimp only
  cases st.base.spkBundles.any (fun x => x.1 == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.base.principals.find? (fun x => x.1 == u.val) with
    | none => simp
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      simp only [simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh,
        simulateQ_gapDhFullImpl_primGdhQ_x25519Base,
        simulateQ_gapDhFullImpl_primGdhQ_sigSign,
        simulateQ_gapDhFullImpl_primGdhQ_kemKeyGen,
        pure_bind, simulateQ_pure]
  · simp

private theorem simulateQ_gapDhFullImpl_fgRunInitiateActiveGdh
    (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (dhFlag opkMode : Bool) (ephIdx : Nat) (S : Setup) (maxLen : Nat)
    (U : Bytes) (hasOpk : Bool) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S) (sendOpkCnt : Nat) :
    simulateQ (gapDhFullImpl P ddh)
      (fgRunInitiateActiveGdh dhFlag opkMode ephIdx S maxLen U hasOpk sid u bundle st sendOpkCnt) =
      fgRunInitiateActivePure P ddh dhFlag opkMode ephIdx S maxLen U hasOpk sid u bundle st
        sendOpkCnt := by
  unfold fgRunInitiateActiveGdh fgRunInitiateActivePure
  simp only [security_embedPrim_eq, security_findHonestPrincipalPrim_eq,
    security_isHonestUncorruptedPeerPrim_eq, security_checkBundleProvenancePrim_eq]
  cases (!(if hasOpk then bundle.opkB?.isSome else !bundle.opkB?.isSome))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.base.sessions.any (fun e => e.sid == sid)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.base.principals.find? (fun x => x.1 == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim,
          simulateQ_primBaseImpl_koskBundleOkPrim, pure_bind]
        by_cases hKosk : (!koskBundleOkTake S P st.base.principals st.base.spkBundles
          st.base.opkEntries st.advKeyPows bundle) = true
        · simp [hKosk]
        · simp only [hKosk, Bool.false_eq_true, ↓reduceIte,
            simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh,
            simulateQ_gapDhFullImpl_embedPrim, simulateQ_primBaseImpl_resolveSigPkPrim,
            simulateQ_gapDhFullImpl_primGdhQ_sigVerify, pure_bind]
          congr 1; ext ekASkRaw
          congr 1; ext kemCoins
          by_cases hv :
              (!(P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
                  (encodeEC bundle.spkB) bundle.spkSig &&
                 P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
                  (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
          · simp [hv]
          · simp only [hv, Bool.false_eq_true, ↓reduceIte,
              simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_kemEncaps, pure_bind]
            cases P.kemEncaps bundle.pqspkB kemCoins with
            | none => simp
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              simp only [simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_x25519Base,
                simulateQ_gapDhFullImpl_embedPrim,
                simulateQ_primBaseImpl_lookupSpkSkPrim,
                simulateQ_gapDhFullImpl_computeTwoSideOrPairPos,
                simulateQ_gapDhFullImpl_computeOptPos,
                simulateQ_gapDhFullImpl_fgPatch,
                simulateQ_gapDhFullImpl_chooseInitPartnerDrKeyRandGdh,
                simulateQ_primBaseImpl_isHonestUncorruptedPeerPrim,
                simulateQ_primBaseImpl_checkBundleProvenancePrim,
                simulateQ_primBaseImpl_findHonestPrincipalPrim,
                pure_bind]
              congr 1; ext ⟨drKeyReal, fgL'⟩
              congr 1; ext drKeyRand
              cases findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB <;> simp
    · simp
  · simp

private theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveStep
    (pa : FgActiveParams) (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (maxLen : Nat)
    (q : KeyIndQuery S) (stA : FgKeyInd1KeyActiveSimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgKeyInd1KeyActiveStep pa S maxLen q stA) =
      fgKeyInd1KeyActiveStepPure pa P uSk ddh S maxLen q stA := by
  cases q with
  | initPrin u =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPure
      fgInitPrin1KeyActiveGdh fgInitPrin1KeyActivePure
    dsimp only
    cases stA.st1.sim.base.principals.any (fun x => x.1 == u.val) <;> simp
  | genSPK u j =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPure
      fgGenSPK1KeyActiveGdh fgGenSPK1KeyActivePure
    dsimp only
    by_cases hPrin : optNatMatches stA.resolvedPrin? u.val = true
    · simp only [hPrin, ↓reduceIte]
      cases stA.st1.sim.base.spkBundles.any (fun x => x.1 == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases stA.st1.sim.base.principals.find? (fun x => x.1 == u.val) with
        | none => simp
        | some p =>
          rcases p with ⟨_, uEntry⟩
          dsimp only
          by_cases hZero : (stA.st1.sigBudget == 0) = true
          · simp [hZero]
          · simp only [hZero, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
              simulateQ_gapDhWithSignFullImpl_unifGdhSign,
              simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base,
              simulateQ_gapDhWithSignFullImpl_sigChalQ,
              simulateQ_gapDhWithSignFullImpl_primGdhSignQ_kemKeyGen,
              simulateQ_pure, pure_bind, bind_assoc]
      · simp
    · simp only [hPrin, Bool.false_eq_true, ↓reduceIte, liftSimStep1KeyActive,
        simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
        simulateQ_gapDhFullImpl_fgGenSpkActiveGdh, simulateQ_pure]
  | genOPK u j o =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPure
      fgGenOPKActiveGdh fgGenOPKActivePure
    dsimp only
    cases stA.st1.sim.base.opkEntries.any (fun x => x.1 == (u.val, j.val, o.val)) <;> simp
  | initiateOPK u i bundle =>
    simp only [fgKeyInd1KeyActiveStep, fgKeyInd1KeyActiveStepPure,
      fgInitiateActiveGdh, fgInitiateActivePure,
      simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_fgRunInitiateActiveGdh, simulateQ_pure]
  | initiateNoOPK u i bundle =>
    simp only [fgKeyInd1KeyActiveStep, fgKeyInd1KeyActiveStepPure,
      fgInitiateActiveGdh, fgInitiateActivePure,
      simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_fgRunInitiateActiveGdh, simulateQ_pure]
  | acceptOPK k j o hdr =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPure liftSimStep1KeyActive
    cases pa.opkMode <;>
      simp [simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
        simulateQ_gapDhFullImpl_fgRunAcceptOPKGdh,
        simulateQ_gapDhFullImpl_fgRunAcceptOPKGdhOpk]
  | _ =>
    simp only [fgKeyInd1KeyActiveStep, fgKeyInd1KeyActiveStepPure, liftSimStep1KeyActive,
      simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_fgKeyIndStep, simulateQ_pure]

private theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveFinish
    (pa : FgActiveParams) (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (maxLen : Nat)
    (stA : FgKeyInd1KeyActiveSimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgKeyInd1KeyActiveFinish pa S maxLen stA) =
      pure (fgKeyInd1KeyActiveFinishPure pa S P ddh maxLen stA) := by
  unfold fgKeyInd1KeyActiveFinish fgKeyInd1KeyActiveFinishPure
  split_ifs <;>
    simp [simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_extractCdhFromSimState,
      simulateQ_gapDhFullImpl_extractCdh2FromAdvRoLog,
      simulateQ_gapDhFullImpl_extractCdh4FromAdvRoLog]

private theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveRunWithParams
    (pa : FgActiveParams) (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh)
      (fgKeyInd1KeyActiveRunWithParams pa S b A) =
    (do
      let secb ← $ᵗ Bool
      let initSt := FgKeyInd1KeyActiveSimState.empty S b secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) +
        fgKeyInd1KeyActiveSimImpl pa P uSk ddh S b.q_total
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return fgKeyInd1KeyActiveFinishPure pa S P ddh b.q_total finalSt) := by
  unfold fgKeyInd1KeyActiveRunWithParams
  dsimp only
  rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign]
  congr 1; funext secb
  rw [simulateQ_bind,
    simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep P uSk ddh _ _
      (simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveStep pa P uSk ddh S b.q_total)]
  congr 1; funext ⟨_, finalSt⟩
  rw [simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveFinish]

private theorem gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdvAt_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (useDh1 : Bool) (ord1 spkOrd : Nat)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdvAt useDh1 ord1 spkOrd S b A) =
    (do
      let u ← sampleScalar32
      let v ← sampleScalar32
      let U := P.x25519Base u
      let V := P.x25519Base v
      let pa := if useDh1 then activeParamsDh1 b U V ord1 spkOrd
                else activeParamsDh3 b U V ord1 spkOrd
      let secb ← $ᵗ Bool
      let initSt := FgKeyInd1KeyActiveSimState.empty S b secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) +
        fgKeyInd1KeyActiveSimImpl pa P u ddh S b.q_total
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return (pow8 (fgKeyInd1KeyActiveFinishPure pa S P ddh b.q_total finalSt) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhWithSignExp fgKeyInd1KeyGapDhActiveAdvAt
  congr 1; funext u
  congr 1; funext v
  change (simulateQ (gapDhWithSignFullImpl P u ddh)
      (fgKeyInd1KeyActiveRunWithParams _ S b A) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  rw [simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveRunWithParams]
  simp only [bind_assoc, pure_bind]

/-! ## Creation-order pre-sampling -/

private def dynTargetIdx {S : Setup} (useDh1 : Bool) (targetOrd : Nat)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) : Nat :=
  if useDh1 then
    match q with
    | .initPrin u => if hst.base.principals.length == targetOrd then u.val else S.N_id
    | _ => S.N_id
  else
    match q with
    | .initiateOPK u i _ =>
      if hst.base.sessions.length == targetOrd then initSessionSlotIdx (.sendOPK u i)
      else S.N_send_tot
    | .initiateNoOPK u i _ =>
      if hst.base.sessions.length == targetOrd then initSessionSlotIdx (.sendNoOPK u i)
      else S.N_send_tot
    | _ => S.N_send_tot

private def dynSpkIdx {S : Setup} (spkOrd : Nat)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) : Nat :=
  match q with
  | .genSPK u j =>
    if hst.base.spkBundles.length == spkOrd then spkBundleFlatIdx S u j else S.N_spk_tot
  | _ => S.N_spk_tot

private noncomputable def pqxdhKeyIndFgOrdPreImpl1Key (useDh1 : Bool) (targetOrd spkOrd : Nat)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp) :=
  fun q => StateT.mk fun hst =>
    (pqxdhKeyIndFgPreImpl1Key useDh1
      (dynTargetIdx useDh1 targetOrd q hst)
      (dynSpkIdx spkOrd q hst)
      optUsk optVsk S P q).run hst

private theorem pqxdhKeyIndFgOrdPreImpl1Key_none_none_eq {S : Setup} (useDh1 : Bool)
    (targetOrd spkOrd : Nat) (P : Primitives) :
    pqxdhKeyIndFgOrdPreImpl1Key useDh1 targetOrd spkOrd none none S P =
      pqxdhKeyIndFgImpl1Key S P := by
  funext q
  change (StateT.mk fun hst =>
      (pqxdhKeyIndFgPreImpl1Key useDh1 (dynTargetIdx useDh1 targetOrd q hst)
        (dynSpkIdx spkOrd q hst) none none S P q).run hst) =
    pqxdhKeyIndFgImpl1Key S P q
  simp only [pqxdhKeyIndFgPreImpl1Key_none_none_eq]
  rfl

private def hasFiredSpkOrd {S : Setup} (spkOrd : Nat) (hst : KeyIndFgCutoffState S) : Prop :=
  spkOrd < hst.base.spkBundles.length

private def hasFiredPrinOrd {S : Setup} (pOrd : Nat) (hst : KeyIndFgCutoffState S) : Prop :=
  pOrd < hst.base.principals.length

private theorem pqxdhKeyIndFgPreImpl1Key_lengths_mono {S : Setup}
    (useDh1 : Bool) (tIdx bIdx : Nat) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl1Key useDh1 tIdx bIdx optUsk optVsk S P q).run hst)) :
    hst.base.principals.length ≤ x.2.base.principals.length ∧
    hst.base.spkBundles.length ≤ x.2.base.spkBundles.length ∧
    hst.base.sessions.length ≤ x.2.base.sessions.length := by
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      rw [hB]; simp
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq
      have hB := (Prod.mk.inj hEq).2
      rw [hB]; exact ⟨le_rfl, le_rfl, le_rfl⟩
  | _ =>
    exact mem_support_pqxdhKeyIndFgPreImpl_elim useDh1 tIdx bIdx optUsk optVsk P _ hst x hx
      (fun hP hS _ hSe => by rw [hP, hS, hSe]; exact ⟨le_rfl, le_rfl, le_rfl⟩)
      (fun _ _ hEq _ _ => by cases hEq)
      (fun _ _ _ _ _ hB => by rw [hB]; simp)
      (fun _ _ _ _ _ _ _ hB => by rw [hB]; simp)
      (fun _ _ _ _ _ _ _ hB => by rw [hB]; simp)
      (fun _ _ _ hB => by rw [hB]; simp)
      (fun _ _ _ hP hS hSe _ => by rw [hP, hS, hSe]; exact ⟨le_rfl, le_rfl, le_rfl⟩)
      (fun _ _ _ _ _ hP hS _ hSe => by rw [hP, hS, hSe]; simp)
      (fun _ _ hB => by rw [hB]; simp)

private theorem pqxdhKeyIndFgOrdPreImpl1Key_lengths_mono {S : Setup}
    (useDh1 : Bool) (targetOrd spkOrd : Nat) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgOrdPreImpl1Key useDh1 targetOrd spkOrd optUsk optVsk S P q).run hst)) :
    hst.base.principals.length ≤ x.2.base.principals.length ∧
    hst.base.spkBundles.length ≤ x.2.base.spkBundles.length ∧
    hst.base.sessions.length ≤ x.2.base.sessions.length :=
  pqxdhKeyIndFgPreImpl1Key_lengths_mono useDh1 (dynTargetIdx useDh1 targetOrd q hst)
    (dynSpkIdx spkOrd q hst) optUsk optVsk P q hst x hx

private theorem pqxdhKeyIndFgPreImpl1Key_spkBundles_step {S : Setup}
    (useDh1 : Bool) (tIdx bIdx : Nat) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl1Key useDh1 tIdx bIdx optUsk optVsk S P q).run hst)) :
    x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 := by
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      rw [hB]; simp
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq
      have hB := (Prod.mk.inj hEq).2
      rw [hB]; omega
  | _ =>
    exact mem_support_pqxdhKeyIndFgPreImpl_elim useDh1 tIdx bIdx optUsk optVsk P _ hst x hx
      (fun _ hS _ _ => by rw [hS]; omega)
      (fun _ _ hEq _ _ => by cases hEq)
      (fun _ _ _ _ _ hB => by rw [hB]; simp)
      (fun _ _ _ _ _ _ _ hB => by rw [hB]; simp)
      (fun _ _ _ _ _ _ _ hB => by rw [hB]; simp)
      (fun _ _ _ hB => by rw [hB]; simp)
      (fun _ _ _ _ hS _ _ => by rw [hS]; omega)
      (fun _ _ _ _ _ _ hS _ _ => by rw [hS]; omega)
      (fun _ _ hB => by rw [hB]; simp)

private theorem pqxdhKeyIndFgOrdPreImpl1Key_spkBundles_step {S : Setup}
    (useDh1 : Bool) (targetOrd spkOrd : Nat) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgOrdPreImpl1Key useDh1 targetOrd spkOrd optUsk optVsk S P q).run hst)) :
    x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 :=
  pqxdhKeyIndFgPreImpl1Key_spkBundles_step useDh1 (dynTargetIdx useDh1 targetOrd q hst)
    (dynSpkIdx spkOrd q hst) optUsk optVsk P q hst x hx

private theorem evalDist_preSample_spkOrd_1Key {S : Setup} {α : Type}
    (useDh1 : Bool) (targetOrd spkOrd : Nat) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgOrdPreImpl1Key useDh1 targetOrd spkOrd optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgOrdPreImpl1Key useDh1 targetOrd spkOrd optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
      𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredSpkOrd spkOrd)
    (pqxdhKeyIndFgOrdPreImpl1Key useDh1 targetOrd spkOrd optUsk none S P)
    (fun vSk => pqxdhKeyIndFgOrdPreImpl1Key useDh1 targetOrd spkOrd optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      Nat.lt_of_lt_of_le hFired
        (pqxdhKeyIndFgOrdPreImpl1Key_lengths_mono useDh1 targetOrd spkOrd optUsk none P q s x
          hx).2.1⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q with
    | initPrin _ => rfl
    | genSPK u j =>
      have hNeLen : (s.base.spkBundles.length == spkOrd) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hFired)
      have hNeSlot : (spkBundleFlatIdx S u j == S.N_spk_tot) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (spkSlotFlatIdx_lt S u.isLt j.isLt))
      unfold pqxdhKeyIndFgOrdPreImpl1Key dynSpkIdx pqxdhKeyIndFgPreImpl1Key
        pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
      simp only [StateT_run_mk, hNeLen, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind]
      cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none => rfl
        | some p => rcases p with ⟨_, _⟩; simp [hNeSlot]
      · rfl
    | _ => rfl
  · cases q with
    | initPrin _ => exact Or.inl (fun _ => rfl)
    | genSPK u j =>
      by_cases hLen : (s.base.spkBundles.length == spkOrd) = true
      · unfold pqxdhKeyIndFgOrdPreImpl1Key dynSpkIdx pqxdhKeyIndFgPreImpl1Key
          pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
        simp only [StateT_run_mk, hLen, ↓reduceIte,
          StateT.run_bind, StateT.run_get, pure_bind, beq_self_eq_true]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => exact Or.inl (fun _ => rfl)
          | some p =>
            rcases p with ⟨_, _⟩
            dsimp only
            refine Or.inr ⟨fun _ => ?_, fun vSk x hx => ?_⟩
            · simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc]
            · simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc,
                MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨_, _, _, _, _, _, hEq⟩
              have hB := (Prod.mk.inj hEq).2
              unfold hasFiredSpkOrd
              rw [hB, ← beq_iff_eq.mp hLen]
              simp
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun vSk => ?_)
        have hNeSlot : (spkBundleFlatIdx S u j == S.N_spk_tot) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (spkSlotFlatIdx_lt S u.isLt j.isLt))
        unfold pqxdhKeyIndFgOrdPreImpl1Key dynSpkIdx pqxdhKeyIndFgPreImpl1Key
          pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
        simp only [StateT_run_mk, hLen, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => rfl
          | some p => rcases p with ⟨_, _⟩; simp [hNeSlot]
        · rfl
    | _ => exact Or.inl (fun _ => rfl)

private theorem evalDist_preSample_prinOrd_dh1_1Key {S : Setup} {α : Type}
    (pOrd spkOrd : Nat) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
      𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredPrinOrd pOrd)
    (pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd none optVsk S P)
    (fun uSk => pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      Nat.lt_of_lt_of_le hFired
        (pqxdhKeyIndFgOrdPreImpl1Key_lengths_mono true pOrd spkOrd none optVsk P q s x hx).1⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro uSk
    cases q with
    | initPrin u =>
      have hNeLen : (s.base.principals.length == pOrd) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hFired)
      have hNeSlot : (u.val == S.N_id) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)
      unfold pqxdhKeyIndFgOrdPreImpl1Key dynTargetIdx pqxdhKeyIndFgPreImpl1Key
        fgPreInitPrin1Key liftFgBase
      simp only [StateT_run_mk, hNeLen, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
        StateT.run_bind, StateT.run_get, pure_bind]
      cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hNeSlot]
    | _ => rfl
  · cases q with
    | initPrin u =>
      by_cases hLen : (s.base.principals.length == pOrd) = true
      · unfold pqxdhKeyIndFgOrdPreImpl1Key dynTargetIdx pqxdhKeyIndFgPreImpl1Key
          fgPreInitPrin1Key liftFgBase
        simp only [StateT_run_mk, hLen, ↓reduceIte, Bool.true_and, beq_self_eq_true,
          StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun _ => ?_, fun uSk x hx => ?_⟩
          · simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind,
              support_pure, Set.mem_singleton_iff] at hx
            have hB := (Prod.mk.inj hx).2
            unfold hasFiredPrinOrd
            rw [hB, ← beq_iff_eq.mp hLen]
            simp
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun uSk => ?_)
        have hNeSlot : (u.val == S.N_id) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)
        unfold pqxdhKeyIndFgOrdPreImpl1Key dynTargetIdx pqxdhKeyIndFgPreImpl1Key
          fgPreInitPrin1Key liftFgBase
        simp only [StateT_run_mk, hLen, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
          StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hNeSlot]
    | _ => exact Or.inl (fun _ => rfl)

private theorem evalDist_preSample_sessOrd_dh3_1Key {S : Setup} {α : Type}
    (sOrd spkOrd : Nat) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
      𝒟[(simulateQ fullLazy oa).run hst >>= obs] :=
  evalDist_preSample_sessOrd_1Key sOrd spkOrd optVsk P oa hst obs

private theorem evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh1 {S : Setup}
    (pOrd spkOrd : Nat) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
      𝒟[runKeyIndFgSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim1Key
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) none S P) A.run).run
          (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_spkOrd_1Key true pOrd spkOrd (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_prinOrd_dh1_1Key pOrd spkOrd none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgOrdPreImpl1Key_none_none_eq]
  simp only [pure_bind]

private theorem evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh3 {S : Setup}
    (sOrd spkOrd : Nat) (P : Primitives) (A : KeyIndAdversary S)
    (obs : Bool × Bool × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd (some uSk) (some vSk) S P
    𝒟[do
        let uSk ← sampleScalar32
        let vSk ← sampleScalar32
        let secb ← $ᵗ Bool
        let initSt := KeyIndFgCutoffState.empty S secb
        let (b', finalHst) ← (simulateQ (fullPre uSk vSk) A.run).run initSt
        obs (secb, b', finalHst)] =
      𝒟[runKeyIndFgSim1Key S P A >>= obs] := by
  intro fullPre
  unfold runKeyIndFgSim1Key
  simp only [bind_assoc]
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ =>
    OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _)]
  rw [OracleComp.evalDist_bind_bind_swap sampleScalar32 ($ᵗ Bool) _]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hV : ∀ uSk,
      𝒟[sampleScalar32 >>= fun vSk =>
        (simulateQ (fullPre uSk vSk) A.run).run (KeyIndFgCutoffState.empty S secb) >>= fun x =>
          obs (secb, x.1, x.2)] =
      𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndFgCutoffState S) ProbComp) +
        pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd (some uSk) none S P) A.run).run
          (KeyIndFgCutoffState.empty S secb) >>= fun x => obs (secb, x.1, x.2)] :=
    fun uSk => evalDist_preSample_spkOrd_1Key false sOrd spkOrd (some uSk) P A.run
      (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))
  rw [OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun uSk _ => hV uSk)]
  rw [evalDist_preSample_sessOrd_dh3_1Key sOrd spkOrd none P A.run
    (KeyIndFgCutoffState.empty S secb) (fun x => obs (secb, x.1, x.2))]
  rw [pqxdhKeyIndFgOrdPreImpl1Key_none_none_eq]
  simp only [pure_bind]

/-! ## Dynamic slot retargeting and per-ordinal bounds -/

private theorem evalDist_simulateQ_eq_zero_of_dead_preserved_inv
    {ι α St : Type} {QSpec : OracleSpec.{0, 0} ι}
    (Inv : St → Prop) (Dead : St → Bool)
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (hInvPres : ∀ q st, Inv st → ∀ x ∈ support ((impl q).run st), Inv x.2)
    (hPres : ∀ q st, Inv st → Dead st = true → ∀ x ∈ support ((impl q).run st), Dead x.2 = true)
    (obs : α × St → ProbComp Bool)
    (hObs : ∀ a st, Inv st → Dead st = true → 𝒟[obs (a, st)] {true} = 0)
    (oa : OracleComp (unifSpec + QSpec) α) (st : St) (hInv : Inv st) (hDead : Dead st = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
    𝒟[(simulateQ full oa).run st >>= obs] {true} = 0 := by
  intro full
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hObs a st hInv hDead
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full]
      rw [simulateQ_run_query_inl, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun u _ => ih u st hInv hDead)
    · dsimp only [full]
      rw [simulateQ_run_query_inr, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun x hx =>
        ih x.1 x.2 (hInvPres gq st hInv x hx) (hPres gq st hInv hDead x hx))

private theorem evalDist_simulateQ_le_of_step_or_dead_inv
    {ι α St1 St2 : Type} {QSpec : OracleSpec.{0, 0} ι}
    (Inv1 : St1 → Prop)
    (Dead : St1 → Bool)
    (Rel : ℕ → St1 → St2 → Prop)
    (impl1 : QueryImpl QSpec (StateT St1 ProbComp))
    (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hInvPres : ∀ q s1, Inv1 s1 → ∀ x ∈ support ((impl1 q).run s1), Inv1 x.2)
    (hDeadPres : ∀ q s1, Inv1 s1 → Dead s1 = true →
      ∀ x ∈ support ((impl1 q).run s1), Dead x.2 = true)
    (hStep : ∀ (q : ι) (rem : ℕ) (s1 : St1) (s2 : St2),
      Inv1 s1 →
      Dead s1 = false →
      Rel (rem + 1) s1 s2 →
      ∀ (k1 : QSpec.Range q × St1 → ProbComp Bool)
        (k2 : QSpec.Range q × St2 → ProbComp Bool),
        (∀ r s1' s2', Inv1 s1' → Dead s1' = false → Rel rem s1' s2' →
          𝒟[k1 (r, s1')] {true} ≤ 𝒟[k2 (r, s2')] {true}) →
        (∀ r s1', Inv1 s1' → Dead s1' = true → 𝒟[k1 (r, s1')] {true} = 0) →
        𝒟[(impl1 q).run s1 >>= k1] {true} ≤ 𝒟[(impl2 q).run s2 >>= k2] {true})
    (obs1 : α × St1 → ProbComp Bool)
    (obs2 : α × St2 → ProbComp Bool)
    (hDeadObs : ∀ a s1, Inv1 s1 → Dead s1 = true → 𝒟[obs1 (a, s1)] {true} = 0)
    (hObs : ∀ a rem s1 s2, Inv1 s1 → Dead s1 = false → Rel rem s1 s2 →
      𝒟[obs1 (a, s1)] {true} ≤ 𝒟[obs2 (a, s2)] {true})
    (oa : OracleComp (unifSpec + QSpec) α) (rem : ℕ)
    (hQb : IsQueryBoundP oa (fun q : ℕ ⊕ ι => isGameQuery q = true) rem)
    (s1 : St1) (s2 : St2) (hInv1 : Inv1 s1) (hRel : Rel rem s1 s2) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    𝒟[(simulateQ full1 oa).run s1 >>= obs1] {true} ≤
      𝒟[(simulateQ full2 oa).run s2 >>= obs2] {true} := by
  intro full1 full2
  induction oa using OracleComp.inductionOn generalizing rem s1 s2 with
  | pure a =>
    by_cases hD : Dead s1 = true
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind, hDeadObs a s1 hInv1 hD, zero_le]
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hObs a rem s1 s2 hInv1 (Bool.eq_false_iff.mpr hD) hRel
  | query_bind q mx ih =>
    by_cases hD : Dead s1 = true
    · rw [evalDist_simulateQ_eq_zero_of_dead_preserved_inv Inv1 Dead impl1 hInvPres hDeadPres obs1
        hDeadObs _ s1 hInv1 hD]
      exact zero_le
    · have hDF : Dead s1 = false := Bool.eq_false_iff.mpr hD
      rw [isQueryBoundP_query_bind_iff] at hQb
      rcases q with uq | gq
      · rcases hQb with ⟨_, hCont⟩
        simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at hCont
        dsimp only [full1, full2]
        rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
        exact evalDist_bind_true_mono_of_support _ _ _ (fun u _ =>
          ih u rem (hCont u) s1 s2 hInv1 hRel)
      · rcases hQb with ⟨hAbs | hPos, hCont⟩
        · exfalso; exact hAbs rfl
        · obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 := ⟨rem - 1, by omega⟩
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at hCont
          dsimp only [full1, full2]
          rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
          let k1' : QSpec.Range gq × St1 → ProbComp Bool :=
            open scoped Classical in
            fun x => if Inv1 x.2 then (simulateQ full1 (mx x.1)).run x.2 >>= obs1 else pure false
          have hLhsEq : 𝒟[(impl1 gq).run s1 >>= fun x =>
              (simulateQ full1 (mx x.1)).run x.2 >>= obs1] =
              𝒟[(impl1 gq).run s1 >>= k1'] :=
            OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => by
              simp only [k1', hInvPres gq s1 hInv1 x hx, ↓reduceIte])
          rw [hLhsEq]
          exact hStep gq rem' s1 s2 hInv1 hDF hRel
            k1'
            (fun x => (simulateQ full2 (mx x.1)).run x.2 >>= obs2)
            (fun r s1' s2' hI' _ hR => by
              simp only [k1', hI', ↓reduceIte]
              exact ih r rem' (hCont r) s1' s2' hI' hR)
            (fun r s1' hI' hD' => by
              simp only [k1', hI', ↓reduceIte]
              exact evalDist_simulateQ_eq_zero_of_dead_preserved_inv Inv1 Dead impl1 hInvPres
                hDeadPres obs1 hDeadObs (mx r) s1' hI' hD')

private theorem reverse_getElem?_of_ge {α : Type} (xs : List α) (ord : Nat) (h : xs.length ≤ ord) :
    xs.reverse[ord]? = none :=
  List.getElem?_eq_none (by simpa using h)

private theorem reverse_cons_getElem?_eq {α : Type} (x : α) (xs : List α) :
    (x :: xs).reverse[xs.length]? = some x := by
  rw [List.reverse_cons, List.getElem?_append_right (by simp)]
  simp

private theorem reverse_cons_getElem?_of_lt {α : Type} (x : α) (xs : List α) (ord : Nat)
    (h : ord < xs.length) :
    (x :: xs).reverse[ord]? = xs.reverse[ord]? := by
  rw [List.reverse_cons, List.getElem?_append_left (by simpa using h)]

private theorem reverse_map_getElem? {α β : Type} (f : α → β) (xs : List α) (ord : Nat) :
    (xs.map f).reverse[ord]? = (xs.reverse[ord]?).map f := by
  rw [← List.map_reverse, List.getElem?_map]

private theorem prinSlotAtOrd_of_ge {S : Setup} (st : KeyIndState S) (pOrd : Nat)
    (h : st.principals.length ≤ pOrd) :
    prinSlotAtOrd S st pOrd = S.N_id := by
  unfold prinSlotAtOrd; rw [reverse_getElem?_of_ge _ _ h]

private theorem spkSlotAtOrd_of_ge {S : Setup} (st : KeyIndState S) (spkOrd : Nat)
    (h : st.spkBundles.length ≤ spkOrd) :
    spkSlotAtOrd S st spkOrd = S.N_spk_tot := by
  unfold spkSlotAtOrd; rw [reverse_getElem?_of_ge _ _ h]

private theorem sessSlotAtOrd_of_ge {S : Setup} (st : KeyIndState S) (sOrd : Nat)
    (h : st.sessions.length ≤ sOrd) :
    sessSlotAtOrd S st sOrd = S.N_send_tot := by
  unfold sessSlotAtOrd; rw [reverse_getElem?_of_ge _ _ h]

private theorem prinSlotAtOrd_mem_of_lt {S : Setup} (st : KeyIndState S) (pOrd : Nat)
    (h : pOrd < st.principals.length) :
    ∃ kv ∈ st.principals, kv.1 = prinSlotAtOrd S st pOrd := by
  have hLtRev : pOrd < st.principals.reverse.length := by simpa using h
  have hGet : st.principals.reverse[pOrd]? = some (st.principals.reverse[pOrd]'hLtRev) :=
    List.getElem?_eq_getElem hLtRev
  refine ⟨st.principals.reverse[pOrd]'hLtRev,
    List.mem_reverse.mp (List.getElem_mem hLtRev), ?_⟩
  unfold prinSlotAtOrd; rw [hGet]

private theorem spkSlotAtOrd_mem_of_lt {S : Setup} (st : KeyIndState S) (spkOrd : Nat)
    (h : spkOrd < st.spkBundles.length) :
    ∃ kb ∈ st.spkBundles, spkBundleFlatIdxVal S kb.1 = spkSlotAtOrd S st spkOrd := by
  have hLtRev : spkOrd < st.spkBundles.reverse.length := by simpa using h
  have hGet : st.spkBundles.reverse[spkOrd]? = some (st.spkBundles.reverse[spkOrd]'hLtRev) :=
    List.getElem?_eq_getElem hLtRev
  refine ⟨st.spkBundles.reverse[spkOrd]'hLtRev,
    List.mem_reverse.mp (List.getElem_mem hLtRev), ?_⟩
  unfold spkSlotAtOrd; rw [hGet]

private theorem sessSlotAtOrd_mem_of_lt {S : Setup} (st : KeyIndState S) (sOrd : Nat)
    (h : sOrd < st.sessions.length) :
    ∃ s ∈ st.sessions, initSessionSlotIdx s.sid = sessSlotAtOrd S st sOrd := by
  have hLtRev : sOrd < st.sessions.reverse.length := by simpa using h
  have hGet : st.sessions.reverse[sOrd]? = some (st.sessions.reverse[sOrd]'hLtRev) :=
    List.getElem?_eq_getElem hLtRev
  refine ⟨st.sessions.reverse[sOrd]'hLtRev,
    List.mem_reverse.mp (List.getElem_mem hLtRev), ?_⟩
  unfold sessSlotAtOrd; rw [hGet]

private theorem prinSlotAtOrd_cons_eq {S : Setup} (st st' : KeyIndState S) (u : Nat)
    (e : PrincipalEntry) (pOrd : Nat)
    (hP : st'.principals = (u, e) :: st.principals) (hLen : st.principals.length = pOrd) :
    prinSlotAtOrd S st' pOrd = u := by
  unfold prinSlotAtOrd; rw [hP, ← hLen, reverse_cons_getElem?_eq]

private theorem prinSlotAtOrd_cons_of_lt {S : Setup} (st st' : KeyIndState S) (u : Nat)
    (e : PrincipalEntry) (pOrd : Nat)
    (hP : st'.principals = (u, e) :: st.principals) (hLt : pOrd < st.principals.length) :
    prinSlotAtOrd S st' pOrd = prinSlotAtOrd S st pOrd := by
  unfold prinSlotAtOrd; rw [hP, reverse_cons_getElem?_of_lt _ _ _ hLt]

private theorem prinSlotAtOrd_map {S : Setup} (st st' : KeyIndState S)
    (f : Nat × PrincipalEntry → Nat × PrincipalEntry) (hf : ∀ kv, (f kv).1 = kv.1) (pOrd : Nat)
    (hP : st'.principals = st.principals.map f) :
    prinSlotAtOrd S st' pOrd = prinSlotAtOrd S st pOrd := by
  unfold prinSlotAtOrd; rw [hP, reverse_map_getElem?]
  cases st.principals.reverse[pOrd]? with
  | none => rfl
  | some kv => exact hf kv

private theorem spkSlotAtOrd_cons_eq {S : Setup} (st st' : KeyIndState S) (u : Fin S.N_id)
    (j : Fin S.N_recv) (bEntry : SpkBundleEntry) (spkOrd : Nat)
    (hS : st'.spkBundles = ((u.val, j.val), bEntry) :: st.spkBundles)
    (hLen : st.spkBundles.length = spkOrd) :
    spkSlotAtOrd S st' spkOrd = spkBundleFlatIdx S u j := by
  unfold spkSlotAtOrd; rw [hS, ← hLen, reverse_cons_getElem?_eq]; rfl

private theorem spkSlotAtOrd_cons_of_lt {S : Setup} (st st' : KeyIndState S) (k : Nat × Nat)
    (bEntry : SpkBundleEntry) (spkOrd : Nat)
    (hS : st'.spkBundles = (k, bEntry) :: st.spkBundles) (hLt : spkOrd < st.spkBundles.length) :
    spkSlotAtOrd S st' spkOrd = spkSlotAtOrd S st spkOrd := by
  unfold spkSlotAtOrd; rw [hS, reverse_cons_getElem?_of_lt _ _ _ hLt]

private theorem spkSlotAtOrd_map {S : Setup} (st st' : KeyIndState S)
    (f : (Nat × Nat) × SpkBundleEntry → (Nat × Nat) × SpkBundleEntry)
    (hf : ∀ kb, (f kb).1 = kb.1) (spkOrd : Nat)
    (hS : st'.spkBundles = st.spkBundles.map f) :
    spkSlotAtOrd S st' spkOrd = spkSlotAtOrd S st spkOrd := by
  unfold spkSlotAtOrd; rw [hS, reverse_map_getElem?]
  cases st.spkBundles.reverse[spkOrd]? with
  | none => rfl
  | some kb => dsimp only [Option.map]; rw [hf kb]

private theorem sessSlotAtOrd_cons_eq {S : Setup} (st st' : KeyIndState S)
    (s : KeyIndInitiatorEntry S) (sOrd : Nat)
    (hSe : st'.sessions = s :: st.sessions) (hLen : st.sessions.length = sOrd) :
    sessSlotAtOrd S st' sOrd = initSessionSlotIdx s.sid := by
  unfold sessSlotAtOrd; rw [hSe, ← hLen, reverse_cons_getElem?_eq]

private theorem sessSlotAtOrd_cons_of_lt {S : Setup} (st st' : KeyIndState S)
    (s : KeyIndInitiatorEntry S) (sOrd : Nat)
    (hSe : st'.sessions = s :: st.sessions) (hLt : sOrd < st.sessions.length) :
    sessSlotAtOrd S st' sOrd = sessSlotAtOrd S st sOrd := by
  unfold sessSlotAtOrd; rw [hSe, reverse_cons_getElem?_of_lt _ _ _ hLt]

private theorem sessSlotAtOrd_map {S : Setup} (st st' : KeyIndState S)
    (f : KeyIndInitiatorEntry S → KeyIndInitiatorEntry S) (hf : ∀ s, (f s).sid = s.sid)
    (sOrd : Nat) (hSe : st'.sessions = st.sessions.map f) :
    sessSlotAtOrd S st' sOrd = sessSlotAtOrd S st sOrd := by
  unfold sessSlotAtOrd; rw [hSe, reverse_map_getElem?]
  cases st.sessions.reverse[sOrd]? with
  | none => rfl
  | some s => dsimp only [Option.map]; rw [hf s]

private theorem fgPreInitiate_sid_mem {S : Setup} (useDh1 : Bool) (sIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : KeyIndState S)
    (x : KeyIndResponse × KeyIndState S)
    (hx : x ∈ support ((fgPreInitiate useDh1 sIdx optUsk S P sid u bundle).run st)) :
    ∀ s ∈ x.2.sessions, s ∈ st.sessions ∨ s.sid = sid := by
  unfold fgPreInitiate at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  revert hx
  cases st.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs
    | some p =>
      rcases p with ⟨_, _⟩; dsimp only
      cases koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff]
        intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind]
        rintro ⟨_, _, _, _, hb⟩; revert hb
        split_ifs
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs
        · cases P.kemEncaps bundle.pqspkB _ with
          | none =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
            intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs
          | some sc =>
            rcases sc with ⟨_, _⟩; dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
              bind_assoc, pure_bind, MonadAttach.mem_support_bind]
            rintro ⟨⟨_, _⟩, _, _, _, hb⟩; revert hb
            cases findHonestPrincipal P st.principals bundle.ikB <;>
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
              intro hEq s hs
              rw [(Prod.mk.inj hEq).2] at hs
              rcases List.mem_cons.mp hs with rfl | hMem
              · exact Or.inr rfl
              · exact Or.inl hMem
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs

private def ValidOrdInv {S : Setup} (spkOrd : Nat) (V : Bytes)
    (hst : KeyIndFgCutoffState S) : Prop :=
  (∀ kv ∈ hst.base.principals, kv.1 < S.N_id) ∧
  (∀ kb ∈ hst.base.spkBundles, kb.1.1 < S.N_id ∧ kb.1.2 < S.N_recv) ∧
  (∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid < S.N_send_tot) ∧
  spkTargetIsV (spkSlotAtOrd S hst.base spkOrd) V hst = true

private theorem validOrdInv_empty {S : Setup} (spkOrd : Nat) (V : Bytes) (secb : Bool) :
    ValidOrdInv spkOrd V (KeyIndFgCutoffState.empty S secb) :=
  ⟨fun _ h => False.elim (List.not_mem_nil h),
   fun _ h => False.elim (List.not_mem_nil h),
   fun _ h => False.elim (List.not_mem_nil h), rfl⟩

private theorem spkBundleFlatIdxVal_lt_of_bounds {S : Setup} {k : Nat × Nat}
    (hk : k.1 < S.N_id ∧ k.2 < S.N_recv) :
    spkBundleFlatIdxVal S k < S.N_spk_tot := by
  change spkBundleFlatIdx S ⟨k.1, hk.1⟩ ⟨k.2, hk.2⟩ < S.N_spk_tot
  exact spkSlotFlatIdx_lt S hk.1 hk.2

private theorem hasFiredSpk_of_spkOrd_lt {S : Setup} (spkOrd : Nat)
    (hst : KeyIndFgCutoffState S)
    (hSpkB : ∀ kb ∈ hst.base.spkBundles, kb.1.1 < S.N_id ∧ kb.1.2 < S.N_recv)
    (hLt : spkOrd < hst.base.spkBundles.length) :
    hasFiredSpk S (spkSlotAtOrd S hst.base spkOrd) hst := by
  obtain ⟨⟨⟨u0, j0⟩, b0⟩, hMem, hVal⟩ := spkSlotAtOrd_mem_of_lt hst.base spkOrd hLt
  have hk := hSpkB ((u0, j0), b0) hMem
  exact ⟨⟨u0, hk.1⟩, ⟨j0, hk.2⟩, hVal,
    List.any_eq_true.mpr ⟨((u0, j0), b0), hMem, beq_self_eq_true _⟩⟩

private theorem pqxdhKeyIndFgPreImpl_sessions_len_of_ne_init {S : Setup}
    (useDh1 : Bool) (tIdx bIdx : Nat) (optU optV : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S)
    (hNoOpk : ∀ u i b, q ≠ .initiateOPK u i b)
    (hNoNoOpk : ∀ u i b, q ≠ .initiateNoOPK u i b)
    (hst : KeyIndFgCutoffState S) (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl useDh1 tIdx bIdx optU optV S P q).run hst)) :
    x.2.base.sessions.length = hst.base.sessions.length := by
  have unch : x.2.base = hst.base → x.2.base.sessions.length = hst.base.sessions.length :=
    fun h => by rw [h]
  cases q with
  | initiateOPK u i b => exact absurd rfl (hNoOpk u i b)
  | initiateNoOPK u i b => exact absurd rfl (hNoNoOpk u i b)
  | initPrin u =>
    unfold pqxdhKeyIndFgPreImpl fgPreInitPrin at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, _, _, hEq⟩; rw [(Prod.mk.inj hEq).2]
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unch (Prod.mk.inj hEq).2
  | genSPK u j =>
    unfold pqxdhKeyIndFgPreImpl fgPreGenSPK at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact unch (Prod.mk.inj hEq).2
      | some p =>
        rcases p with ⟨_, _⟩
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff]
        rintro ⟨_, _, _, _, _, _, _, _, hEq⟩; rw [(Prod.mk.inj hEq).2]
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unch (Prod.mk.inj hEq).2
  | corruptIK u =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unch (Prod.mk.inj hEq).2
    | some p =>
      rcases p with ⟨_, _⟩
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; rw [(Prod.mk.inj hEq).2]
  | genOPK u j o =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩; rw [(Prod.mk.inj hEq).2]
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unch (Prod.mk.inj hEq).2
  | acceptOPK k j o hdr =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    split_ifs
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
    · cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
      | some kp =>
        rcases kp with ⟨_, _⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
          | some op =>
            rcases op with ⟨_, _⟩; dsimp only
            split_ifs
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
            · cases acceptKeys P _ with
              | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
              | some _ =>
                dsimp only
                cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
                | some _ =>
                  dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    bind_assoc, pure_bind, MonadAttach.mem_support_bind]
                  rintro ⟨⟨_, _⟩, _, y, hy, hb⟩
                  rcases mem_support_recordKeyIndResp P _ _ y hy with ⟨_, _, _, hSe⟩
                  revert hb
                  cases findHonestPrincipal P hst.base.principals hdr.ikAPk <;>
                  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                    intro hEq; rw [(Prod.mk.inj hEq).2, hSe]
  | acceptNoOPK k j l hdr =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    split_ifs
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
    · cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
      | some kp =>
        rcases kp with ⟨_, _⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          cases acceptKeys P _ with
          | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
          | some _ =>
            dsimp only
            cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
            | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro h; exact unch (Prod.mk.inj h).2
            | some _ =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                bind_assoc, pure_bind, MonadAttach.mem_support_bind]
              rintro ⟨⟨_, _⟩, _, y, hy, hb⟩
              rcases mem_support_recordKeyIndResp P _ _ y hy with ⟨_, _, _, hSe⟩
              revert hb
              cases findHonestPrincipal P hst.base.principals hdr.ikAPk <;>
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                intro hEq; rw [(Prod.mk.inj hEq).2, hSe]
  | testSession sid =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    by_cases h1 : (!isKeyIndSessionTestable hst.base sid) = true
    · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro h; exact unch (Prod.mk.inj h).2
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      cases hst.base.sessions.find? (fun e => e.sid == sid) with
      | some _ =>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff]
        intro hEq; rw [(Prod.mk.inj hEq).2]; simp
      | none =>
        cases hst.base.respSessions.find? (fun r => r.sid == sid) <;>
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff]
          intro hEq; rw [(Prod.mk.inj hEq).2]
  | revealSessionKey sid =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      by_cases ht : e.tested = true
      · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro h; exact unch (Prod.mk.inj h).2
      · simp only [ht, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff]
        intro hEq; rw [(Prod.mk.inj hEq).2]; simp
    | none =>
      cases hst.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro h; exact unch (Prod.mk.inj h).2
      | some r =>
        by_cases ht : r.tested = true
        · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro h; exact unch (Prod.mk.inj h).2
        · simp only [ht, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff]
          intro hEq; rw [(Prod.mk.inj hEq).2]
  | roQuery secrets =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨_, _⟩, _, hEq⟩; rw [(Prod.mk.inj hEq).2]
  | revealDhSecrets =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb
    exact unch (Prod.mk.inj hb).2
  | registerKey sk =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl registerAdvKey at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    split_ifs <;>
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; rw [(Prod.mk.inj hEq).2]
  | revealSpkSk u j =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) <;>
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; rw [(Prod.mk.inj hEq).2]

private theorem pqxdhKeyIndFgOrdPreImpl1Key_preserves_validOrdInv {S : Setup}
    (useDh1 : Bool) (tOrd spkOrd : Nat) (uSk vSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hInv : ValidOrdInv spkOrd (P.x25519Base vSk) hst)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgOrdPreImpl1Key useDh1 tOrd spkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    ValidOrdInv spkOrd (P.x25519Base vSk) x.2 := by
  set V := P.x25519Base vSk
  rcases hInv with ⟨hPrinB, hSpkB, hSessB, hSpkV⟩
  have hUnchSpk : x.2.base.spkBundles = hst.base.spkBundles →
      spkTargetIsV (spkSlotAtOrd S x.2.base spkOrd) V x.2 = true := by
    intro hS
    have hOrdEq : spkSlotAtOrd S x.2.base spkOrd = spkSlotAtOrd S hst.base spkOrd := by
      unfold spkSlotAtOrd; rw [hS]
    unfold spkTargetIsV at hSpkV ⊢
    rw [hOrdEq, hS]; exact hSpkV
  have hInitCases :
      (∃ u, q = .initPrin u) ∨
      (∃ u i bundle, q = .initiateOPK u i bundle) ∨
      (∃ u i bundle, q = .initiateNoOPK u i bundle) ∨
      ((∀ u, q ≠ .initPrin u) ∧
       (∀ u i bundle, q ≠ .initiateOPK u i bundle) ∧
       (∀ u i bundle, q ≠ .initiateNoOPK u i bundle)) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | initiateOPK u i b => exact Or.inr (Or.inl ⟨u, i, b, rfl⟩)
    | initiateNoOPK u i b => exact Or.inr (Or.inr (Or.inl ⟨u, i, b, rfl⟩))
    | _ =>
      exact Or.inr (Or.inr (Or.inr
        ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩))
  rcases hInitCases with ⟨u, rfl⟩ | ⟨u, i, bundle, rfl⟩ | ⟨u, i, bundle, rfl⟩ |
    ⟨hNeInit, hNoOpk, hNoNoOpk⟩
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      refine ⟨?_, by rw [hB]; exact hSpkB, by rw [hB]; exact hSessB, hUnchSpk (by rw [hB])⟩
      rw [hB]; dsimp only; intro kv hMem
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact u.isLt
      · exact hPrinB kv hMem
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact ⟨by rw [hB]; exact hPrinB, by rw [hB]; exact hSpkB, by rw [hB]; exact hSessB,
        hUnchSpk (by rw [hB])⟩
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      intro hb
      exact mem_support_fgPreInitiate_elim _ _ _ P (.sendOPK u i) u bundle hst.base _ hb
        (fun hEq => by
          dsimp only at hEq
          exact ⟨by rw [hEq]; exact hPrinB, by rw [hEq]; exact hSpkB,
            by rw [hEq]; exact hSessB, hUnchSpk (by rw [hEq])⟩)
        (fun _ _ _ hEq => by
          dsimp only at hEq
          exact ⟨by rw [hEq]; exact hPrinB, by rw [hEq]; exact hSpkB, fun s hs => by
            rcases fgPreInitiate_sid_mem _ _ _ P (.sendOPK u i) u bundle hst.base _ hb s hs with
              hOld | hSid
            · exact hSessB s hOld
            · rw [hSid]
              exact Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _),
            hUnchSpk (by rw [hEq])⟩)
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact ⟨by rw [hB]; exact hPrinB, by rw [hB]; exact hSpkB, by rw [hB]; exact hSessB,
        hUnchSpk (by rw [hB])⟩
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      intro hb
      exact mem_support_fgPreInitiate_elim _ _ _ P (.sendNoOPK u i) u bundle hst.base _ hb
        (fun hEq => by
          dsimp only at hEq
          exact ⟨by rw [hEq]; exact hPrinB, by rw [hEq]; exact hSpkB,
            by rw [hEq]; exact hSessB, hUnchSpk (by rw [hEq])⟩)
        (fun _ _ _ hEq => by
          dsimp only at hEq
          exact ⟨by rw [hEq]; exact hPrinB, by rw [hEq]; exact hSpkB, fun s hs => by
            rcases fgPreInitiate_sid_mem _ _ _ P (.sendNoOPK u i) u bundle hst.base _ hb s hs with
              hOld | hSid
            · exact hSessB s hOld
            · rw [hSid]; exact initSessionSlotIdx_sendNoOPK_lt u i,
            hUnchSpk (by rw [hEq])⟩)
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact ⟨by rw [hB]; exact hPrinB, by rw [hB]; exact hSpkB, by rw [hB]; exact hSessB,
        hUnchSpk (by rw [hB])⟩
  · unfold pqxdhKeyIndFgOrdPreImpl1Key at hx
    simp only [StateT_run_mk] at hx
    rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin useDh1 _ _ _ _ P q hNeInit] at hx
    have hSessLen := pqxdhKeyIndFgPreImpl_sessions_len_of_ne_init useDh1
      (dynTargetIdx useDh1 tOrd q hst) (dynSpkIdx spkOrd q hst) (some uSk) (some vSk)
      P q hNoOpk hNoNoOpk hst x hx
    refine mem_support_pqxdhKeyIndFgPreImpl_elim useDh1
      (dynTargetIdx useDh1 tOrd q hst) (dynSpkIdx spkOrd q hst) (some uSk) (some vSk) P q hst x hx
      (fun hP hS _ hSe => ⟨hP ▸ hPrinB, hS ▸ hSpkB, hSe ▸ hSessB, hUnchSpk hS⟩)
      (fun u _ hq _ _ => absurd hq (hNeInit u))
      (fun u _ _ _ _ hB => ⟨by
        rw [hB]; dsimp only; rintro kv hMem
        rcases List.mem_map.mp hMem with ⟨⟨idx, e⟩, hOld, hEq⟩
        dsimp only at hEq
        have h1 : kv.1 = idx := by split_ifs at hEq <;> (subst hEq; rfl)
        rw [h1]; exact hPrinB (idx, e) hOld,
        by rw [hB]; exact hSpkB, by rw [hB]; exact hSessB, hUnchSpk (by rw [hB])⟩)
      (fun u j bEntry hq hAny _ hTgt hB => ?_)
      (fun _ _ _ _ _ _ _ hB => ⟨by rw [hB]; exact hPrinB, by rw [hB]; exact hSpkB,
        by rw [hB]; exact hSessB, hUnchSpk (by rw [hB])⟩)
      (fun s _ _ hB => by rw [hB] at hSessLen; simp at hSessLen)
      (fun _ _ _ hP hS hSe _ => ⟨hP ▸ hPrinB, hS ▸ hSpkB, hSe ▸ hSessB, hUnchSpk hS⟩)
      (fun f hfSid _ _ _ hP hS _ hSe => ⟨hP ▸ hPrinB, hS ▸ hSpkB, fun s hs => by
        rw [hSe, List.mem_map] at hs
        rcases hs with ⟨s0, hs0, rfl⟩
        rw [hfSid s0]; exact hSessB s0 hs0, hUnchSpk hS⟩)
      (fun u j hB => ⟨by rw [hB]; exact hPrinB, by
        rw [hB]; dsimp only; rintro kb hMem
        rcases List.mem_map.mp hMem with ⟨⟨idx, b⟩, hOld, hEq⟩
        dsimp only at hEq
        have h1 : kb.1 = idx := by split_ifs at hEq <;> (subst hEq; rfl)
        rw [h1]; exact hSpkB (idx, b) hOld,
        by rw [hB]; exact hSessB, by
        have hOrdEq := spkSlotAtOrd_map hst.base x.2.base
          (fun (idx, b) => if idx == (u.val, j.val) then (idx, { b with revealed := true })
            else (idx, b))
          (fun ⟨idx, b⟩ => by dsimp only; split_ifs <;> rfl) spkOrd (by rw [hB])
        rw [hOrdEq, spkTargetIsV_map_revealed_base _ V u j hst x.2 hB]
        exact hSpkV⟩)
    have hSpkB' : ∀ kb ∈ x.2.base.spkBundles, kb.1.1 < S.N_id ∧ kb.1.2 < S.N_recv := by
      rw [hB]; dsimp only; intro kb hMem
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact ⟨u.isLt, j.isLt⟩
      · exact hSpkB kb hMem
    refine ⟨by rw [hB]; exact hPrinB, hSpkB', by rw [hB]; exact hSessB, ?_⟩
    rcases lt_trichotomy spkOrd hst.base.spkBundles.length with hLt | hEqLen | hGt
    · rw [spkSlotAtOrd_cons_of_lt hst.base x.2.base _ bEntry spkOrd (by rw [hB]) hLt]
      have hFired := hasFiredSpk_of_spkOrd_lt spkOrd hst hSpkB hLt
      have hNeSlot : (spkBundleFlatIdx S u j == spkSlotAtOrd S hst.base spkOrd) = false := by
        cases hS : (spkBundleFlatIdx S u j == spkSlotAtOrd S hst.base spkOrd)
        · rfl
        · exfalso
          have := spkBundles_any_of_hasFiredSpk S _ hst hFired u j hS
          rw [hAny] at this; cases this
      unfold spkTargetIsV at hSpkV ⊢
      rw [hB]; dsimp only
      rw [List.all_cons, hSpkV, Bool.and_true]
      have hSlotV : (spkBundleFlatIdxVal S (u.val, j.val) == spkSlotAtOrd S hst.base spkOrd) =
          false := hNeSlot
      simp [hSlotV]
    · rw [spkSlotAtOrd_cons_eq hst.base x.2.base u j bEntry spkOrd (by rw [hB]) hEqLen.symm]
      have hDynEq : (spkBundleFlatIdx S u j == dynSpkIdx spkOrd q hst) = true := by
        simp [hq, dynSpkIdx, hEqLen]
      have hPk : bEntry.spkPk = V := (hTgt vSk rfl hDynEq).2
      unfold spkTargetIsV
      rw [hB]; dsimp only
      rw [List.all_cons]
      refine Bool.and_eq_true_iff.mpr ⟨by simp [spkBundleFlatIdxVal, spkBundleFlatIdx, hPk], ?_⟩
      rw [List.all_eq_true]
      rintro ⟨k, bOld⟩ hMem
      have hk := hSpkB (k, bOld) hMem
      have hNe : (spkBundleFlatIdxVal S k == spkBundleFlatIdx S u j) = false := by
        cases hE : (spkBundleFlatIdxVal S k == spkBundleFlatIdx S u j)
        · rfl
        · exfalso
          have hInj := spkBundleFlatIdx_inj S ⟨k.1, hk.1⟩ u ⟨k.2, hk.2⟩ j (beq_iff_eq.mp hE)
          have hkEq : k = (u.val, j.val) :=
            Prod.ext (congrArg Fin.val hInj.1) (congrArg Fin.val hInj.2)
          have hAnyT : hst.base.spkBundles.any (fun (k0, _) => k0 == (u.val, j.val)) = true :=
            List.any_eq_true.mpr ⟨(k, bOld), hMem, beq_iff_eq.mpr hkEq⟩
          rw [hAny] at hAnyT; cases hAnyT
      simp [hNe]
    · have hGe : x.2.base.spkBundles.length ≤ spkOrd := by
        rw [hB]; dsimp only [List.length_cons]; omega
      rw [spkSlotAtOrd_of_ge x.2.base spkOrd hGe]
      unfold spkTargetIsV
      rw [List.all_eq_true]
      rintro ⟨k, b0⟩ hMem
      have hLtSlot := spkBundleFlatIdxVal_lt_of_bounds (hSpkB' (k, b0) hMem)
      have hNe : (spkBundleFlatIdxVal S k == S.N_spk_tot) = false :=
        beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hLtSlot)
      simp [hNe]

private theorem pqxdhKeyIndFgOrdPreImpl1Key_spkSlotAtOrd_eq_of_lt {S : Setup}
    (useDh1 : Bool) (tOrd spkOrd : Nat) (uSk vSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hSpkOrdLt : spkOrd < hst.base.spkBundles.length)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgOrdPreImpl1Key useDh1 tOrd spkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    spkSlotAtOrd S x.2.base spkOrd = spkSlotAtOrd S hst.base spkOrd := by
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNeInit
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩; unfold spkSlotAtOrd; rw [(Prod.mk.inj hEq).2]
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; unfold spkSlotAtOrd; rw [(Prod.mk.inj hEq).2]
  · unfold pqxdhKeyIndFgOrdPreImpl1Key at hx
    simp only [StateT_run_mk] at hx
    rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin useDh1 _ _ _ _ P q hNeInit] at hx
    exact mem_support_pqxdhKeyIndFgPreImpl_elim useDh1 (dynTargetIdx useDh1 tOrd q hst)
      (dynSpkIdx spkOrd q hst) (some uSk) (some vSk) P q hst x hx
      (fun _ hS _ _ => by unfold spkSlotAtOrd; rw [hS])
      (fun u _ hq _ _ => absurd hq (hNeInit u))
      (fun _ _ _ _ _ hB => by unfold spkSlotAtOrd; rw [hB])
      (fun _ _ _ _ _ _ _ hB => spkSlotAtOrd_cons_of_lt hst.base x.2.base _ _ spkOrd
        (by rw [hB]) hSpkOrdLt)
      (fun _ _ _ _ _ _ _ hB => by unfold spkSlotAtOrd; rw [hB])
      (fun _ _ _ hB => by unfold spkSlotAtOrd; rw [hB])
      (fun _ _ _ _ hS _ _ => by unfold spkSlotAtOrd; rw [hS])
      (fun _ _ _ _ _ _ hS _ _ => by unfold spkSlotAtOrd; rw [hS])
      (fun u j hB => spkSlotAtOrd_map hst.base x.2.base
        (fun (idx, b) => if idx == (u.val, j.val) then (idx, { b with revealed := true })
          else (idx, b))
        (fun ⟨idx, b⟩ => by dsimp only; split_ifs <;> rfl) spkOrd (by rw [hB]))

private theorem pqxdhKeyIndFgOrdPreImpl1Key_preserves_spkTargetRevealed {S : Setup}
    (useDh1 : Bool) (tOrd spkOrd bIdx : Nat) (uSk vSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hRev : spkTargetRevealed bIdx hst = true)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgOrdPreImpl1Key useDh1 tOrd spkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    bIdx < S.N_spk_tot ∧ spkTargetRevealed bIdx x.2 = true := by
  unfold spkTargetRevealed at hRev
  rcases Bool.and_eq_true_iff.mp hRev with ⟨hDec, hAll⟩
  have hFired : hasFiredSpk S bIdx hst := @of_decide_eq_true _ (Classical.propDecidable _) hDec
  have hbLt : bIdx < S.N_spk_tot := by
    rcases hFired with ⟨u0, j0, rfl, _⟩
    exact spkSlotFlatIdx_lt S u0.isLt j0.isLt
  refine ⟨hbLt, ?_⟩
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNeInit
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      rw [spkTargetRevealed_eq_of_spkBundles_eq bIdx (hst1 := hst) (hst2 := x.2)
        (by rw [(Prod.mk.inj hEq).2])]
      exact Bool.and_eq_true_iff.mpr ⟨hDec, hAll⟩
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq
      rw [spkTargetRevealed_eq_of_spkBundles_eq bIdx (hst1 := hst) (hst2 := x.2)
        (by rw [(Prod.mk.inj hEq).2])]
      exact Bool.and_eq_true_iff.mpr ⟨hDec, hAll⟩
  · unfold pqxdhKeyIndFgOrdPreImpl1Key at hx
    simp only [StateT_run_mk] at hx
    rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin useDh1 _ _ _ _ P q hNeInit] at hx
    have hFired' : @decide (hasFiredSpk S bIdx x.2) (Classical.propDecidable _) = true :=
      @decide_eq_true _ (Classical.propDecidable _)
        ((pqxdhKeyIndFgPreImpl_preserves_hasFired useDh1 (dynTargetIdx useDh1 tOrd q hst)
          (dynSpkIdx spkOrd q hst) (some uSk) (some vSk) P q hst x hx).1 bIdx hFired)
    unfold spkTargetRevealed
    rw [hFired', Bool.true_and]
    have hUnchanged : x.2.base.spkBundles = hst.base.spkBundles →
        x.2.base.spkBundles.all (fun (k, b) => !(spkBundleFlatIdxVal S k == bIdx) || b.revealed) =
          true := fun hS => by rw [hS]; exact hAll
    refine mem_support_pqxdhKeyIndFgPreImpl_elim useDh1 (dynTargetIdx useDh1 tOrd q hst)
      (dynSpkIdx spkOrd q hst) (some uSk) (some vSk) P q hst x hx
      (fun _ hS _ _ => hUnchanged hS)
      (fun u _ hq _ _ => absurd hq (hNeInit u))
      (fun _ _ _ _ _ hB => hUnchanged (by rw [hB]))
      (fun u j bEntry _ hAny _ _ hB => ?_)
      (fun _ _ _ _ _ _ _ hB => hUnchanged (by rw [hB]))
      (fun _ _ _ hB => hUnchanged (by rw [hB]))
      (fun _ _ _ _ hS _ _ => hUnchanged hS)
      (fun _ _ _ _ _ _ hS _ _ => hUnchanged hS)
      (fun u j hB => ?_)
    · rw [hB]; dsimp only; rw [List.all_cons, hAll, Bool.and_true]
      by_cases hSlot : (spkBundleFlatIdx S u j == bIdx) = true
      · exfalso
        have := spkBundles_any_of_hasFiredSpk S bIdx hst hFired u j hSlot
        rw [hAny] at this; cases this
      · have hSlotV : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = false := by
          simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using hSlot
        simp [hSlotV]
    · rw [hB]; dsimp only; rw [List.all_map, List.all_eq_true]
      rintro ⟨k, b⟩ hMem; dsimp only [Function.comp_apply]
      split_ifs
      · simp
      · exact List.all_eq_true.mp hAll (k, b) hMem

private theorem pqxdhKeyIndFgOrdPreImpl1Key_preserves_deadDh1Ord {S : Setup}
    (pOrd spkOrd : Nat) (uSk vSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hInv : ValidOrdInv spkOrd (P.x25519Base vSk) hst)
    (hDead : deadDh1Full (prinSlotAtOrd S hst.base pOrd) (spkSlotAtOrd S hst.base spkOrd) hst =
      true)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    deadDh1Full (prinSlotAtOrd S x.2.base pOrd) (spkSlotAtOrd S x.2.base spkOrd) x.2 = true := by
  rcases Bool.or_eq_true_iff.mp hDead with hD | hR
  · set uCur := prinSlotAtOrd S hst.base pOrd
    unfold deadDh1 at hD
    cases hFP : hst.base.principals.find? (fun (u0, _) => u0 == uCur) with
    | none => rw [hFP] at hD; cases hD
    | some p0 =>
      rcases p0 with ⟨u0, e0⟩
      rw [hFP] at hD
      have hu0Mem : (u0, e0) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
      have hu0Eq : u0 = uCur :=
        beq_iff_eq.mp (List.find?_some (p := fun (kv : Nat × PrincipalEntry) => kv.1 == uCur) hFP)
      have huCurLt : uCur < S.N_id := hu0Eq ▸ hInv.1 (u0, e0) hu0Mem
      have hpOrdLt : pOrd < hst.base.principals.length := by
        by_contra hGe
        have := prinSlotAtOrd_of_ge hst.base pOrd (Nat.le_of_not_lt hGe)
        exact Nat.ne_of_lt huCurLt this
      refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
      have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
        cases q with
        | initPrin u => exact Or.inl ⟨u, rfl⟩
        | _ => exact Or.inr (fun _ h => by cases h)
      rcases hInitOrNe with ⟨u, rfl⟩ | hNeInit
      · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
        rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
        revert hb
        cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
          rintro ⟨_, _, hEq⟩
          have hB := (Prod.mk.inj hEq).2
          rw [prinSlotAtOrd_cons_of_lt hst.base x.2.base u.val _ pOrd (by rw [hB]) hpOrdLt]
          have hNeU : (u.val == uCur) = false := by
            cases hE : (u.val == uCur)
            · rfl
            · exfalso
              have hAnyT : hst.base.principals.any (fun (idx, _) => idx == u.val) = true :=
                List.any_eq_true.mpr ⟨(u0, e0), hu0Mem,
                  beq_iff_eq.mpr (hu0Eq.trans (beq_iff_eq.mp hE).symm)⟩
              rw [hAny] at hAnyT; cases hAnyT
          unfold deadDh1; rw [hB]; dsimp only [List.find?]; rw [hNeU, hFP]; exact hD
        · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          have hOrdEq : prinSlotAtOrd S x.2.base pOrd = uCur := by
            unfold uCur prinSlotAtOrd; rw [hB]
          rw [hOrdEq, deadDh1_eq_of_principals uCur (hst1 := hst) (hst2 := x.2) (by rw [hB])]
          unfold deadDh1; rw [hFP]; exact hD
      · unfold pqxdhKeyIndFgOrdPreImpl1Key at hx
        simp only [StateT_run_mk] at hx
        rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin true _ _ _ _ P q hNeInit] at hx
        have hUnchP : x.2.base.principals = hst.base.principals →
            deadDh1 (prinSlotAtOrd S x.2.base pOrd) x.2 = true := by
          intro hP
          have hOrdEq : prinSlotAtOrd S x.2.base pOrd = uCur := by
            unfold uCur prinSlotAtOrd; rw [hP]
          rw [hOrdEq, deadDh1_eq_of_principals uCur (hst1 := hst) (hst2 := x.2) hP]
          unfold deadDh1; rw [hFP]; exact hD
        refine mem_support_pqxdhKeyIndFgPreImpl_elim true (dynTargetIdx true pOrd q hst)
          (dynSpkIdx spkOrd q hst) (some uSk) (some vSk) P q hst x hx
          (fun hP _ _ _ => hUnchP hP)
          (fun u _ hq _ _ => absurd hq (hNeInit u))
          (fun u _ _ _ _ hB => ?_)
          (fun _ _ _ _ _ _ _ hB => hUnchP (by rw [hB]))
          (fun _ _ _ _ _ _ _ hB => hUnchP (by rw [hB]))
          (fun _ _ _ hB => hUnchP (by rw [hB]))
          (fun _ _ _ hP _ _ _ => hUnchP hP)
          (fun _ _ _ _ _ hP _ _ _ => hUnchP hP)
          (fun _ _ hB => hUnchP (by rw [hB]))
        have hOrdEq := prinSlotAtOrd_map hst.base x.2.base
          (fun (idx, e) => if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
          (fun ⟨idx, e⟩ => by dsimp only; split_ifs <;> rfl) pOrd (by rw [hB])
        rw [hOrdEq]; unfold deadDh1; rw [hB]; dsimp only
        have hPred : ((fun (u1, _) => u1 == uCur) ∘
            (fun (idx, e) => if idx == u.val then (idx, { e with corrupted := true })
              else (idx, e) : Nat × PrincipalEntry → Nat × PrincipalEntry)) =
            (fun (u1, _) => u1 == uCur) := by
          funext ⟨idx, e⟩; dsimp; split_ifs <;> rfl
        rw [List.find?_map, hPred, hFP]
        dsimp only [Option.map_some]
        split_ifs <;> simp [hD]
  · rcases pqxdhKeyIndFgOrdPreImpl1Key_preserves_spkTargetRevealed true pOrd spkOrd
      (spkSlotAtOrd S hst.base spkOrd) uSk vSk P q hst hR x hx with ⟨hbLt, hR'⟩
    have hSpkOrdLt : spkOrd < hst.base.spkBundles.length := by
      by_contra hGe
      have := spkSlotAtOrd_of_ge hst.base spkOrd (Nat.le_of_not_lt hGe)
      exact Nat.ne_of_lt hbLt this
    have hSpkOrdEq := pqxdhKeyIndFgOrdPreImpl1Key_spkSlotAtOrd_eq_of_lt true pOrd spkOrd uSk vSk
      P q hst hSpkOrdLt x hx
    exact Bool.or_eq_true_iff.mpr (Or.inr (hSpkOrdEq.symm ▸ hR'))

private theorem pqxdhKeyIndFgOrdPreImpl1Key_preserves_deadDh3Ord {S : Setup}
    (sOrd spkOrd : Nat) (uSk vSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hInv : ValidOrdInv spkOrd (P.x25519Base vSk) hst)
    (hDead : deadDh3Full P (sessSlotAtOrd S hst.base sOrd) (spkSlotAtOrd S hst.base spkOrd)
      (P.x25519Base vSk) hst = true)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    deadDh3Full P (sessSlotAtOrd S x.2.base sOrd) (spkSlotAtOrd S x.2.base spkOrd)
      (P.x25519Base vSk) x.2 = true := by
  have hInv' := pqxdhKeyIndFgOrdPreImpl1Key_preserves_validOrdInv false sOrd spkOrd uSk vSk P q hst
    hInv x hx
  rcases Bool.or_eq_true_iff.mp hDead with hD | hR
  · set sCur := sessSlotAtOrd S hst.base sOrd
    unfold deadDh3 at hD
    rcases Bool.and_eq_true_iff.mp hD with ⟨_, hSessFind⟩
    cases hFS : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sCur) with
    | none => rw [hFS] at hSessFind; cases hSessFind
    | some s0 =>
      rw [hFS] at hSessFind
      have hs0Mem : s0 ∈ hst.base.sessions := List.mem_of_find?_eq_some hFS
      have hs0Eq : initSessionSlotIdx s0.sid = sCur :=
        beq_iff_eq.mp
          (List.find?_some (p := fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sCur)
            hFS)
      have hsCurLt : sCur < S.N_send_tot := hs0Eq ▸ hInv.2.2.1 s0 hs0Mem
      have hsOrdLt : sOrd < hst.base.sessions.length := by
        by_contra hGe
        have := sessSlotAtOrd_of_ge hst.base sOrd (Nat.le_of_not_lt hGe)
        exact Nat.ne_of_lt hsCurLt this
      have hFired : hasFiredSess S sCur hst :=
        List.any_eq_true.mpr ⟨s0, hs0Mem, beq_iff_eq.mpr hs0Eq⟩
      refine Bool.or_eq_true_iff.mpr (Or.inl ?_)
      unfold deadDh3
      rw [hInv'.2.2.2, Bool.true_and]
      have hUnchS : x.2.base.sessions = hst.base.sessions →
          (match x.2.base.sessions.find?
              (fun s => initSessionSlotIdx s.sid == sessSlotAtOrd S x.2.base sOrd) with
            | some s => P.pow8 s.peerSpkPk != P.pow8 (P.x25519Base vSk)
            | none => false) = true := by
        intro hSe
        have hOrdEq : sessSlotAtOrd S x.2.base sOrd = sCur := by
          unfold sCur sessSlotAtOrd; rw [hSe]
        rw [hOrdEq, hSe, hFS]; exact hSessFind
      have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
        cases q with
        | initPrin u => exact Or.inl ⟨u, rfl⟩
        | _ => exact Or.inr (fun _ h => by cases h)
      rcases hInitOrNe with ⟨u, rfl⟩ | hNeInit
      · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
        rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
        simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
        revert hb
        cases hst.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
          rintro ⟨_, _, hEq⟩; exact hUnchS (by rw [(Prod.mk.inj hEq).2])
        · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; exact hUnchS (by rw [(Prod.mk.inj hEq).2])
      · unfold pqxdhKeyIndFgOrdPreImpl1Key at hx
        simp only [StateT_run_mk] at hx
        rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin false _ _ _ _ P q hNeInit] at hx
        refine mem_support_pqxdhKeyIndFgPreImpl_elim false (dynTargetIdx false sOrd q hst)
          (dynSpkIdx spkOrd q hst) (some uSk) (some vSk) P q hst x hx
          (fun _ _ _ hSe => hUnchS hSe)
          (fun u _ hq _ _ => absurd hq (hNeInit u))
          (fun _ _ _ _ _ hB => hUnchS (by rw [hB]))
          (fun _ _ _ _ _ _ _ hB => hUnchS (by rw [hB]))
          (fun _ _ _ _ _ _ _ hB => hUnchS (by rw [hB]))
          (fun s _ hAnyF hB => ?_)
          (fun _ _ _ _ _ hSe _ => hUnchS hSe)
          (fun f hfSid _ hfPeer _ _ _ _ hSe => ?_)
          (fun _ _ hB => hUnchS (by rw [hB]))
        · rw [sessSlotAtOrd_cons_of_lt hst.base x.2.base s sOrd (by rw [hB]) hsOrdLt]
          have hNeS : (initSessionSlotIdx s.sid == sCur) = false := by
            cases hE : (initSessionSlotIdx s.sid == sCur)
            · rfl
            · exfalso
              have := sessions_any_of_hasFiredSess sCur hst hFired s.sid hE
                (by rw [beq_iff_eq.mp hE]; exact hsCurLt)
              rw [hAnyF] at this; cases this
          rw [hB]; dsimp only [List.find?]; rw [hNeS, hFS]; exact hSessFind
        · rw [sessSlotAtOrd_map hst.base x.2.base f hfSid sOrd hSe, hSe]
          have hPred : (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sCur) ∘ f =
              (fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == sCur) := by
            funext s; dsimp; rw [hfSid s]
          rw [List.find?_map, hPred, hFS]; dsimp only [Option.map_some]
          rw [hfPeer s0]; exact hSessFind
  · rcases pqxdhKeyIndFgOrdPreImpl1Key_preserves_spkTargetRevealed false sOrd spkOrd
      (spkSlotAtOrd S hst.base spkOrd) uSk vSk P q hst hR x hx with ⟨hbLt, hR'⟩
    have hSpkOrdLt : spkOrd < hst.base.spkBundles.length := by
      by_contra hGe
      have := spkSlotAtOrd_of_ge hst.base spkOrd (Nat.le_of_not_lt hGe)
      exact Nat.ne_of_lt hbLt this
    have hSpkOrdEq := pqxdhKeyIndFgOrdPreImpl1Key_spkSlotAtOrd_eq_of_lt false sOrd spkOrd uSk vSk
      P q hst hSpkOrdLt x hx
    exact Bool.or_eq_true_iff.mpr (Or.inr (hSpkOrdEq.symm ▸ hR'))

private theorem erasePrincipalsFg_of_absent (uIdx : Nat) (L : List (Nat × PrincipalEntry))
    (hAbs : ∀ kv ∈ L, kv.1 ≠ uIdx) :
    erasePrincipalsFg uIdx L = L := by
  unfold erasePrincipalsFg erasePrincipalEntryFg
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, e⟩
    have hNe : (idx == uIdx) = false := beq_eq_false_iff_ne.mpr (hAbs (idx, e) List.mem_cons_self)
    simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte,
      ih (fun kv hMem => hAbs kv (List.mem_cons_of_mem _ hMem))]

private theorem eraseSpkBundlesFg_of_absent {S : Setup} (bIdx : Nat)
    (L : List ((Nat × Nat) × SpkBundleEntry))
    (hAbs : ∀ kb ∈ L, spkBundleFlatIdxVal S kb.1 ≠ bIdx) :
    eraseSpkBundlesFg S bIdx L = L := by
  unfold eraseSpkBundlesFg eraseSpkBundleEntryFg
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    have hNe : (spkBundleFlatIdxVal S k == bIdx) = false :=
      beq_eq_false_iff_ne.mpr (hAbs (k, b) List.mem_cons_self)
    simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte,
      ih (fun kb hMem => hAbs kb (List.mem_cons_of_mem _ hMem))]

private theorem eraseSessionsFg_of_absent {S : Setup} (sIdx : Nat)
    (L : List (KeyIndInitiatorEntry S))
    (hAbs : ∀ s ∈ L, initSessionSlotIdx s.sid ≠ sIdx) :
    eraseSessionsFg sIdx L = L := by
  unfold eraseSessionsFg eraseSessionEntryFg
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    have hNe : (initSessionSlotIdx hd.sid == sIdx) = false :=
      beq_eq_false_iff_ne.mpr (hAbs hd List.mem_cons_self)
    simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte,
      ih (fun s hMem => hAbs s (List.mem_cons_of_mem _ hMem))]

private theorem spkTargetIsV_of_absent {S : Setup} (bIdx : Nat) (V : Bytes)
    (hst : KeyIndFgCutoffState S)
    (hAbs : ∀ kb ∈ hst.base.spkBundles, spkBundleFlatIdxVal S kb.1 ≠ bIdx) :
    spkTargetIsV bIdx V hst = true := by
  unfold spkTargetIsV
  rw [List.all_eq_true]
  rintro ⟨k, b⟩ hMem
  have hNe : (spkBundleFlatIdxVal S k == bIdx) = false :=
    beq_eq_false_iff_ne.mpr (hAbs (k, b) hMem)
  simp [hNe]

private theorem spkTargetRevealed_of_absent {S : Setup} (bIdx : Nat)
    (hst : KeyIndFgCutoffState S)
    (hAbs : ∀ kb ∈ hst.base.spkBundles, spkBundleFlatIdxVal S kb.1 ≠ bIdx) :
    spkTargetRevealed bIdx hst = false := by
  unfold spkTargetRevealed
  have hNotFired : ¬ hasFiredSpk S bIdx hst := by
    rintro ⟨u0, j0, rfl, hAny⟩
    rcases List.any_eq_true.mp hAny with ⟨⟨k, b⟩, hMem, hkEq⟩
    have hk : k = (u0.val, j0.val) := beq_iff_eq.mp hkEq
    exact hAbs (k, b) hMem (by simp [hk, spkBundleFlatIdxVal, spkBundleFlatIdx])
  have hDec : @decide (hasFiredSpk S bIdx hst) (Classical.propDecidable _) = false :=
    @decide_eq_false _ (Classical.propDecidable _) hNotFired
  rw [hDec, Bool.false_and]

private theorem deadDh1_of_absent {S : Setup} (uIdx : Nat) (hst : KeyIndFgCutoffState S)
    (hAbs : ∀ kv ∈ hst.base.principals, kv.1 ≠ uIdx) :
    deadDh1 uIdx hst = false := by
  unfold deadDh1
  have hNone : hst.base.principals.find? (fun (u0, _) => u0 == uIdx) = none := by
    rw [List.find?_eq_none]
    rintro ⟨idx, e⟩ hMem
    simpa [beq_iff_eq] using hAbs (idx, e) hMem
  rw [hNone]

private theorem deadDh3_of_absent_sess {S : Setup} (P : Primitives) (sIdx bIdx : Nat) (V : Bytes)
    (hst : KeyIndFgCutoffState S)
    (hAbs : ∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ sIdx) :
    deadDh3 P sIdx bIdx V hst = false := by
  unfold deadDh3
  have hNone : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) = none := by
    rw [List.find?_eq_none]
    intro s hMem
    simpa [beq_iff_eq] using hAbs s hMem
  rw [hNone, Bool.and_false]

private theorem clearTargetSecIKAsign_of_absent {S : Setup} (uIdx : Nat)
    (st : FgKeyIndSimState S) (hAbs : ∀ kv ∈ st.base.principals, kv.1 ≠ uIdx) :
    clearTargetSecIKAsign uIdx st = st := by
  have hMap : ∀ (L : List (Nat × PrincipalEntry)), (∀ kv ∈ L, kv.1 ≠ uIdx) →
      L.map (fun (idx, e) => (idx, clearTargetPrinSecSign uIdx idx e)) = L := by
    intro L hAbsL
    unfold clearTargetPrinSecSign
    induction L with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨idx, e⟩
      have hNe : (idx == uIdx) = false :=
        beq_eq_false_iff_ne.mpr (hAbsL (idx, e) List.mem_cons_self)
      simp only [List.map_cons, hNe, Bool.false_eq_true, ↓reduceIte,
        ih (fun kv hMem => hAbsL kv (List.mem_cons_of_mem _ hMem))]
  have hM := hMap st.base.principals hAbs
  rcases st with ⟨base, fgL, rawRoCache, advRoLog, advKeyPows⟩
  rcases base with ⟨secb, principals, spkBundles, opkEntries, sessions, respSessions,
    usedRecvOPK, usedRecvNoOPK, seenKyberBaseKeys, roCache, advKeys⟩
  dsimp only at hM
  unfold clearTargetSecIKAsign clearTargetSecIKAsignBase
  dsimp only
  rw [hM]

private theorem bundleSignedMessages_of_absent (uIdx : Nat)
    (L : List ((Nat × Nat) × SpkBundleEntry))
    (hAbs : ∀ kb ∈ L, kb.1.1 ≠ uIdx) :
    bundleSignedMessages uIdx L = [] := by
  unfold bundleSignedMessages
  have hF : L.filter (fun ((u, _), _) => u == uIdx) = [] := by
    rw [List.filter_eq_nil_iff]
    rintro ⟨⟨u, j⟩, b⟩ hMem
    simpa [beq_iff_eq] using hAbs ((u, j), b) hMem
  rw [hF]; rfl

private theorem validOrdInv_of_validKeyIndEcFg {S : Setup} (spkOrd : Nat) (V : Bytes)
    (hst : KeyIndFgCutoffState S)
    (hVEc : ValidKeyIndEcFg S hst.base)
    (hSpkV : spkTargetIsV (spkSlotAtOrd S hst.base spkOrd) V hst = true) :
    ValidOrdInv spkOrd V hst := by
  refine ⟨hVEc.1.1, hVEc.2.1.1, fun s hs => ?_, hSpkV⟩
  have hSend : IsSendSessionId S s.sid :=
    hVEc.2.2.2.1.1 s.sid (by
      simp only [List.mem_map]
      exact ⟨(s.sid, s.hdr.ekAPk), List.mem_map.mpr ⟨s, hs, rfl⟩, rfl⟩)
  cases hSid : s.sid with
  | sendOPK u i =>
    exact Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)
  | sendNoOPK u i =>
    exact initSessionSlotIdx_sendNoOPK_lt u i
  | recvOPK _ _ _ => rw [hSid] at hSend; cases hSend
  | recvNoOPK _ _ _ => rw [hSid] at hSend; cases hSend

private theorem deadDh1Full_retarget {S : Setup} (u0 u1 b0 b1 : Nat)
    (hst : KeyIndFgCutoffState S)
    (hu : u0 = u1 ∨ (∀ kv ∈ hst.base.principals, kv.1 ≠ u0 ∧ kv.1 ≠ u1))
    (hb : b0 = b1 ∨
      (∀ kb ∈ hst.base.spkBundles,
        spkBundleFlatIdxVal S kb.1 ≠ b0 ∧ spkBundleFlatIdxVal S kb.1 ≠ b1)) :
    deadDh1Full u0 b0 hst = deadDh1Full u1 b1 hst := by
  have hD : deadDh1 u0 hst = deadDh1 u1 hst := by
    rcases hu with rfl | hAbsU
    · rfl
    · rw [deadDh1_of_absent u0 hst (fun kv h => (hAbsU kv h).1),
          deadDh1_of_absent u1 hst (fun kv h => (hAbsU kv h).2)]
  have hR : spkTargetRevealed b0 hst = spkTargetRevealed b1 hst := by
    rcases hb with rfl | hAbsB
    · rfl
    · rw [spkTargetRevealed_of_absent b0 hst (fun kb h => (hAbsB kb h).1),
          spkTargetRevealed_of_absent b1 hst (fun kb h => (hAbsB kb h).2)]
  unfold deadDh1Full
  rw [hD, hR]

private theorem deadDh3Full_retarget {S : Setup} (P : Primitives) (s0 s1 b0 b1 : Nat)
    (V : Bytes) (hst : KeyIndFgCutoffState S)
    (hs : s0 = s1 ∨
      (∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ s0 ∧ initSessionSlotIdx s.sid ≠ s1))
    (hb : b0 = b1 ∨
      (∀ kb ∈ hst.base.spkBundles,
        spkBundleFlatIdxVal S kb.1 ≠ b0 ∧ spkBundleFlatIdxVal S kb.1 ≠ b1)) :
    deadDh3Full P s0 b0 V hst = deadDh3Full P s1 b1 V hst := by
  have hSpkV : spkTargetIsV b0 V hst = spkTargetIsV b1 V hst := by
    rcases hb with rfl | hAbsB
    · rfl
    · rw [spkTargetIsV_of_absent b0 V hst (fun kb h => (hAbsB kb h).1),
          spkTargetIsV_of_absent b1 V hst (fun kb h => (hAbsB kb h).2)]
  have hD : deadDh3 P s0 b0 V hst = deadDh3 P s1 b1 V hst := by
    rcases hs with rfl | hAbsS
    · unfold deadDh3; rw [hSpkV]
    · rw [deadDh3_of_absent_sess P s0 b0 V hst (fun s h => (hAbsS s h).1),
          deadDh3_of_absent_sess P s1 b1 V hst (fun s h => (hAbsS s h).2)]
  have hR : spkTargetRevealed b0 hst = spkTargetRevealed b1 hst := by
    rcases hb with rfl | hAbsB
    · rfl
    · rw [spkTargetRevealed_of_absent b0 hst (fun kb h => (hAbsB kb h).1),
          spkTargetRevealed_of_absent b1 hst (fun kb h => (hAbsB kb h).2)]
  unfold deadDh3Full
  rw [hD, hR]

private theorem fgSimInvDh1_1Key_retarget {S : Setup} (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (u0 u1 b0 b1 : Nat) (uSk vSk : Bytes) (rem : Nat)
    (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hu : u0 = u1 ∨
      ((∀ kv ∈ hst.base.principals, kv.1 ≠ u0 ∧ kv.1 ≠ u1) ∧
       (∀ kb ∈ hst.base.spkBundles, kb.1.1 ≠ u0)))
    (hb : b0 = b1 ∨
      (∀ kb ∈ hst.base.spkBundles,
        spkBundleFlatIdxVal S kb.1 ≠ b0 ∧ spkBundleFlatIdxVal S kb.1 ≠ b1))
    (hInv : FgSimInvDh1_1Key S b P R u0 b0 uSk vSk rem hst st) :
    FgSimInvDh1_1Key S b P R u1 b1 uSk vSk rem hst st := by
  rcases hInv with ⟨stGhost, hSim, hGInv, hBudget, hSecEq⟩
  rcases hGInv with ⟨hBase, hAdv, hCache, hFgLen, hAdvLen, hVEc, hSpkV, hPrin, hSpk, hOpk, hSess⟩
  have hEraseP : erasePrincipalsFg u0 hst.base.principals =
      erasePrincipalsFg u1 hst.base.principals := by
    rcases hu with rfl | ⟨hAbsU, _⟩
    · rfl
    · rw [erasePrincipalsFg_of_absent u0 _ (fun kv h => (hAbsU kv h).1),
          erasePrincipalsFg_of_absent u1 _ (fun kv h => (hAbsU kv h).2)]
  have hEraseB : eraseSpkBundlesFg S b0 hst.base.spkBundles =
      eraseSpkBundlesFg S b1 hst.base.spkBundles := by
    rcases hb with rfl | hAbsB
    · rfl
    · rw [eraseSpkBundlesFg_of_absent b0 _ (fun kb h => (hAbsB kb h).1),
          eraseSpkBundlesFg_of_absent b1 _ (fun kb h => (hAbsB kb h).2)]
  have hBase' : stGhost.base = eraseStateFg true u1 b1 hst.base := by
    rw [hBase]; unfold eraseStateFg; simp only [↓reduceIte, hEraseP, hEraseB]
  have hSim' : st.sim = clearTargetSecIKAsign u1 stGhost := by
    rcases hu with rfl | ⟨hAbsU, _⟩
    · exact hSim
    · have hGhostP : stGhost.base.principals = hst.base.principals := by
        rw [hBase]; unfold eraseStateFg; dsimp only [↓reduceIte]
        exact erasePrincipalsFg_of_absent u0 _ (fun kv h => (hAbsU kv h).1)
      rw [hSim,
          clearTargetSecIKAsign_of_absent u0 stGhost (by rw [hGhostP]; exact fun kv h => (hAbsU kv h).1),
          clearTargetSecIKAsign_of_absent u1 stGhost (by rw [hGhostP]; exact fun kv h => (hAbsU kv h).2)]
  have hSpkV' : spkTargetIsV b1 (P.x25519Base vSk) hst = true := by
    rcases hb with rfl | hAbsB
    · exact hSpkV
    · exact spkTargetIsV_of_absent b1 _ hst (fun kb h => (hAbsB kb h).2)
  have hBudget' :
      2 * min S.N_spk_tot S.N_recv ≤
        (bundleSignedMessages u1 hst.base.spkBundles).length + 2 * st.sigBudget := by
    rcases hu with rfl | ⟨_, hNoSpkU0⟩
    · exact hBudget
    · rw [bundleSignedMessages_of_absent u0 _ hNoSpkU0] at hBudget
      dsimp only [List.length_nil] at hBudget
      omega
  refine ⟨stGhost, hSim', ⟨hBase', hAdv, hCache, hFgLen, hAdvLen, hVEc, hSpkV', ?_, ?_, hOpk, hSess⟩,
    hBudget', hSecEq⟩
  · intro kv hMem
    rcases hPrin kv hMem with ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun hEq => ?_⟩
    rcases hu with rfl | ⟨hAbsU, _⟩
    · exact h3 hEq
    · exact absurd (beq_iff_eq.mp hEq) (hAbsU kv hMem).2
  · intro kb hMem
    rcases hSpk kb hMem with ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun hEq => ?_⟩
    rcases hb with rfl | hAbsB
    · exact h3 hEq
    · exact absurd (beq_iff_eq.mp hEq) (hAbsB kb hMem).2

private theorem fgSimInvDh3_1Key_retarget {S : Setup} (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (s0 s1 b0 b1 : Nat)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (rem : Nat)
    (hst : KeyIndFgCutoffState S) (st : FgKeyInd1KeySimState S)
    (hs : s0 = s1 ∨
      (∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ s0 ∧ initSessionSlotIdx s.sid ≠ s1))
    (hb : b0 = b1 ∨
      (∀ kb ∈ hst.base.spkBundles,
        spkBundleFlatIdxVal S kb.1 ≠ b0 ∧ spkBundleFlatIdxVal S kb.1 ≠ b1))
    (hInv : FgSimInvDh3_1Key S b P hP s0 b0 uSk vSk huSk hvSk rem hst st) :
    FgSimInvDh3_1Key S b P hP s1 b1 uSk vSk huSk hvSk rem hst st := by
  rcases hInv with ⟨hBase, hAdv, hCache, hFgLen, hAdvLen, hVEc, hSpkV, hPrin, hSpk, hOpk, hSess⟩
  have hEraseS : eraseSessionsFg s0 hst.base.sessions =
      eraseSessionsFg s1 hst.base.sessions := by
    rcases hs with rfl | hAbsS
    · rfl
    · rw [eraseSessionsFg_of_absent s0 _ (fun s h => (hAbsS s h).1),
          eraseSessionsFg_of_absent s1 _ (fun s h => (hAbsS s h).2)]
  have hEraseB : eraseSpkBundlesFg S b0 hst.base.spkBundles =
      eraseSpkBundlesFg S b1 hst.base.spkBundles := by
    rcases hb with rfl | hAbsB
    · rfl
    · rw [eraseSpkBundlesFg_of_absent b0 _ (fun kb h => (hAbsB kb h).1),
          eraseSpkBundlesFg_of_absent b1 _ (fun kb h => (hAbsB kb h).2)]
  have hBase' : st.sim.base = eraseStateFg false s1 b1 hst.base := by
    rw [hBase]; unfold eraseStateFg; simp only [Bool.false_eq_true, ↓reduceIte, hEraseS, hEraseB]
  have hSpkV' : spkTargetIsV b1 (P.x25519Base vSk) hst = true := by
    rcases hb with rfl | hAbsB
    · exact hSpkV
    · exact spkTargetIsV_of_absent b1 _ hst (fun kb h => (hAbsB kb h).2)
  refine ⟨hBase', hAdv, hCache, hFgLen, hAdvLen, hVEc, hSpkV', hPrin, ?_, hOpk, ?_⟩
  · intro kb hMem
    rcases hSpk kb hMem with ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun hEq => ?_⟩
    rcases hb with rfl | hAbsB
    · exact h3 hEq
    · exact absurd (beq_iff_eq.mp hEq) (hAbsB kb hMem).2
  · intro s hMem
    rcases hSess s hMem with ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun hEq => ?_⟩
    rcases hs with rfl | hAbsS
    · exact h3 hEq
    · exact absurd (beq_iff_eq.mp hEq) (hAbsS s hMem).2


private theorem prinSlotAtOrd_eq_ite {S : Setup} (st : KeyIndState S) (pOrd : Nat) :
    (if pOrd < st.principals.length then prinSlotAtOrd S st pOrd else S.N_id) =
      prinSlotAtOrd S st pOrd := by
  split_ifs with h
  · rfl
  · exact (prinSlotAtOrd_of_ge st pOrd (Nat.le_of_not_lt h)).symm

private theorem spkSlotAtOrd_eq_ite {S : Setup} (st : KeyIndState S) (spkOrd : Nat) :
    (if spkOrd < st.spkBundles.length then spkSlotAtOrd S st spkOrd else S.N_spk_tot) =
      spkSlotAtOrd S st spkOrd := by
  split_ifs with h
  · rfl
  · exact (spkSlotAtOrd_of_ge st spkOrd (Nat.le_of_not_lt h)).symm

private theorem sessSlotAtOrd_eq_ite {S : Setup} (st : KeyIndState S) (sOrd : Nat) :
    (if sOrd < st.sessions.length then sessSlotAtOrd S st sOrd else S.N_send_tot) =
      sessSlotAtOrd S st sOrd := by
  split_ifs with h
  · rfl
  · exact (sessSlotAtOrd_of_ge st sOrd (Nat.le_of_not_lt h)).symm

private def stepPrinSlot {S : Setup} (pOrd : Nat) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) : Nat :=
  if pOrd < hst.base.principals.length then prinSlotAtOrd S hst.base pOrd
  else match q with
    | .initPrin u =>
      if !hst.base.principals.any (fun (idx, _) => idx == u.val) &&
         (hst.base.principals.length == pOrd) then u.val else S.N_id
    | _ => S.N_id

private def stepSpkSlot {S : Setup} (spkOrd : Nat) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) : Nat :=
  if spkOrd < hst.base.spkBundles.length then spkSlotAtOrd S hst.base spkOrd
  else match q with
    | .genSPK u j =>
      if !hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) &&
         (hst.base.spkBundles.length == spkOrd) then spkBundleFlatIdx S u j else S.N_spk_tot
    | _ => S.N_spk_tot

private def stepSessSlot {S : Setup} (sOrd : Nat) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) : Nat :=
  if sOrd < hst.base.sessions.length then sessSlotAtOrd S hst.base sOrd
  else match q with
    | .initiateOPK u i _ =>
      if !hst.base.sessions.any (fun e => e.sid == .sendOPK u i) &&
         (hst.base.sessions.length == sOrd) then initSessionSlotIdx (.sendOPK u i)
      else S.N_send_tot
    | .initiateNoOPK u i _ =>
      if !hst.base.sessions.any (fun e => e.sid == .sendNoOPK u i) &&
         (hst.base.sessions.length == sOrd) then initSessionSlotIdx (.sendNoOPK u i)
      else S.N_send_tot
    | _ => S.N_send_tot

private theorem stepPrinSlot_retarget_pre {S : Setup} (pOrd spkOrd : Nat) (V : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) (hOrd : ValidOrdInv spkOrd V hst) :
    prinSlotAtOrd S hst.base pOrd = stepPrinSlot pOrd q hst ∨
      ((∀ kv ∈ hst.base.principals,
          kv.1 ≠ prinSlotAtOrd S hst.base pOrd ∧ kv.1 ≠ stepPrinSlot pOrd q hst) ∧
       (∀ kb ∈ hst.base.spkBundles, kb.1.1 ≠ prinSlotAtOrd S hst.base pOrd)) := by
  by_cases hLt : pOrd < hst.base.principals.length
  · exact Or.inl (by simp [stepPrinSlot, hLt])
  · right
    have hCur : prinSlotAtOrd S hst.base pOrd = S.N_id :=
      prinSlotAtOrd_of_ge hst.base pOrd (Nat.le_of_not_lt hLt)
    refine ⟨fun kv hMem => ⟨by rw [hCur]; exact Nat.ne_of_lt (hOrd.1 kv hMem), ?_⟩,
      fun kb hMem => by rw [hCur]; exact Nat.ne_of_lt (hOrd.2.1 kb hMem).1⟩
    unfold stepPrinSlot
    simp only [hLt, ↓reduceIte]
    cases q with
    | initPrin u =>
      dsimp only
      cases hAny : hst.base.principals.any (fun x => x.1 == u.val)
      · simp only [Bool.not_false, Bool.true_and]
        split_ifs with hEqLen
        · intro hEq
          have hT : hst.base.principals.any (fun x => x.1 == u.val) = true :=
            List.any_eq_true.mpr ⟨kv, hMem, beq_iff_eq.mpr hEq⟩
          rw [hAny] at hT; cases hT
        · exact Nat.ne_of_lt (hOrd.1 kv hMem)
      · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact Nat.ne_of_lt (hOrd.1 kv hMem)
    | _ => exact Nat.ne_of_lt (hOrd.1 kv hMem)

private theorem stepSpkSlot_retarget_pre {S : Setup} (spkOrd : Nat) (V : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) (hOrd : ValidOrdInv spkOrd V hst) :
    spkSlotAtOrd S hst.base spkOrd = stepSpkSlot spkOrd q hst ∨
      (∀ kb ∈ hst.base.spkBundles,
        spkBundleFlatIdxVal S kb.1 ≠ spkSlotAtOrd S hst.base spkOrd ∧
        spkBundleFlatIdxVal S kb.1 ≠ stepSpkSlot spkOrd q hst) := by
  by_cases hLt : spkOrd < hst.base.spkBundles.length
  · exact Or.inl (by simp [stepSpkSlot, hLt])
  · right
    have hCur : spkSlotAtOrd S hst.base spkOrd = S.N_spk_tot :=
      spkSlotAtOrd_of_ge hst.base spkOrd (Nat.le_of_not_lt hLt)
    intro kb hMem
    have hKbLt := spkBundleFlatIdxVal_lt_of_bounds (hOrd.2.1 kb hMem)
    refine ⟨by rw [hCur]; exact Nat.ne_of_lt hKbLt, ?_⟩
    unfold stepSpkSlot
    simp only [hLt, ↓reduceIte]
    cases q with
    | genSPK u j =>
      dsimp only
      cases hAny : hst.base.spkBundles.any (fun x => x.1 == (u.val, j.val))
      · simp only [Bool.not_false, Bool.true_and]
        split_ifs with hEqLen
        · intro hEq
          have hkBounds := hOrd.2.1 kb hMem
          have hInj := spkBundleFlatIdx_inj S ⟨kb.1.1, hkBounds.1⟩ u ⟨kb.1.2, hkBounds.2⟩ j hEq
          have hkEq : kb.1 = (u.val, j.val) :=
            Prod.ext (congrArg Fin.val hInj.1) (congrArg Fin.val hInj.2)
          have hT : hst.base.spkBundles.any (fun x => x.1 == (u.val, j.val)) = true :=
            List.any_eq_true.mpr ⟨kb, hMem, beq_iff_eq.mpr hkEq⟩
          rw [hAny] at hT; cases hT
        · exact Nat.ne_of_lt hKbLt
      · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact Nat.ne_of_lt hKbLt
    | _ => exact Nat.ne_of_lt hKbLt

private theorem stepSessSlot_retarget_pre {S : Setup} (sOrd spkOrd : Nat) (V : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S) (hOrd : ValidOrdInv spkOrd V hst) :
    sessSlotAtOrd S hst.base sOrd = stepSessSlot sOrd q hst ∨
      (∀ s ∈ hst.base.sessions,
        initSessionSlotIdx s.sid ≠ sessSlotAtOrd S hst.base sOrd ∧
        initSessionSlotIdx s.sid ≠ stepSessSlot sOrd q hst) := by
  by_cases hLt : sOrd < hst.base.sessions.length
  · exact Or.inl (by simp [stepSessSlot, hLt])
  · right
    have hCur : sessSlotAtOrd S hst.base sOrd = S.N_send_tot :=
      sessSlotAtOrd_of_ge hst.base sOrd (Nat.le_of_not_lt hLt)
    intro s hMem
    have hsLt : initSessionSlotIdx s.sid < S.N_send_tot := hOrd.2.2.1 s hMem
    refine ⟨by rw [hCur]; exact Nat.ne_of_lt hsLt, ?_⟩
    unfold stepSessSlot
    simp only [hLt, ↓reduceIte]
    cases q with
    | initiateOPK u i _ =>
      dsimp only
      by_cases hSidMem : ∃ x ∈ hst.base.sessions, x.sid = .sendOPK u i
      · rcases hSidMem with ⟨s0, hs0, hs0Eq⟩
        have hNotAll : ¬ ((∀ x ∈ hst.base.sessions, x.sid ≠ .sendOPK u i) ∧
            hst.base.sessions.length = sOrd) := fun h => h.1 s0 hs0 hs0Eq
        simp [hNotAll, Nat.ne_of_lt hsLt]
      · simp only [not_exists, not_and] at hSidMem
        split_ifs with hCond
        · intro hEq
          have hSidEq := initSessionSlotIdx_inj_of_lt hEq
            (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _))
          exact hSidMem s hMem hSidEq
        · exact Nat.ne_of_lt hsLt
    | initiateNoOPK u i _ =>
      dsimp only
      by_cases hSidMem : ∃ x ∈ hst.base.sessions, x.sid = .sendNoOPK u i
      · rcases hSidMem with ⟨s0, hs0, hs0Eq⟩
        have hNotAll : ¬ ((∀ x ∈ hst.base.sessions, x.sid ≠ .sendNoOPK u i) ∧
            hst.base.sessions.length = sOrd) := fun h => h.1 s0 hs0 hs0Eq
        simp [hNotAll, Nat.ne_of_lt hsLt]
      · simp only [not_exists, not_and] at hSidMem
        split_ifs with hCond
        · intro hEq
          have hSidEq := initSessionSlotIdx_inj_of_lt hEq (initSessionSlotIdx_sendNoOPK_lt u i)
          exact hSidMem s hMem hSidEq
        · exact Nat.ne_of_lt hsLt
    | _ => exact Nat.ne_of_lt hsLt

private theorem pqxdhKeyIndFgOrdPreImpl1Key_run_dh1_eq {S : Setup}
    (pOrd spkOrd : Nat) (uSk vSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hOrd : ValidOrdInv spkOrd (P.x25519Base vSk) hst) :
    (pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) (some vSk) S P q).run hst =
      (pqxdhKeyIndFgPreImpl1Key true (stepPrinSlot pOrd q hst) (stepSpkSlot spkOrd q hst)
        (some uSk) (some vSk) S P q).run hst := by
  have hCases :
      (∃ u, q = .initPrin u) ∨
      (∃ u j, q = .genSPK u j) ∨
      ((∀ u, q ≠ .initPrin u) ∧ (∀ u j, q ≠ .genSPK u j)) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | genSPK u j => exact Or.inr (Or.inl ⟨u, j, rfl⟩)
    | _ => exact Or.inr (Or.inr ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩)
  rcases hCases with ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨hNeInit, hNeSpk⟩
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key liftFgBase fgPreInitPrin1Key
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hTgtEq : (u.val == dynTargetIdx true pOrd (.initPrin u) hst) =
          (u.val == stepPrinSlot pOrd (.initPrin u) hst) := by
        unfold dynTargetIdx stepPrinSlot
        simp only [↓reduceIte, hAny, Bool.not_false, Bool.true_and]
        by_cases hLt : pOrd < hst.base.principals.length
        · simp only [hLt, ↓reduceIte]
          have hNeLen : (hst.base.principals.length == pOrd) = false :=
            beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
          simp only [hNeLen, Bool.false_eq_true, ↓reduceIte]
          have hNe1 : (u.val == S.N_id) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)
          rcases prinSlotAtOrd_mem_of_lt hst.base pOrd hLt with ⟨⟨idx0, e0⟩, hMem0, hEq0⟩
          have hNe2 : (u.val == prinSlotAtOrd S hst.base pOrd) = false := by
            cases hE : (u.val == prinSlotAtOrd S hst.base pOrd)
            · rfl
            · exfalso
              have hT : hst.base.principals.any (fun (idx, _) => idx == u.val) = true :=
                List.any_eq_true.mpr ⟨(idx0, e0), hMem0,
                  beq_iff_eq.mpr (hEq0.trans (beq_iff_eq.mp hE).symm)⟩
              rw [hAny] at hT; cases hT
          rw [hNe1, hNe2]
        · simp only [hLt, ↓reduceIte]
      simp only [hTgtEq]
    · simp
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl
      liftFgBase fgPreGenSPK
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hTgtEq : (spkBundleFlatIdx S u j == dynSpkIdx spkOrd (.genSPK u j) hst) =
          (spkBundleFlatIdx S u j == stepSpkSlot spkOrd (.genSPK u j) hst) := by
        unfold dynSpkIdx stepSpkSlot
        simp only [hAny, Bool.not_false, Bool.true_and]
        by_cases hLt : spkOrd < hst.base.spkBundles.length
        · simp only [hLt, ↓reduceIte]
          have hNeLen : (hst.base.spkBundles.length == spkOrd) = false :=
            beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
          simp only [hNeLen, Bool.false_eq_true, ↓reduceIte]
          have hNe1 : (spkBundleFlatIdx S u j == S.N_spk_tot) = false :=
            beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (spkSlotFlatIdx_lt S u.isLt j.isLt))
          have hFired := hasFiredSpk_of_spkOrd_lt spkOrd hst hOrd.2.1 hLt
          have hNe2 : (spkBundleFlatIdx S u j == spkSlotAtOrd S hst.base spkOrd) = false := by
            cases hE : (spkBundleFlatIdx S u j == spkSlotAtOrd S hst.base spkOrd)
            · rfl
            · exfalso
              have hT := spkBundles_any_of_hasFiredSpk S _ hst hFired u j hE
              rw [hAny] at hT; cases hT
          rw [hNe1, hNe2]
        · simp only [hLt, ↓reduceIte]
      simp only [hTgtEq]
    · simp
  · unfold pqxdhKeyIndFgOrdPreImpl1Key
    simp only [StateT_run_mk]
    rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin true _ _ _ _ P q hNeInit,
        pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin true _ _ _ _ P q hNeInit]
    cases q with
    | initPrin u => exact absurd rfl (hNeInit u)
    | genSPK u j => exact absurd rfl (hNeSpk u j)
    | initiateOPK u i bundle => rfl
    | initiateNoOPK u i bundle => rfl
    | _ => rfl

private theorem pqxdhKeyIndFgOrdPreImpl1Key_run_dh3_eq {S : Setup}
    (sOrd spkOrd : Nat) (uSk vSk : Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hOrd : ValidOrdInv spkOrd (P.x25519Base vSk) hst) :
    (pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd (some uSk) (some vSk) S P q).run hst =
      (pqxdhKeyIndFgPreImpl1Key false (stepSessSlot sOrd q hst) (stepSpkSlot spkOrd q hst)
        (some uSk) (some vSk) S P q).run hst := by
  have hCases :
      (∃ u, q = .initPrin u) ∨
      (∃ u j, q = .genSPK u j) ∨
      (∃ u i bundle, q = .initiateOPK u i bundle) ∨
      (∃ u i bundle, q = .initiateNoOPK u i bundle) ∨
      ((∀ u, q ≠ .initPrin u) ∧ (∀ u j, q ≠ .genSPK u j) ∧
       (∀ u i bundle, q ≠ .initiateOPK u i bundle) ∧
       (∀ u i bundle, q ≠ .initiateNoOPK u i bundle)) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | genSPK u j => exact Or.inr (Or.inl ⟨u, j, rfl⟩)
    | initiateOPK u i b => exact Or.inr (Or.inr (Or.inl ⟨u, i, b, rfl⟩))
    | initiateNoOPK u i b => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u, i, b, rfl⟩)))
    | _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨(fun _ h => by cases h), (fun _ _ h => by cases h),
         (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩)))
  rcases hCases with ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨u, i, bundle, rfl⟩ | ⟨u, i, bundle, rfl⟩ |
    ⟨hNeInit, hNeSpk, hNoOpk, hNoNoOpk⟩
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key
    simp only [StateT_run_mk, fgPreInitPrin1Key_false_eq]
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl
      liftFgBase fgPreGenSPK
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hTgtEq : (spkBundleFlatIdx S u j == dynSpkIdx spkOrd (.genSPK u j) hst) =
          (spkBundleFlatIdx S u j == stepSpkSlot spkOrd (.genSPK u j) hst) := by
        unfold dynSpkIdx stepSpkSlot
        simp only [hAny, Bool.not_false, Bool.true_and]
        by_cases hLt : spkOrd < hst.base.spkBundles.length
        · simp only [hLt, ↓reduceIte]
          have hNeLen : (hst.base.spkBundles.length == spkOrd) = false :=
            beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
          simp only [hNeLen, Bool.false_eq_true, ↓reduceIte]
          have hNe1 : (spkBundleFlatIdx S u j == S.N_spk_tot) = false :=
            beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (spkSlotFlatIdx_lt S u.isLt j.isLt))
          have hFired := hasFiredSpk_of_spkOrd_lt spkOrd hst hOrd.2.1 hLt
          have hNe2 : (spkBundleFlatIdx S u j == spkSlotAtOrd S hst.base spkOrd) = false := by
            cases hE : (spkBundleFlatIdx S u j == spkSlotAtOrd S hst.base spkOrd)
            · rfl
            · exfalso
              have hT := spkBundles_any_of_hasFiredSpk S _ hst hFired u j hE
              rw [hAny] at hT; cases hT
          rw [hNe1, hNe2]
        · simp only [hLt, ↓reduceIte]
      simp only [hTgtEq]
    · simp
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl
      liftFgBase fgPreInitiate
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases hAny : hst.base.sessions.any (fun e => e.sid == .sendOPK u i)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hTgtEq : (initSessionSlotIdx (.sendOPK u i) ==
              dynTargetIdx false sOrd (.initiateOPK u i bundle) hst) =
            (initSessionSlotIdx (.sendOPK u i) ==
              stepSessSlot sOrd (.initiateOPK u i bundle) hst) := by
          unfold dynTargetIdx stepSessSlot
          simp only [Bool.false_eq_true, ↓reduceIte, hAny, Bool.not_false, Bool.true_and]
          by_cases hLt : sOrd < hst.base.sessions.length
          · simp only [hLt, ↓reduceIte]
            have hNeLen : (hst.base.sessions.length == sOrd) = false :=
              beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
            simp only [hNeLen, Bool.false_eq_true, ↓reduceIte]
            have hSidLt : initSessionSlotIdx (.sendOPK u i) < S.N_send_tot :=
              Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)
            have hNe1 : (initSessionSlotIdx (.sendOPK u i) == S.N_send_tot) = false :=
              beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hSidLt)
            rcases sessSlotAtOrd_mem_of_lt hst.base sOrd hLt with ⟨s0, hs0Mem, hs0Eq⟩
            have hNe2 : (initSessionSlotIdx (.sendOPK u i) == sessSlotAtOrd S hst.base sOrd) =
                false := by
              cases hE : (initSessionSlotIdx (.sendOPK u i) == sessSlotAtOrd S hst.base sOrd)
              · rfl
              · exfalso
                have hSidEq := initSessionSlotIdx_inj_of_lt
                  ((beq_iff_eq.mp hE).trans hs0Eq.symm) (hOrd.2.2.1 s0 hs0Mem)
                have hT : hst.base.sessions.any (fun e => e.sid == .sendOPK u i) = true :=
                  List.any_eq_true.mpr ⟨s0, hs0Mem, beq_iff_eq.mpr hSidEq.symm⟩
                rw [hAny] at hT; cases hT
            rw [hNe1, hNe2]
          · simp only [hLt, ↓reduceIte]
        simp only [hTgtEq]
      · simp
    · simp
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl
      liftFgBase fgPreInitiate
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind]
      cases hAny : hst.base.sessions.any (fun e => e.sid == .sendNoOPK u i)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hTgtEq : (initSessionSlotIdx (.sendNoOPK u i) ==
              dynTargetIdx false sOrd (.initiateNoOPK u i bundle) hst) =
            (initSessionSlotIdx (.sendNoOPK u i) ==
              stepSessSlot sOrd (.initiateNoOPK u i bundle) hst) := by
          unfold dynTargetIdx stepSessSlot
          simp only [Bool.false_eq_true, ↓reduceIte, hAny, Bool.not_false, Bool.true_and]
          by_cases hLt : sOrd < hst.base.sessions.length
          · simp only [hLt, ↓reduceIte]
            have hNeLen : (hst.base.sessions.length == sOrd) = false :=
              beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
            simp only [hNeLen, Bool.false_eq_true, ↓reduceIte]
            have hSidLt : initSessionSlotIdx (.sendNoOPK u i) < S.N_send_tot :=
              initSessionSlotIdx_sendNoOPK_lt u i
            have hNe1 : (initSessionSlotIdx (.sendNoOPK u i) == S.N_send_tot) = false :=
              beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hSidLt)
            rcases sessSlotAtOrd_mem_of_lt hst.base sOrd hLt with ⟨s0, hs0Mem, hs0Eq⟩
            have hNe2 : (initSessionSlotIdx (.sendNoOPK u i) == sessSlotAtOrd S hst.base sOrd) =
                false := by
              cases hE : (initSessionSlotIdx (.sendNoOPK u i) == sessSlotAtOrd S hst.base sOrd)
              · rfl
              · exfalso
                have hSidEq := initSessionSlotIdx_inj_of_lt
                  ((beq_iff_eq.mp hE).trans hs0Eq.symm) (hOrd.2.2.1 s0 hs0Mem)
                have hT : hst.base.sessions.any (fun e => e.sid == .sendNoOPK u i) = true :=
                  List.any_eq_true.mpr ⟨s0, hs0Mem, beq_iff_eq.mpr hSidEq.symm⟩
                rw [hAny] at hT; cases hT
            rw [hNe1, hNe2]
          · simp only [hLt, ↓reduceIte]
        simp only [hTgtEq]
      · simp
    · simp
  · unfold pqxdhKeyIndFgOrdPreImpl1Key
    simp only [StateT_run_mk]
    rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin false _ _ _ _ P q hNeInit,
        pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin false _ _ _ _ P q hNeInit]
    cases q with
    | initPrin u => exact absurd rfl (hNeInit u)
    | genSPK u j => exact absurd rfl (hNeSpk u j)
    | initiateOPK u i b => exact absurd rfl (hNoOpk u i b)
    | initiateNoOPK u i b => exact absurd rfl (hNoNoOpk u i b)
    | _ => rfl


private def nextActiveState (prinFlag : Bool) (pOrd : Nat) {S : Setup} (q : KeyIndQuery S)
    (stA : FgKeyInd1KeyActiveSimState S) (st1' : FgKeyInd1KeySimState S) :
    FgKeyInd1KeyActiveSimState S :=
  match q with
  | .initPrin u =>
    let created := !stA.st1.sim.base.principals.any (fun (idx, _) => idx == u.val)
    let tp' :=
      if created && prinFlag && (stA.st1.sim.base.principals.length == pOrd) then some u.val
      else stA.resolvedPrin?
    { stA with st1 := st1', resolvedPrin? := tp' }
  | .initiateOPK _ _ _ =>
    let cnt' :=
      if st1'.sim.base.sessions.length == stA.st1.sim.base.sessions.length then stA.sendOpkCnt
      else stA.sendOpkCnt + 1
    { stA with st1 := st1', sendOpkCnt := cnt' }
  | _ =>
    { stA with st1 := st1' }

private theorem nextActiveState_false_resolvedPrin {S : Setup} (sOrd : Nat) (q : KeyIndQuery S)
    (stA : FgKeyInd1KeyActiveSimState S) (st1' : FgKeyInd1KeySimState S) :
    (nextActiveState false sOrd q stA st1').resolvedPrin? = stA.resolvedPrin? := by
  cases q <;> simp [nextActiveState]

private theorem any_fst_eq_of_map_fst_eq {α β₁ β₂ : Type*} [BEq α] (a : α)
    {l1 : List (α × β₁)} {l2 : List (α × β₂)} (h : l1.map Prod.fst = l2.map Prod.fst) :
    l1.any (fun (k, _) => k == a) = l2.any (fun (k, _) => k == a) := by
  have h1 : (fun (x : α × β₁) => match x with | (k, _) => k == a) = (fun x => x.1 == a) := by
    funext ⟨k, _⟩; rfl
  have h2 : (fun (x : α × β₂) => match x with | (k, _) => k == a) = (fun x => x.1 == a) := by
    funext ⟨k, _⟩; rfl
  have := congrArg (fun L => L.any (· == a)) h
  rw [h1, h2]
  simpa only [List.any_map, Function.comp_def] using this

private theorem any_sid_eq_of_map_sid_eq {S : Setup} (sid : SessionId S)
    {l1 l2 : List (KeyIndInitiatorEntry S)}
    (h : l1.map KeyIndInitiatorEntry.sid = l2.map KeyIndInitiatorEntry.sid) :
    l1.any (fun e => e.sid == sid) = l2.any (fun e => e.sid == sid) := by
  have := congrArg (fun L => L.any (· == sid)) h
  simpa only [List.any_map, Function.comp_def] using this

private theorem stepPrinSlot_eq_post {S : Setup} (pOrd spkOrd : Nat) (uSk vSk : Bytes)
    (P : Primitives) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (stA : FgKeyInd1KeyActiveSimState S) (st1' : FgKeyInd1KeySimState S)
    (hPrinKeys : stA.st1.sim.base.principals.map Prod.fst = hst.base.principals.map Prod.fst)
    (hRes : stA.resolvedPrin? =
      (if pOrd < hst.base.principals.length then some (prinSlotAtOrd S hst.base pOrd) else none))
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    stepPrinSlot pOrd q hst = prinSlotAtOrd S x.2.base pOrd ∧
      (nextActiveState true pOrd q stA st1').resolvedPrin? =
        (if pOrd < x.2.base.principals.length then some (prinSlotAtOrd S x.2.base pOrd)
         else none) := by
  have hPrinLen : stA.st1.sim.base.principals.length = hst.base.principals.length := by
    have := congrArg List.length hPrinKeys; simpa using this
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNeInit
  · have hAnyEq := any_fst_eq_of_map_fst_eq u.val hPrinKeys
    unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      have hB := (Prod.mk.inj hEq).2
      have hLen' : x.2.base.principals.length = hst.base.principals.length + 1 := by
        rw [hB]; rfl
      unfold stepPrinSlot nextActiveState
      dsimp only
      rw [hAnyEq, hAny, hPrinLen, hRes]
      rcases lt_trichotomy pOrd hst.base.principals.length with hLt | hEqLen | hGt
      · have hNeLen : (hst.base.principals.length == pOrd) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
        have hLt' : pOrd < x.2.base.principals.length := by omega
        have hOrdEq := prinSlotAtOrd_cons_of_lt hst.base x.2.base u.val _ pOrd (by rw [hB]) hLt
        simp [hLt, hLt', hNeLen, hOrdEq]
      · subst hEqLen
        have hLt' : hst.base.principals.length < x.2.base.principals.length := by omega
        have hOrdEq := prinSlotAtOrd_cons_eq hst.base x.2.base u.val _ hst.base.principals.length
          (by rw [hB]) rfl
        simp [hLt', hOrdEq]
      · have hNotLt : ¬ (pOrd < hst.base.principals.length) := by omega
        have hNotLt' : ¬ (pOrd < x.2.base.principals.length) := by omega
        have hNeLen : (hst.base.principals.length == pOrd) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hGt)
        have hOrdEq := prinSlotAtOrd_of_ge x.2.base pOrd (by omega)
        simp [hNotLt, hNotLt', hNeLen, hOrdEq]
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      have hPEq : x.2.base.principals = hst.base.principals := by rw [hB]
      unfold stepPrinSlot nextActiveState
      dsimp only
      rw [hAnyEq, hAny, hRes]
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [prinSlotAtOrd_eq_ite, hPEq]
      exact ⟨by unfold prinSlotAtOrd; rw [hPEq], by unfold prinSlotAtOrd; rw [hPEq]⟩
  · unfold pqxdhKeyIndFgOrdPreImpl1Key at hx
    simp only [StateT_run_mk] at hx
    rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin true _ _ _ _ P q hNeInit] at hx
    have hStepEq : stepPrinSlot pOrd q hst = prinSlotAtOrd S hst.base pOrd := by
      unfold stepPrinSlot
      cases q with
      | initPrin u => exact absurd rfl (hNeInit u)
      | _ => exact prinSlotAtOrd_eq_ite hst.base pOrd
    have hResNext : (nextActiveState true pOrd q stA st1').resolvedPrin? = stA.resolvedPrin? := by
      cases q with
      | initPrin u => exact absurd rfl (hNeInit u)
      | _ => rfl
    have hPost : prinSlotAtOrd S x.2.base pOrd = prinSlotAtOrd S hst.base pOrd ∧
        x.2.base.principals.length = hst.base.principals.length := by
      refine mem_support_pqxdhKeyIndFgPreImpl_elim true (dynTargetIdx true pOrd q hst)
        (dynSpkIdx spkOrd q hst) (some uSk) (some vSk) P q hst x hx
        (fun hP _ _ _ => ⟨by unfold prinSlotAtOrd; rw [hP], congrArg List.length hP⟩)
        (fun u _ hq _ _ => absurd hq (hNeInit u))
        (fun u _ _ _ _ hB => ⟨prinSlotAtOrd_map hst.base x.2.base
          (fun (idx, e) => if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
          (fun ⟨idx, e⟩ => by dsimp only; split_ifs <;> rfl) pOrd (by rw [hB]),
          by rw [hB]; simp⟩)
        (fun _ _ _ _ _ _ _ hB => ⟨by unfold prinSlotAtOrd; rw [hB], by rw [hB]⟩)
        (fun _ _ _ _ _ _ _ hB => ⟨by unfold prinSlotAtOrd; rw [hB], by rw [hB]⟩)
        (fun _ _ _ hB => ⟨by unfold prinSlotAtOrd; rw [hB], by rw [hB]⟩)
        (fun _ _ _ hP _ _ _ => ⟨by unfold prinSlotAtOrd; rw [hP], congrArg List.length hP⟩)
        (fun _ _ _ _ _ hP _ _ _ => ⟨by unfold prinSlotAtOrd; rw [hP], congrArg List.length hP⟩)
        (fun _ _ hB => ⟨by unfold prinSlotAtOrd; rw [hB], by rw [hB]⟩)
    rw [hStepEq, hResNext, hRes, hPost.1, hPost.2]
    exact ⟨rfl, rfl⟩

private theorem stepSpkSlot_retarget_post {S : Setup} (useDh1 : Bool) (tOrd spkOrd : Nat)
    (uSk vSk : Bytes) (P : Primitives) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hOrd : ValidOrdInv spkOrd (P.x25519Base vSk) hst)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgOrdPreImpl1Key useDh1 tOrd spkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    stepSpkSlot spkOrd q hst = spkSlotAtOrd S x.2.base spkOrd ∨
      (∀ kb ∈ x.2.base.spkBundles,
        spkBundleFlatIdxVal S kb.1 ≠ stepSpkSlot spkOrd q hst ∧
        spkBundleFlatIdxVal S kb.1 ≠ spkSlotAtOrd S x.2.base spkOrd) := by
  by_cases hLt : spkOrd < hst.base.spkBundles.length
  · left
    unfold stepSpkSlot; simp only [hLt, ↓reduceIte]
    exact (pqxdhKeyIndFgOrdPreImpl1Key_spkSlotAtOrd_eq_of_lt useDh1 tOrd spkOrd uSk vSk P q hst
      hLt x hx).symm
  · have hCases :
        (∃ u, q = .initPrin u) ∨
        (∃ u j, q = .genSPK u j) ∨
        ((∀ u, q ≠ .initPrin u) ∧ (∀ u j, q ≠ .genSPK u j)) := by
      cases q with
      | initPrin u => exact Or.inl ⟨u, rfl⟩
      | genSPK u j => exact Or.inr (Or.inl ⟨u, j, rfl⟩)
      | _ => exact Or.inr (Or.inr ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩)
    rcases hCases with ⟨u, rfl⟩ | ⟨u, j, rfl⟩ | ⟨hNeInit, hNeSpk⟩
    · left
      unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
      rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
      have hSEq : x.2.base.spkBundles = hst.base.spkBundles := by
        revert hb
        cases hst.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
            monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
            MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
          rintro ⟨_, _, hEq⟩; rw [(Prod.mk.inj hEq).2]
        · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; rw [(Prod.mk.inj hEq).2]
      unfold stepSpkSlot; simp only [hLt, ↓reduceIte]
      exact (spkSlotAtOrd_of_ge x.2.base spkOrd (by rw [hSEq]; omega)).symm
    · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl
        fgPreGenSPK at hx
      rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
      have hUnchCase : x.2.base.spkBundles = hst.base.spkBundles →
          stepSpkSlot spkOrd (.genSPK u j) hst = spkSlotAtOrd S x.2.base spkOrd ∨
            (∀ kb ∈ x.2.base.spkBundles,
              spkBundleFlatIdxVal S kb.1 ≠ stepSpkSlot spkOrd (.genSPK u j) hst ∧
              spkBundleFlatIdxVal S kb.1 ≠ spkSlotAtOrd S x.2.base spkOrd) := by
        intro hSEq
        have hOrdEq : spkSlotAtOrd S x.2.base spkOrd = spkSlotAtOrd S hst.base spkOrd := by
          unfold spkSlotAtOrd; rw [hSEq]
        rcases stepSpkSlot_retarget_pre spkOrd (P.x25519Base vSk) (.genSPK u j) hst hOrd with
          hE | hAbs
        · exact Or.inl (hE.symm.trans hOrdEq.symm)
        · right
          intro kb hMem; rw [hSEq] at hMem; rw [hOrdEq]
          exact ⟨(hAbs kb hMem).2, (hAbs kb hMem).1⟩
      revert hb
      cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hFind : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; exact hUnchCase (by rw [(Prod.mk.inj hEq).2])
        | some p0 =>
          rcases p0 with ⟨_, uEntry⟩
          simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
            Set.mem_singleton_iff]
          rintro ⟨_, _, _, _, _, _, _, _, hEq⟩
          have hB := (Prod.mk.inj hEq).2
          left
          unfold stepSpkSlot
          simp only [hLt, ↓reduceIte, hAny, Bool.not_false, Bool.true_and]
          by_cases hEqLen : hst.base.spkBundles.length = spkOrd
          · simp only [beq_iff_eq.mpr hEqLen, ↓reduceIte]
            exact (spkSlotAtOrd_cons_eq hst.base x.2.base u j _ spkOrd (by rw [hB]) hEqLen).symm
          · have hNeB : (hst.base.spkBundles.length == spkOrd) = false :=
              beq_eq_false_iff_ne.mpr hEqLen
            simp only [hNeB, Bool.false_eq_true, ↓reduceIte]
            have hGt : hst.base.spkBundles.length < spkOrd := by omega
            exact (spkSlotAtOrd_of_ge x.2.base spkOrd (by rw [hB]; dsimp; omega)).symm
      · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact hUnchCase (by rw [(Prod.mk.inj hEq).2])
    · left
      unfold pqxdhKeyIndFgOrdPreImpl1Key at hx
      simp only [StateT_run_mk] at hx
      rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin useDh1 _ _ _ _ P q hNeInit] at hx
      have hStep : stepSpkSlot spkOrd q hst = S.N_spk_tot := by
        unfold stepSpkSlot; simp only [hLt, ↓reduceIte]
      have hLenEq : x.2.base.spkBundles.length = hst.base.spkBundles.length :=
        mem_support_pqxdhKeyIndFgPreImpl_elim useDh1 (dynTargetIdx useDh1 tOrd q hst)
          (dynSpkIdx spkOrd q hst) (some uSk) (some vSk) P q hst x hx
          (fun _ hS _ _ => congrArg List.length hS)
          (fun u _ hq _ _ => absurd hq (hNeInit u))
          (fun _ _ _ _ _ hB => by rw [hB])
          (fun u j _ hq _ _ _ _ => absurd hq (hNeSpk u j))
          (fun _ _ _ _ _ _ _ hB => by rw [hB])
          (fun _ _ _ hB => by rw [hB])
          (fun _ _ _ _ hS _ _ => congrArg List.length hS)
          (fun _ _ _ _ _ _ hS _ _ => congrArg List.length hS)
          (fun _ _ hB => by rw [hB]; exact List.length_map _)
      rw [hStep]
      exact (spkSlotAtOrd_of_ge x.2.base spkOrd (by omega)).symm

private theorem stepSessSlot_retarget_post {S : Setup} (sOrd spkOrd : Nat)
    (uSk vSk : Bytes) (P : Primitives) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hOrd : ValidOrdInv spkOrd (P.x25519Base vSk) hst)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd (some uSk) (some vSk)
      S P q).run hst)) :
    stepSessSlot sOrd q hst = sessSlotAtOrd S x.2.base sOrd ∨
      (∀ s ∈ x.2.base.sessions,
        initSessionSlotIdx s.sid ≠ stepSessSlot sOrd q hst ∧
        initSessionSlotIdx s.sid ≠ sessSlotAtOrd S x.2.base sOrd) := by
  have hUnchCase : x.2.base.sessions = hst.base.sessions →
      stepSessSlot sOrd q hst = sessSlotAtOrd S x.2.base sOrd ∨
        (∀ s ∈ x.2.base.sessions,
          initSessionSlotIdx s.sid ≠ stepSessSlot sOrd q hst ∧
          initSessionSlotIdx s.sid ≠ sessSlotAtOrd S x.2.base sOrd) := by
    intro hSEq
    have hOrdEq : sessSlotAtOrd S x.2.base sOrd = sessSlotAtOrd S hst.base sOrd := by
      unfold sessSlotAtOrd; rw [hSEq]
    rcases stepSessSlot_retarget_pre sOrd spkOrd (P.x25519Base vSk) q hst hOrd with hE | hAbs
    · exact Or.inl (hE.symm.trans hOrdEq.symm)
    · right
      intro s hMem; rw [hSEq] at hMem; rw [hOrdEq]
      exact ⟨(hAbs s hMem).2, (hAbs s hMem).1⟩
  have hCases :
      (∃ u, q = .initPrin u) ∨
      (∃ u i bundle, q = .initiateOPK u i bundle) ∨
      (∃ u i bundle, q = .initiateNoOPK u i bundle) ∨
      ((∀ u, q ≠ .initPrin u) ∧
       (∀ u i bundle, q ≠ .initiateOPK u i bundle) ∧
       (∀ u i bundle, q ≠ .initiateNoOPK u i bundle)) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | initiateOPK u i b => exact Or.inr (Or.inl ⟨u, i, b, rfl⟩)
    | initiateNoOPK u i b => exact Or.inr (Or.inr (Or.inl ⟨u, i, b, rfl⟩))
    | _ =>
      exact Or.inr (Or.inr (Or.inr
        ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩))
  rcases hCases with ⟨u, rfl⟩ | ⟨u, i, bundle, rfl⟩ | ⟨u, i, bundle, rfl⟩ |
    ⟨hNeInit, hNoOpk, hNoNoOpk⟩
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key fgPreInitPrin1Key at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩; exact hUnchCase (by rw [(Prod.mk.inj hEq).2])
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact hUnchCase (by rw [(Prod.mk.inj hEq).2])
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      intro hb
      refine mem_support_fgPreInitiate_elim _ _ _ P (.sendOPK u i) u bundle hst.base _ hb
        (fun hEq => by dsimp only at hEq; exact hUnchCase (by rw [hEq]))
        (fun sEntry roCache' hAnyF hEq => ?_)
      dsimp only at hEq
      have hCons : x.2.base.sessions = sEntry :: hst.base.sessions := by rw [hEq]
      have hSid : sEntry.sid = .sendOPK u i := by
        rcases fgPreInitiate_sid_mem _ _ _ P (.sendOPK u i) u bundle hst.base _ hb sEntry
            (by rw [hCons]; exact List.mem_cons_self) with hOld | hSid
        · exfalso
          have hT : hst.base.sessions.any (fun e => e.sid == sEntry.sid) = true :=
            List.any_eq_true.mpr ⟨sEntry, hOld, beq_self_eq_true _⟩
          rw [hAnyF] at hT; cases hT
        · exact hSid
      rw [hSid] at hAnyF
      left
      unfold stepSessSlot
      simp only [hAnyF, Bool.not_false, Bool.true_and]
      rcases lt_trichotomy sOrd hst.base.sessions.length with hLt | hEqLen | hGt
      · simp only [hLt, ↓reduceIte]
        exact (sessSlotAtOrd_cons_of_lt hst.base x.2.base sEntry sOrd hCons hLt).symm
      · subst hEqLen
        simp only [Nat.lt_irrefl, beq_self_eq_true, ↓reduceIte, ← hSid]
        exact (sessSlotAtOrd_cons_eq hst.base x.2.base sEntry hst.base.sessions.length
          hCons rfl).symm
      · have hNotLt : ¬ (sOrd < hst.base.sessions.length) := by omega
        have hNeLen : (hst.base.sessions.length == sOrd) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hGt)
        simp only [hNotLt, hNeLen, Bool.false_eq_true, ↓reduceIte]
        exact (sessSlotAtOrd_of_ge x.2.base sOrd (by rw [hCons]; dsimp; omega)).symm
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact hUnchCase (by rw [(Prod.mk.inj hEq).2])
  · unfold pqxdhKeyIndFgOrdPreImpl1Key pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      intro hb
      refine mem_support_fgPreInitiate_elim _ _ _ P (.sendNoOPK u i) u bundle hst.base _ hb
        (fun hEq => by dsimp only at hEq; exact hUnchCase (by rw [hEq]))
        (fun sEntry roCache' hAnyF hEq => ?_)
      dsimp only at hEq
      have hCons : x.2.base.sessions = sEntry :: hst.base.sessions := by rw [hEq]
      have hSid : sEntry.sid = .sendNoOPK u i := by
        rcases fgPreInitiate_sid_mem _ _ _ P (.sendNoOPK u i) u bundle hst.base _ hb sEntry
            (by rw [hCons]; exact List.mem_cons_self) with hOld | hSid
        · exfalso
          have hT : hst.base.sessions.any (fun e => e.sid == sEntry.sid) = true :=
            List.any_eq_true.mpr ⟨sEntry, hOld, beq_self_eq_true _⟩
          rw [hAnyF] at hT; cases hT
        · exact hSid
      rw [hSid] at hAnyF
      left
      unfold stepSessSlot
      simp only [hAnyF, Bool.not_false, Bool.true_and]
      rcases lt_trichotomy sOrd hst.base.sessions.length with hLt | hEqLen | hGt
      · simp only [hLt, ↓reduceIte]
        exact (sessSlotAtOrd_cons_of_lt hst.base x.2.base sEntry sOrd hCons hLt).symm
      · subst hEqLen
        simp only [Nat.lt_irrefl, beq_self_eq_true, ↓reduceIte, ← hSid]
        exact (sessSlotAtOrd_cons_eq hst.base x.2.base sEntry hst.base.sessions.length
          hCons rfl).symm
      · have hNotLt : ¬ (sOrd < hst.base.sessions.length) := by omega
        have hNeLen : (hst.base.sessions.length == sOrd) = false :=
          beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hGt)
        simp only [hNotLt, hNeLen, Bool.false_eq_true, ↓reduceIte]
        exact (sessSlotAtOrd_of_ge x.2.base sOrd (by rw [hCons]; dsimp; omega)).symm
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact hUnchCase (by rw [(Prod.mk.inj hEq).2])
  · unfold pqxdhKeyIndFgOrdPreImpl1Key at hx
    simp only [StateT_run_mk] at hx
    rw [pqxdhKeyIndFgPreImpl1Key_eq_of_ne_initPrin false _ _ _ _ P q hNeInit] at hx
    have hSessLen := pqxdhKeyIndFgPreImpl_sessions_len_of_ne_init false
      (dynTargetIdx false sOrd q hst) (dynSpkIdx spkOrd q hst) (some uSk) (some vSk)
      P q hNoOpk hNoNoOpk hst x hx
    have hStepEq : stepSessSlot sOrd q hst = sessSlotAtOrd S hst.base sOrd := by
      unfold stepSessSlot
      cases q with
      | initiateOPK u i b => exact absurd rfl (hNoOpk u i b)
      | initiateNoOPK u i b => exact absurd rfl (hNoNoOpk u i b)
      | _ => exact sessSlotAtOrd_eq_ite hst.base sOrd
    have hOrdEq : sessSlotAtOrd S x.2.base sOrd = sessSlotAtOrd S hst.base sOrd :=
      mem_support_pqxdhKeyIndFgPreImpl_elim false (dynTargetIdx false sOrd q hst)
        (dynSpkIdx spkOrd q hst) (some uSk) (some vSk) P q hst x hx
        (fun _ _ _ hSe => by unfold sessSlotAtOrd; rw [hSe])
        (fun u _ hq _ _ => absurd hq (hNeInit u))
        (fun _ _ _ _ _ hB => by unfold sessSlotAtOrd; rw [hB])
        (fun _ _ _ _ _ _ _ hB => by unfold sessSlotAtOrd; rw [hB])
        (fun _ _ _ _ _ _ _ hB => by unfold sessSlotAtOrd; rw [hB])
        (fun s _ _ hB => by rw [hB] at hSessLen; simp at hSessLen)
        (fun _ _ _ _ _ hSe _ => by unfold sessSlotAtOrd; rw [hSe])
        (fun f hfSid _ _ _ _ _ _ hSe => sessSlotAtOrd_map hst.base x.2.base f hfSid sOrd hSe)
        (fun _ _ hB => by unfold sessSlotAtOrd; rw [hB])
    exact Or.inl (hStepEq.trans hOrdEq.symm)


private theorem nextActiveState_st1 (prinFlag : Bool) (pOrd : Nat) {S : Setup}
    (q : KeyIndQuery S) (stA : FgKeyInd1KeyActiveSimState S) (st1' : FgKeyInd1KeySimState S) :
    (nextActiveState prinFlag pOrd q stA st1').st1 = st1' := by
  cases q <;> rfl

private theorem erasePrincipalsFg_map_fst (uIdx : Nat)
    (ps : List (Nat × PrincipalEntry)) :
    (erasePrincipalsFg uIdx ps).map Prod.fst = ps.map Prod.fst := by
  unfold erasePrincipalsFg erasePrincipalEntryFg
  induction ps with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, e⟩
    simp only [List.map_cons, ih]

private theorem clearTargetPrinSecSign_map_fst (uIdx : Nat)
    (ps : List (Nat × PrincipalEntry)) :
    (ps.map (fun (idx, e) => (idx, clearTargetPrinSecSign uIdx idx e))).map Prod.fst =
      ps.map Prod.fst := by
  induction ps with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨idx, e⟩
    simp only [List.map_cons, ih]

private theorem eraseSpkBundlesFg_map_fst {S : Setup} (bIdx : Nat)
    (bs : List ((Nat × Nat) × SpkBundleEntry)) :
    (eraseSpkBundlesFg S bIdx bs).map Prod.fst = bs.map Prod.fst := by
  unfold eraseSpkBundlesFg eraseSpkBundleEntryFg
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    simp only [List.map_cons, ih]

private theorem eraseSessionsFg_map_sid {S : Setup} (sIdx : Nat)
    (ss : List (KeyIndInitiatorEntry S)) :
    (eraseSessionsFg sIdx ss).map KeyIndInitiatorEntry.sid =
      ss.map KeyIndInitiatorEntry.sid := by
  unfold eraseSessionsFg eraseSessionEntryFg
  induction ss with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, ih]; split <;> rfl

private theorem fgSimInvDh1_1Key_maps {S : Setup} {b : QueryBudget} {P : Primitives}
    {R : FgSlotReps P} {uIdx bIdx : Nat} {uSk vSk : Bytes} {rem : Nat}
    {hst : KeyIndFgCutoffState S} {st : FgKeyInd1KeySimState S}
    (hInv : FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk rem hst st) :
    st.sim.base.principals.map Prod.fst = hst.base.principals.map Prod.fst ∧
    st.sim.base.spkBundles.map Prod.fst = hst.base.spkBundles.map Prod.fst ∧
    ValidKeyIndEcFg S hst.base := by
  rcases hInv with ⟨stGhost, hSim, hGInv, _, _⟩
  rcases hGInv with ⟨hBase, _, _, _, _, hVEc, _, _, _, _, _⟩
  refine ⟨?_, ?_, hVEc⟩
  · rw [hSim, clearTargetSecIKAsign_base_principals, clearTargetPrinSecSign_map_fst, hBase]
    unfold eraseStateFg; dsimp only [↓reduceIte]
    exact erasePrincipalsFg_map_fst uIdx hst.base.principals
  · rw [hSim, clearTargetSecIKAsign_base_spkBundles, hBase]
    unfold eraseStateFg; dsimp only [↓reduceIte]
    exact eraseSpkBundlesFg_map_fst bIdx hst.base.spkBundles

private theorem fgSimInvDh3_1Key_maps {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {sIdx bIdx : Nat}
    {uSk vSk : Bytes} {huSk : uSk.length = 32} {hvSk : vSk.length = 32} {rem : Nat}
    {hst : KeyIndFgCutoffState S} {st : FgKeyInd1KeySimState S}
    (hInv : FgSimInvDh3_1Key S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st) :
    st.sim.base.principals = hst.base.principals ∧
    st.sim.base.spkBundles.map Prod.fst = hst.base.spkBundles.map Prod.fst ∧
    st.sim.base.sessions.map KeyIndInitiatorEntry.sid =
      hst.base.sessions.map KeyIndInitiatorEntry.sid ∧
    ValidKeyIndEcFg S hst.base := by
  rcases hInv with ⟨hBase, _, _, _, _, hVEc, _, _, _, _, _⟩
  refine ⟨?_, ?_, ?_, hVEc⟩
  · rw [hBase]; rfl
  · rw [hBase]; unfold eraseStateFg; dsimp only [Bool.false_eq_true, ↓reduceIte]
    exact eraseSpkBundlesFg_map_fst bIdx hst.base.spkBundles
  · rw [hBase]; unfold eraseStateFg; dsimp only [Bool.false_eq_true, ↓reduceIte]
    exact eraseSessionsFg_map_sid sIdx hst.base.sessions

private theorem active_isTargetSpk_eq {S : Setup} (spkOrd : Nat) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hst : KeyIndFgCutoffState S)
    (hOrd : ValidOrdInv spkOrd V hst)
    (hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false) :
    (hst.base.spkBundles.length == spkOrd) =
      (spkBundleFlatIdx S u j == stepSpkSlot spkOrd (.genSPK u j) hst) := by
  unfold stepSpkSlot
  simp only [hAny, Bool.not_false, Bool.true_and]
  by_cases hLt : spkOrd < hst.base.spkBundles.length
  · simp only [hLt, ↓reduceIte]
    have hNeLen : (hst.base.spkBundles.length == spkOrd) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
    have hFired := hasFiredSpk_of_spkOrd_lt spkOrd hst hOrd.2.1 hLt
    have hNe2 : (spkBundleFlatIdx S u j == spkSlotAtOrd S hst.base spkOrd) = false := by
      cases hE : (spkBundleFlatIdx S u j == spkSlotAtOrd S hst.base spkOrd)
      · rfl
      · exfalso
        have hT := spkBundles_any_of_hasFiredSpk S _ hst hFired u j hE
        rw [hAny] at hT; cases hT
    rw [hNeLen, hNe2]
  · simp only [hLt, ↓reduceIte]
    cases hEqLen : (hst.base.spkBundles.length == spkOrd)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (spkSlotFlatIdx_lt S u.isLt j.isLt))).symm
    · simp

private theorem fgGenSpkActivePure_eq {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (tStep spkOrd maxLen : Nat)
    (U V V0 : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hst : KeyIndFgCutoffState S) (sim : FgKeyIndSimState S)
    (hOrd : ValidOrdInv spkOrd V0 hst)
    (hSpkKeys : sim.base.spkBundles.map Prod.fst = hst.base.spkBundles.map Prod.fst) :
    fgGenSpkActivePure P spkOrd V u j sim =
      fgKeyIndStepPure P ddh useDh1 tStep (stepSpkSlot spkOrd (.genSPK u j) hst) S maxLen U V
        (.genSPK u j) sim := by
  have hAnyEq := any_fst_eq_of_map_fst_eq (u.val, j.val) hSpkKeys
  have hLenEq : sim.base.spkBundles.length = hst.base.spkBundles.length := by
    have := congrArg List.length hSpkKeys; simpa using this
  unfold fgGenSpkActivePure fgKeyIndStepPure
  dsimp only
  cases hAny : sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases sim.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => rfl
    | some p0 =>
      rcases p0 with ⟨_, uEntry⟩
      have hHstAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false :=
        hAnyEq.symm.trans hAny
      have hTgtEq : (sim.base.spkBundles.length == spkOrd) =
          (spkBundleFlatIdx S u j == stepSpkSlot spkOrd (.genSPK u j) hst) := by
        rw [hLenEq]
        exact active_isTargetSpk_eq spkOrd V0 u j hst hOrd hHstAny
      simp only [hTgtEq]
  · simp

private theorem fgGenSPK1KeyActivePure_eq {S : Setup} (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (tStep spkOrd maxLen : Nat)
    (U V V0 : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hOrd : ValidOrdInv spkOrd V0 hst)
    (hSpkKeys : stA.st1.sim.base.spkBundles.map Prod.fst = hst.base.spkBundles.map Prod.fst)
    (hMatch : optNatMatches stA.resolvedPrin? u.val = (useDh1 && (u.val == tStep))) :
    fgGenSPK1KeyActivePure P uSk spkOrd V u j stA =
      (fgGenSPK1KeyPure P uSk ddh useDh1 tStep useDh1 tStep
          (stepSpkSlot spkOrd (.genSPK u j) hst) S maxLen U V u j stA.st1 >>=
        fun p => pure (p.1, { stA with st1 := p.2 })) := by
  have hAnyEq := any_fst_eq_of_map_fst_eq (u.val, j.val) hSpkKeys
  have hLenEq : stA.st1.sim.base.spkBundles.length = hst.base.spkBundles.length := by
    have := congrArg List.length hSpkKeys; simpa using this
  unfold fgGenSPK1KeyActivePure fgGenSPK1KeyPure
  rw [hMatch]
  cases (useDh1 && (u.val == tStep))
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind,
      fgGenSpkActivePure_eq P ddh useDh1 tStep spkOrd maxLen U V V0 u j hst stA.st1.sim
        hOrd hSpkKeys]
  · simp only [↓reduceIte]
    cases hAny : stA.st1.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p0 =>
        rcases p0 with ⟨_, uEntry⟩
        dsimp only
        cases stA.st1.sigBudget == 0
        · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
          have hHstAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false :=
            hAnyEq.symm.trans hAny
          have hTgtEq : (stA.st1.sim.base.spkBundles.length == spkOrd) =
              (spkBundleFlatIdx S u j == stepSpkSlot spkOrd (.genSPK u j) hst) := by
            rw [hLenEq]
            exact active_isTargetSpk_eq spkOrd V0 u j hst hOrd hHstAny
          simp only [hTgtEq]
        · simp
    · simp

private theorem fgInitiateActivePure_opk_eq {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (ord1 ephOrd tStep bStep maxLen : Nat)
    (U V : Bytes) (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput)
    (stA : FgKeyInd1KeyActiveSimState S)
    (hEphEq : stA.st1.sim.base.sessions.any (fun e => e.sid == .sendOPK u i) = false →
      ((!useDh1) && (stA.st1.sim.base.sessions.length == ephOrd)) =
      ((!useDh1) && (initSessionSlotIdx (.sendOPK u i) == tStep))) :
    fgInitiateActivePure P ddh useDh1 false ephOrd S maxLen U true (.sendOPK u i) u bundle stA =
      (fgKeyIndStepPure P ddh useDh1 tStep bStep S maxLen U V (.initiateOPK u i bundle)
          stA.st1.sim >>=
        fun p => pure (p.1,
          nextActiveState useDh1 ord1 (.initiateOPK u i bundle) stA
            { stA.st1 with sim := p.2 })) := by
  unfold fgInitiateActivePure fgRunInitiateActivePure fgKeyIndStepPure fgRunInitiatePure
    nextActiveState
  dsimp only
  cases bundle.opkB? with
  | none => simp
  | some opkPair =>
    simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, Option.isNone_some,
      ↓reduceIte]
    cases hAny : stA.st1.sim.base.sessions.any (fun e => e.sid == .sendOPK u i)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hEph := hEphEq hAny
      cases stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p0 =>
        rcases p0 with ⟨_, uEntry⟩
        dsimp only
        cases koskBundleOkTake S P stA.st1.sim.base.principals stA.st1.sim.base.spkBundles
          stA.st1.sim.base.opkEntries stA.st1.sim.advKeyPows bundle
        · simp
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hEph, bind_assoc]
          congr 1; funext ekASkRaw
          congr 1; funext kemCoins
          cases (P.sigVerify
              (resolveSigPk P (stA.st1.sim.base.principals.take S.N_dh) bundle.ikB)
              (encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify
              (resolveSigPk P (stA.st1.sim.base.principals.take S.N_dh) bundle.ikB)
              (encodeKEM bundle.pqspkB) bundle.pqspkSig)
          · simp
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases P.kemEncaps bundle.pqspkB kemCoins with
            | none => simp
            | some kemPair =>
              rcases kemPair with ⟨ss, kemCt⟩
              dsimp only
              simp only [bind_assoc]
              congr 1; funext fgPair
              rcases fgPair with ⟨drKeyReal, fgL'⟩
              dsimp only
              congr 1; funext drKeyRand
              cases findHonestPrincipal P (stA.st1.sim.base.principals.take S.N_dh) bundle.ikB <;>
                simp
    · simp

private theorem fgInitiateActivePure_noopk_eq {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (ord1 ephOrd tStep bStep maxLen : Nat)
    (U V : Bytes) (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
    (stA : FgKeyInd1KeyActiveSimState S)
    (hEphEq : stA.st1.sim.base.sessions.any (fun e => e.sid == .sendNoOPK u i) = false →
      ((!useDh1) && (stA.st1.sim.base.sessions.length == ephOrd)) =
      ((!useDh1) && (initSessionSlotIdx (.sendNoOPK u i) == tStep))) :
    fgInitiateActivePure P ddh useDh1 false ephOrd S maxLen U false (.sendNoOPK u i) u bundle stA =
      (fgKeyIndStepPure P ddh useDh1 tStep bStep S maxLen U V (.initiateNoOPK u i bundle)
          stA.st1.sim >>=
        fun p => pure (p.1,
          nextActiveState useDh1 ord1 (.initiateNoOPK u i bundle) stA
            { stA.st1 with sim := p.2 })) := by
  unfold fgInitiateActivePure fgRunInitiateActivePure fgKeyIndStepPure fgRunInitiatePure
    nextActiveState
  dsimp only
  cases bundle.opkB? with
  | some _ => simp
  | none =>
    simp only [Option.isSome_none, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Bool.true_and]
    cases hAny : stA.st1.sim.base.sessions.any (fun e => e.sid == .sendNoOPK u i)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hEph := hEphEq hAny
      cases stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p0 =>
        rcases p0 with ⟨_, uEntry⟩
        dsimp only
        cases koskBundleOkTake S P stA.st1.sim.base.principals stA.st1.sim.base.spkBundles
          stA.st1.sim.base.opkEntries stA.st1.sim.advKeyPows bundle
        · simp
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hEph, bind_assoc]
          congr 1; funext ekASkRaw
          congr 1; funext kemCoins
          cases (P.sigVerify
              (resolveSigPk P (stA.st1.sim.base.principals.take S.N_dh) bundle.ikB)
              (encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify
              (resolveSigPk P (stA.st1.sim.base.principals.take S.N_dh) bundle.ikB)
              (encodeKEM bundle.pqspkB) bundle.pqspkSig)
          · simp
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases P.kemEncaps bundle.pqspkB kemCoins with
            | none => simp
            | some kemPair =>
              rcases kemPair with ⟨ss, kemCt⟩
              dsimp only
              simp only [bind_assoc]
              congr 1; funext fgPair
              rcases fgPair with ⟨drKeyReal, fgL'⟩
              dsimp only
              congr 1; funext drKeyRand
              cases findHonestPrincipal P (stA.st1.sim.base.principals.take S.N_dh) bundle.ikB <;>
                simp
    · simp

private def activeSigSlack (S : Setup) (b : QueryBudget) : Nat :=
  min S.N_spk_tot S.N_recv - activeSigBudget S b

private def toStaticSt1 (S : Setup) (b : QueryBudget) (st1 : FgKeyInd1KeySimState S) :
    FgKeyInd1KeySimState S :=
  { st1 with sigBudget := st1.sigBudget + activeSigSlack S b }

private def fromStaticSt1 (S : Setup) (b : QueryBudget) (st1 : FgKeyInd1KeySimState S) :
    FgKeyInd1KeySimState S :=
  { st1 with sigBudget := st1.sigBudget - activeSigSlack S b }

private theorem fromStaticSt1_toStaticSt1 (S : Setup) (b : QueryBudget)
    (st1 : FgKeyInd1KeySimState S) :
    fromStaticSt1 S b (toStaticSt1 S b st1) = st1 := by
  cases st1; simp [fromStaticSt1, toStaticSt1]

private theorem fromStaticSt1_upd_sim (S : Setup) (b : QueryBudget)
    (st1 : FgKeyInd1KeySimState S) (sim' : FgKeyIndSimState S) :
    fromStaticSt1 S b { toStaticSt1 S b st1 with sim := sim' } = { st1 with sim := sim' } := by
  cases st1; simp [fromStaticSt1, toStaticSt1]

private theorem toStaticSt1_fromStaticSt1_of_le (S : Setup) (b : QueryBudget)
    (st1 : FgKeyInd1KeySimState S) (h : activeSigSlack S b ≤ st1.sigBudget) :
    toStaticSt1 S b (fromStaticSt1 S b st1) = st1 := by
  rcases st1 with ⟨sim, sigBudget⟩
  simp only [toStaticSt1, fromStaticSt1, FgKeyInd1KeySimState.mk.injEq, true_and] at h ⊢
  omega

private theorem toStaticSt1_empty (S : Setup) (b : QueryBudget) (secb : Bool) :
    toStaticSt1 S b (FgKeyInd1KeyActiveSimState.empty S b secb).st1 =
      FgKeyInd1KeySimState.empty S secb := by
  unfold toStaticSt1 activeSigSlack FgKeyInd1KeyActiveSimState.empty FgKeyInd1KeySimState.empty
    activeSigBudget
  dsimp only
  congr 1
  omega

private theorem bundleSignedMessages_length_le (k : Nat)
    (bs : List ((Nat × Nat) × SpkBundleEntry)) :
    (bundleSignedMessages k bs).length ≤ 2 * bs.length := by
  have h1 : ∀ (l : List ((Nat × Nat) × SpkBundleEntry)),
      (l.flatMap (fun (_, b) => [encodeEC b.spkPk, encodeKEM b.pqspkPk])).length = 2 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simp [List.flatMap_cons, ih]; omega
  unfold bundleSignedMessages
  rw [h1]
  exact Nat.mul_le_mul_left 2 (List.length_filter_le _ bs)

private theorem activeSigSlack_or_pos_of_inv {S : Setup} (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : Nat) (uSk vSk : Bytes) (rem : Nat)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hInv : FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk (rem + 1) hst (toStaticSt1 S b stA.st1))
    (hLen : hst.base.spkBundles.length + (rem + 1) ≤ b.q_total) :
    activeSigSlack S b = 0 ∨ 1 ≤ stA.st1.sigBudget := by
  rcases hInv with ⟨_, _, _, hBud, _⟩
  have hMsgLen := bundleSignedMessages_length_le uIdx hst.base.spkBundles
  simp only [toStaticSt1, activeSigSlack, activeSigBudget] at hBud ⊢
  omega

private theorem activeSigSlack_le_of_inv {S : Setup} (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (uIdx bIdx : Nat) (uSk vSk : Bytes) (rem : Nat)
    (hst : KeyIndFgCutoffState S) (st1' : FgKeyInd1KeySimState S)
    (hInv : FgSimInvDh1_1Key S b P R uIdx bIdx uSk vSk rem hst st1')
    (hLen : hst.base.spkBundles.length + rem ≤ b.q_total) :
    activeSigSlack S b ≤ st1'.sigBudget := by
  rcases hInv with ⟨_, _, _, hBud, _⟩
  have hMsgLen := bundleSignedMessages_length_le uIdx hst.base.spkBundles
  simp only [activeSigSlack, activeSigBudget]
  omega

private theorem fgGenSPK1KeyActivePure_dh1_eq {S : Setup} (b : QueryBudget)
    (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (tStep spkOrd maxLen : Nat)
    (U V V0 : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hOrd : ValidOrdInv spkOrd V0 hst)
    (hSpkKeys : stA.st1.sim.base.spkBundles.map Prod.fst = hst.base.spkBundles.map Prod.fst)
    (hMatch : optNatMatches stA.resolvedPrin? u.val = (u.val == tStep))
    (hBud : activeSigSlack S b = 0 ∨ 1 ≤ stA.st1.sigBudget) :
    fgGenSPK1KeyActivePure P uSk spkOrd V u j stA =
      (fgGenSPK1KeyPure P uSk ddh true tStep true tStep
          (stepSpkSlot spkOrd (.genSPK u j) hst) S maxLen U V u j
          (toStaticSt1 S b stA.st1) >>=
        fun p => pure (p.1, { stA with st1 := fromStaticSt1 S b p.2 })) := by
  have hAnyEq := any_fst_eq_of_map_fst_eq (u.val, j.val) hSpkKeys
  have hLenEq : stA.st1.sim.base.spkBundles.length = hst.base.spkBundles.length := by
    have := congrArg List.length hSpkKeys; simpa using this
  unfold fgGenSPK1KeyActivePure fgGenSPK1KeyPure
  rw [hMatch]
  simp only [Bool.true_and]
  cases (u.val == tStep)
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind, toStaticSt1,
      fgGenSpkActivePure_eq P ddh true tStep spkOrd maxLen U V V0 u j hst stA.st1.sim
        hOrd hSpkKeys]
    refine congrArg _ (funext fun p => ?_)
    cases stA.st1; simp [fromStaticSt1]
  · simp only [↓reduceIte]
    have hSimEq : (toStaticSt1 S b stA.st1).sim = stA.st1.sim := rfl
    simp only [hSimEq]
    cases hAny : stA.st1.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [fromStaticSt1_toStaticSt1]
      | some p0 =>
        rcases p0 with ⟨_, uEntry⟩
        dsimp only
        have hZeroEq : ((toStaticSt1 S b stA.st1).sigBudget == 0) = (stA.st1.sigBudget == 0) := by
          apply Bool.eq_iff_iff.mpr
          simp only [toStaticSt1, beq_iff_eq]
          omega
        rw [hZeroEq]
        cases hZ : (stA.st1.sigBudget == 0)
        · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
          have hHstAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false :=
            hAnyEq.symm.trans hAny
          have hTgtEq : (stA.st1.sim.base.spkBundles.length == spkOrd) =
              (spkBundleFlatIdx S u j == stepSpkSlot spkOrd (.genSPK u j) hst) := by
            rw [hLenEq]
            exact active_isTargetSpk_eq spkOrd V0 u j hst hOrd hHstAny
          have hSubEq : (toStaticSt1 S b stA.st1).sigBudget - 1 - activeSigSlack S b =
              stA.st1.sigBudget - 1 := by
            have hPos : stA.st1.sigBudget ≠ 0 := beq_eq_false_iff_ne.mp hZ
            simp only [toStaticSt1]; omega
          simp only [hTgtEq, fromStaticSt1, hSubEq]
        · simp [fromStaticSt1_toStaticSt1]
    · simp [fromStaticSt1_toStaticSt1]

private theorem fgKeyInd1KeyActiveStepPure_dh1_eq {S : Setup} (b : QueryBudget)
    (P : Primitives) (uSk vSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (pOrd spkOrd maxLen : Nat) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hOrd : ValidOrdInv spkOrd (P.x25519Base vSk) hst)
    (hPrinKeys : stA.st1.sim.base.principals.map Prod.fst = hst.base.principals.map Prod.fst)
    (hSpkKeys : stA.st1.sim.base.spkBundles.map Prod.fst = hst.base.spkBundles.map Prod.fst)
    (hRes : stA.resolvedPrin? =
      (if pOrd < hst.base.principals.length then some (prinSlotAtOrd S hst.base pOrd) else none))
    (hBud : activeSigSlack S b = 0 ∨ 1 ≤ stA.st1.sigBudget) :
    let U := P.x25519Base uSk
    let V := P.x25519Base vSk
    fgKeyInd1KeyActiveStepPure (activeParamsDh1 b U V pOrd spkOrd) P uSk ddh S maxLen q stA =
      (fgKeyInd1KeyStepPure P uSk ddh true (stepPrinSlot pOrd q hst) (stepSpkSlot spkOrd q hst)
          S maxLen U V q (toStaticSt1 S b stA.st1) >>=
        fun p => pure (p.1, nextActiveState true pOrd q stA (fromStaticSt1 S b p.2))) := by
  intro U V
  have hSimEq : (toStaticSt1 S b stA.st1).sim = stA.st1.sim := rfl
  cases q with
  | initPrin u =>
    have hAnyEq := any_fst_eq_of_map_fst_eq u.val hPrinKeys
    have hLenEq : stA.st1.sim.base.principals.length = hst.base.principals.length := by
      have := congrArg List.length hPrinKeys; simpa using this
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh1 fgInitPrin1KeyActivePure
      fgKeyInd1KeyStepPure fgInitPrin1KeyPure nextActiveState
    dsimp only
    simp only [hSimEq]
    cases hAny : stA.st1.sim.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, bind_assoc,
        pure_bind, fromStaticSt1_upd_sim]
      have hHstAny : hst.base.principals.any (fun (idx, _) => idx == u.val) = false :=
        hAnyEq.symm.trans hAny
      have hTgtEq : (stA.st1.sim.base.principals.length == pOrd) =
          (u.val == stepPrinSlot pOrd (.initPrin u) hst) := by
        rw [hLenEq]
        unfold stepPrinSlot
        simp only [hHstAny, Bool.not_false, Bool.true_and]
        by_cases hLt : pOrd < hst.base.principals.length
        · simp only [hLt, ↓reduceIte]
          have hNeLen : (hst.base.principals.length == pOrd) = false :=
            beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
          rcases prinSlotAtOrd_mem_of_lt hst.base pOrd hLt with ⟨⟨idx0, e0⟩, hMem0, hEq0⟩
          have hNe2 : (u.val == prinSlotAtOrd S hst.base pOrd) = false := by
            cases hE : (u.val == prinSlotAtOrd S hst.base pOrd)
            · rfl
            · exfalso
              have hT : hst.base.principals.any (fun (idx, _) => idx == u.val) = true :=
                List.any_eq_true.mpr ⟨(idx0, e0), hMem0,
                  beq_iff_eq.mpr (hEq0.trans (beq_iff_eq.mp hE).symm)⟩
              rw [hHstAny] at hT; cases hT
          rw [hNeLen, hNe2]
        · simp only [hLt, ↓reduceIte]
          cases (hst.base.principals.length == pOrd)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact (beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)).symm
          · simp
      simp only [hTgtEq]
    · simp [fromStaticSt1_toStaticSt1]
  | genSPK u j =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh1 fgKeyInd1KeyStepPure nextActiveState
    dsimp only
    refine fgGenSPK1KeyActivePure_dh1_eq b P uSk ddh (stepPrinSlot pOrd (.genSPK u j) hst)
      spkOrd maxLen U V V u j hst stA hOrd hSpkKeys ?_ hBud
    rw [hRes]; unfold stepPrinSlot
    by_cases hLt : pOrd < hst.base.principals.length
    · simp only [hLt, ↓reduceIte, optNatMatches]
    · simp only [hLt, ↓reduceIte, optNatMatches]
      exact (beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)).symm
  | genOPK u j o =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh1 fgGenOPKActivePure
      fgKeyInd1KeyStepPure fgKeyIndStepPure nextActiveState
    dsimp only
    simp only [hSimEq, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind,
      fromStaticSt1_upd_sim]
    cases stA.st1.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) <;> simp
  | initiateOPK u i bundle =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh1 fgKeyInd1KeyStepPure
    dsimp only
    simp only [hSimEq, bind_assoc, pure_bind, fromStaticSt1_upd_sim]
    exact fgInitiateActivePure_opk_eq P ddh true pOrd (b.q_total + 1)
      (stepPrinSlot pOrd (.initiateOPK u i bundle) hst)
      (stepSpkSlot spkOrd (.initiateOPK u i bundle) hst) maxLen U V u i bundle stA (fun _ => rfl)
  | initiateNoOPK u i bundle =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh1 fgKeyInd1KeyStepPure
    dsimp only
    simp only [hSimEq, bind_assoc, pure_bind, fromStaticSt1_upd_sim]
    exact fgInitiateActivePure_noopk_eq P ddh true pOrd (b.q_total + 1)
      (stepPrinSlot pOrd (.initiateNoOPK u i bundle) hst)
      (stepSpkSlot spkOrd (.initiateNoOPK u i bundle) hst) maxLen U V u i bundle stA (fun _ => rfl)
  | acceptOPK k j o hdr =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh1 fgKeyInd1KeyStepPure fgKeyIndStepPure
      nextActiveState
    simp [hSimEq, fromStaticSt1_upd_sim]
  | _ =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh1 fgKeyInd1KeyStepPure fgKeyIndStepPure
      nextActiveState
    simp [hSimEq, fromStaticSt1_upd_sim]

private theorem active_isTargetEph_opk_eq {S : Setup} (sOrd spkOrd : Nat) (V : Bytes)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput)
    (hst : KeyIndFgCutoffState S) (hOrd : ValidOrdInv spkOrd V hst)
    (hAny : hst.base.sessions.any (fun e => e.sid == .sendOPK u i) = false) :
    (hst.base.sessions.length == sOrd) =
      (initSessionSlotIdx (.sendOPK u i) == stepSessSlot sOrd (.initiateOPK u i bundle) hst) := by
  unfold stepSessSlot
  simp only [hAny, Bool.not_false, Bool.true_and]
  by_cases hLt : sOrd < hst.base.sessions.length
  · simp only [hLt, ↓reduceIte]
    have hNeLen : (hst.base.sessions.length == sOrd) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
    rcases sessSlotAtOrd_mem_of_lt hst.base sOrd hLt with ⟨s0, hs0Mem, hs0Eq⟩
    have hNe2 : (initSessionSlotIdx (.sendOPK u i) == sessSlotAtOrd S hst.base sOrd) = false := by
      cases hE : (initSessionSlotIdx (.sendOPK u i) == sessSlotAtOrd S hst.base sOrd)
      · rfl
      · exfalso
        have hSidEq := initSessionSlotIdx_inj_of_lt
          ((beq_iff_eq.mp hE).trans hs0Eq.symm) (hOrd.2.2.1 s0 hs0Mem)
        have hT : hst.base.sessions.any (fun e => e.sid == .sendOPK u i) = true :=
          List.any_eq_true.mpr ⟨s0, hs0Mem, beq_iff_eq.mpr hSidEq.symm⟩
        rw [hAny] at hT; cases hT
    rw [hNeLen, hNe2]
  · simp only [hLt, ↓reduceIte]
    cases (hst.base.sessions.length == sOrd)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hSidLt : initSessionSlotIdx (.sendOPK u i) < S.N_send_tot :=
        Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _)
      exact (beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hSidLt)).symm
    · simp

private theorem active_isTargetEph_noopk_eq {S : Setup} (sOrd spkOrd : Nat) (V : Bytes)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
    (hst : KeyIndFgCutoffState S) (hOrd : ValidOrdInv spkOrd V hst)
    (hAny : hst.base.sessions.any (fun e => e.sid == .sendNoOPK u i) = false) :
    (hst.base.sessions.length == sOrd) =
      (initSessionSlotIdx (.sendNoOPK u i) ==
        stepSessSlot sOrd (.initiateNoOPK u i bundle) hst) := by
  unfold stepSessSlot
  simp only [hAny, Bool.not_false, Bool.true_and]
  by_cases hLt : sOrd < hst.base.sessions.length
  · simp only [hLt, ↓reduceIte]
    have hNeLen : (hst.base.sessions.length == sOrd) = false :=
      beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)
    rcases sessSlotAtOrd_mem_of_lt hst.base sOrd hLt with ⟨s0, hs0Mem, hs0Eq⟩
    have hNe2 :
        (initSessionSlotIdx (.sendNoOPK u i) == sessSlotAtOrd S hst.base sOrd) = false := by
      cases hE : (initSessionSlotIdx (.sendNoOPK u i) == sessSlotAtOrd S hst.base sOrd)
      · rfl
      · exfalso
        have hSidEq := initSessionSlotIdx_inj_of_lt
          ((beq_iff_eq.mp hE).trans hs0Eq.symm) (hOrd.2.2.1 s0 hs0Mem)
        have hT : hst.base.sessions.any (fun e => e.sid == .sendNoOPK u i) = true :=
          List.any_eq_true.mpr ⟨s0, hs0Mem, beq_iff_eq.mpr hSidEq.symm⟩
        rw [hAny] at hT; cases hT
    rw [hNeLen, hNe2]
  · simp only [hLt, ↓reduceIte]
    cases (hst.base.sessions.length == sOrd)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (initSessionSlotIdx_sendNoOPK_lt u i))).symm
    · simp

private theorem fgKeyInd1KeyActiveStepPure_dh3_eq {S : Setup} (b : QueryBudget)
    (P : Primitives) (uSk vSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (sOrd spkOrd maxLen : Nat) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hOrd : ValidOrdInv spkOrd (P.x25519Base vSk) hst)
    (hSpkKeys : stA.st1.sim.base.spkBundles.map Prod.fst = hst.base.spkBundles.map Prod.fst)
    (hSessSids : stA.st1.sim.base.sessions.map KeyIndInitiatorEntry.sid =
      hst.base.sessions.map KeyIndInitiatorEntry.sid)
    (hRes : stA.resolvedPrin? = none) :
    let U := P.x25519Base uSk
    let V := P.x25519Base vSk
    fgKeyInd1KeyActiveStepPure (activeParamsDh3 b U V sOrd spkOrd) P uSk ddh S maxLen q stA =
      (fgKeyInd1KeyStepPure P uSk ddh false (stepSessSlot sOrd q hst) (stepSpkSlot spkOrd q hst)
          S maxLen U V q stA.st1 >>=
        fun p => pure (p.1, nextActiveState false sOrd q stA p.2)) := by
  intro U V
  cases q with
  | initPrin u =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh3 fgInitPrin1KeyActivePure
      fgKeyInd1KeyStepPure fgInitPrin1KeyPure nextActiveState
    dsimp only
    cases stA.st1.sim.base.principals.any (fun (idx, _) => idx == u.val) <;> simp
  | genSPK u j =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh3 fgKeyInd1KeyStepPure nextActiveState
    dsimp only
    exact fgGenSPK1KeyActivePure_eq P uSk ddh false (stepSessSlot sOrd (.genSPK u j) hst)
      spkOrd maxLen U V V u j hst stA hOrd hSpkKeys (by simp [hRes, optNatMatches])
  | genOPK u j o =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh3 fgGenOPKActivePure
      fgKeyInd1KeyStepPure fgKeyIndStepPure nextActiveState
    dsimp only
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
    cases stA.st1.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) <;> simp
  | initiateOPK u i bundle =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh3 fgKeyInd1KeyStepPure
    dsimp only
    rw [bind_assoc]
    simp only [pure_bind]
    refine fgInitiateActivePure_opk_eq P ddh false sOrd sOrd
      (stepSessSlot sOrd (.initiateOPK u i bundle) hst)
      (stepSpkSlot spkOrd (.initiateOPK u i bundle) hst) maxLen U V u i bundle stA (fun hAny => ?_)
    have hAnyEq := any_sid_eq_of_map_sid_eq (.sendOPK u i) hSessSids
    have hLenEq : stA.st1.sim.base.sessions.length = hst.base.sessions.length := by
      have := congrArg List.length hSessSids; simpa using this
    simp only [Bool.not_false, Bool.true_and, hLenEq]
    exact active_isTargetEph_opk_eq sOrd spkOrd V u i bundle hst hOrd (hAnyEq.symm.trans hAny)
  | initiateNoOPK u i bundle =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh3 fgKeyInd1KeyStepPure
    dsimp only
    rw [bind_assoc]
    simp only [pure_bind]
    refine fgInitiateActivePure_noopk_eq P ddh false sOrd sOrd
      (stepSessSlot sOrd (.initiateNoOPK u i bundle) hst)
      (stepSpkSlot spkOrd (.initiateNoOPK u i bundle) hst) maxLen U V u i bundle stA
      (fun hAny => ?_)
    have hAnyEq := any_sid_eq_of_map_sid_eq (.sendNoOPK u i) hSessSids
    have hLenEq : stA.st1.sim.base.sessions.length = hst.base.sessions.length := by
      have := congrArg List.length hSessSids; simpa using this
    simp only [Bool.not_false, Bool.true_and, hLenEq]
    exact active_isTargetEph_noopk_eq sOrd spkOrd V u i bundle hst hOrd (hAnyEq.symm.trans hAny)
  | acceptOPK k j o hdr =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh3 fgKeyInd1KeyStepPure fgKeyIndStepPure
      nextActiveState
    simp
  | _ =>
    unfold fgKeyInd1KeyActiveStepPure activeParamsDh3 fgKeyInd1KeyStepPure fgKeyIndStepPure
      nextActiveState
    simp

private def FgActiveRelDh1 (S : Setup) (b : QueryBudget) (P : Primitives)
    (R : FgSlotReps P) (pOrd spkOrd : Nat) (uSk vSk : Bytes)
    (rem : Nat) (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S) : Prop :=
  FgSimInvDh1_1Key S b P R (prinSlotAtOrd S hst.base pOrd) (spkSlotAtOrd S hst.base spkOrd)
    uSk vSk rem hst (toStaticSt1 S b stA.st1) ∧
  stA.resolvedPrin? =
    (if pOrd < hst.base.principals.length then some (prinSlotAtOrd S hst.base pOrd) else none) ∧
  hst.base.spkBundles.length + rem ≤ b.q_total

private def FgActiveRelDh3 (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sOrd spkOrd : Nat)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : Nat) (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S) : Prop :=
  FgSimInvDh3_1Key S b P hP (sessSlotAtOrd S hst.base sOrd) (spkSlotAtOrd S hst.base spkOrd)
    uSk vSk huSk hvSk rem hst stA.st1 ∧
  stA.resolvedPrin? = none

private theorem fgStepCoupling_dh1Ord_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (pOrd spkOrd : Nat)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : Nat)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hOrd : ValidOrdInv spkOrd (P.x25519Base vSk) hst)
    (hDead : deadDh1Full (prinSlotAtOrd S hst.base pOrd) (spkSlotAtOrd S hst.base spkOrd) hst =
      false)
    (hRel : FgActiveRelDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk)
      pOrd spkOrd uSk vSk (rem + 1) hst stA)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeyActiveSimState S → ProbComp Bool)
    (hCont : ∀ r hst' stA',
      ValidOrdInv spkOrd (P.x25519Base vSk) hst' →
      deadDh1Full (prinSlotAtOrd S hst'.base pOrd) (spkSlotAtOrd S hst'.base spkOrd) hst' =
        false →
      FgActiveRelDh1 S b P (FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk)
        pOrd spkOrd uSk vSk rem hst' stA' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, stA')] {true})
    (hDeadCont : ∀ r hst',
      ValidOrdInv spkOrd (P.x25519Base vSk) hst' →
      deadDh1Full (prinSlotAtOrd S hst'.base pOrd) (spkSlotAtOrd S hst'.base spkOrd) hst' =
        true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) (some vSk) S P q).run hst >>=
        k1] {true} ≤
      𝒟[(fgKeyInd1KeyActiveSimImpl
            (activeParamsDh1 b (P.x25519Base uSk) (P.x25519Base vSk) pOrd spkOrd)
            P uSk P.isValidDhTriple S b.q_total q).run stA >>= k2] {true} := by
  let R := FgSlotReps.ofDh1 P hP uSk vSk huSk hvSk
  rcases hRel with ⟨hRelInv, hRelRes, hRelLen⟩
  have hBud := activeSigSlack_or_pos_of_inv b P R _ _ uSk vSk rem hst stA hRelInv hRelLen
  rcases fgSimInvDh1_1Key_maps hRelInv with ⟨hPrinKeys, hSpkKeys, _⟩
  have huPre := stepPrinSlot_retarget_pre pOrd spkOrd (P.x25519Base vSk) q hst hOrd
  have hbPre := stepSpkSlot_retarget_pre spkOrd (P.x25519Base vSk) q hst hOrd
  have hDeadStep : deadDh1Full (stepPrinSlot pOrd q hst) (stepSpkSlot spkOrd q hst) hst = false :=
    (deadDh1Full_retarget _ _ _ _ hst (huPre.imp id And.left) hbPre).symm.trans hDead
  have hInvStep : FgSimInvDh1_1Key S b P R (stepPrinSlot pOrd q hst) (stepSpkSlot spkOrd q hst)
      uSk vSk (rem + 1) hst (toStaticSt1 S b stA.st1) :=
    fgSimInvDh1_1Key_retarget b P R _ _ _ _ uSk vSk (rem + 1) hst (toStaticSt1 S b stA.st1)
      huPre hbPre hRelInv
  let m1 := (pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) (some vSk) S P q).run hst
  let k1' : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool :=
    open scoped Classical in fun p => if p ∈ support m1 then k1 p else pure false
  have hLhsEq : 𝒟[m1 >>= k1] = 𝒟[m1 >>= k1'] :=
    OracleComp.evalDist_bind_congr_of_support _ _ _ (fun p hp => by simp only [k1', hp, ↓reduceIte])
  change 𝒟[m1 >>= k1] {true} ≤ _
  rw [hLhsEq]
  have hm1Eq : m1 = (pqxdhKeyIndFgPreImpl1Key true (stepPrinSlot pOrd q hst)
      (stepSpkSlot spkOrd q hst) (some uSk) (some vSk) S P q).run hst :=
    pqxdhKeyIndFgOrdPreImpl1Key_run_dh1_eq pOrd spkOrd uSk vSk P q hst hOrd
  have hRhsEq :
      ((fgKeyInd1KeyActiveSimImpl
          (activeParamsDh1 b (P.x25519Base uSk) (P.x25519Base vSk) pOrd spkOrd)
          P uSk P.isValidDhTriple S b.q_total q).run stA >>= k2) =
      ((fgKeyInd1KeySimImpl P uSk P.isValidDhTriple true (stepPrinSlot pOrd q hst)
          (stepSpkSlot spkOrd q hst) S b.q_total (P.x25519Base uSk) (P.x25519Base vSk) q).run
          (toStaticSt1 S b stA.st1) >>=
        fun p => k2 (p.1, nextActiveState true pOrd q stA (fromStaticSt1 S b p.2))) := by
    unfold fgKeyInd1KeyActiveSimImpl fgKeyInd1KeySimImpl
    simp only [StateT_run_mk,
      fgKeyInd1KeyActiveStepPure_dh1_eq b P uSk vSk P.isValidDhTriple pOrd spkOrd b.q_total q
        hst stA hOrd hPrinKeys hSpkKeys hRelRes hBud,
      bind_assoc, pure_bind]
  rw [hm1Eq, hRhsEq]
  exact fgStepCoupling_dh1_1Key S b P hP (stepPrinSlot pOrd q hst) (stepSpkSlot spkOrd q hst)
    uSk vSk huSk hvSk q rem hst (toStaticSt1 S b stA.st1) hDeadStep hInvStep k1'
    (fun p => k2 (p.1, nextActiveState true pOrd q stA (fromStaticSt1 S b p.2)))
    (fun r hst' st1' hDF' hInv' => by
      by_cases hx : (r, hst') ∈ support m1
      · simp only [k1', hx, ↓reduceIte]
        have hOrd' := pqxdhKeyIndFgOrdPreImpl1Key_preserves_validOrdInv true pOrd spkOrd uSk vSk
          P q hst hOrd (r, hst') hx
        have hStepLen := pqxdhKeyIndFgOrdPreImpl1Key_spkBundles_step true pOrd spkOrd
          (some uSk) (some vSk) P q hst (r, hst') hx
        have hLen' : hst'.base.spkBundles.length + rem ≤ b.q_total := by
          dsimp only at hStepLen; omega
        rcases stepPrinSlot_eq_post pOrd spkOrd uSk vSk P q hst stA (fromStaticSt1 S b st1')
          hPrinKeys hRelRes (r, hst') hx with ⟨huPost, hResPost⟩
        have hbPost := stepSpkSlot_retarget_post true pOrd spkOrd uSk vSk P q hst hOrd (r, hst') hx
        have hDeadOrd' :
            deadDh1Full (prinSlotAtOrd S hst'.base pOrd) (spkSlotAtOrd S hst'.base spkOrd) hst' =
              false :=
          (deadDh1Full_retarget _ _ _ _ hst' (Or.inl huPost) hbPost).symm.trans hDF'
        have hInvOrd' := fgSimInvDh1_1Key_retarget b P R _ _ _ _ uSk vSk rem hst' st1'
          (Or.inl huPost) hbPost hInv'
        have hSlackLe := activeSigSlack_le_of_inv b P R _ _ uSk vSk rem hst' st1' hInvOrd' hLen'
        have hRound := toStaticSt1_fromStaticSt1_of_le S b st1' hSlackLe
        exact hCont r hst' (nextActiveState true pOrd q stA (fromStaticSt1 S b st1'))
          hOrd' hDeadOrd'
          ⟨by simpa only [nextActiveState_st1, hRound] using hInvOrd', hResPost, hLen'⟩
      · simp [k1', hx])
    (fun r hst' hDT' => by
      by_cases hx : (r, hst') ∈ support m1
      · simp only [k1', hx, ↓reduceIte]
        have hOrd' := pqxdhKeyIndFgOrdPreImpl1Key_preserves_validOrdInv true pOrd spkOrd uSk vSk
          P q hst hOrd (r, hst') hx
        have huPost := (stepPrinSlot_eq_post pOrd spkOrd uSk vSk P q hst stA stA.st1 hPrinKeys
          hRelRes (r, hst') hx).1
        have hbPost := stepSpkSlot_retarget_post true pOrd spkOrd uSk vSk P q hst hOrd (r, hst') hx
        have hDeadOrd' :
            deadDh1Full (prinSlotAtOrd S hst'.base pOrd) (spkSlotAtOrd S hst'.base spkOrd) hst' =
              true :=
          (deadDh1Full_retarget _ _ _ _ hst' (Or.inl huPost) hbPost).symm.trans hDT'
        exact hDeadCont r hst' hOrd' hDeadOrd'
      · simp [k1', hx])

private theorem fgStepCoupling_dh3Ord_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sOrd spkOrd : Nat)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (q : KeyIndQuery S) (rem : Nat)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hOrd : ValidOrdInv spkOrd (P.x25519Base vSk) hst)
    (hDead : deadDh3Full P (sessSlotAtOrd S hst.base sOrd) (spkSlotAtOrd S hst.base spkOrd)
      (P.x25519Base vSk) hst = false)
    (hRel : FgActiveRelDh3 S b P hP sOrd spkOrd uSk vSk huSk hvSk (rem + 1) hst stA)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeyActiveSimState S → ProbComp Bool)
    (hCont : ∀ r hst' stA',
      ValidOrdInv spkOrd (P.x25519Base vSk) hst' →
      deadDh3Full P (sessSlotAtOrd S hst'.base sOrd) (spkSlotAtOrd S hst'.base spkOrd)
        (P.x25519Base vSk) hst' = false →
      FgActiveRelDh3 S b P hP sOrd spkOrd uSk vSk huSk hvSk rem hst' stA' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, stA')] {true})
    (hDeadCont : ∀ r hst',
      ValidOrdInv spkOrd (P.x25519Base vSk) hst' →
      deadDh3Full P (sessSlotAtOrd S hst'.base sOrd) (spkSlotAtOrd S hst'.base spkOrd)
        (P.x25519Base vSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd (some uSk) (some vSk) S P q).run hst >>=
        k1] {true} ≤
      𝒟[(fgKeyInd1KeyActiveSimImpl
            (activeParamsDh3 b (P.x25519Base uSk) (P.x25519Base vSk) sOrd spkOrd)
            P uSk P.isValidDhTriple S b.q_total q).run stA >>= k2] {true} := by
  rcases fgSimInvDh3_1Key_maps hRel.1 with ⟨_, hSpkKeys, hSessSids, _⟩
  have hsPre := stepSessSlot_retarget_pre sOrd spkOrd (P.x25519Base vSk) q hst hOrd
  have hbPre := stepSpkSlot_retarget_pre spkOrd (P.x25519Base vSk) q hst hOrd
  have hDeadStep :
      deadDh3Full P (stepSessSlot sOrd q hst) (stepSpkSlot spkOrd q hst) (P.x25519Base vSk) hst =
        false :=
    (deadDh3Full_retarget P _ _ _ _ (P.x25519Base vSk) hst hsPre hbPre).symm.trans hDead
  have hInvStep : FgSimInvDh3_1Key S b P hP (stepSessSlot sOrd q hst) (stepSpkSlot spkOrd q hst)
      uSk vSk huSk hvSk (rem + 1) hst stA.st1 :=
    fgSimInvDh3_1Key_retarget b P hP _ _ _ _ uSk vSk huSk hvSk (rem + 1) hst stA.st1 hsPre hbPre
      hRel.1
  let m1 := (pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd (some uSk) (some vSk) S P q).run hst
  let k1' : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool :=
    open scoped Classical in fun p => if p ∈ support m1 then k1 p else pure false
  have hLhsEq : 𝒟[m1 >>= k1] = 𝒟[m1 >>= k1'] :=
    OracleComp.evalDist_bind_congr_of_support _ _ _ (fun p hp => by simp only [k1', hp, ↓reduceIte])
  change 𝒟[m1 >>= k1] {true} ≤ _
  rw [hLhsEq]
  have hm1Eq : m1 = (pqxdhKeyIndFgPreImpl1Key false (stepSessSlot sOrd q hst)
      (stepSpkSlot spkOrd q hst) (some uSk) (some vSk) S P q).run hst :=
    pqxdhKeyIndFgOrdPreImpl1Key_run_dh3_eq sOrd spkOrd uSk vSk P q hst hOrd
  have hRhsEq :
      ((fgKeyInd1KeyActiveSimImpl
          (activeParamsDh3 b (P.x25519Base uSk) (P.x25519Base vSk) sOrd spkOrd)
          P uSk P.isValidDhTriple S b.q_total q).run stA >>= k2) =
      ((fgKeyInd1KeySimImpl P uSk P.isValidDhTriple false (stepSessSlot sOrd q hst)
          (stepSpkSlot spkOrd q hst) S b.q_total (P.x25519Base uSk) (P.x25519Base vSk) q).run
          stA.st1 >>= fun p => k2 (p.1, nextActiveState false sOrd q stA p.2)) := by
    unfold fgKeyInd1KeyActiveSimImpl fgKeyInd1KeySimImpl
    simp only [StateT_run_mk,
      fgKeyInd1KeyActiveStepPure_dh3_eq b P uSk vSk P.isValidDhTriple sOrd spkOrd b.q_total q
        hst stA hOrd hSpkKeys hSessSids hRel.2,
      bind_assoc, pure_bind]
  rw [hm1Eq, hRhsEq]
  exact fgStepCoupling_dh3_1Key S b P hP (stepSessSlot sOrd q hst) (stepSpkSlot spkOrd q hst)
    uSk vSk huSk hvSk q rem hst stA.st1 hDeadStep hInvStep k1'
    (fun p => k2 (p.1, nextActiveState false sOrd q stA p.2))
    (fun r hst' st1' hDF' hInv' => by
      by_cases hx : (r, hst') ∈ support m1
      · simp only [k1', hx, ↓reduceIte]
        have hOrd' := pqxdhKeyIndFgOrdPreImpl1Key_preserves_validOrdInv false sOrd spkOrd uSk vSk
          P q hst hOrd (r, hst') hx
        have hsPost := stepSessSlot_retarget_post sOrd spkOrd uSk vSk P q hst hOrd (r, hst') hx
        have hbPost := stepSpkSlot_retarget_post false sOrd spkOrd uSk vSk P q hst hOrd (r, hst') hx
        have hDeadOrd' :
            deadDh3Full P (sessSlotAtOrd S hst'.base sOrd) (spkSlotAtOrd S hst'.base spkOrd)
              (P.x25519Base vSk) hst' = false :=
          (deadDh3Full_retarget P _ _ _ _ (P.x25519Base vSk) hst' hsPost hbPost).symm.trans hDF'
        have hInvOrd' := fgSimInvDh3_1Key_retarget b P hP _ _ _ _ uSk vSk huSk hvSk rem hst' st1'
          hsPost hbPost hInv'
        exact hCont r hst' (nextActiveState false sOrd q stA st1') hOrd' hDeadOrd'
          ⟨by simpa only [nextActiveState_st1] using hInvOrd',
           (nextActiveState_false_resolvedPrin sOrd q stA st1').trans hRel.2⟩
      · simp [k1', hx])
    (fun r hst' hDT' => by
      by_cases hx : (r, hst') ∈ support m1
      · simp only [k1', hx, ↓reduceIte]
        have hOrd' := pqxdhKeyIndFgOrdPreImpl1Key_preserves_validOrdInv false sOrd spkOrd uSk vSk
          P q hst hOrd (r, hst') hx
        have hsPost := stepSessSlot_retarget_post sOrd spkOrd uSk vSk P q hst hOrd (r, hst') hx
        have hbPost := stepSpkSlot_retarget_post false sOrd spkOrd uSk vSk P q hst hOrd (r, hst') hx
        have hDeadOrd' :
            deadDh3Full P (sessSlotAtOrd S hst'.base sOrd) (spkSlotAtOrd S hst'.base spkOrd)
              (P.x25519Base vSk) hst' = true :=
          (deadDh3Full_retarget P _ _ _ _ (P.x25519Base vSk) hst' hsPost hbPost).symm.trans hDT'
        exact hDeadCont r hst' hOrd' hDeadOrd'
      · simp [k1', hx])

/-- Creation-order per-ordinal `GapDhWithSign` bound for Leg `DH1` (`IK_A` at `pOrd`,
    `SPK_B` at `spkOrd`) against `fgKeyInd1KeyGapDhActiveAdvAt true pOrd spkOrd S b A`. -/
theorem prob_badKeyIndFgDh1OrdAt_1Key_le_gapDhWithSign_active
    (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b)
    (pOrd : Nat) (_hpOrd : pOrd < activeIdCount S b.q_on)
    (spkOrd : Nat) (_hspkOrd : spkOrd < activeSpkCount S b.q_on) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog)]
        {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAt true pOrd spkOrd S b A) := by
  unfold GapDhWithSignReal GapDhWithSign
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh1 pOrd spkOrd P A.1
    (fun x => pure (badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.2.base x.2.2.advRoLog))]
  rw [gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  simp only [↓reduceIte]
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    A.2.2.2.2.1
  let R := FgSlotReps.ofDh1 P hP uSk vSk huLen hvLen
  exact evalDist_simulateQ_le_of_step_or_dead_inv
    (ValidOrdInv spkOrd (P.x25519Base vSk))
    (fun s1 => deadDh1Full (prinSlotAtOrd S s1.base pOrd) (spkSlotAtOrd S s1.base spkOrd) s1)
    (FgActiveRelDh1 S b P R pOrd spkOrd uSk vSk)
    (pqxdhKeyIndFgOrdPreImpl1Key true pOrd spkOrd (some uSk) (some vSk) S P)
    (fgKeyInd1KeyActiveSimImpl
      (activeParamsDh1 b (P.x25519Base uSk) (P.x25519Base vSk) pOrd spkOrd)
      P uSk P.isValidDhTriple S b.q_total)
    (fun q s1 hI x hx =>
      pqxdhKeyIndFgOrdPreImpl1Key_preserves_validOrdInv true pOrd spkOrd uSk vSk P q s1 hI x hx)
    (fun q s1 hI hD x hx =>
      pqxdhKeyIndFgOrdPreImpl1Key_preserves_deadDh1Ord pOrd spkOrd uSk vSk P q s1 hI hD x hx)
    (fun q rem s1 s2 hI hDF hRel k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh1Ord_1Key S b P hP pOrd spkOrd uSk vSk huLen hvLen q rem s1 s2 hI hDF hRel
        k1 k2 hCont hDeadCont)
    (fun x => pure (badKeyIndFgDh1OrdAt P b.q_ro pOrd spkOrd x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (fgKeyInd1KeyActiveFinishPure
        (activeParamsDh1 b (P.x25519Base uSk) (P.x25519Base vSk) pOrd spkOrd)
        S P P.isValidDhTriple b.q_total x.2) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun _ s1 _ hD => by
      unfold badKeyIndFgDh1OrdAt
      simp [badKeyIndFgDh1At_eq_false_of_deadDh1Full P b.q_ro _ _ s1 hD])
    (fun a rem s1 s2 _ hDF hRel => by
      unfold badKeyIndFgDh1OrdAt fgKeyInd1KeyActiveFinishPure activeParamsDh1
      dsimp only [↓reduceIte]
      exact fgSimInvDh1_1Key_terminal_le S b P hP R b.q_ro
        (prinSlotAtOrd S s1.base pOrd) (spkSlotAtOrd S s1.base spkOrd)
        uSk vSk a rem s1 (toStaticSt1 S b s2.st1) hDF hRel.1)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyInd1KeyActiveSimState.empty S b secb)
    (validOrdInv_empty spkOrd (P.x25519Base vSk) secb)
    ⟨by rw [toStaticSt1_empty]; exact fgSimInvDh1_1Key_empty S b P R _ _ uSk vSk secb,
     by simp [KeyIndFgCutoffState.empty, FgKeyInd1KeyActiveSimState.empty, KeyIndState.empty],
     by simp [KeyIndFgCutoffState.empty, KeyIndState.empty]⟩

/-- Creation-order per-ordinal `GapDhWithSign` bound for Leg `DH3` (`EK_A` at `sOrd`,
    `SPK_B` at `spkOrd`) against `fgKeyInd1KeyGapDhActiveAdvAt false sOrd spkOrd S b A`. -/
theorem prob_badKeyIndFgDh3OrdAt_1Key_le_gapDhWithSign_active
    (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (A : BoundedAdv (KeyIndAdversary S) b)
    (sOrd : Nat) (_hsOrd : sOrd < activeSendCount S b.q_on)
    (spkOrd : Nat) (_hspkOrd : spkOrd < activeSpkCount S b.q_on) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog)]
        {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAt false sOrd spkOrd S b A) := by
  unfold GapDhWithSignReal GapDhWithSign
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh3 sOrd spkOrd P A.1
    (fun x => pure (badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.2.base x.2.2.advRoLog))]
  rw [gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdvAt_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun uSk huSk => ?_)
  have huLen : uSk.length = 32 := length_of_mem_support_sampleScalar32 huSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun vSk hvSk => ?_)
  have hvLen : vSk.length = 32 := length_of_mem_support_sampleScalar32 hvSk
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hQb : IsQueryBoundP A.1.run (fun q : ℕ ⊕ KeyIndQuery S => isGameQuery q = true) b.q_total :=
    A.2.2.2.2.1
  exact evalDist_simulateQ_le_of_step_or_dead_inv
    (ValidOrdInv spkOrd (P.x25519Base vSk))
    (fun s1 => deadDh3Full P (sessSlotAtOrd S s1.base sOrd) (spkSlotAtOrd S s1.base spkOrd)
      (P.x25519Base vSk) s1)
    (FgActiveRelDh3 S b P hP sOrd spkOrd uSk vSk huLen hvLen)
    (pqxdhKeyIndFgOrdPreImpl1Key false sOrd spkOrd (some uSk) (some vSk) S P)
    (fgKeyInd1KeyActiveSimImpl
      (activeParamsDh3 b (P.x25519Base uSk) (P.x25519Base vSk) sOrd spkOrd)
      P uSk P.isValidDhTriple S b.q_total)
    (fun q s1 hI x hx =>
      pqxdhKeyIndFgOrdPreImpl1Key_preserves_validOrdInv false sOrd spkOrd uSk vSk P q s1 hI x hx)
    (fun q s1 hI hD x hx =>
      pqxdhKeyIndFgOrdPreImpl1Key_preserves_deadDh3Ord sOrd spkOrd uSk vSk P q s1 hI hD x hx)
    (fun q rem s1 s2 hI hDF hRel k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh3Ord_1Key S b P hP sOrd spkOrd uSk vSk huLen hvLen q rem s1 s2 hI hDF hRel
        k1 k2 hCont hDeadCont)
    (fun x => pure (badKeyIndFgDh3OrdAt P b.q_ro sOrd spkOrd x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (fgKeyInd1KeyActiveFinishPure
        (activeParamsDh3 b (P.x25519Base uSk) (P.x25519Base vSk) sOrd spkOrd)
        S P P.isValidDhTriple b.q_total x.2) ==
      P.pow8 (P.x25519 uSk (P.x25519Base vSk))))
    (fun _ s1 _ hD => by
      unfold badKeyIndFgDh3OrdAt
      simp [badKeyIndFgDh3At_eq_false_of_deadDh3Full P b.q_ro _ _ (P.x25519Base vSk) s1 hD])
    (fun a rem s1 s2 _ hDF hRel => by
      unfold badKeyIndFgDh3OrdAt fgKeyInd1KeyActiveFinishPure activeParamsDh3
        pureExtractCdhFromSimState
      dsimp only [Bool.false_eq_true, ↓reduceIte]
      exact fgSimInvDh3_terminal_le S b P hP b.q_ro
        (sessSlotAtOrd S s1.base sOrd) (spkSlotAtOrd S s1.base spkOrd)
        uSk vSk huLen hvLen a rem s1 s2.st1.sim hDF hRel.1)
    A.1.run b.q_total hQb
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyInd1KeyActiveSimState.empty S b secb)
    (validOrdInv_empty spkOrd (P.x25519Base vSk) secb)
    ⟨fgSimInvDh3_empty S b P hP _ _ uSk vSk huLen hvLen secb, rfl⟩

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhHop
