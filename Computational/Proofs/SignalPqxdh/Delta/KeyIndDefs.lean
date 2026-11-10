/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingF
public import Computational.Proofs.SignalPqxdh.Security.Reductions
import Computational.Proofs.SignalPqxdh.Security.FgGapDhCoupling
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# PQXDH Key Indistinguishability with Imperfect KEM Correctness: Hop Statements

Defines the KEM decapsulation failure event `hasBadKemCorrRecords` and the single-key experiment
`kemCorrExpProb` (DEV-PQ21), replacing perfect KEM correctness in partnered root-key agreement with
a third up-to-bad disjunct bounded by `N_spk_tot · N_send_tot · δ` per branch. States the modular
hop obligations for two-key `KeyInd` under `CryptoWellFormedPrimitivesδ` and assembles them into
`pqxdh_key_ind_withδ_of_hops`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-- Whether initiator record `i` and responder record `r` share a Kyber pre-key and ciphertext whose
    decapsulation under `r.pqspkSk` differs from `some i.kemSs`. -/
def isKemCorrPair {S : Setup} (P : Primitives)
    (i : _root_.Proofs.SignalPqxdh.Security.InitKemRecord S)
    (r : _root_.Proofs.SignalPqxdh.Security.RecvKemRecord) : Bool :=
  decide (r.pqspkPk = i.pqspkPk) && decide (r.kemCt = i.kemCt) &&
    decide (P.kemDecaps r.pqspkSk r.kemCt ≠ some i.kemSs)

/-- KEM correctness failure at flat index `idx = bIdx * N_send_tot + sIdx`. -/
def hasBadKemCorrRecordsAt (S : Setup) (P : Primitives) (idx : Nat)
    (initRecs : List (_root_.Proofs.SignalPqxdh.Security.InitKemRecord S))
    (recvRecs : List _root_.Proofs.SignalPqxdh.Security.RecvKemRecord) : Bool :=
  initRecs.any (fun i =>
    (i.sendIdx == idx % S.N_send_tot) &&
    recvRecs.any (fun r => (r.bIdx == idx / S.N_send_tot) && isKemCorrPair P i r))

def hasBadKemCorrRecords (S : Setup) (P : Primitives)
    (initRecs : List (_root_.Proofs.SignalPqxdh.Security.InitKemRecord S))
    (recvRecs : List _root_.Proofs.SignalPqxdh.Security.RecvKemRecord) : Bool :=
  (List.range (S.N_spk_tot * S.N_send_tot)).any (fun idx =>
    hasBadKemCorrRecordsAt S P idx initRecs recvRecs)

/-- Single-key KEM correctness experiment against public-key selector `choosePk`. -/
noncomputable def kemCorrExpProb (P : Primitives) (choosePk : Bytes → Bytes → ProbComp Bytes) :
    ProbComp Bool := do
  let (pk, sk) ← sampleKemKeyGen P
  let pk' ← choosePk pk sk
  let r ← sampleCoins32
  match P.kemEncaps pk' r with
  | none => return false
  | some (ss, ct) => return (decide (pk' = pk) && decide (P.kemDecaps sk ct ≠ some ss))

theorem kemCorrExpProb_le (P : Primitives) (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (choosePk : Bytes → Bytes → ProbComp Bytes) :
    (𝒟[kemCorrExpProb P choosePk] {true}).toReal ≤ δ := by
  refine le_trans ?_ hδ
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  unfold kemCorrExpProb sampleKemKeyGen
  simp only [bind_assoc, pure_bind]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun seed _ => ?_)
  rw [← OracleComp.evalDist_bind_const (choosePk (P.kemKeyGen seed).1 (P.kemKeyGen seed).2)
    (sampleCoins32 >>= fun r => pure (kemHonestExchangeFails P seed r))]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun pk' _ => ?_)
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ MeasurableSet.of_discrete
    (fun r _ => ?_)
  cases hEnc : P.kemEncaps pk' r with
  | none => simp
  | some p =>
    obtain ⟨ss, ct⟩ := p
    by_cases hpk : pk' = (P.kemKeyGen seed).1
    · subst hpk
      simp [kemHonestExchangeFails, hEnc]
    · simp [hpk]

/-- Two-key `G0 -> G3` hop bound under `CryptoWellFormedPrimitivesδ`. -/
def KIHopG0G3Stmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b),
      |KeyIndAdvantage S P A.1 - keyIndAdvG3 S P A.1| ≤
        (S.N_id : ℝ) * SigEufCma P (sigReductionKeyInd S b A) +
        ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
        (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd S b A) +
        ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256

/-- Two-key `GapDH` bound on `badKeyIndFgAny4` under `CryptoWellFormedPrimitivesδ`. -/
def KIGapDhStmt (S : Setup) : Prop :=
  ∀ (b : QueryBudget) (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (A : BoundedAdv (KeyIndAdversary S) b),
      (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
          pure (badKeyIndFgAny4 P b.q_ro x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
        ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
          (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
          (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
          GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdv4 S b A)

/-- State-level implication from `ValidTagState` and `lazyStop` to `badKeyIndFgAny4`,
    `isKeyIndG3Abort`, or `hasBadKemCorrRecords`. -/
def KIStopStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (maxLen : ℕ) (adv : KeyIndAdvCutoffState S),
      ValidTagState P maxLen adv →
      lazyStop adv = true →
      badKeyIndFgAny4 P maxLen adv.shCr.base adv.advRoLog = true ∨
      isKeyIndG3Abort P adv.shCr = true ∨
      hasBadKemCorrRecords S P adv.shCr.initKemRecs adv.shCr.recvKemRecs = true

/-- Up-to-bad `G3 -> G3.5` coupling bound including `hasBadKemCorrRecords`. -/
def KICouplingStmt (S : Setup) : Prop :=
  ∀ (P : Primitives) (maxLen : ℕ) (A : KeyIndAdversary S),
    (∀ (testReal : Bool),
      let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl false false testReal S P
      ∀ p ∈ support ((simulateQ full A.run).run (KeyIndLazyState.empty S)),
      lazyStop p.2.adv = true →
      badKeyIndFgAny4 P maxLen p.2.adv.shCr.base p.2.adv.advRoLog = true ∨
      isKeyIndG3Abort P p.2.adv.shCr = true ∨
      hasBadKemCorrRecords S P p.2.adv.shCr.initKemRecs p.2.adv.shCr.recvKemRecs = true) →
    keyIndAdvG3 S P A ≤
      2 * (𝒟[runKeyIndFgSim S P A >>= fun x =>
        pure (badKeyIndFgAny4 P maxLen x.2.2.base x.2.2.advRoLog)] {true}).toReal +
      2 * (𝒟[runKeyIndShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal

/-- Per-index reduction of `hasBadKemCorrRecordsAt` in `runKeyIndShCrSim` to `kemCorrExpProb`. -/
def KICorrAtStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (A : KeyIndAdversary S) (idx : ℕ), idx < S.N_spk_tot * S.N_send_tot →
      ∃ choosePk : Bytes → Bytes → ProbComp Bytes,
        (𝒟[runKeyIndShCrSim S P A >>= fun x =>
            pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)]
          {true}).toReal ≤
          (𝒟[kemCorrExpProb P choosePk] {true}).toReal

theorem prob_hasBadKemCorrRecords_le (S : Setup) (hAt : KICorrAtStmt S)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (A : KeyIndAdversary S) :
    (𝒟[runKeyIndShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
  have hU := _root_.SignalPqxdh.Security.toReal_any_range_le_sum (runKeyIndShCrSim S P A)
    (S.N_spk_tot * S.N_send_tot)
    (fun idx x => hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)
  refine le_trans hU ?_
  calc (∑ k ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        (𝒟[runKeyIndShCrSim S P A >>= fun x =>
          pure (hasBadKemCorrRecordsAt S P k x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal)
      ≤ ∑ _k ∈ Finset.range (S.N_spk_tot * S.N_send_tot), δ := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        obtain ⟨choosePk, hC⟩ := hAt P hP A k (Finset.mem_range.mp hk)
        exact le_trans hC (kemCorrExpProb_le P δ hδ choosePk)
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem x25519_comm_of_pow8_eqδ (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (a sk pk : Bytes) (hpow : P.pow8 pk = P.pow8 (P.x25519Base sk)) :
    P.x25519 a pk = P.x25519 sk (P.x25519Base a) := by
  rw [hP.x25519_pow8_congr a pk (P.x25519Base sk)
        (hP.pow8_base_len pk sk hpow) (hP.x25519Base_len sk) hpow,
      hP.toWellFormedPrimitivesδ.x25519_comm a sk]

/-- Partnered initiator and responder sessions derive equal root keys whenever
    `hasBadKemCorrRecords` is false. -/
theorem keyIndPartner_imp_drKeyReal_eqδ {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (hst : KeyIndShCrState S) (hKS : ValidKeyStores S P hst.base)
    (hSend : hst.sendCount ≤ S.N_send_tot)
    (hNoCorr : hasBadKemCorrRecords S P hst.initKemRecs hst.recvKemRecs = false)
    {s : KeyIndInitiatorEntry S} {r : KeyIndRespEntry S}
    (hs : ValidInitSession S P hst s) (hr : ValidRespSession S P hst r)
    (hPart : keyIndPartner P s r = true) :
    s.drKeyReal.rootKey = r.drKeyReal.rootKey := by
  rcases hKS with ⟨_, _, _, hPrins, hSpks, hOpks, _⟩
  rcases hs with ⟨_, _hekLen, hekPk, _, _, _, _, _, _, _, _,
    u, uEntry, kemCoins, ss_s, initRec, huMem, hsIkPk, _hEnc, hInitMem, hInitLt, _, hInitPk,
    hInitCt, hInitSs, hsKey⟩
  rcases hr with ⟨k, j, kEntry, bEntry, ss_r, recEntry, _, hkMem, hbMem, _,
    hrRespIk, hrSpk, hrPqspk, _, _, _, _, _, _, hDec, hRecMem, hRecIdx, hRecPk, hRecSk, hRecCt,
    _hRecSs, hrOpkCases⟩
  unfold keyIndPartner at hPart
  simp only [Bool.and_eq_true, beq_iff_eq] at hPart
  rcases hPart with ⟨⟨⟨⟨⟨⟨hPowIkA, hPowIkB⟩, hPowSpk⟩, hMapOpk⟩, hEkEq⟩, hPqEq⟩, hCtEq⟩
  have huIk := hPrins (u, uEntry) huMem
  have hkIk := hPrins (k.val, kEntry) hkMem
  have hbSpk := hSpks ((k.val, j.val), bEntry) hbMem
  rcases hbSpk with ⟨_hbSkLen, hbSpkPk, _, _⟩
  have hSsEq : ss_s = ss_r := by
    have hbLt := spkBundleFlatIdx_lt_tot S k j
    have hsLt : initRec.sendIdx < S.N_send_tot := Nat.lt_of_lt_of_le hInitLt hSend
    set bIdx := _root_.SignalPqxdh.Security.RoKem.spkBundleFlatIdx S k j with hbIdx
    have hIdxLt : bIdx * S.N_send_tot + initRec.sendIdx < S.N_spk_tot * S.N_send_tot := by
      calc bIdx * S.N_send_tot + initRec.sendIdx
          < bIdx * S.N_send_tot + S.N_send_tot := Nat.add_lt_add_left hsLt _
        _ = (bIdx + 1) * S.N_send_tot := by ring
        _ ≤ S.N_spk_tot * S.N_send_tot := Nat.mul_le_mul_right _ hbLt
    have hNpos : 0 < S.N_send_tot := Nat.lt_of_le_of_lt (Nat.zero_le _) hsLt
    have hDiv : (bIdx * S.N_send_tot + initRec.sendIdx) / S.N_send_tot = bIdx := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hNpos, Nat.div_eq_of_lt hsLt, Nat.zero_add]
    have hMod : (bIdx * S.N_send_tot + initRec.sendIdx) % S.N_send_tot = initRec.sendIdx := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsLt]
    unfold hasBadKemCorrRecords at hNoCorr
    rw [List.any_eq_false] at hNoCorr
    have hAt := hNoCorr (bIdx * S.N_send_tot + initRec.sendIdx) (List.mem_range.mpr hIdxLt)
    unfold hasBadKemCorrRecordsAt at hAt
    rw [hDiv, hMod] at hAt
    have hPair : isKemCorrPair P initRec recEntry = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      apply hAt
      refine List.any_eq_true.mpr ⟨initRec, hInitMem, ?_⟩
      simp only [beq_self_eq_true, Bool.true_and]
      exact List.any_eq_true.mpr ⟨recEntry, hRecMem, by simp [hRecIdx, hc]⟩
    have hPkEq : recEntry.pqspkPk = initRec.pqspkPk := by
      rw [hRecPk, hInitPk, hPqEq, hrPqspk]
    have hCtEq' : recEntry.kemCt = initRec.kemCt := by
      rw [hRecCt, hInitCt, hCtEq]
    unfold isKemCorrPair at hPair
    simp only [hPkEq, hCtEq', decide_true, Bool.true_and, decide_eq_false_iff_not,
      not_not] at hPair
    rw [hRecSk] at hPair
    rw [hInitCt, hCtEq, hDec, hInitSs] at hPair
    exact (Option.some.inj hPair).symm
  have hDh1 : P.x25519 uEntry.secIKA0 s.peerSpkPk = P.x25519 bEntry.spkSk r.hdr.ikAPk := by
    have hSpkPow : P.pow8 s.peerSpkPk = P.pow8 (P.x25519Base bEntry.spkSk) := by
      rw [hPowSpk, hrSpk, hbSpkPk]
    have hIkAPow : P.pow8 r.hdr.ikAPk = P.pow8 (P.x25519Base uEntry.secIKA0) := by
      rw [← hPowIkA, hsIkPk, huIk.2]
    rw [x25519_comm_of_pow8_eqδ P hP uEntry.secIKA0 bEntry.spkSk s.peerSpkPk hSpkPow]
    exact (hP.x25519_pow8_congr bEntry.spkSk r.hdr.ikAPk (P.x25519Base uEntry.secIKA0)
      (hP.pow8_base_len r.hdr.ikAPk uEntry.secIKA0 hIkAPow)
      (hP.x25519Base_len uEntry.secIKA0) hIkAPow).symm
  have hDh2 : P.x25519 s.ekASk s.peerIkPk = P.x25519 kEntry.secIKA0 r.hdr.ekAPk := by
    have hIkBPow : P.pow8 s.peerIkPk = P.pow8 (P.x25519Base kEntry.secIKA0) := by
      rw [hPowIkB, hrRespIk, hkIk.2]
    rw [x25519_comm_of_pow8_eqδ P hP s.ekASk kEntry.secIKA0 s.peerIkPk hIkBPow,
        ← hekPk, hEkEq]
  have hDh3 : P.x25519 s.ekASk s.peerSpkPk = P.x25519 bEntry.spkSk r.hdr.ekAPk := by
    have hSpkPow : P.pow8 s.peerSpkPk = P.pow8 (P.x25519Base bEntry.spkSk) := by
      rw [hPowSpk, hrSpk, hbSpkPk]
    rw [x25519_comm_of_pow8_eqδ P hP s.ekASk bEntry.spkSk s.peerSpkPk hSpkPow,
        ← hekPk, hEkEq]
  rcases hrOpkCases with ⟨hrOpkNone, _, hrKey⟩ | ⟨o, oEntry, hoMem, hrOpkSome, _, hrKey⟩
  · rw [hrOpkNone] at hMapOpk
    cases hsOpk : s.peerOpkPk? with
    | none =>
      rw [hsKey, hrKey, hsOpk, Option.map_none, hDh1, hDh2, hDh3, hSsEq]
    | some _ =>
      rw [hsOpk] at hMapOpk
      nomatch hMapOpk
  · rw [hrOpkSome] at hMapOpk
    cases hsOpk : s.peerOpkPk? with
    | none =>
      rw [hsOpk] at hMapOpk
      nomatch hMapOpk
    | some sOpkPk =>
      rw [hsOpk] at hMapOpk
      simp only [Option.map_some, Option.some.injEq] at hMapOpk
      have hoOpk := hOpks ((k.val, j.val, o), oEntry) hoMem
      have hOpkPow : P.pow8 sOpkPk = P.pow8 (P.x25519Base oEntry.opkSk) := by
        rw [hMapOpk, hoOpk.2]
      have hDh4 : P.x25519 s.ekASk sOpkPk = P.x25519 oEntry.opkSk r.hdr.ekAPk := by
        rw [x25519_comm_of_pow8_eqδ P hP s.ekASk oEntry.opkSk sOpkPk hOpkPow,
            ← hekPk, hEkEq]
      rw [hsKey, hrKey, hsOpk, Option.map_some, hDh1, hDh2, hDh3, hDh4, hSsEq]

/-- Assembles the two-key hop obligations into `Pqxdh2KeyKeyIndReductionBoundδ` for
    `pqxdhKeyIndSimulators`. -/
theorem pqxdh_key_ind_withδ_of_hops (S : Setup)
    (hHop : KIHopG0G3Stmt S) (hGdh : KIGapDhStmt S) (hStop : KIStopStmt S)
    (hCoup : KICouplingStmt S) (hAt : KICorrAtStmt S) :
    Pqxdh2KeyKeyIndReductionBoundδ S (pqxdhKeyIndSimulators S) := by
  intro P hP δ hδ b A
  have h03 := hHop P hP b A
  have hC := hCoup P b.q_ro A.1 (by
    intro testReal full p hp hS
    exact hStop P hP b.q_ro p.2.adv
      (validTagState_of_mem_support_simulateQ P false false testReal b A p hp) hS)
  have hG := hGdh b P hP A
  have hCorr := prob_hasBadKemCorrRecords_le S hAt P hP δ hδ A.1
  have hNonneg : 0 ≤ KeyIndAdvantage S P A.1 :=
    _root_.SignalPqxdh.Security.keyIndAdvantage_nonneg S P A.1
  have htri := abs_sub_le (KeyIndAdvantage S P A.1) (keyIndAdvG3 S P A.1) 0
  have hG3_nonneg : 0 ≤ keyIndAdvG3 S P A.1 := by
    unfold keyIndAdvG3
    exact ENNReal.toReal_nonneg
  have hAbs0 : |KeyIndAdvantage S P A.1 - 0| = KeyIndAdvantage S P A.1 := by
    rw [sub_zero, abs_of_nonneg hNonneg]
  have hAbs3 : |keyIndAdvG3 S P A.1 - 0| = keyIndAdvG3 S P A.1 := by
    rw [sub_zero, abs_of_nonneg hG3_nonneg]
  rw [hAbs0, hAbs3] at htri
  have hTerm : 2 * ((S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ) = kemDecapsFailureTermReal S δ := by
    unfold kemDecapsFailureTermReal; ring
  unfold pqxdhKeyIndAdvantageBoundδReal pqxdhKeyIndBoundReal pqxdhKeyIndSimulators
  dsimp only
  set_option exponentiation.threshold 512 in
  linarith

end Proofs.SignalPqxdh.Security.PqxdhDelta
