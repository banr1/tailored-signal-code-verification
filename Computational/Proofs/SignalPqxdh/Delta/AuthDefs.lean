/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyIndDefs
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c3
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c4
import Computational.Proofs.SignalPqxdh.Security.AuthAssembly
import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmac

/-!
# PQXDH authentication with imperfect KEM correctness: hop statements

Defines the KEM correctness bad event `hasBadAuthKemCorr` and up-to-bad predicate `badSendδ` on
authentication hybrid states, states the δ hop interfaces proved under `Delta/Auth/`, and
assembles them into `pqxdh_auth_with_fixedδ_of_hops` (DEV-PQ21).
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.AuthSubHops1to3
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-! ## KEM correctness bad event -/

/-- Whether initiator KEM record `i` and responder KEM record `r` share a public key and ciphertext
but decapsulate to a different shared secret. -/
def isAuthKemCorrPair {S : Setup} (P : Primitives)
    (i : _root_.SignalPqxdh.Security.InitKemRecord S)
    (r : _root_.SignalPqxdh.Security.RecvKemRecord) : Bool :=
  decide (r.pqspkPk = i.pqspkPk) && decide (r.kemCt = i.kemCt) &&
    decide (P.kemDecaps r.pqspkSk r.kemCt ≠ some i.kemSs)

/-- Whether `AuthHybridState` contains an initiator/responder KEM record pair violating
decapsulation correctness. -/
def hasBadAuthKemCorr {S : Setup} (P : Primitives) (h : AuthHybridState S) : Bool :=
  h.initKemRecs.any (fun i => h.recvKemRecs.any (isAuthKemCorrPair P i))

/-- Up-to-bad predicate for the δ `G3 → G3.5` step, extending `authCutoffG3G3_5Latched` with
`hasBadAuthKemCorr`. -/
def badSendδ {S : Setup} (P : Primitives) (maxRo : ℕ) (s : AuthSendLatchedState S) : Bool :=
  (badAuthFgAnyLatchedMono P maxRo s.toFg || s.respEkCollLatched) || hasBadAuthKemCorr P s.hyb

/-- Matching ideal and responder authentication handshakes derive identical `buildSecrets` inputs
when `hasBadAuthKemCorr P hst = false`. -/
theorem matchIdealAuthHandshake_imp_secrets_eqδ {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (hst : AuthHybridState S)
    (hKS : ValidAuthKeyStores S P hst.base)
    (hNoCorr : hasBadAuthKemCorr P hst = false)
    {s : IdealAuthSession S} {sessEntry : AuthInitiatorEntry S}
    {u : Nat} {uEntry : PrincipalEntry} {kemCoins ss_s : Bytes}
    {initRec : _root_.SignalPqxdh.Security.InitKemRecord S}
    (hs : ValidIdealAuthSession S P hst s sessEntry u uEntry kemCoins ss_s initRec)
    {k : Fin S.N_id} {j : Fin S.N_recv}
    {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {opkPk? dh4? : Option Bytes} {ss_r : Bytes}
    {recEntry : _root_.SignalPqxdh.Security.RecvKemRecord} {hdr : HandshakeHdr}
    (hr : ValidAuthRespHandshake S P hst k j kEntry bEntry opkPk? dh4? ss_r recEntry hdr)
    (hMatch : matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk hdr s =
      true) :
    idealSessionSecrets P uEntry sessEntry.ekASk ss_s s =
      recvHandshakeSecrets P kEntry bEntry dh4? ss_r hdr := by
  rcases hKS with ⟨_, _, _, hPrins, hSpks, hOpks, _⟩
  rcases hs with ⟨_, _, _, hekPk, _, _, _, _, huMem, _, hsIkPk, _, hInitMem, hInitPk, hInitCt,
    hInitSs, _, _, _⟩
  rcases hr with ⟨hkMem, hbMem, _, _, _, hDec, hRecMem, hRecPk, hRecSk, hRecCt, _, hrOpkCases⟩
  unfold matchIdealAuthHandshake at hMatch
  simp only [Bool.and_eq_true, beq_iff_eq] at hMatch
  rcases hMatch with ⟨⟨⟨⟨⟨⟨hPowIkA, hPowIkB⟩, hPowSpk⟩, hOpkMatch⟩, hPowEk⟩, hPqEq⟩, hCtEq⟩
  have huIk := hPrins (u, uEntry) huMem
  have hkIk := hPrins (k.val, kEntry) hkMem
  rcases hSpks ((k.val, j.val), bEntry) hbMem with ⟨_, hbSpkPk, _⟩
  have hSsEq : ss_s = ss_r := by
    have hPkEq : recEntry.pqspkPk = initRec.pqspkPk := by
      rw [hRecPk, hInitPk]
      exact hPqEq
    have hCtEq' : recEntry.kemCt = initRec.kemCt := by
      rw [hRecCt, hInitCt]
      exact hCtEq
    have hPair : isAuthKemCorrPair P initRec recEntry = false := by
      have h1 : hst.recvKemRecs.any (isAuthKemCorrPair P initRec) = false :=
        Bool.eq_false_iff.mpr (List.any_eq_false.mp hNoCorr initRec hInitMem)
      exact Bool.eq_false_iff.mpr (List.any_eq_false.mp h1 recEntry hRecMem)
    have hDecS : P.kemDecaps recEntry.pqspkSk recEntry.kemCt = some initRec.kemSs := by
      by_contra hNe
      have hT : isAuthKemCorrPair P initRec recEntry = true := by
        unfold isAuthKemCorrPair
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
          decide_eq_true_iff]
        exact ⟨⟨hPkEq, hCtEq'⟩, hNe⟩
      rw [hT] at hPair
      cases hPair
    rw [hRecSk, hRecCt, hInitSs, hDec] at hDecS
    exact (Option.some.inj hDecS).symm
  have hIkAPow : P.pow8 hdr.ikAPk = P.pow8 (P.x25519Base uEntry.secIKA0) := by
    rw [hPowIkA, hsIkPk, huIk.2]
  have hEkPow : P.pow8 hdr.ekAPk = P.pow8 (P.x25519Base sessEntry.ekASk) := by
    rw [hPowEk, hekPk]
  have hDh1 : P.x25519 uEntry.secIKA0 s.peerSpkPk = P.x25519 bEntry.spkSk hdr.ikAPk := by
    have hSpkPow : P.pow8 s.peerSpkPk = P.pow8 (P.x25519Base bEntry.spkSk) := by
      rw [← hPowSpk, hbSpkPk]
    rw [x25519_comm_of_pow8_eq_auth P hP uEntry.secIKA0 bEntry.spkSk s.peerSpkPk hSpkPow]
    exact (hP.x25519_pow8_congr bEntry.spkSk hdr.ikAPk (P.x25519Base uEntry.secIKA0)
      (hP.pow8_base_len hdr.ikAPk uEntry.secIKA0 hIkAPow)
      (hP.x25519Base_len uEntry.secIKA0) hIkAPow).symm
  have hDh2 : P.x25519 sessEntry.ekASk s.peerIkPk = P.x25519 kEntry.secIKA0 hdr.ekAPk := by
    have hIkBPow : P.pow8 s.peerIkPk = P.pow8 (P.x25519Base kEntry.secIKA0) := by
      rw [← hPowIkB, hkIk.2]
    rw [x25519_comm_of_pow8_eq_auth P hP sessEntry.ekASk kEntry.secIKA0 s.peerIkPk hIkBPow]
    exact (hP.x25519_pow8_congr kEntry.secIKA0 hdr.ekAPk (P.x25519Base sessEntry.ekASk)
      (hP.pow8_base_len hdr.ekAPk sessEntry.ekASk hEkPow)
      (hP.x25519Base_len sessEntry.ekASk) hEkPow).symm
  have hDh3 : P.x25519 sessEntry.ekASk s.peerSpkPk = P.x25519 bEntry.spkSk hdr.ekAPk := by
    have hSpkPow : P.pow8 s.peerSpkPk = P.pow8 (P.x25519Base bEntry.spkSk) := by
      rw [← hPowSpk, hbSpkPk]
    rw [x25519_comm_of_pow8_eq_auth P hP sessEntry.ekASk bEntry.spkSk s.peerSpkPk hSpkPow]
    exact (hP.x25519_pow8_congr bEntry.spkSk hdr.ekAPk (P.x25519Base sessEntry.ekASk)
      (hP.pow8_base_len hdr.ekAPk sessEntry.ekASk hEkPow)
      (hP.x25519Base_len sessEntry.ekASk) hEkPow).symm
  unfold idealSessionSecrets recvHandshakeSecrets
  rcases hrOpkCases with ⟨hrOpkNone, hrDh4None⟩ | ⟨o, oEntry, hoMem, hrOpkSome, hrDh4Some⟩
  · rw [hrOpkNone] at hOpkMatch
    cases hsOpk : s.peerOpkPk? with
    | none =>
      rw [hrDh4None, Option.map_none, hDh1, hDh2, hDh3, hSsEq]
    | some _ =>
      rw [hsOpk] at hOpkMatch; nomatch hOpkMatch
  · rw [hrOpkSome] at hOpkMatch
    cases hsOpk : s.peerOpkPk? with
    | none =>
      rw [hsOpk] at hOpkMatch; nomatch hOpkMatch
    | some sOpkPk =>
      rw [hsOpk] at hOpkMatch
      have hPowOpk : P.pow8 oEntry.opkPk = P.pow8 sOpkPk := beq_iff_eq.mp hOpkMatch
      have hoOpk := hOpks ((k.val, j.val, o), oEntry) hoMem
      have hOpkPowBase : P.pow8 sOpkPk = P.pow8 (P.x25519Base oEntry.opkSk) := by
        rw [← hPowOpk, hoOpk.2]
      have hDh4 : P.x25519 sessEntry.ekASk sOpkPk = P.x25519 oEntry.opkSk hdr.ekAPk := by
        rw [x25519_comm_of_pow8_eq_auth P hP sessEntry.ekASk oEntry.opkSk sOpkPk hOpkPowBase]
        exact (hP.x25519_pow8_congr oEntry.opkSk hdr.ekAPk (P.x25519Base sessEntry.ekASk)
          (hP.pow8_base_len hdr.ekAPk sessEntry.ekASk hEkPow)
          (hP.x25519Base_len sessEntry.ekASk) hEkPow).symm
      rw [hrDh4Some, Option.map_some, hDh1, hDh2, hDh3, hDh4, hSsEq]

/-! ## Hop statements -/

/-- `.recvOPK` step coupling on `AuthSendLatchedState` under `CryptoWellFormedPrimitivesδ` with bad
event `badSendδ`. -/
def AuthRecvOPKδStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (maxRo : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
      (s35 s3 : AuthSendLatchedState S),
      AuthSendWinGuardedCoupledInv P s35 s3 →
      isAuthG3Abort P s3.hyb = false →
      s3.hyb.base.hasWonAuth = false →
      badSendδ P maxRo s3 = false →
      s3.adv.advRoLog.length ≤ maxRo →
      s3.adv.respRecs.length ≤ S.N_sess_tot →
      RelProbUpToBad
        (fun y35 y3 =>
          (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
          (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
        (fun y3 => badSendδ P maxRo y3.2)
        ((pqxdhAuthSendLatchedStageImpl .g3_5 S P (.recvOPK k j o msg)).run s35)
        ((pqxdhAuthSendLatchedStageImpl .g3 S P (.recvOPK k j o msg)).run s3)

/-- `.recvNoOPK` step coupling on `AuthSendLatchedState` under `CryptoWellFormedPrimitivesδ` with
bad event `badSendδ`. -/
def AuthRecvNoOPKδStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (maxRo : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
      (s35 s3 : AuthSendLatchedState S),
      AuthSendWinGuardedCoupledInv P s35 s3 →
      isAuthG3Abort P s3.hyb = false →
      s3.hyb.base.hasWonAuth = false →
      badSendδ P maxRo s3 = false →
      s3.adv.advRoLog.length ≤ maxRo →
      s3.adv.respRecs.length ≤ S.N_sess_tot →
      RelProbUpToBad
        (fun y35 y3 =>
          (y35.1 = y3.1 ∧ AuthSendWinGuardedCoupledInv P y35.2 y3.2) ∨
          (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
        (fun y3 => badSendδ P maxRo y3.2)
        ((pqxdhAuthSendLatchedStageImpl .g3_5 S P (.recvNoOPK k j l msg)).run s35)
        ((pqxdhAuthSendLatchedStageImpl .g3 S P (.recvNoOPK k j l msg)).run s3)

/-- Monotonicity of `hasBadAuthKemCorr` along `.g3` send-latched steps. -/
def AuthCorrMonoStmt (S : Setup) : Prop :=
  ∀ (P : Primitives) (q : AuthQuery S) (s : AuthSendLatchedState S),
    hasBadAuthKemCorr P s.hyb = true →
    ∀ y ∈ support ((pqxdhAuthSendLatchedStageImpl .g3 S P q).run s),
      hasBadAuthKemCorr P y.2.hyb = true

/-- `G3 → G3.5` cutoff bound with the `hasBadAuthKemCorr` bad-event term. -/
def AuthCutoffδStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      |authFixedAdvG3 S P A.1 - authFixedAdvG3_5 S P A.1| ≤
        2 * (𝒟[runAuthFgLatchedSim S P A.1 >>= fun x =>
          pure (badAuthFgAnyLatched P b.q_ro x.2.2)] {true}).toReal +
        2 * (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 +
        2 * (𝒟[runAuthSendLatchedSim .g3 S P A.1 >>= fun x =>
          pure (hasBadAuthKemCorr P x.2.2.hyb)] {true}).toReal

/-- Derivation of `AuthCutoffδStmt` from the `.recvOPK`/`.recvNoOPK` couplings and bad-event
monotonicity. -/
def AuthCutoffGlueStmt (S : Setup) : Prop :=
  AuthRecvOPKδStmt S → AuthRecvNoOPKδStmt S → AuthCorrMonoStmt S → AuthCutoffδStmt S

/-- Transfer of `hasBadAuthKemCorr` in `runAuthSendLatchedSim .g3` to `hasBadKemCorrRecords` in
`runAuthShCrSim`. -/
def AuthCorrTransferStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b),
      (𝒟[runAuthSendLatchedSim .g3 S P A.1 >>= fun x =>
          pure (hasBadAuthKemCorr P x.2.2.hyb)] {true}).toReal ≤
        (𝒟[runAuthShCrSim S P A.1 >>= fun x =>
          pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal

/-- Per-index reduction from the KEM correctness bad event in `runAuthShCrSim` to `kemCorrExpProb`. -/
def AuthCorrAtStmt (S : Setup) : Prop :=
  ∀ (P : Primitives), CryptoWellFormedPrimitivesδ P →
    ∀ (A : AuthAdversary S) (idx : ℕ), idx < S.N_spk_tot * S.N_send_tot →
      ∃ choosePk : Bytes → Bytes → ProbComp Bytes,
        (𝒟[runAuthShCrSim S P A >>= fun x =>
            pure (hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)]
          {true}).toReal ≤
          (𝒟[kemCorrExpProb P choosePk] {true}).toReal

/-! ## Union bound and assembly -/

/-- Union bound of `N_spk_tot * N_send_tot * δ` on `hasBadKemCorrRecords` in `runAuthShCrSim`. -/
theorem prob_hasBadKemCorrRecords_auth_le (S : Setup) (hAt : AuthCorrAtStmt S)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (A : AuthAdversary S) :
    (𝒟[runAuthShCrSim S P A >>= fun x =>
        pure (hasBadKemCorrRecords S P x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal ≤
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
  have hU := _root_.SignalPqxdh.Security.toReal_any_range_le_sum (runAuthShCrSim S P A)
    (S.N_spk_tot * S.N_send_tot)
    (fun idx x => hasBadKemCorrRecordsAt S P idx x.2.2.initKemRecs x.2.2.recvKemRecs)
  refine le_trans hU ?_
  calc (∑ k ∈ Finset.range (S.N_spk_tot * S.N_send_tot),
        (𝒟[runAuthShCrSim S P A >>= fun x =>
          pure (hasBadKemCorrRecordsAt S P k x.2.2.initKemRecs x.2.2.recvKemRecs)] {true}).toReal)
      ≤ ∑ _k ∈ Finset.range (S.N_spk_tot * S.N_send_tot), δ := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        obtain ⟨choosePk, hC⟩ := hAt P hP A k (Finset.mem_range.mp hk)
        exact le_trans hC (kemCorrExpProb_le P δ hδ choosePk)
    _ = (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- `G3 → G3.5` authentication hop bound under `CryptoWellFormedPrimitivesδ`. -/
theorem auth_hop_G3_G3_5_leδ (S : Setup) (hCut : AuthCutoffδStmt S)
    (hTr : AuthCorrTransferStmt S) (hAt : AuthCorrAtStmt S)
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    |authFixedAdvG3 S P A.1 - authFixedAdvG3_5 S P A.1| ≤
      2 * ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDH P P.isValidDhTriple P.pow8 (fgAuthGapDhAdv4 S b A) +
      2 * (S.N_send_tot : ℝ) * (S.N_recv_tot : ℝ) / (2 : ℝ) ^ 250 +
      kemDecapsFailureTermReal S δ := by
  have hC := hCut P hP b A
  have hAny := prob_badAuthFgAnyLatched_runAuthFgLatchedSim_le_gapDh S b P hP A
  have hT := hTr P hP b A
  have hU := prob_hasBadKemCorrRecords_auth_le S hAt P hP δ hδ A.1
  have hTerm : kemDecapsFailureTermReal S δ = 2 * ((S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * δ) := by
    unfold kemDecapsFailureTermReal; ring
  rw [hTerm]
  linarith

/-- Assembles `PqxdhAuthReductionBoundδ S (pqxdhAuthSimulators S)` from the δ `G3 → G3.5` hop
statements. -/
theorem pqxdh_auth_with_fixedδ_of_hops (S : Setup)
    (hOPK : AuthRecvOPKδStmt S) (hNoOPK : AuthRecvNoOPKδStmt S) (hMono : AuthCorrMonoStmt S)
    (hGlue : AuthCutoffGlueStmt S) (hTr : AuthCorrTransferStmt S) (hAt : AuthCorrAtStmt S) :
    PqxdhAuthReductionBoundδ S (pqxdhAuthSimulators S) := by
  intro P hP δ hδ b A
  have h03 := auth_hop_G0_G3_le S P hP b A
  have h335 := auth_hop_G3_G3_5_leδ S (hGlue hOPK hNoOPK hMono) hTr hAt P hP δ hδ b A
  have h3536 := _root_.SignalPqxdh.Security.hop_G3_5_G3_6 S P hP b A
  have h3637 := hop_G3_6_G3_7 S P hP b A
  have h3738 := hop_G3_7_G3_8 S P hP b A
  have h385 := (authSubHops4to5Bundle S).hop_G3_8_G5 P hP b A
  have hInt := aeadMuIntCtxt_le_prfHmac S P hP b A
  have hG5 := authFixedAdvG5_eq_zero S P A.1
  have hNonneg : 0 ≤ AuthAdvantageReal S P A.1 := authAdvantage_nonneg S P A.1
  have htri1 := abs_sub_le (AuthAdvantageReal S P A.1) (authFixedAdvG3 S P A.1) (authFixedAdvG5 S P A.1)
  have htri2 :=
    abs_sub_le (authFixedAdvG3 S P A.1) (authFixedAdvG3_5 S P A.1) (authFixedAdvG5 S P A.1)
  have htri3 :=
    abs_sub_le (authFixedAdvG3_5 S P A.1) (authFixedAdvG3_6 S P A.1) (authFixedAdvG5 S P A.1)
  have htri4 :=
    abs_sub_le (authFixedAdvG3_6 S P A.1) (authFixedAdvG3_7 S P A.1) (authFixedAdvG5 S P A.1)
  have htri5 :=
    abs_sub_le (authFixedAdvG3_7 S P A.1) (authFixedAdvG3_8 S P A.1) (authFixedAdvG5 S P A.1)
  have hAbs0 : |AuthAdvantageReal S P A.1 - authFixedAdvG5 S P A.1| = AuthAdvantageReal S P A.1 := by
    rw [hG5, sub_zero, abs_of_nonneg hNonneg]
  clear hOPK hNoOPK hMono hGlue hTr hAt
  unfold pqxdhAuthAdvantageBoundδReal pqxdhAuthBoundReal pqxdhKeyIndBoundReal pqxdhAuthSimulators
    authSubHops4to5Bundle authSubHops4to5Bundle_of_int at *
  dsimp only at *
  set_option exponentiation.threshold 512 in
  linarith

end Proofs.SignalPqxdh.Security.PqxdhDelta
