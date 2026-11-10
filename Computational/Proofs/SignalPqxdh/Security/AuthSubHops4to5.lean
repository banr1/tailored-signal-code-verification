/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthHopInterface
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead
public import Computational.Proofs.SignalPqxdh.Security.SigHopA
import Computational.Proofs.SignalPqxdh.Security.FgGapDhA -- shake: keep
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC -- shake: keep

/-!
# Helper lemmas for `pqxdh_auth` post-handshake sub-hops 4–5 (`G3.8 → G4 → G5`)

Defines `PrimBaseSpec` step liftings, `cacheAuthAdvKeys` commutation lemmas, and query-bound
combinators over `AeadIntSimSpec` for the AEAD sub-hops of `pqxdh_auth`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh
  (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt initSessionSlotIdx_sendNoOPK_lt
   initSessionSlotIdx_inj_of_lt RelProbUpToBad simulateQ_relProbUpToBad
   evalDist_simulateQ_eq_of_step_or_bad)

def cacheAuthAdvKeys {S : Setup} (P : Primitives) (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with
    base := { hst.base with
      advKeys := hst.base.advKeys.map (fun (_, pk) => (P.pow8 pk, pk)) } }

@[simp] theorem eraseAuthEvents_idem {S : Setup} (hst : AuthHybridState S) :
    eraseAuthEvents (eraseAuthEvents hst) = eraseAuthEvents hst := rfl

@[simp] theorem eraseAuthEvents_empty (S : Setup) (secb : Bool) :
    eraseAuthEvents (AuthHybridState.empty S secb) = AuthHybridState.empty S secb := rfl

@[simp] theorem allHonestEcPksAuth_eraseAuthEvents {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) :
    allHonestEcPksAuth P (eraseAuthEvents hst) = allHonestEcPksAuth P hst := rfl

@[simp] theorem hasEcPkCollisionAuth_eraseAuthEvents {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) :
    hasEcPkCollisionAuth P (eraseAuthEvents hst) = hasEcPkCollisionAuth P hst := rfl

@[simp] theorem hasBadSigAuth_eraseAuthEvents {S : Setup} (hst : AuthHybridState S) :
    hasBadSigAuth (eraseAuthEvents hst) = hasBadSigAuth hst := rfl

@[simp] theorem hasKemPkCollisionAuth_eraseAuthEvents {S : Setup} (hst : AuthHybridState S) :
    hasKemPkCollisionAuth (eraseAuthEvents hst) = hasKemPkCollisionAuth hst := rfl

@[simp] theorem hasBadKemShCrAuth_eraseAuthEvents {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) :
    hasBadKemShCrAuth P (eraseAuthEvents hst) = hasBadKemShCrAuth P hst := rfl

@[simp] theorem finalizeAuthGame_false_eraseAuthEvents {S : Setup} (useRo : Bool)
    (P : Primitives) (b' : Bool) (hst : AuthHybridState S) :
    finalizeAuthGame (σ := AuthHybridState S) useRo false S P b' (eraseAuthEvents hst) =
      finalizeAuthGame (σ := AuthHybridState S) useRo false S P b' hst := rfl

@[simp] theorem finalizeAuthGame_cacheAuthAdvKeys {S : Setup} (useRo checkAuth : Bool)
    (P : Primitives) (b' : Bool) (hst : AuthHybridState S) :
    finalizeAuthGame (σ := AuthHybridState S) useRo checkAuth S P b' (cacheAuthAdvKeys P hst) =
      finalizeAuthGame (σ := AuthHybridState S) useRo checkAuth S P b' hst := rfl

@[simp] theorem simulateQ_primQ_spqrInitSend (P : Primitives) (k coins : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.spqrInitSend k coins)) =
      (pure (P.spqrInitSend k coins) : ProbComp (primSpec.Range (.spqrInitSend k coins))) := rfl

@[simp] theorem simulateQ_primQ_spqrInitRecv (P : Primitives) (k msg : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.spqrInitRecv k msg)) =
      (pure (P.spqrInitRecv k msg) : ProbComp (primSpec.Range (.spqrInitRecv k msg))) := rfl

@[simp] theorem simulateQ_primQ_rootCreateChain (P : Primitives) (rk dh : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.rootCreateChain rk dh)) =
      (pure (P.rootCreateChain rk dh) : ProbComp (primSpec.Range (.rootCreateChain rk dh))) := rfl

@[simp] theorem simulateQ_primQ_chainKdfSeed (P : Primitives) (ck : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.chainKdfSeed ck)) =
      (pure (P.chainKdfSeed ck) : ProbComp (primSpec.Range (.chainKdfSeed ck))) := rfl

@[simp] theorem simulateQ_primQ_chainKdfNext (P : Primitives) (ck : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.chainKdfNext ck)) =
      (pure (P.chainKdfNext ck) : ProbComp (primSpec.Range (.chainKdfNext ck))) := rfl

@[simp] theorem simulateQ_primQ_deriveMsgKeys (P : Primitives) (mkSeed : Bytes)
    (salt? : Option Bytes) :
    simulateQ (primBaseImpl P) (primQ (.deriveMsgKeys mkSeed salt?)) =
      (pure (P.deriveMsgKeys mkSeed salt?) :
        ProbComp (primSpec.Range (.deriveMsgKeys mkSeed salt?))) := rfl

@[simp] theorem simulateQ_primQ_aeadEnc (P : Primitives) (mk : MessageKeys) (ad pt : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.aeadEnc mk ad pt)) =
      (pure (P.aeadEnc mk ad pt) : ProbComp (primSpec.Range (.aeadEnc mk ad pt))) := rfl

@[simp] theorem simulateQ_primQ_aeadDec (P : Primitives) (mk : MessageKeys) (ad ct : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.aeadDec mk ad ct)) =
      (pure (P.aeadDec mk ad ct) : ProbComp (primSpec.Range (.aeadDec mk ad ct))) := rfl

@[simp] theorem evalHkdfOrRo_true_eq_pure (P : Primitives)
    (roCache : List (Bytes × DRKey)) (secrets : Bytes) :
    evalHkdfOrRo true P roCache secrets = evalHkdfRoPure roCache secrets := rfl

@[simp] theorem evalRootKdfOrRo_true_eq_pure (P : Primitives)
    (rootRoCache : List ((Bytes × Bytes) × (Bytes × Bytes))) (rk dh : Bytes) :
    evalRootKdfOrRo true P rootRoCache rk dh = evalRootKdfRoPure rootRoCache rk dh := rfl

theorem simulateQ_mapMPrim {α β : Type} (P : Primitives)
    (f : α → OracleComp PrimBaseSpec β) (fPure : α → β)
    (hf : ∀ a, simulateQ (primBaseImpl P) (f a) = pure (fPure a)) :
    ∀ (L : List α), simulateQ (primBaseImpl P) (mapMPrim f L) = pure (L.map fPure)
  | [] => rfl
  | x :: xs => by
    simp only [mapMPrim, simulateQ_bind, hf x, pure_bind, List.map_cons]
    rw [simulateQ_mapMPrim P f fPure hf xs, pure_bind]
    rfl

theorem primBounded_checkBundleProvenanceExactPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    PrimBounded (checkBundleProvenanceExactPrim S principals spkBundles opkEntries bundle)
      (S.N_dh * 4) := by
  unfold checkBundleProvenanceExactPrim
  have h1 : S.N_dh * 2 + S.N_dh * 2 = S.N_dh * 4 := by omega
  rw [← h1]
  refine primBounded_bind_le (S.N_dh * 2)
    (primBounded_findHonestPrincipalPrim S principals bundle.ikB) (fun r => ?_)
  cases r with
  | none => exact primBounded_pure'
  | some kp =>
    rcases kp with ⟨k, _⟩
    dsimp only
    cases bundle.opkB? with
    | none => exact primBounded_pure'
    | some opkPair =>
      rcases opkPair with ⟨_, opkPk⟩
      dsimp only
      have hopk : PrimBounded
          (anyMPrim (fun ((u, _, _), e) => do
            let p1 ← primQ (.pow8 e.opkPk)
            let p2 ← primQ (.pow8 opkPk)
            return (u == k && p1 == p2)) (opkEntries.take S.N_dh))
          (S.N_dh * 2) := by
        refine primBounded_anyMPrim_take _ 2 S.N_dh opkEntries (fun ((u, _, _), e) => ?_)
        refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
        exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
      exact primBounded_bind_le 0 hopk (fun _ => primBounded_pure')

theorem simulateQ_checkBundleProvenanceExactPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput)
    (hPrin : principals.length ≤ S.N_dh)
    (hOpk : opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (checkBundleProvenanceExactPrim S principals spkBundles opkEntries bundle) =
      pure (checkBundleProvenanceExact P principals spkBundles opkEntries bundle) := by
  unfold checkBundleProvenanceExactPrim checkBundleProvenanceExact
  rw [simulateQ_bind, simulateQ_findHonestPrincipalPrim S P principals bundle.ikB hPrin, pure_bind]
  cases findHonestPrincipal P principals bundle.ikB with
  | none => rfl
  | some kp =>
    rcases kp with ⟨k, _⟩
    dsimp only
    cases bundle.opkB? with
    | none => rfl
    | some opkPair =>
      rcases opkPair with ⟨_, opkPk⟩
      dsimp only
      rw [List.take_of_length_le hOpk, simulateQ_bind,
          simulateQ_anyMPrim P _
            (fun ((u, _, _), e) => u == k && P.pow8 e.opkPk == P.pow8 opkPk)
            (fun _ => rfl) opkEntries,
          pure_bind]
      rfl

theorem primBounded_sameOpkPkPrim (o1 o2 : Option Bytes) :
    PrimBounded (sameOpkPkPrim o1 o2) 2 := by
  unfold sameOpkPkPrim
  cases o1 <;> cases o2
  · exact primBounded_pure'
  · exact primBounded_pure'
  · exact primBounded_pure'
  · refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
    exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
theorem primBounded_matchIdealAuthHandshakePrim {S : Setup}
    (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) :
    PrimBounded (matchIdealAuthHandshakePrim ikBPk spkBPk opkBPk? pqspkBPk hdr s) 10 := by
  unfold matchIdealAuthHandshakePrim
  refine primBounded_bind_le 9 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 8 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 7 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 6 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 5 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 4 (primBounded_primQ _) (fun _ => ?_)
  refine primBounded_bind_le 2 (primBounded_sameOpkPkPrim opkBPk? s.peerOpkPk?) (fun _ => ?_)
  refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
  exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')

theorem simulateQ_matchIdealAuthHandshakePrim {S : Setup} (P : Primitives)
    (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) :
    simulateQ (primBaseImpl P)
      (matchIdealAuthHandshakePrim ikBPk spkBPk opkBPk? pqspkBPk hdr s) =
      pure (matchIdealAuthHandshake P ikBPk spkBPk opkBPk? pqspkBPk hdr s) := by
  unfold matchIdealAuthHandshakePrim matchIdealAuthHandshake sameOpkPkPrim
  cases opkBPk? <;> cases s.peerOpkPk? <;> rfl

theorem simulateQ_allHonestEcPksAuthPrim (S : Setup) (P : Primitives) (hst : AuthHybridState S)
    (hPrin : hst.base.principals.length ≤ S.N_dh)
    (hSpk : hst.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.base.opkEntries.length ≤ S.N_dh)
    (hSess : hst.base.sessions.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P) (allHonestEcPksAuthPrim S hst.base) =
      pure (allHonestEcPksAuth P hst) := by
  unfold allHonestEcPksAuthPrim allHonestEcPksAuth HasAuthState.toAuthState
  dsimp only
  rw [List.take_of_length_le hPrin, List.take_of_length_le hSpk,
      List.take_of_length_le hOpk, List.take_of_length_le hSess,
      simulateQ_bind,
      simulateQ_mapMPrim P _ (fun (_, e) => P.pow8 e.ikAPk) (fun _ => rfl) hst.base.principals,
      pure_bind, simulateQ_bind,
      simulateQ_mapMPrim P _ (fun (_, b) => P.pow8 b.spkPk) (fun _ => rfl) hst.base.spkBundles,
      pure_bind, simulateQ_bind,
      simulateQ_mapMPrim P _ (fun (_, o) => P.pow8 o.opkPk) (fun _ => rfl) hst.base.opkEntries,
      pure_bind, simulateQ_bind,
      simulateQ_mapMPrim P _
        (fun s => P.pow8 (P.x25519Base s.ekASk)) (fun _ => rfl) hst.base.sessions,
      pure_bind]
  rfl
def ValidRecvKemRecords (P : Primitives) (recvRecs : List RecvKemRecord) : Prop :=
  ∀ r ∈ recvRecs, P.kemDecaps r.pqspkSk r.kemCt = some r.kemSs

theorem hasBadKemShCrRecordsPure_eq {S : Setup} (P : Primitives)
    (initRecs : List (InitKemRecord S)) (recvRecs : List RecvKemRecord)
    (hValid : ValidRecvKemRecords P recvRecs) :
    hasBadKemShCrRecordsPure initRecs recvRecs =
      hasBadKemShCrRecords P initRecs recvRecs := by
  unfold hasBadKemShCrRecordsPure hasBadKemShCrRecords
  congr 1
  funext i
  induction recvRecs with
  | nil => rfl
  | cons r rs ih =>
    have hr : P.kemDecaps r.pqspkSk r.kemCt = some r.kemSs := hValid r List.mem_cons_self
    have hbeq : (P.kemDecaps r.pqspkSk r.kemCt == some i.kemSs) = (r.kemSs == i.kemSs) := by
      rw [hr]
      cases h : (r.kemSs == i.kemSs)
      · have hne : r.kemSs ≠ i.kemSs := beq_eq_false_iff_ne.mp h
        exact beq_eq_false_iff_ne.mpr (fun heq => hne (Option.some.inj heq))
      · have heq : r.kemSs = i.kemSs := beq_iff_eq.mp h
        exact beq_iff_eq.mpr (congrArg some heq)
    simp only [List.any_cons, hbeq, ih (fun r' hr' => hValid r' (List.mem_cons_of_mem _ hr'))]

theorem allChallengedCleanAux {S : Setup} (useRo : Bool) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (sessions : List (AuthInitiatorEntry S))
    (hNoSig : sessions.any (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest)) = false) :
    sessions.all (fun s => !s.challenged || (s.fresh && s.pqspkHonest)) =
      sessions.all (fun s => !s.challenged || authInitCorruptionClause P useRo principals s) := by
  induction sessions with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at hNoSig
    rcases hNoSig with ⟨hs, hss⟩
    simp only [List.all_cons, ih hss]
    congr 1
    congr 1
    unfold authInitCorruptionClause
    cases hfresh : s.fresh with
    | false => rfl
    | true =>
      rw [hfresh] at hs
      cases hpq : s.pqspkHonest with
      | false =>
        rw [hpq] at hs
        simp at hs
      | true =>
        cases useRo <;> simp

theorem allChallengedCleanPure_eq_of_hasBadSigAuth_false {S : Setup}
    (useRo : Bool) (P : Primitives) (hst : AuthHybridState S)
    (hNoSig : hasBadSigAuth hst = false) :
    allChallengedCleanPure hst.base =
      hst.base.sessions.all (fun s =>
        !s.challenged || authInitCorruptionClause P useRo hst.base.principals s) :=
  allChallengedCleanAux useRo P hst.base.principals hst.base.sessions hNoSig

theorem simulateQ_finalizeAuthGameNoAuthPrim (S : Setup) (P : Primitives)
    (b' : Bool) (finalSt : AuthHybridState S)
    (hPrin : finalSt.base.principals.length ≤ S.N_dh)
    (hSpk : finalSt.base.spkBundles.length ≤ S.N_dh)
    (hOpk : finalSt.base.opkEntries.length ≤ S.N_dh)
    (hSess : finalSt.base.sessions.length ≤ S.N_dh)
    (hValidKem : ValidRecvKemRecords P finalSt.recvKemRecs) :
    simulateQ (primBaseImpl P) (finalizeAuthGameNoAuthPrim S b' finalSt) =
      finalizeAuthGame (σ := AuthHybridState S) true false S P b' finalSt := by
  unfold finalizeAuthGameNoAuthPrim finalizeAuthGame
  rw [simulateQ_bind, simulateQ_allHonestEcPksAuthPrim S P finalSt hPrin hSpk hOpk hSess,
      pure_bind, hasBadKemShCrRecordsPure_eq P finalSt.initKemRecs finalSt.recvKemRecs hValidKem]
  have hEc :
    hasDuplicateBytes (allHonestEcPksAuth P finalSt) = hasEcPkCollisionAuth P finalSt := rfl
  have hKem :
    hasBadKemShCrRecords P finalSt.initKemRecs finalSt.recvKemRecs =
      hasBadKemShCrAuth P finalSt := rfl
  rw [hEc, hKem]
  dsimp only
  by_cases hBad : (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt ||
                   hasKemPkCollisionAuth finalSt || hasBadKemShCrAuth P finalSt) = true
  · simp only [hBad, ↓reduceIte, simulateQ_embedUnif]
  · have hBadF : (hasEcPkCollisionAuth P finalSt || hasBadSigAuth finalSt ||
                  hasKemPkCollisionAuth finalSt || hasBadKemShCrAuth P finalSt) = false :=
      Bool.eq_false_iff.mpr hBad
    have hNoSig : hasBadSigAuth finalSt = false := by
      revert hBadF
      cases hasEcPkCollisionAuth P finalSt <;> cases hasBadSigAuth finalSt <;> simp
    rw [← allChallengedCleanPure_eq_of_hasBadSigAuth_false true P finalSt hNoSig]
    simp only [hBadF, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    split <;> simp [simulateQ_embedUnif]

theorem primBounded_stepAuthOtherPrim (useRo : Bool) (S : Setup) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) :
    PrimBounded (stepAuthOtherPrim useRo S q hst) 4 := by
  unfold stepAuthOtherPrim
  cases q with
  | initPrin u =>
    dsimp only
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 2 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
      refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
      refine primBounded_bind_le 1 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | corruptIK u =>
    dsimp only
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) <;>
      exact primBounded_pure'
  | genSPK u j =>
    dsimp only
    split
    · exact primBounded_pure'
    · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => exact primBounded_pure'
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        refine primBounded_bind_le 4 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
        refine primBounded_bind_le 3 (primBounded_primQ _) (fun _ => ?_)
        refine primBounded_bind_le 3 (primBounded_embedUnif sampleRandom64 0) (fun _ => ?_)
        refine primBounded_bind_le 2 (primBounded_primQ _) (fun _ => ?_)
        refine primBounded_bind_le 1 primBounded_sampleKemKeyGenPrim (fun _ => ?_)
        refine primBounded_bind_le 1 (primBounded_embedUnif sampleRandom64 0) (fun _ => ?_)
        exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | genOPK u j o =>
    dsimp only
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 1 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | registerKey sk =>
    dsimp only
    split
    · exact primBounded_pure'
    · refine primBounded_bind_le 1 (primBounded_primQ _) (fun _ => ?_)
      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
  | roQuery secrets =>
    dsimp only
    split
    · exact primBounded_pure'
    · exact primBounded_bind_le 0
        (primBounded_evalHkdfOrRoPrim true _ secrets) (fun _ => primBounded_pure')
  | roRootQuery rk dh =>
    dsimp only
    split
    · exact primBounded_pure'
    · exact primBounded_bind_le 0
        (primBounded_embedUnif (evalRootKdfRoPure _ rk dh) 0) (fun _ => primBounded_pure')
  | revealDhSecrets =>
    dsimp only
    split <;> exact primBounded_pure'
  | sendOPK _ _ _ _ _ | sendNoOPK _ _ _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ =>
    exact primBounded_pure'

theorem primBounded_ite {α : Type} {P : Prop} [Decidable P]
    {t e : OracleComp PrimBaseSpec α} {n : Nat}
    (ht : PrimBounded t n) (he : PrimBounded e n) :
    PrimBounded (if P then t else e) n := by
  by_cases h : P <;> simp [h, ht, he]

theorem primBounded_bind_step {α β : Type}
    {oa : OracleComp PrimBaseSpec α} {f : α → OracleComp PrimBaseSpec β}
    {n : Nat} (m1 m2 : Nat)
    (h1 : PrimBounded oa m1) (h2 : ∀ a, PrimBounded (f a) m2)
    (h : m1 + m2 ≤ n := by omega) :
    PrimBounded (oa >>= f) n :=
  primBounded_mono (primBounded_bind h1 h2) h

theorem runWithPrimStep_pure {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (a : α) (st : St) :
    runWithPrimStep step (pure a) st = pure (a, st) := rfl

@[simp]
theorem runWithPrimStep_query_inl {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (n : Nat) (mx : (unifSpec + GSpec).Range (Sum.inl n) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithPrimStep step (liftM (OracleSpec.query (Sum.inl n)) >>= mx) st =
      (liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n)) >>=
        fun u => runWithPrimStep step (mx u) st) := rfl

@[simp]
theorem runWithPrimStep_query_inr {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (gq : ιI) (mx : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithPrimStep step (liftM (OracleSpec.query (Sum.inr gq)) >>= mx) st =
      (step gq st >>= fun p => runWithPrimStep step (mx p.1) p.2) := rfl

@[simp]
theorem runWithPrimStepFuel_query_inl {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (defaultVal : α)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (n : Nat) (mx : (unifSpec + GSpec).Range (Sum.inl n) → OracleComp (unifSpec + GSpec) α)
    (fuel : Nat) (st : St) :
    runWithPrimStepFuel defaultVal step (liftM (OracleSpec.query (Sum.inl n)) >>= mx) fuel st =
      (liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n)) >>=
        fun u => runWithPrimStepFuel defaultVal step (mx u) fuel st) := rfl

@[simp]
theorem runWithPrimStepFuel_query_inr_zero {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (defaultVal : α)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (gq : ιI) (mx : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithPrimStepFuel defaultVal step (liftM (OracleSpec.query (Sum.inr gq)) >>= mx) 0 st =
      pure (defaultVal, st) := rfl

@[simp]
theorem runWithPrimStepFuel_query_inr_succ {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (defaultVal : α)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (gq : ιI) (mx : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (fuel : Nat) (st : St) :
    runWithPrimStepFuel defaultVal step
      (liftM (OracleSpec.query (Sum.inr gq)) >>= mx) (fuel + 1) st =
      (step gq st >>= fun p => runWithPrimStepFuel defaultVal step (mx p.1) fuel p.2) := rfl

theorem runWithPrimStepFuel_eq_runWithPrimStep {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (defaultVal : α)
    (step : (q : ιI) → St → OracleComp PrimBaseSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (Q fuel : Nat)
    (h_mx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => isGameQuery q = true) Q)
    (h_le : Q ≤ fuel) (st : St) :
    runWithPrimStepFuel defaultVal step mx fuel st = runWithPrimStep step mx st := by
  induction mx using OracleComp.inductionOn generalizing Q fuel st with
  | pure x => rfl
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h_mx
    cases q with
    | inl n =>
      rcases h_mx with ⟨_, h_cont⟩
      have hnl : ¬ (isGameQuery (Sum.inl n : ℕ ⊕ ιI) = true) := by simp [isGameQuery]
      simp only [hnl] at h_cont
      rw [runWithPrimStepFuel_query_inl, runWithPrimStep_query_inl]
      congr 1; funext u
      exact ih u Q fuel (h_cont u) h_le st
    | inr gq =>
      rcases h_mx with ⟨h_first, h_cont⟩
      have hgr : isGameQuery (Sum.inr gq : ℕ ⊕ ιI) = true := rfl
      rcases h_first with h_abs | hQpos
      · exfalso; exact h_abs hgr
      · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
        obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
        simp only [hgr, ↓reduceIte, Nat.add_sub_cancel] at h_cont
        rw [runWithPrimStepFuel_query_inr_succ, runWithPrimStep_query_inr]
        congr 1; funext p
        exact ih p.1 Q' fuel' (h_cont p.1) (by omega) p.2

end SignalPqxdh.Security
