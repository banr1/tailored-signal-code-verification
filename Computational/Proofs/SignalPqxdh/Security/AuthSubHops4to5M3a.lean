/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C2b
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
import VCVio.EvalDist.Monad.Basic

/-!
# Multi-Key `INT-CTXT` State Projection

Defines the key-masking projection `projectMuState` for `aeadMuIntReductionAuth` and proves pure
`simulateQ` characterizations of the reduction's primitive sub-computations on projected states.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

def maskMuSession {S : Setup} (s : IdealAuthSession S) : IdealAuthSession S :=
  { s with deriveMessageKeys := default }

def maskMuCache {S : Setup} (c : AuthMkSaltCache S) : AuthMkSaltCache S :=
  c.map (fun (k, (r0, _)) => (k, (r0, default)))

/-- Reduction view of a hybrid state with events erased, adversary keys normalized, and all
    ideal-session message keys masked. -/
def projectMuHybrid {S : Setup} (P : Primitives) (hst : AuthHybridState S) : AuthHybridState S :=
  let e := eraseAuthEvents hst
  { e with
    base := { e.base with advKeys := e.base.advKeys.map (fun (_, pk) => (P.pow8 pk, pk)) }
    idealSessions := e.idealSessions.map maskMuSession }

def projectMuState {S : Setup} (P : Primitives) (hst : AuthHybridStateFixed S) :
    AuthHybridStateFixed S :=
  { toAuthHybridState := projectMuHybrid P hst.toAuthHybridState
    recvCount := hst.recvCount
    mkSaltCache := maskMuCache hst.mkSaltCache }

@[simp] theorem maskMuSession_sid {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).sid = s.sid := by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_drKey {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).drKey = s.drKey := by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_ephAPk {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).ephAPk = s.ephAPk :=
        by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_rk1 {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).rk1 = s.rk1 := by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_ck1_0 {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).ck1_0 = s.ck1_0 := by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_mkSeed {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).mkSeed = s.mkSeed :=
        by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_ck1_1 {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).ck1_1 = s.ck1_1 := by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_spqrSalt? {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).spqrSalt? = s.spqrSalt? :=
        by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_ad {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).ad = s.ad := by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_aeadCt {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).aeadCt = s.aeadCt :=
        by unfold maskMuSession; rfl
@[simp] theorem maskMuSession_msgPlain {S : Setup} (s : IdealAuthSession S) :
    (maskMuSession s).msgPlain = s.msgPlain :=
        by unfold maskMuSession; rfl

theorem find?_maskMuSession {S : Setup}
    (P : Primitives) (ikBPk spkBPk : Bytes) (opkBPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (sessions : List (IdealAuthSession S)) :
    (sessions.map maskMuSession).find?
      (matchIdealAuthHandshake P ikBPk spkBPk opkBPk? pqspkBPk hdr) =
    (sessions.find?
      (matchIdealAuthHandshake P ikBPk spkBPk opkBPk? pqspkBPk hdr)).map maskMuSession := by
  rw [List.find?_map]
  congr 2

theorem find?_maskMuCache_pred {S : Setup}
    (c : AuthMkSaltCache S) (p : SessionId S × Option Bytes → Bool) :
    (maskMuCache c).find? (fun (k, _) => p k) =
      (c.find? (fun (k, _) => p k)).map (fun (k, (r0, _)) => (k, (r0, default))) := by
  unfold maskMuCache; rw [List.find?_map]; rfl

def isFreshSenderM3 (o : Option (Nat × PrincipalEntry)) : Bool :=
  match o with
  | some (_, sEntry) => !sEntry.corrupted
  | none => false

theorem or_r_isFreshSenderM3_eq
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool}
    (l : Bool) (o : Option (Nat × PrincipalEntry))
    (hSome : ∀ a b,
      G (some (a, b)) (fun _ sEntry => !sEntry.corrupted) (fun _ => false) = !b.corrupted)
    (hNone : G none (fun _ sEntry => !sEntry.corrupted) (fun _ => false) = false) :
    (l || G o (fun _ sEntry => !sEntry.corrupted) (fun _ => false)) =
      (l || isFreshSenderM3 o) := by
  rcases o with _ | ⟨a, b⟩
  · exact congrArg (l || ·) hNone
  · exact congrArg (l || ·) (hSome a b)

theorem prep_isFreshSenderM3_eq {S : Setup}
    {G : Option (Nat × PrincipalEntry) → (Nat → PrincipalEntry → Bool) → (Unit → Bool) → Bool}
    (o : Option (Nat × PrincipalEntry))
    (hSome : ∀ a b,
      G (some (a, b)) (fun _ sEntry => !sEntry.corrupted) (fun _ => false) = !b.corrupted)
    (hNone : G none (fun _ sEntry => !sEntry.corrupted) (fun _ => false) = false) :
    AuthIntRecvSchedPrep.mk (S := S)
      (G o (fun _ sEntry => !sEntry.corrupted) (fun _ => false)) =
      AuthIntRecvSchedPrep.mk (S := S) (isFreshSenderM3 o) := by
  rcases o with _ | ⟨a, b⟩
  · exact congrArg (AuthIntRecvSchedPrep.mk (S := S)) hNone
  · exact congrArg (AuthIntRecvSchedPrep.mk (S := S)) (hSome a b)

theorem simulateQ_prepAuthIntRecvSchedPrim_mu {S : Setup} (P : Primitives) (hstDec : AuthHybridState S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes)
    (secrets : Bytes) (msg : PreKeyMsg)
    (hPrinLen : hstDec.base.principals.length ≤ S.N_dh)
    (hSessLen : hstDec.idealSessions.length ≤ S.N_sess_tot) :
    simulateQ (primBaseImpl P)
      (prepAuthIntRecvSchedPrim S (projectMuHybrid P hstDec)
        kEntry bEntry opkPk? secrets msg) =
    (do
      let st := hstDec.base
      let senderPrincipal? := findHonestPrincipal P st.principals msg.hdr.ikAPk
      let isUncorruptedHonestSender : Bool :=
        match senderPrincipal? with | some (_, sEntry) => !sEntry.corrupted | none => false
      let matchedSess? : Option (IdealAuthSession S) :=
        hstDec.idealSessions.find?
          (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
      let useIdealBranch : Bool := matchedSess?.isSome || isUncorruptedHonestSender
      let (drKey, roCache') ← (
        if useIdealBranch && true then
          match matchedSess? with
          | some s => pure (s.drKey, st.roCache)
          | none   => do let dk ← sampleDRKey96; pure (dk, st.roCache)
        else evalHkdfOrRo true P st.roCache secrets)
      let dhRatchet := P.x25519 bEntry.spkSk msg.ephAPk
      let sameEph : Bool :=
        match matchedSess? with | some s => P.pow8 msg.ephAPk == P.pow8 s.ephAPk | none => false
      let ((rk1, ck1_0), rootRoCache') ← (
        if useIdealBranch && true then
          match matchedSess? with
          | some s =>
            if sameEph then pure ((s.rk1, s.ck1_0), st.rootRoCache)
            else do let r ← sampleBytes32; let c ← sampleBytes32; pure ((r, c), st.rootRoCache)
          | none => do let r ← sampleBytes32; let c ← sampleBytes32; pure ((r, c), st.rootRoCache)
        else evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
      let (mkSeed, ck1_1) ← (
        if useIdealBranch && true then
          match matchedSess? with
          | some s =>
            if sameEph then pure (s.mkSeed, s.ck1_1)
            else do let ms ← sampleBytes32; let cn ← sampleBytes32; pure (ms, cn)
          | none => do let ms ← sampleBytes32; let cn ← sampleBytes32; pure (ms, cn)
        else pure (P.chainKdfSeed ck1_0, P.chainKdfNext ck1_0))
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => return none
      | some (_pqrStB, spqrSalt?) =>
        return some {
          isUncorruptedHonestSender := isUncorruptedHonestSender,
          matchedSess? := matchedSess?.map (maskMuSession),
          useIdealBranch := useIdealBranch, drKey := drKey, roCache' := roCache',
          sameEph := sameEph, rk1 := rk1, ck1_0 := ck1_0, rootRoCache' := rootRoCache',
          mkSeed := mkSeed, ck1_1 := ck1_1, spqrSalt? := spqrSalt? }) := by
  unfold prepAuthIntRecvSchedPrim
  have hb_princ : (projectMuHybrid P hstDec).base.principals =
      hstDec.base.principals := rfl
  have hb_ro : (projectMuHybrid P hstDec).base.roCache = hstDec.base.roCache := rfl
  have hb_rro : (projectMuHybrid P hstDec).base.rootRoCache =
      hstDec.base.rootRoCache := rfl
  have hb_sess : ((projectMuHybrid P hstDec).idealSessions).take S.N_sess_tot =
      hstDec.idealSessions.map (maskMuSession) :=
    List.take_of_length_le (by simp [projectMuHybrid, eraseAuthEvents, hSessLen])
  dsimp only
  rw [hb_princ, hb_ro, hb_rro, hb_sess,
      simulateQ_bind, simulateQ_findHonestPrincipalPrim S P _ msg.hdr.ikAPk hPrinLen, pure_bind,
      simulateQ_bind,
      simulateQ_findMPrim P _ _ (simulateQ_matchIdealAuthHandshakePrim P kEntry.ikAPk bEntry.spkPk
          opkPk? bEntry.pqspkPk msg.hdr) _,
      find?_maskMuSession, pure_bind]
  simp only [Option.isSome_map]
  generalize hstDec.idealSessions.find?
    (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr)
        = matchedSess?
  repeat (rw [or_r_isFreshSenderM3_eq matchedSess?.isSome
    (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk)]; all_goals try (intros; rfl))
  repeat (rw [prep_isFreshSenderM3_eq
    (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk)]; all_goals try (intros; rfl))
  generalize isFreshSenderM3 (findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk)
    = isUncorruptedHonestSender
  rcases matchedSess? with _ | s
  · cases isUncorruptedHonestSender
    · simp only [Option.map, Option.isSome, Bool.false_or, Bool.and_true, Bool.false_eq_true,
        ↓reduceIte, simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, sim_fg_x25519,
        sim_fg_chainKdfSeed, sim_fg_chainKdfNext, sim_fg_spqrInitRecv, pure_bind]
      congr 1; funext ⟨drKey, roCache'⟩
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg <;> simp only [simulateQ_pure]
    · simp only [Option.map, Option.isSome, Bool.false_or, Bool.and_true,
        ↓reduceIte, simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, sim_fg_x25519,
        sim_fg_spqrInitRecv, pure_bind]
      congr 1; funext ⟨drKey, roCache'⟩
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      congr 1; funext ⟨mkSeed, ck1_1⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg <;> simp only [simulateQ_pure]
  · simp only [Option.map, Option.isSome, Bool.true_or, Bool.and_true, ↓reduceIte,
      simulateQ_bind, simulateQ_pure, sim_fg_x25519, sim_fg_pow8,
      maskMuSession_drKey, maskMuSession_ephAPk, maskMuSession_rk1,
      maskMuSession_ck1_0, maskMuSession_mkSeed, maskMuSession_ck1_1, pure_bind]
    rcases Bool.eq_false_or_eq_true (P.pow8 msg.ephAPk == P.pow8 s.ephAPk) with hE | hE
    · simp only [hE, ↓reduceIte, simulateQ_pure, sim_fg_spqrInitRecv, pure_bind]
      cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg <;> simp only [simulateQ_pure]
    · simp only [hE, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
        simulateQ_pure, sim_fg_spqrInitRecv, pure_bind]
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      congr 1; funext ⟨mkSeed, ck1_1⟩
      cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg <;> simp only [simulateQ_pure]

theorem finishErasedRecvOPK_eq_projectMuHybrid {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes)
        × (Bytes × Bytes)))) :
    finishErasedRecvOPK k j o usedTriples' (findHonestPrincipal P hstDec.base.principals
        msg.hdr.ikAPk).isSome
      (projectMuHybrid P hstDec) res? =
    Prod.map id (projectMuHybrid P)
      (finishAuthHybridRecvOPK true P k j o kEntry bEntry oEntry usedTriples' msg hstDec res?) := by
  unfold finishErasedRecvOPK finishAuthHybridRecvOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some sp =>
      rcases sp with ⟨_, senderEntry⟩
      dsimp only [Option.isSome, ↓reduceIte]
      cases !senderEntry.corrupted <;> rfl

theorem finishErasedRecvNoOPK_eq_projectMuHybrid {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes)
        × (Bytes × Bytes)))) :
    finishErasedRecvNoOPK k j l usedTriples' (findHonestPrincipal P hstDec.base.principals
        msg.hdr.ikAPk).isSome
      (projectMuHybrid P hstDec) res? =
    Prod.map id (projectMuHybrid P)
      (finishAuthHybridRecvNoOPK true P k j l kEntry bEntry usedTriples' msg hstDec res?) := by
  unfold finishErasedRecvNoOPK finishAuthHybridRecvNoOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some sp =>
      rcases sp with ⟨_, senderEntry⟩
      dsimp only [Option.isSome, ↓reduceIte]
      cases !senderEntry.corrupted <;> rfl

theorem simulateQ_finishPrepareAuthRecvPrim_mu {S : Setup} (P : Primitives)
    (kVal jVal : Nat) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkSk? opkPk? : Option Bytes)
    (mkFinish : List (Nat × UInt32 × UInt32 × Bytes) → Bool → AuthHybridState S →
      Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) → AuthResponse × AuthHybridState S)
    (msg : PreKeyMsg) (hst : AuthHybridState S)
    (hPrin : hst.base.principals.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishPrepareAuthRecvPrim S kVal jVal kEntry bEntry opkSk? opkPk? mkFinish msg
        (projectMuHybrid P hst)) =
    pure (
      let (replayOk, usedTriples') :=
        checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys kVal msg.hdr.pqspkId msg.hdr.spkId
            msg.hdr.ekAPk
      if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then none
      else match P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
      | none => none
      | some ss =>
        let rRec : RecvKemRecord := {
          k := kVal, j := jVal, pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
          kemCt := msg.hdr.kemCt, kemSs := ss }
        let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
        let dh1 := P.x25519 bEntry.spkSk msg.hdr.ikAPk
        let dh2 := P.x25519 kEntry.secIKA0 msg.hdr.ekAPk
        let dh3 := P.x25519 bEntry.spkSk msg.hdr.ekAPk
        let dh4? := opkSk?.map (fun opkSk => P.x25519 opkSk msg.hdr.ekAPk)
        let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
        some {
          kEntry := kEntry, bEntry := bEntry, opkPk? := opkPk?, secrets := secrets,
          hstDec := projectMuHybrid P hstDec,
          finish := mkFinish usedTriples'
            (findHonestPrincipal P hst.base.principals msg.hdr.ikAPk).isSome
            (projectMuHybrid P hstDec) }) := by
  unfold finishPrepareAuthRecvPrim
  have hb_kyber : (projectMuHybrid P hst).base.seenKyberBaseKeys =
      hst.base.seenKyberBaseKeys := rfl
  have hb_princ : (projectMuHybrid P hst).base.principals = hst.base.principals :=
      rfl
  dsimp only; rw [hb_kyber, hb_princ, simulateQ_bind, sim_fg_isCanonical, pure_bind,
    simulateQ_bind, sim_fg_isCanonical, pure_bind]
  by_cases h1 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys kVal msg.hdr.pqspkId
      msg.hdr.spkId msg.hdr.ekAPk).1 ||
                 !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
  · simp [h1, simulateQ_pure]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, sim_fg_kemDecaps, pure_bind]
    cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
    | none => simp [simulateQ_pure]
    | some ss =>
      dsimp only
      rw [simulateQ_bind, sim_fg_x25519, pure_bind, simulateQ_bind, sim_fg_x25519, pure_bind,
          simulateQ_bind, sim_fg_x25519, pure_bind, simulateQ_bind]
      cases opkSk? <;>
        (simp only [simulateQ_bind, sim_fg_x25519, simulateQ_pure, pure_bind,
          simulateQ_findHonestPrincipalPrim S P _ msg.hdr.ikAPk hPrin]; rfl)

theorem simulateQ_prepareAuthRecvOPKPrim_mu {S : Setup} (P : Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S)
    (hPrin : hst.base.principals.length ≤ S.N_dh)
    (hNoWin : hst.base.hasWonAuth = false) :
    simulateQ (primBaseImpl P)
        (prepareAuthRecvOPKPrim S k j o msg (projectMuHybrid P hst)) =
      pure ((prepareAuthHybridRecvOPK true P k j o msg hst).map (fun prep =>
        { kEntry  := prep.kEntry
          bEntry  := prep.bEntry
          opkPk?  := prep.opkPk?
          secrets := prep.secrets
          hstDec  := projectMuHybrid P prep.hstDec
          finish  := fun res? => Prod.map id (projectMuHybrid P) (prep.finish res?)
              })) := by
  unfold prepareAuthRecvOPKPrim prepareAuthHybridRecvOPK
  have hb_used : (projectMuHybrid P hst).base.usedRecvOPK = hst.base.usedRecvOPK :=
      rfl
  have hb_princ : (projectMuHybrid P hst).base.principals = hst.base.principals :=
      rfl
  have hb_adv : (projectMuHybrid P hst).base.advKeys =
      hst.base.advKeys.map (fun (_, pk) => (P.pow8 pk, pk)) := rfl
  have hb_spk : (projectMuHybrid P hst).base.spkBundles = hst.base.spkBundles := rfl
  have hb_opk : (projectMuHybrid P hst).base.opkEntries = hst.base.opkEntries := rfl
  dsimp only; simp only [hNoWin, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  rw [hb_used, hb_princ, hb_adv, hb_spk, hb_opk]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == some (UInt32.ofNat o.val) && msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, simulateQ_pure, Option.map]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [h2, ↓reduceIte, simulateQ_pure, Option.map]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      rw [simulateQ_bind,
          simulateQ_koskSenderOkPrim S P _ _ msg.hdr.ikAPk hPrin (validAdvKeysPow8_map P _),
          koskSenderOk_map_advKeys, pure_bind]
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, simulateQ_pure, Option.map]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp [simulateQ_pure]
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp [simulateQ_pure]
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none => simp [simulateQ_pure]
            | some op =>
              rcases op with ⟨_, oEntry⟩
              dsimp only
              by_cases h4 : oEntry.consumed = true
              · simp only [h4, ↓reduceIte, simulateQ_pure, Option.map]
              · simp only [h4, Bool.false_eq_true, ↓reduceIte,
                  simulateQ_finishPrepareAuthRecvPrim_mu P k.val j.val kEntry bEntry
                    (some oEntry.opkSk) (some oEntry.opkPk) (finishErasedRecvOPK k j o)
                        msg hst hPrin]
                congr 1
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                    msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                               !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [h5, ↓reduceIte, Option.map]
                · simp only [h5, Bool.false_eq_true, ↓reduceIte]
                  cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none => rfl
                  | some ss =>
                    dsimp only [Option.map]; congr 1; congr 1; funext res?
                    exact finishErasedRecvOPK_eq_projectMuHybrid P k j o kEntry
                        bEntry oEntry _ msg _ res?

theorem simulateQ_prepareAuthRecvNoOPKPrim_mu {S : Setup} (P : Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S)
    (hPrin : hst.base.principals.length ≤ S.N_dh)
    (hNoWin : hst.base.hasWonAuth = false) :
    simulateQ (primBaseImpl P)
        (prepareAuthRecvNoOPKPrim S k j l msg (projectMuHybrid P hst)) =
      pure ((prepareAuthHybridRecvNoOPK true P k j l msg hst).map (fun prep =>
        { kEntry  := prep.kEntry
          bEntry  := prep.bEntry
          opkPk?  := prep.opkPk?
          secrets := prep.secrets
          hstDec  := projectMuHybrid P prep.hstDec
          finish  := fun res? => Prod.map id (projectMuHybrid P) (prep.finish res?)
              })) := by
  unfold prepareAuthRecvNoOPKPrim prepareAuthHybridRecvNoOPK
  have hb_used : (projectMuHybrid P hst).base.usedRecvNoOPK = hst.base.usedRecvNoOPK
      := rfl
  have hb_princ : (projectMuHybrid P hst).base.principals = hst.base.principals :=
      rfl
  have hb_adv : (projectMuHybrid P hst).base.advKeys =
      hst.base.advKeys.map (fun (_, pk) => (P.pow8 pk, pk)) := rfl
  have hb_spk : (projectMuHybrid P hst).base.spkBundles = hst.base.spkBundles := rfl
  dsimp only; simp only [hNoWin, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  rw [hb_used, hb_princ, hb_adv, hb_spk]
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == none && msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, simulateQ_pure, Option.map]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [h2, ↓reduceIte, simulateQ_pure, Option.map]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      rw [simulateQ_bind,
          simulateQ_koskSenderOkPrim S P _ _ msg.hdr.ikAPk hPrin (validAdvKeysPow8_map P _),
          koskSenderOk_map_advKeys, pure_bind]
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, simulateQ_pure, Option.map]
      · simp only [h3, Bool.false_eq_true, ↓reduceIte]
        cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp [simulateQ_pure]
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp [simulateQ_pure]
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            dsimp only
            rw [simulateQ_finishPrepareAuthRecvPrim_mu P k.val j.val kEntry bEntry
                  none none (finishErasedRecvNoOPK k j l) msg hst hPrin]
            congr 1
            by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                msg.hdr.spkId msg.hdr.ekAPk).1 ||
                           !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
            · simp only [h5, ↓reduceIte, Option.map]
            · simp only [h5, Bool.false_eq_true, ↓reduceIte]
              cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => rfl
              | some ss =>
                dsimp only [Option.map]; congr 1; congr 1; funext res?
                exact finishErasedRecvNoOPK_eq_projectMuHybrid P k j l kEntry bEntry
                    _ msg _ res?

theorem prepareAuthHybridRecvOPK_valid_mu {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (hV : ValidAuthLengths S hst)
    {prep : PreparedAuthRecv S}
    (hp : prepareAuthHybridRecvOPK checkAuth P k j o msg hst = some prep) :
    prep.hstDec.base.principals = hst.base.principals ∧
    prep.hstDec.base.usedSendSessions = hst.base.usedSendSessions ∧
    prep.hstDec.idealSessions = hst.idealSessions ∧
    ∀ res?, ValidAuthLengths S (prep.finish res?).2 ∧
      (prep.finish res?).2.base.usedSendSessions = hst.base.usedSendSessions ∧
      (prep.finish res?).2.idealSessions = hst.idealSessions := by
  unfold prepareAuthHybridRecvOPK at hp
  have h0 : (checkAuth && hst.base.hasWonAuth) = false := by
    cases h : (checkAuth && hst.base.hasWonAuth) <;> simp [h] at hp ⊢
  simp only [h0, Bool.false_eq_true, ↓reduceIte] at hp
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == some (UInt32.ofNat o.val) && msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, reduceCtorEq] at hp
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hp
    by_cases h2 : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [h2, ↓reduceIte, reduceCtorEq] at hp
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hp
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, reduceCtorEq] at hp
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hp
        cases hf1 : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp only [hf1, reduceCtorEq] at hp
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hf2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp only [hf1, hf2, reduceCtorEq] at hp
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            cases hf3 : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
                with
            | none => simp only [hf1, hf2, hf3, reduceCtorEq] at hp
            | some op =>
              rcases op with ⟨_, oEntry⟩
              simp only [hf1, hf2, hf3] at hp
              by_cases h4 : oEntry.consumed = true
              · simp only [h4, ↓reduceIte, reduceCtorEq] at hp
              · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hp
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                    msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                               !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [h5, ↓reduceIte, reduceCtorEq] at hp
                · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hp
                  cases hkem : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none => simp only [hkem, reduceCtorEq] at hp
                  | some ss =>
                    simp only [hkem, Option.some.injEq] at hp
                    subst hp; refine ⟨rfl, rfl, rfl, fun res? => ?_⟩
                    unfold finishAuthHybridRecvOPK; dsimp only
                    cases res? with
                    | none => exact ⟨hV, rfl, rfl⟩
                    | some r =>
                      rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
                      have hVO' := (validOpkEntries_map_consumed S P (k.val, j.val, o.val)
                          hst.base.opkEntries hV.2.2.1).1
                      cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                      | none => exact ⟨⟨hV.1, hV.2.1, hVO', hV.2.2.2.1, hV.2.2.2.2⟩, rfl, rfl⟩
                      | some sp =>
                        rcases sp with ⟨_, senderEntry⟩; dsimp only
                        split_ifs <;> exact ⟨⟨hV.1, hV.2.1, hVO', hV.2.2.2.1, hV.2.2.2.2⟩, rfl, rfl⟩

theorem prepareAuthHybridRecvNoOPK_valid_mu {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) (hV : ValidAuthLengths S hst)
    {prep : PreparedAuthRecv S}
    (hp : prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst = some prep) :
    prep.hstDec.base.principals = hst.base.principals ∧
    prep.hstDec.base.usedSendSessions = hst.base.usedSendSessions ∧
    prep.hstDec.idealSessions = hst.idealSessions ∧
    ∀ res?, ValidAuthLengths S (prep.finish res?).2 ∧
      (prep.finish res?).2.base.usedSendSessions = hst.base.usedSendSessions ∧
      (prep.finish res?).2.idealSessions = hst.idealSessions := by
  unfold prepareAuthHybridRecvNoOPK at hp
  have h0 : (checkAuth && hst.base.hasWonAuth) = false := by
    cases h : (checkAuth && hst.base.hasWonAuth) <;> simp [h] at hp ⊢
  simp only [h0, Bool.false_eq_true, ↓reduceIte] at hp
  by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
                   msg.hdr.opkId? == none && msg.hdr.ikAPk.length == 32 &&
                   msg.hdr.ekAPk.length == 32 && msg.ephAPk.length == 32)) = true
  · simp only [h1, ↓reduceIte, reduceCtorEq] at hp
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hp
    by_cases h2 : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [h2, ↓reduceIte, reduceCtorEq] at hp
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hp
      by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
      · simp only [h3, ↓reduceIte, reduceCtorEq] at hp
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hp
        cases hf1 : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none => simp only [hf1, reduceCtorEq] at hp
        | some kp =>
          rcases kp with ⟨_, kEntry⟩
          cases hf2 : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none => simp only [hf1, hf2, reduceCtorEq] at hp
          | some bp =>
            rcases bp with ⟨_, bEntry⟩
            simp only [hf1, hf2] at hp
            by_cases h4 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                msg.hdr.spkId msg.hdr.ekAPk).1 ||
                           !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
            · simp only [h4, ↓reduceIte, reduceCtorEq] at hp
            · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hp
              cases hkem : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
              | none => simp only [hkem, reduceCtorEq] at hp
              | some ss =>
                simp only [hkem, Option.some.injEq] at hp
                subst hp; refine ⟨rfl, rfl, rfl, fun res? => ?_⟩
                unfold finishAuthHybridRecvNoOPK; dsimp only
                cases res? with
                | none => exact ⟨hV, rfl, rfl⟩
                | some r =>
                  rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩; dsimp only
                  cases findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
                  | none => exact ⟨hV, rfl, rfl⟩
                  | some sp =>
                    rcases sp with ⟨_, senderEntry⟩; dsimp only
                    split_ifs <;> exact ⟨hV, rfl, rfl⟩

theorem simulateQ_stepAuthOtherPrim_projectMuState
    {S : Setup} (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    (hNotSend : ¬isAuthSendQuery (Sum.inr q))
    (hNotRecv : ¬isAuthRecvQuery (Sum.inr q))
    (hNoWin : hst.toAuthHybridState.base.hasWonAuth = false) :
    simulateQ (primBaseImpl P) (stepAuthOtherPrim true S q (projectMuState P hst)) =
      Prod.map id (projectMuState P) <$>
        ((pqxdhAuthHybridSplitFixedImpl .g3_8 .g3_8 true true S P q).run hst) := by
  have hStage : (AuthHybridStage.g3_8).idealMsgKeys = true := rfl
  unfold stepAuthOtherPrim pqxdhAuthHybridSplitFixedImpl pqxdhAuthHybridKoskImpl
    liftAuthBase pqxdhAuthImpl registerAdvKey projectMuState projectMuHybrid eraseAuthEvents
  cases q with
  | sendOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | sendNoOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | recvOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | recvNoOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | initPrin u =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
        simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]; rfl
    · simp [StateT.run_pure, Prod.map]
  | corruptIK u =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_set, StateT.run_pure, Prod.map]
  | genSPK u j =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, Prod.map]
      | some p =>
        rcases p with ⟨_, uEntry⟩; dsimp only
        simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_sampleKemKeyGenPrim,
          simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]; rfl
    · simp [StateT.run_pure, Prod.map]
  | genOPK u j o =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases hst.toAuthHybridState.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
        simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]; rfl
    · simp [StateT.run_pure, Prod.map]
  | registerKey sk =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc]
    cases (sk.length != 32)
    · simp only [Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_pure, pure_bind,
        StateT.run_bind, StateT.run_set,
        StateT.run_pure, map_pure, Prod.map]; rfl
    · simp only [↓reduceIte, simulateQ_pure, StateT.run_pure, pure_bind, map_pure, Prod.map, id_eq]
  | roQuery secrets =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      simulateQ_bind, simulateQ_evalHkdfOrRoPrim, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]; rfl
  | roRootQuery rk dh =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      simulateQ_bind, simulateQ_embedUnif, evalRootKdfOrRo_true_eq_pure, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]; rfl
  | revealDhSecrets =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, simulateQ_pure, map_pure, Prod.map]; rfl

theorem validAuthLengths_stepAuthOther_mu
    {S : Setup} (P : Primitives) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hNotSend : ¬isAuthSendQuery (Sum.inr q))
    (hNotRecv : ¬isAuthRecvQuery (Sum.inr q))
    (hNoWin : hst.toAuthHybridState.base.hasWonAuth = false)
    (hV : ValidAuthLengths S hst.toAuthHybridState)
    {y : (authSpec S).Range q × AuthHybridStateFixed S}
    (hy : y ∈ support ((pqxdhAuthHybridSplitFixedImpl .g3_8 .g3_8 true true S P q).run hst)) :
    ValidAuthLengths S y.2.toAuthHybridState ∧
    y.2.toAuthHybridState.base.usedSendSessions = hst.toAuthHybridState.base.usedSendSessions ∧
    y.2.toAuthHybridState.idealSessions = hst.toAuthHybridState.idealSessions ∧
    y.2.recvCount = hst.recvCount ∧
    y.2.mkSaltCache = hst.mkSaltCache := by
  have hStage : (AuthHybridStage.g3_8).idealMsgKeys = true := rfl
  rcases hV with ⟨hVP, hVS, hVO, hVSess, hIdealLe⟩
  unfold pqxdhAuthHybridSplitFixedImpl pqxdhAuthHybridKoskImpl liftAuthBase pqxdhAuthImpl
      registerAdvKey at hy
  cases q with
  | sendOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | sendNoOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | recvOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | recvNoOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | initPrin u =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hFresh : hst.toAuthHybridState.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [hFresh, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨secIKA0, _, secIKAsign, _, rfl⟩
      exact ⟨⟨(validPrincipals_cons S u _ hst.toAuthHybridState.base.principals hVP hFresh).1,
        hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    · simp only [hFresh, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | corruptIK u =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hFind : hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [hFind, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    | some p =>
      rcases p with ⟨_, entry⟩
      simp only [hFind, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨⟨(validPrincipals_map_corrupted S P u.val hst.toAuthHybridState.base.principals hVP).1,
        hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | genSPK u j =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hFresh : hst.toAuthHybridState.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [hFresh, Bool.false_eq_true, ↓reduceIte] at hy
      cases hFind : hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [hFind, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
      | some p =>
        rcases p with ⟨_, uEntry⟩
        simp only [hFind, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
        rcases hy with ⟨spkSk, _, rSpk, _, kemCoins, _, rPq, _, rfl⟩
        exact ⟨⟨hVP,
            (validSpkBundles_cons S u j _ hst.toAuthHybridState.base.spkBundles hVS hFresh).1,
          hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    · simp only [hFresh, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | genOPK u j o =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hFresh : hst.toAuthHybridState.base.opkEntries.any (fun (k, _) => k == (u.val, j.val,
        o.val))
    · simp only [hFresh, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
      rcases hy with ⟨opkSk, _, rfl⟩
      exact ⟨⟨hVP, hVS,
          (validOpkEntries_cons S u j o _ hst.toAuthHybridState.base.opkEntries hVO hFresh).1,
        hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    · simp only [hFresh, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | registerKey sk =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc] at hy
    cases hLen : (sk.length != 32)
    · simp only [hLen, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
    · simp only [hLen, ↓reduceIte, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff]
        at hy
      subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | roQuery secrets =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨dk, roCache'⟩, _, rfl⟩
    exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | roRootQuery rk dh =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨out, rootRoCache'⟩, _, rfl⟩
    exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩
  | revealDhSecrets =>
    simp only [hStage, hNoWin, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact ⟨⟨hVP, hVS, hVO, hVSess, hIdealLe⟩, rfl, rfl, rfl, rfl⟩

end SignalPqxdh.Security
