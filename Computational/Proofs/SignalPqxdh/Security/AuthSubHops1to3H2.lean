/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H1
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section
open OracleComp OracleSpec MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh
namespace SignalPqxdh.Security.AuthSubHops1to3
private theorem option_eq_none_or_eq_some {α : Type} (o : Option α) :
    o = none ∨ ∃ a, o = some a := by
  cases o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩
private theorem bool_eq_false_or_eq_true (b : Bool) :
    b = false ∨ b = true := by
  cases b <;> simp
private theorem forall_support_bind {α β : Type} (m : ProbComp α) (f : α → ProbComp β)
  (P : β → Prop)
    (h : ∀ a, ∀ b ∈ support (f a), P b) :
    ∀ b ∈ support (m >>= f), P b := by
  intro b hb
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hb
  rcases hb with ⟨a, _, hb⟩
  exact h a b hb
private theorem forall_support_pure {α : Type} (x : α) (P : α → Prop) (h : P x) :
    ∀ b ∈ support (pure x : ProbComp α), P b := by
  intro b hb
  rw [support_pure, Set.mem_singleton_iff] at hb
  exact hb ▸ h
def eraseIdealCk1_0MkSeed {S : Setup} (s : IdealAuthSession S) : IdealAuthSession S :=
  { s with ck1_0 := [], mkSeed := [] }
def eraseAuthCk1_0MkSeed {S : Setup} (hst : AuthHybridState S) : AuthHybridState S :=
  { hst with idealSessions := hst.idealSessions.map eraseIdealCk1_0MkSeed }
def eraseAuthFixedCk1_0MkSeed {S : Setup} (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { toAuthHybridState := eraseAuthCk1_0MkSeed hst.toAuthHybridState
    recvCount := hst.recvCount
    mkSaltCache := hst.mkSaltCache }
@[simp] theorem eraseAuthCk1_0MkSeed_base {S : Setup} (hst : AuthHybridState S) :
    (eraseAuthCk1_0MkSeed hst).base = hst.base := rfl
@[simp] theorem eraseAuthCk1_0MkSeed_initKemRecs {S : Setup} (hst : AuthHybridState S) :
    (eraseAuthCk1_0MkSeed hst).initKemRecs = hst.initKemRecs := rfl
@[simp] theorem eraseAuthCk1_0MkSeed_recvKemRecs {S : Setup} (hst : AuthHybridState S) :
    (eraseAuthCk1_0MkSeed hst).recvKemRecs = hst.recvKemRecs := rfl
@[simp] theorem eraseAuthCk1_0MkSeed_idealSessions {S : Setup} (hst : AuthHybridState S) :
    (eraseAuthCk1_0MkSeed hst).idealSessions = hst.idealSessions.map eraseIdealCk1_0MkSeed := rfl
@[simp] theorem finalizeAuthFixed_eraseAuthCk1_0MkSeed {S : Setup} (P : Primitives) (secb b' : Bool)
    (hst : AuthHybridState S) :
    finalizeAuthFixed P secb b' (eraseAuthCk1_0MkSeed hst) = finalizeAuthFixed P secb b' hst := rfl
@[simp] theorem matchIdealAuthHandshake_eraseIdealCk1_0MkSeed {S : Setup} (P : Primitives)
    (ikBPk spkBPk : Bytes) (opkPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (s : IdealAuthSession S) :
    matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr (eraseIdealCk1_0MkSeed s) =
      matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr s := rfl
@[simp] theorem find?_matchIdealAuthHandshake_eraseIdealCk1_0MkSeed {S : Setup} (P : Primitives)
    (ikBPk spkBPk : Bytes) (opkPk? : Option Bytes) (pqspkBPk : Bytes)
    (hdr : HandshakeHdr) (l : List (IdealAuthSession S)) :
    (l.map eraseIdealCk1_0MkSeed).find? (matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr)
      =
      (l.find? (matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr)).map
        eraseIdealCk1_0MkSeed := by
  induction l with
  | nil => rfl
  | cons s tl ih =>
    simp only [List.map_cons, List.find?_cons, matchIdealAuthHandshake_eraseIdealCk1_0MkSeed]
    cases matchIdealAuthHandshake P ikBPk spkBPk opkPk? pqspkBPk hdr s
    · exact ih
    · rfl
@[simp] theorem match_sameEph_map_eraseIdealCk1_0MkSeed {S : Setup} (P : Primitives)
    (ms? : Option (IdealAuthSession S)) (ephAPk : Bytes) : (match ms?.map eraseIdealCk1_0MkSeed with
     | some s => P.pow8 ephAPk == P.pow8 s.ephAPk
     | none => false) =
    (match ms? with
     | some s => P.pow8 ephAPk == P.pow8 s.ephAPk
     | none => false) := by
  cases ms? <;> rfl
def erasePreparedAuthRecvMk {S : Setup} (prep : PreparedAuthRecv S) : PreparedAuthRecv S :=
  { prep with
    hstDec := eraseAuthCk1_0MkSeed prep.hstDec
    matchedSess? := prep.matchedSess?.map eraseIdealCk1_0MkSeed
    finish := fun res? =>
      let (resp, hst') := prep.finish res?
      (resp, eraseAuthCk1_0MkSeed hst') }
theorem finishAuthHybridRecvOPK_eraseAuthCk1_0MkSeed {S : Setup} (checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    let x := finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg hstDec
      res?
    (x.1, eraseAuthCk1_0MkSeed x.2) =
      finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg
        (eraseAuthCk1_0MkSeed hstDec) res? := by
  dsimp only [eraseAuthCk1_0MkSeed]
  unfold finishAuthHybridRecvOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      cases senderEntry.corrupted <;> rfl
theorem finishAuthHybridRecvNoOPK_eraseAuthCk1_0MkSeed {S : Setup} (checkAuth : Bool)
  (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S) (res?) :
    let x := finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec res?
    (x.1, eraseAuthCk1_0MkSeed x.2) =
      finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg
        (eraseAuthCk1_0MkSeed hstDec) res? := by
  dsimp only [eraseAuthCk1_0MkSeed]
  unfold finishAuthHybridRecvNoOPK
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none => rfl
    | some p =>
      rcases p with ⟨_, senderEntry⟩
      dsimp only
      cases senderEntry.corrupted <;> rfl
theorem prepareAuthHybridRecvOPK_eraseAuthCk1_0MkSeed {S : Setup} (checkAuth : Bool)
  (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthHybridRecvOPK checkAuth P k j o msg (eraseAuthCk1_0MkSeed hst) =
      (prepareAuthHybridRecvOPK checkAuth P k j o msg hst).map erasePreparedAuthRecvMk := by
  unfold prepareAuthHybridRecvOPK erasePreparedAuthRecvMk
  dsimp only [eraseAuthCk1_0MkSeed_base]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · split; · rfl
    split; · rfl
    split
    · rfl
    · simp only [Option.map_some, eraseAuthCk1_0MkSeed_initKemRecs,
                  eraseAuthCk1_0MkSeed_recvKemRecs,
        eraseAuthCk1_0MkSeed_idealSessions, find?_matchIdealAuthHandshake_eraseIdealCk1_0MkSeed]
      congr 2
      · exact match_sameEph_map_eraseIdealCk1_0MkSeed P _ _
      · funext res?
        apply Eq.symm
        exact finishAuthHybridRecvOPK_eraseAuthCk1_0MkSeed checkAuth P k j o _ _ _ _ msg _ res?
  · rfl
theorem prepareAuthHybridRecvNoOPK_eraseAuthCk1_0MkSeed {S : Setup} (checkAuth : Bool)
  (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (hst : AuthHybridState S) :
    prepareAuthHybridRecvNoOPK checkAuth P k j l msg (eraseAuthCk1_0MkSeed hst) =
      (prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst).map erasePreparedAuthRecvMk := by
  unfold prepareAuthHybridRecvNoOPK erasePreparedAuthRecvMk
  dsimp only [eraseAuthCk1_0MkSeed_base]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · split; · rfl
    split
    · rfl
    · simp only [Option.map_some, eraseAuthCk1_0MkSeed_initKemRecs,
                  eraseAuthCk1_0MkSeed_recvKemRecs,
        eraseAuthCk1_0MkSeed_idealSessions, find?_matchIdealAuthHandshake_eraseIdealCk1_0MkSeed]
      congr 2
      · exact match_sameEph_map_eraseIdealCk1_0MkSeed P _ _
      · funext res?
        apply Eq.symm
        exact finishAuthHybridRecvNoOPK_eraseAuthCk1_0MkSeed checkAuth P k j l _ _ _ msg _ res?
  · rfl
def InvMkIdealSid {S : Setup} (hst : AuthHybridState S) : Prop :=
  ∀ s ∈ hst.idealSessions, sessionSlotIndex s.sid < S.N_sess_tot
theorem invMkIdealSid_empty (S : Setup) (secb : Bool) :
    InvMkIdealSid (AuthHybridState.empty S secb) := by
  intro s hs; cases hs
theorem invMkIdealSid_finishAuthHybridSend {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (isFreshPeer : Bool)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes) (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) (hst : AuthHybridState S)
    (hSid : sessionSlotIndex sid < S.N_sess_tot) (hInv : InvMkIdealSid hst) :
    InvMkIdealSid (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
      spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst).2 := by
  unfold finishAuthHybridSend InvMkIdealSid
  dsimp only
  split
  · intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hSid
    · exact hInv s hs
  · exact hInv
theorem invMkIdealSid_runAuthHybridSendKosk_g3_8 {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) (hSid : sessionSlotIndex sid < S.N_sess_tot)
    (hInv : InvMkIdealSid hst) :
    ∀ x ∈ support ((runAuthHybridSendKosk .g3_8 true S P sid u bundle m0 m1).run hst),
      InvMkIdealSid x.2 := by
  rw [runAuthHybridSendKosk_eq]
  simp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
    AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys, AuthHybridStage.idealFreshAead,
    Bool.and_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases bool_eq_false_or_eq_true (m0.length != m1.length) with h1 | h1 <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
  · rcases bool_eq_false_or_eq_true (hst.base.usedSendSessions.contains sid) with h2 | h2 <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
    · rcases option_eq_none_or_eq_some (hst.base.principals.find? (fun x => x.1 == u.val)) with h3 |
        ⟨⟨_, uEntry⟩, h3⟩ <;>
        rw [h3]
      · exact forall_support_pure _ _ hInv
      · dsimp only
        rcases option_eq_none_or_eq_some (findHonestPrincipal P hst.base.principals bundle.ikB) with
          hpeer | ⟨⟨pIdx, pEntry⟩, hpeer⟩ <;>
          rw [hpeer] <;> dsimp only
        · rcases bool_eq_false_or_eq_true (m0 != m1) with hm | hm <;>
            simp only [hm, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
          · rcases bool_eq_false_or_eq_true (!koskBundleOk P hst.base.principals hst.base.spkBundles
                                              hst.base.opkEntries hst.base.advKeys bundle) with hk |
                                                hk <;>
              simp only [hk, Bool.false_eq_true, ↓reduceIte]
            · refine forall_support_bind _ _ _ (fun ekASk => ?_)
              refine forall_support_bind _ _ _ (fun kemCoins => ?_)
              refine forall_support_bind _ _ _ (fun ephASk => ?_)
              refine forall_support_bind _ _ _ (fun spqrCoins => ?_)
              rcases bool_eq_false_or_eq_true (!(P.sigVerify
                                                  (resolveSigPk P hst.base.principals bundle.ikB)
                                                    (encodeEC bundle.spkB) bundle.spkSig &&
                       P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                         (encodeKEM bundle.pqspkB) bundle.pqspkSig)) with hsig | hsig <;>
                simp only [hsig, Bool.false_eq_true, ↓reduceIte]
              · rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
                · exact forall_support_pure _ _ hInv
                · simp only [Option.isSome, Bool.false_and, Bool.or_false, Bool.false_eq_true,
                              ↓reduceIte]
                  refine forall_support_bind _ _ _ (fun ⟨drKey, roCache'⟩ => ?_)
                  refine forall_support_bind _ _ _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
                  rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ |
                    ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                  · exact forall_support_pure _ _ hInv
                  · exact forall_support_pure _ _ (invMkIdealSid_finishAuthHybridSend P sid uEntry _
                                                    _ bundle m0 m1
                      ekASk _ ss kemCt ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg _ _ _ _
                        roCache' rootRoCache' hst hSid hInv)
              · exact forall_support_pure _ _ hInv
            · exact forall_support_pure _ _ hInv
          · exact forall_support_pure _ _ hInv
        · rcases bool_eq_false_or_eq_true (! !pEntry.corrupted && (m0 != m1)) with hm | hm <;>
            simp only [hm, Bool.false_eq_true, ↓reduceIte]
          · rcases bool_eq_false_or_eq_true (!koskBundleOk P hst.base.principals hst.base.spkBundles
                                              hst.base.opkEntries hst.base.advKeys bundle) with hk |
                                                hk <;>
              simp only [hk, Bool.false_eq_true, ↓reduceIte]
            · refine forall_support_bind _ _ _ (fun ekASk => ?_)
              refine forall_support_bind _ _ _ (fun kemCoins => ?_)
              refine forall_support_bind _ _ _ (fun ephASk => ?_)
              refine forall_support_bind _ _ _ (fun spqrCoins => ?_)
              rcases bool_eq_false_or_eq_true (!(P.sigVerify
                                                  (resolveSigPk P hst.base.principals bundle.ikB)
                                                    (encodeEC bundle.spkB) bundle.spkSig &&
                       P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                         (encodeKEM bundle.pqspkB) bundle.pqspkSig)) with hsig | hsig <;>
                simp only [hsig, Bool.false_eq_true, ↓reduceIte]
              · rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
                · exact forall_support_pure _ _ hInv
                · dsimp only
                  rcases bool_eq_false_or_eq_true
                    (!pEntry.corrupted ||
                     ((some (pIdx, pEntry)).isSome &&
                      checkBundleSpkHonIdeal P hst.base.principals hst.base.spkBundles bundle &&
                      (checkBundleProvenanceExact P hst.base.principals hst.base.spkBundles
                        hst.base.opkEntries bundle).2.2)) with hIdeal | hIdeal <;>
                    simp only [hIdeal, Bool.false_eq_true, ↓reduceIte]
                  · refine forall_support_bind _ _ _ (fun ⟨drKey, roCache'⟩ => ?_)
                    refine forall_support_bind _ _ _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
                    rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ |
                      ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                    · exact forall_support_pure _ _ hInv
                    · exact forall_support_pure _ _ (invMkIdealSid_finishAuthHybridSend P sid uEntry
                                                      _ _ bundle m0 m1
                        ekASk _ ss kemCt ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg _ _ _ _
                          roCache' rootRoCache' hst hSid hInv)
                  · refine forall_support_bind _ _ _ (fun drKey => ?_)
                    refine forall_support_bind _ _ _ (fun rk1 => ?_)
                    refine forall_support_bind _ _ _ (fun ck1_0 => ?_)
                    refine forall_support_bind _ _ _ (fun ms => ?_)
                    refine forall_support_bind _ _ _ (fun cn => ?_)
                    rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ |
                      ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
                    · exact forall_support_pure _ _ hInv
                    · dsimp only
                      refine forall_support_bind _ _ _ (fun deriveMessageKeys => ?_)
                      exact forall_support_pure _ _ (invMkIdealSid_finishAuthHybridSend P sid uEntry
                                                      _ _ bundle m0 m1
                        ekASk _ ss kemCt ephASk _ drKey rk1 ck1_0 ms cn spqrSalt? pqRatchetMsg
                          deriveMessageKeys _ _ _ _ _ hst hSid hInv)
              · exact forall_support_pure _ _ hInv
            · exact forall_support_pure _ _ hInv
          · exact forall_support_pure _ _ hInv
    · exact forall_support_pure _ _ hInv
  · exact forall_support_pure _ _ hInv
theorem evalDist_send_g3_8_eq_authMkSendWith_end {S : Setup}
    (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (hst : AuthHybridStateFixed S)
    (hCut : decide (sessionSlotIndex sid < S.N_sess_tot) = true)
    (hWon : hst.base.hasWonAuth = false)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[(do
        let (resp, hst') ← (runAuthHybridSendKosk .g3_8 true S P sid u bundle m0 m1).run
          hst.toAuthHybridState
        k (resp, eraseAuthFixedCk1_0MkSeed { toAuthHybridState := hst', recvCount := hst.recvCount,
                                             mkSaltCache := hst.mkSaltCache }))] =
      𝒟[authMkSendWith S P (fun _ => sampleBytes32) (fun s => decide (s < S.N_sess_tot))
          sid u bundle m0 m1 (eraseAuthFixedCk1_0MkSeed hst) >>= k] := by
  rw [runAuthHybridSendKosk_eq]
  unfold authMkSendWith prepareAuthSendMk finishAuthSendAfterMk
  dsimp only [eraseAuthFixedCk1_0MkSeed, eraseAuthCk1_0MkSeed_base]
  simp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk, AuthHybridStage.idealCk,
    AuthHybridStage.idealMsgKeys, AuthHybridStage.idealFreshAead, hCut, hWon,
    Bool.and_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases bool_eq_false_or_eq_true (m0.length != m1.length) with h1 | h1 <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases bool_eq_false_or_eq_true (hst.base.usedSendSessions.contains sid) with h2 | h2 <;>
    simp only [h2, Bool.false_eq_true, ↓reduceIte, pure_bind]
  rcases option_eq_none_or_eq_some (hst.base.principals.find? (fun x => x.1 == u.val)) with h3 |
    ⟨⟨_, uEntry⟩, h3⟩ <;>
    rw [h3]
  · simp only [pure_bind]
  · dsimp only
    rcases option_eq_none_or_eq_some (findHonestPrincipal P hst.base.principals bundle.ikB) with
      hpeer | ⟨⟨pIdx, pEntry⟩, hpeer⟩ <;>
      rw [hpeer] <;> dsimp only
    · rcases bool_eq_false_or_eq_true (m0 != m1) with hm | hm <;>
        simp only [hm, Bool.not_false, Bool.and_false, Bool.and_true,
          Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases bool_eq_false_or_eq_true (!koskBundleOk P hst.base.principals hst.base.spkBundles
          hst.base.opkEntries hst.base.advKeys bundle) with hk | hk <;>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ekASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemCoins _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ephASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spqrCoins _ => ?_)
      rcases bool_eq_false_or_eq_true (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                                          (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                 bundle.pqspkSig)) with hsig | hsig <;>
        simp only [hsig, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
      · simp only [pure_bind]
      · dsimp only
        simp only [Option.isSome, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                    bind_assoc]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
        refine OracleComp.evalDist_bind_congr_of_support _ _ _
          (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
        rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
        · simp only [pure_bind]
        · unfold finishAuthHybridSend eraseAuthCk1_0MkSeed eraseIdealCk1_0MkSeed
          dsimp only
          simp only [Option.isSome, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                      pure_bind]
    · rcases bool_eq_false_or_eq_true (! !pEntry.corrupted && (m0 != m1)) with hm | hm <;>
        simp only [hm, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases bool_eq_false_or_eq_true (!koskBundleOk P hst.base.principals hst.base.spkBundles
          hst.base.opkEntries hst.base.advKeys bundle) with hk | hk <;>
        simp only [hk, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ekASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemCoins _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ephASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spqrCoins _ => ?_)
      rcases bool_eq_false_or_eq_true (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                                          (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                 bundle.pqspkSig)) with hsig | hsig <;>
        simp only [hsig, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rcases P.kemEncaps bundle.pqspkB kemCoins with _ | ⟨ss, kemCt⟩
      · simp only [pure_bind]
      · dsimp only
        rcases bool_eq_false_or_eq_true
          (!pEntry.corrupted ||
           ((some (pIdx, pEntry)).isSome &&
            checkBundleSpkHonIdeal P hst.base.principals hst.base.spkBundles bundle &&
            (checkBundleProvenanceExact P hst.base.principals hst.base.spkBundles
              hst.base.opkEntries bundle).2.2)) with hIdeal | hIdeal <;>
          simp only [hIdeal, 
            Bool.false_eq_true, ↓reduceIte, bind_assoc]
        · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
          refine OracleComp.evalDist_bind_congr_of_support _ _ _
            (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
          rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
          · simp only [pure_bind]
          · unfold finishAuthHybridSend eraseAuthCk1_0MkSeed eraseIdealCk1_0MkSeed
            dsimp only
            simp only [hIdeal, Bool.false_eq_true, ↓reduceIte, pure_bind]
        · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun drKey _ => ?_)
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rk1 _ => ?_)
          unfold finishAuthSendMk finishAuthHybridSend eraseAuthCk1_0MkSeed eraseIdealCk1_0MkSeed
          dsimp only
          rcases P.spqrInitSend drKey.pqrKey spqrCoins with _ | ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
            <;> dsimp only
          · simp only [pure_bind, evalDist_sampleBytes32_bind_const]
          · simp only [hIdeal, ↓reduceIte, List.map_cons, bind_assoc, pure_bind,
                        evalDist_sampleBytes32_bind_const]
theorem pqxdhAuthHybridFixedImpl_recvOPK_eq_g3_8 {S : Setup}
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) :
    (pqxdhAuthHybridFixedImpl .g3_8 useRo checkAuth S P (.recvOPK k j o msg)).run hst =
      (match prepareAuthHybridRecvOPK checkAuth P k j o msg hst.toAuthHybridState with
       | none => pure (.noneResp, { hst with recvCount := hst.recvCount + 1 })
       | some prep => do
         let (res?, mkSaltCache') ← evalAuthFixedRecvScheduleCached .g3_8 useRo P prep.hstDec
           hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
         let (resp, hst') := prep.finish res?
         pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache :=
                       mkSaltCache' })) := by
  unfold pqxdhAuthHybridFixedImpl prepareAuthHybridRecvOPK
  simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get, pure_bind]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · rename_i kEntry heq1
    split
    · rename_i bEntry heq2
      split
      · rename_i oEntry heq3
        simp only [heq1, heq2, heq3]
        split; · rfl
        split; · rfl
        rcases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with _ | ss
        · rfl
        · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
            bind_assoc, pure_bind]
          congr 1; funext ⟨res?, mkSaltCache'⟩
          cases res? with
          | none => rfl
          | some r =>
            rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
            unfold finishAuthHybridRecvOPK
            dsimp only
            cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk with
            | none => rfl
            | some p =>
              rcases p with ⟨_, senderEntry⟩
              dsimp only
              cases senderEntry.corrupted <;> rfl
      · rename_i hno3
        split
        · rfl
        · rename_i heq
          split at heq
          · rename_i heq3'
            exact False.elim (hno3 _ _ heq3')
          · cases heq
    · rename_i hno2
      split
      · rfl
      · rename_i heq
        split at heq
        · rename_i heq2' _
          exact False.elim (hno2 _ _ heq2')
        · cases heq
  · rename_i hno1
    split
    · rfl
    · rename_i heq
      split at heq
      · rename_i heq1' _ _
        exact False.elim (hno1 _ _ heq1')
      · cases heq
theorem pqxdhAuthHybridFixedImpl_recvNoOPK_eq_g3_8 {S : Setup}
    (useRo checkAuth : Bool) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridStateFixed S) :
    (pqxdhAuthHybridFixedImpl .g3_8 useRo checkAuth S P (.recvNoOPK k j l msg)).run hst =
      (match prepareAuthHybridRecvNoOPK checkAuth P k j l msg hst.toAuthHybridState with
       | none => pure (.noneResp, { hst with recvCount := hst.recvCount + 1 })
       | some prep => do
         let (res?, mkSaltCache') ← evalAuthFixedRecvScheduleCached .g3_8 useRo P prep.hstDec
           hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
         let (resp, hst') := prep.finish res?
         pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount + 1, mkSaltCache :=
                       mkSaltCache' })) := by
  unfold pqxdhAuthHybridFixedImpl prepareAuthHybridRecvNoOPK
  simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get, pure_bind]
  split; · rfl
  split; · rfl
  split; · rfl
  split; · rfl
  split
  · rename_i kEntry heq1
    split
    · rename_i bEntry heq2
      simp only [heq1, heq2]
      split; · rfl
      rcases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with _ | ss
      · rfl
      · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          bind_assoc, pure_bind]
        congr 1; funext ⟨res?, mkSaltCache'⟩
        cases res? with
        | none => rfl
        | some r =>
          rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
          unfold finishAuthHybridRecvNoOPK
          dsimp only
          cases findHonestPrincipal P hst.toAuthHybridState.base.principals msg.hdr.ikAPk with
          | none => rfl
          | some p =>
            rcases p with ⟨_, senderEntry⟩
            dsimp only
            cases senderEntry.corrupted <;> rfl
    · rename_i hno2
      split
      · rfl
      · rename_i heq
        split at heq
        · rename_i heq2'
          exact False.elim (hno2 _ _ heq2')
        · cases heq
  · rename_i hno1
    split
    · rfl
    · rename_i heq
      split at heq
      · rename_i heq1' _
        exact False.elim (hno1 _ _ heq1')
      · cases heq
theorem evalAuthFixedRecvScheduleCached_g3_8_of_wf {S : Setup} (useRo : Bool)
    (P : Primitives) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S) (prep : PreparedAuthRecv S)
    (hWf : PreparedAuthRecvWf P msg hst.toAuthHybridState prep) :
    evalAuthFixedRecvScheduleCached .g3_8 useRo P prep.hstDec
      hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg = (do
      let st := prep.hstDec.base
      let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
      if prep.matchedSess?.isSome || prep.isUncorruptedHonestSender then
        match prep.matchedSess? with
        | some s =>
          if prep.sameEph then
            match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => pure (none, hst.mkSaltCache)
            | some (_pqrStB, spqrSalt?) => do
              let (deriveMessageKeys, mkSaltCache') ←
                if sameSaltKey spqrSalt? s.spqrSalt? then
                  pure (s.deriveMessageKeys, hst.mkSaltCache)
                else
                  match hst.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
                  | some (_, (_, mk)) => pure (mk, hst.mkSaltCache)
                  | none => do
                    let mk ← sampleMessageKeys80
                    pure (mk, ((s.sid, spqrSalt?), (hst.recvCount, mk)) :: hst.mkSaltCache)
              pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
                (s.drKey, s.rk1, s.ck1_1, pt, st.roCache, st.rootRoCache)), mkSaltCache')
          else do
            let r ← sampleBytes32
            let _c ← sampleBytes32
            let _ms ← sampleBytes32
            let cn ← sampleBytes32
            match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none => pure (none, hst.mkSaltCache)
            | some (_pqrStB, _spqrSalt?) => do
              let mk ← sampleMessageKeys80
              pure ((P.aeadDec mk ad msg.aeadCt).map (fun pt =>
                (s.drKey, r, cn, pt, st.roCache, st.rootRoCache)), hst.mkSaltCache)
        | none => do
          let dk ← sampleDRKey96
          let r ← sampleBytes32
          let _c ← sampleBytes32
          let _ms ← sampleBytes32
          let cn ← sampleBytes32
          match P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with
          | none => pure (none, hst.mkSaltCache)
          | some (_pqrStB, _spqrSalt?) => do
            let mk ← sampleMessageKeys80
            pure ((P.aeadDec mk ad msg.aeadCt).map (fun pt =>
              (dk, r, cn, pt, st.roCache, st.rootRoCache)), hst.mkSaltCache)
      else do
        let (drKey, roCache') ← evalHkdfOrRo useRo P st.roCache prep.secrets
        let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo useRo P st.rootRoCache drKey.rootKey
          prep.dhRatchet
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => pure (none, hst.mkSaltCache)
        | some (_pqrStB, spqrSalt?) =>
          let deriveMessageKeys := P.deriveMsgKeys (P.chainKdfSeed ck1_0) spqrSalt?
          pure ((P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
            (drKey, rk1, P.chainKdfNext ck1_0, pt, roCache', rootRoCache')), hst.mkSaltCache)) := by
  unfold evalAuthFixedRecvScheduleCached
  dsimp only
  rw [hWf.matchedSess_eq, hWf.dhRatchet_eq]
  have hU := hWf.isUncorrupted_eq
  have hE := hWf.sameEph_eq
  rcases option_eq_none_or_eq_some (findHonestPrincipal P prep.hstDec.base.principals msg.hdr.ikAPk)
    with hs | ⟨⟨_, sEntry⟩, hs⟩ <;>
    simp only [hs] at hU <;>
    rcases option_eq_none_or_eq_some prep.matchedSess? with hms | ⟨s, hms⟩
  · simp only [hs, hms, hU.symm, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
      AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
      
      Option.isSome, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      pure_bind]
    refine bind_congr (fun ⟨drKey, roCache'⟩ => ?_)
    refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
    rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
      first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · simp only [hms] at hE
    rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph <;>
      simp only [hs, hms, hU.symm, hE, hEph, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.or_false, Bool.true_and, Bool.false_and, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun r => bind_congr (fun c => bind_congr
                                               (fun ms => bind_congr (fun cn => ?_))))
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (simp only; refine bind_congr (fun mk => ?_); rcases
                        P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩
      · rfl
      · dsimp only
        rcases bool_eq_false_or_eq_true (sameSaltKey spqrSalt? s.spqrSalt?) with hSalt | hSalt <;>
          simp only [hSalt, Bool.false_eq_true,
                      ↓reduceIte]
        · cases hst.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
          | none =>
            simp only
            refine bind_congr (fun mk => ?_)
            rcases P.aeadDec _ _ _ with _ | pt <;> rfl
          | some entry =>
            rcases entry with ⟨_, _, mk⟩
            simp only
            rcases P.aeadDec _ _ _ with _ | pt <;> rfl
        · rcases P.aeadDec _ _ _ with _ | pt <;> rfl
  · rcases bool_eq_false_or_eq_true sEntry.corrupted with hsc | hsc <;>
      simp only [hs, hms, hU.symm, hsc, AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.not_false, Bool.not_true, Bool.false_or, Bool.true_and,
        Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun dk => bind_congr (fun r => bind_congr
                                                (fun c => bind_congr
                                                  (fun ms => bind_congr (fun cn => ?_)))))
      rcases P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (simp only; refine bind_congr (fun mk => ?_); rcases
                        P.aeadDec _ _ _ with _ | pt <;> rfl)
    · refine bind_congr (fun ⟨drKey, roCache'⟩ => ?_)
      refine bind_congr (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ => ?_)
      rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (dsimp only; rcases P.aeadDec _ _ _ with _ | pt <;> rfl)
  · simp only [hms] at hE
    rcases bool_eq_false_or_eq_true sEntry.corrupted with hsc | hsc <;>
      rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph <;>
      simp only [hs, hms, hU.symm, hsc, hE, hEph, AuthHybridStage.idealDrKey,
                  AuthHybridStage.idealRk,
        AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
        AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
        Option.isSome, Bool.not_false, Bool.not_true, Bool.true_or, Bool.true_and,
        Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]
    · refine bind_congr (fun r => bind_congr (fun c => bind_congr
                                               (fun ms => bind_congr (fun cn => ?_))))
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (simp only; refine bind_congr (fun mk => ?_); rcases
                        P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩
      · rfl
      · dsimp only
        rcases bool_eq_false_or_eq_true (sameSaltKey spqrSalt? s.spqrSalt?) with hSalt | hSalt <;>
          simp only [hSalt, Bool.false_eq_true,
                      ↓reduceIte]
        · cases hst.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
          | none =>
            simp only
            refine bind_congr (fun mk => ?_)
            rcases P.aeadDec _ _ _ with _ | pt <;> rfl
          | some entry =>
            rcases entry with ⟨_, _, mk⟩
            simp only
            rcases P.aeadDec _ _ _ with _ | pt <;> rfl
        · rcases P.aeadDec _ _ _ with _ | pt <;> rfl
    · refine bind_congr (fun r => bind_congr (fun c => bind_congr
                                               (fun ms => bind_congr (fun cn => ?_))))
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        first | rfl | (simp only; refine bind_congr (fun mk => ?_); rcases
                        P.aeadDec _ _ _ with _ | pt <;> rfl)
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩
      · rfl
      · dsimp only
        rcases bool_eq_false_or_eq_true (sameSaltKey spqrSalt? s.spqrSalt?) with hSalt | hSalt <;>
          simp only [hSalt, Bool.false_eq_true,
                      ↓reduceIte]
        · cases hst.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
          | none =>
            simp only
            refine bind_congr (fun mk => ?_)
            rcases P.aeadDec _ _ _ with _ | pt <;> rfl
          | some entry =>
            rcases entry with ⟨_, _, mk⟩
            simp only
            rcases P.aeadDec _ _ _ with _ | pt <;> rfl
        · rcases P.aeadDec _ _ _ with _ | pt <;> rfl
theorem evalDist_recv_schedule_g3_8_eq_authMkRecvWith_end {S : Setup}
    (P : Primitives) (msg : PreKeyMsg) (hst : AuthHybridStateFixed S) (prep : PreparedAuthRecv S)
    (hInv : InvMkIdealSid hst.toAuthHybridState)
    (hWf : PreparedAuthRecvWf P msg hst.toAuthHybridState prep)
    (hCut : S.N_send_tot + hst.recvCount < S.N_sess_tot)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[(do
        let (res?, mkSaltCache') ← evalAuthFixedRecvScheduleCached .g3_8 true P prep.hstDec
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg
        let (resp, hst') := prep.finish res?
        k (resp, { toAuthHybridState := eraseAuthCk1_0MkSeed hst', recvCount := hst.recvCount + 1,
                   mkSaltCache := mkSaltCache' }))] =
      𝒟[authMkRecvWith S P (fun _ => sampleBytes32) (fun s => decide (s < S.N_sess_tot))
          msg (some (erasePreparedAuthRecvMk prep)) (eraseAuthFixedCk1_0MkSeed hst) >>= k] := by
  rw [evalAuthFixedRecvScheduleCached_g3_8_of_wf true P msg hst prep hWf]
  have hCutD : decide (S.N_send_tot + hst.recvCount < S.N_sess_tot) = true := decide_eq_true hCut
  unfold authMkRecvWith finishAuthRecvUnmatchedAfterMk finishAuthRecvMk erasePreparedAuthRecvMk
    eraseAuthFixedCk1_0MkSeed
  dsimp only [eraseAuthCk1_0MkSeed_base]
  simp only [hCutD, ↓reduceIte]
  rcases option_eq_none_or_eq_some prep.matchedSess? with hms | ⟨s, hms⟩
  · rcases bool_eq_false_or_eq_true prep.isUncorruptedHonestSender with hU | hU
    · simp only [hms, hU, Option.isSome, Option.map, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _
        (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ => ?_)
      rcases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [pure_bind]
    · simp only [hms, hU, Option.isSome, Option.map, Bool.false_or, ↓reduceIte, bind_assoc,
                  ]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun dk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
      rcases P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [bind_assoc, pure_bind, evalDist_sampleBytes32_bind_const]
  · have hs_mem : s ∈ hst.toAuthHybridState.idealSessions :=
      hWf.idealSessions_eq ▸ List.mem_of_find?_eq_some (hWf.matchedSess_eq.trans hms)
    have hs_lt : decide (sessionSlotIndex s.sid < S.N_sess_tot) = true :=
      decide_eq_true (hInv s hs_mem)
    rcases bool_eq_false_or_eq_true prep.sameEph with hEph | hEph <;>
      simp only [hms, hs_lt, hEph, Option.isSome, Option.map, Bool.true_or, Bool.false_eq_true,
                  ↓reduceIte,
        eraseIdealCk1_0MkSeed, bind_assoc, pure_bind]
    · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun r _ => ?_)
      rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩ <;>
        simp only [bind_assoc, pure_bind, evalDist_sampleBytes32_bind_const]
    · rcases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with _ | ⟨_pqrStB, spqrSalt?⟩
      · simp only [pure_bind]
      · dsimp only
        rcases bool_eq_false_or_eq_true (sameSaltKey spqrSalt? s.spqrSalt?) with hSalt | hSalt <;>
          simp only [hSalt, Bool.false_eq_true,
                      ↓reduceIte, pure_bind]
        cases hst.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
        | none => simp only [bind_assoc, pure_bind]
        | some entry =>
          rcases entry with ⟨_, _, mk⟩
          simp only [pure_bind]
theorem step_g3_8_eq_authMkStepWith_end {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hInv : InvMkIdealSid hst.toAuthHybridState)
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(pqxdhAuthHybridFixedImpl .g3_8 true true S P q).run hst >>=
          fun x => k (x.1, eraseAuthFixedCk1_0MkSeed x.2)] =
        𝒟[(authMkCutoffImpl S P S.N_sess_tot q).run (eraseAuthFixedCk1_0MkSeed hst) >>= k]) ∧
    (∀ x ∈ support ((pqxdhAuthHybridFixedImpl .g3_8 true true S P q).run hst),
      InvMkIdealSid x.2.toAuthHybridState ∧
      x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1 else 0)) := by
  dsimp only [authMkCutoffImpl, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendOPK u i) < S.N_sess_tot := by
      have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt (.sendOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authMkStepWith]
    unfold pqxdhAuthHybridFixedImpl pqxdhAuthHybridKoskImpl
    simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun k => evalDist_send_g3_8_eq_authMkSendWith_end P (.sendOPK u i) u bundle m0 m1
                 hst
          (decide_eq_true hSid) hWon k, fun x hx => ?_⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
        exact ⟨invMkIdealSid_runAuthHybridSendKosk_g3_8 P (.sendOPK u i) u bundle m0 m1
          hst.toAuthHybridState hSid hInv (resp, hst') hmem, by dsimp only; omega⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
                    Set.mem_singleton_iff]
        refine ⟨fun _ => rfl, fun x hx => ?_⟩
        subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
        simp only [hWon, hOpt, authMkSendWith, prepareAuthSendMk, eraseAuthFixedCk1_0MkSeed,
          eraseAuthCk1_0MkSeed_base, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] <;>
        (refine ⟨fun _ => trivial, fun x hx => ?_⟩; subst hx; exact ⟨hInv, by dsimp only; omega⟩)
  | sendNoOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendNoOPK u i) < S.N_sess_tot := by
      have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt (.sendNoOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authMkStepWith]
    unfold pqxdhAuthHybridFixedImpl pqxdhAuthHybridKoskImpl
    simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    rcases bool_eq_false_or_eq_true hst.toAuthHybridState.base.hasWonAuth with hWon | hWon
    · simp only [hWon, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt
      · simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun k => evalDist_send_g3_8_eq_authMkSendWith_end P (.sendNoOPK u i) u bundle m0 m1
                 hst
          (decide_eq_true hSid) hWon k, fun x hx => ?_⟩
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
        rcases hx with ⟨⟨resp, hst'⟩, hmem, rfl⟩
        exact ⟨invMkIdealSid_runAuthHybridSendKosk_g3_8 P (.sendNoOPK u i) u bundle m0 m1
          hst.toAuthHybridState hSid hInv (resp, hst') hmem, by dsimp only; omega⟩
      · simp only [hOpt, ↓reduceIte, StateT.run_pure, pure_bind, support_pure,
                    Set.mem_singleton_iff]
        refine ⟨fun _ => rfl, fun x hx => ?_⟩
        subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
        simp only [hWon, hOpt, authMkSendWith, prepareAuthSendMk, eraseAuthFixedCk1_0MkSeed,
          eraseAuthCk1_0MkSeed_base, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] <;>
        (refine ⟨fun _ => trivial, fun x hx => ?_⟩; subst hx; exact ⟨hInv, by dsimp only; omega⟩)
  | recvOPK k' j o msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authMkStepWith]
    rw [pqxdhAuthHybridFixedImpl_recvOPK_eq_g3_8]
    have hErase : (eraseAuthFixedCk1_0MkSeed hst).toAuthHybridState = eraseAuthCk1_0MkSeed
      hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvOPK_eraseAuthCk1_0MkSeed]
    rcases option_eq_none_or_eq_some (prepareAuthHybridRecvOPK true P k' j o msg
                                       hst.toAuthHybridState) with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authMkRecvWith, eraseAuthFixedCk1_0MkSeed, pure_bind, support_pure,
                  Set.mem_singleton_iff]
      refine ⟨fun _ => trivial, fun x hx => ?_⟩
      subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvOPK_wf true P k' j o msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => evalDist_recv_schedule_g3_8_eq_authMkRecvWith_end P msg hst prep hInv hWf hLt
               k,
        fun x hx => ?_⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨res?, mkSaltCache'⟩, _, rfl⟩
      refine ⟨fun s hs => ?_, by dsimp only; omega⟩
      rw [hWf.finish_idealSessions_eq res?] at hs
      exact hInv s hs
  | recvNoOPK k' j l msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authMkStepWith]
    rw [pqxdhAuthHybridFixedImpl_recvNoOPK_eq_g3_8]
    have hErase : (eraseAuthFixedCk1_0MkSeed hst).toAuthHybridState = eraseAuthCk1_0MkSeed
      hst.toAuthHybridState := rfl
    rw [hErase, prepareAuthHybridRecvNoOPK_eraseAuthCk1_0MkSeed]
    rcases option_eq_none_or_eq_some (prepareAuthHybridRecvNoOPK true P k' j l msg
                                       hst.toAuthHybridState) with hPrep | ⟨prep, hPrep⟩ <;>
      rw [hPrep]
    · simp only [Option.map, authMkRecvWith, eraseAuthFixedCk1_0MkSeed, pure_bind, support_pure,
                  Set.mem_singleton_iff]
      refine ⟨fun _ => trivial, fun x hx => ?_⟩
      subst hx; exact ⟨hInv, by dsimp only; omega⟩
    · simp only [Option.map, bind_assoc, pure_bind]
      have hWf := prepareAuthHybridRecvNoOPK_wf true P k' j l msg hst.toAuthHybridState prep hPrep
      refine ⟨fun k => evalDist_recv_schedule_g3_8_eq_authMkRecvWith_end P msg hst prep hInv hWf hLt
               k,
        fun x hx => ?_⟩
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
      rcases hx with ⟨⟨res?, mkSaltCache'⟩, _, rfl⟩
      refine ⟨fun s hs => ?_, by dsimp only; omega⟩
      rw [hWf.finish_idealSessions_eq res?] at hs
      exact hInv s hs
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authMkStepWith]
    unfold pqxdhAuthHybridFixedImpl
    simp only [AuthHybridStage.idealMsgKeys, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      isAuthRecvQuery, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    unfold pqxdhAuthHybridKoskImpl
    dsimp only
    rw [liftAuthBase_other_eq_slots0]
    refine ⟨fun k => congrArg (fun m => 𝒟[m]) (by
        rcases bool_eq_false_or_eq_true hst.base.hasWonAuth with hWon | hWon <;>
          simp [hWon, liftAuthBase, authCkOtherStep, eraseAuthFixedCk1_0MkSeed,
            eraseAuthCk1_0MkSeed, StateT.run_bind]),
      fun x hx => ?_⟩
    obtain ⟨hId, hCnt⟩ := support_authCkOtherStep P _ { hst with slots := {} } hx
    refine ⟨fun s hs => ?_, Nat.le_trans (le_of_eq hCnt) (Nat.le_add_right _ _)⟩
    rw [hId] at hs
    exact hInv s hs
theorem evalDist_authMkCutoffExp_end_eq_g3_8 (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authMkCutoffExp S P S.N_sess_tot A.1] = 𝒟[authFixedExpAtStage .g3_8 S P A.1] := by
  symm
  unfold authFixedExpAtStage authMkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hBound : OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot
    := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  exact evalDist_simulateQ_proj_inv_bound
    (eraseAuthFixedCk1_0MkSeed (S := S)) (fun hst => InvMkIdealSid hst.toAuthHybridState)
    (fun hst => hst.recvCount) (isAuthRecvQueryB (S := S)) (fun _ => rfl)
    S.N_recv_tot
    (pqxdhAuthHybridFixedImpl .g3_8 true true S P) (authMkCutoffImpl S P S.N_sess_tot)
    (fun q hst hInv hRecv => step_g3_8_eq_authMkStepWith_end P q hst hInv hRecv)
    A.1.run
    S.N_recv_tot
    hBound
    (AuthHybridStateFixed.empty S secb) (invMkIdealSid_empty S secb)
    (by simp [AuthHybridStateFixed.empty])
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
theorem isQueryBoundP_deriveMkQ_prf (spqrSalt? : Option Bytes) :
    IsQueryBoundP (deriveMkQ spqrSalt?) (fun q => q.isRight = true) 1 :=
  (isQueryBoundP_query_iff (spec := PrfMkSimSpec) _ (Sum.inr (.derive (effectiveHkdfSaltBytes spqrSalt?))) 1).2
    (fun _ => Nat.zero_lt_one)
theorem isQueryBoundP_deriveMkQ_prim (spqrSalt? : Option Bytes) (n : Nat) :
    IsQueryBoundP (deriveMkQ spqrSalt?) (fun q => isPrimQuery q = true) n :=
  (isQueryBoundP_query_iff (spec := PrfMkSimSpec) _ (Sum.inr (.derive (effectiveHkdfSaltBytes spqrSalt?))) n).2
    (fun h => by cases h)
@[simp]
theorem runWithPrfMkStep_pure {S : Setup} {α : Type}
    (step : (q : AuthQuery S) → AuthHybridStateFixed S → Bool →
      OracleComp PrfMkSimSpec (((authSpec S).Range q × AuthHybridStateFixed S) × Bool))
    (a : α) (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    runWithPrfMkStep step (pure a) hst sentChal = pure ((a, hst), sentChal) := rfl
@[simp]
theorem runWithPrfMkStep_query_bind_inl {S : Setup} {α : Type}
    (step : (q : AuthQuery S) → AuthHybridStateFixed S → Bool →
      OracleComp PrfMkSimSpec (((authSpec S).Range q × AuthHybridStateFixed S) × Bool))
    (uq : unifSpec.Domain) (k : unifSpec.Range uq → OracleComp (unifSpec + authSpec S) α)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    runWithPrfMkStep step (liftM (OracleSpec.query (spec := unifSpec + authSpec S) (Sum.inl uq)) >>=
                            k) hst sentChal =
      (embedUnifMk (liftM (OracleSpec.query (spec := unifSpec) uq)) >>=
        fun u => runWithPrfMkStep step (k u) hst sentChal) := rfl
@[simp]
theorem runWithPrfMkStep_query_bind_inr {S : Setup} {α : Type}
    (step : (q : AuthQuery S) → AuthHybridStateFixed S → Bool →
      OracleComp PrfMkSimSpec (((authSpec S).Range q × AuthHybridStateFixed S) × Bool))
    (gq : AuthQuery S) (k : (authSpec S).Range gq → OracleComp (unifSpec + authSpec S) α)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    runWithPrfMkStep step (liftM (OracleSpec.query (spec := unifSpec + authSpec S) (Sum.inr gq)) >>=
                            k) hst sentChal =
      (step gq hst sentChal >>= fun ((resp, s'), c') => runWithPrfMkStep step (k resp) s' c') := rfl
private theorem isQueryBoundP_bind_le_mk {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    {p : ι → Prop} [DecidablePred p]
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n1 n : ℕ}
    (n2 : ℕ) (h1 : IsQueryBoundP oa p n1) (h2 : ∀ x, IsQueryBoundP (ob x) p n2)
    (hle : n1 + n2 ≤ n) :
    IsQueryBoundP (oa >>= ob) p n :=
  (isQueryBoundP_bind h1 (fun x _ => h2 x)).mono hle
theorem isQueryBoundP_authMkSendReduction_prim (S : Setup) (idx : Nat)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    IsQueryBoundP (authMkSendReduction S idx sid u bundle m0 m1 hst sentChal)
      (fun q => isPrimQuery q = true) (S.N_dh * 30 + 26) := by
  unfold authMkSendReduction
  refine isQueryBoundP_bind_le_mk (S.N_dh * 8 + 5)
    (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_prepareAuthSendMkPrim S sid u bundle m0 m1
                                               hst))
    (fun prep => ?_) (by omega)
  cases prep with
  | done resp hst' => exact isQueryBoundP_pure _ _ _
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
    pqRatchetMsg msgPlain =>
    dsimp only
    split
    · refine isQueryBoundP_bind_le_mk (S.N_dh * 8 + 5)
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
          (fun _ => ?_) (by omega)
      refine isQueryBoundP_bind_le_mk (S.N_dh * 8 + 5) (isQueryBoundP_deriveMkQ_prim spqrSalt? 0)
        (fun _ => ?_) (by omega)
      exact isQueryBoundP_bind_le_mk 0
        (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_finishAuthSendMkPrim S sid _ _ bundle
                                                   m0 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
        (fun _ => isQueryBoundP_pure _ _ _) (by omega)
    · split
      · refine isQueryBoundP_bind_le_mk (S.N_dh * 8 + 5)
          (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
            (fun _ => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (S.N_dh * 8 + 5)
          (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleMessageKeys80 0))
            (fun _ => ?_) (by omega)
        exact isQueryBoundP_bind_le_mk 0
          (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_finishAuthSendMkPrim S sid _ _
                                                     bundle m0 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
          (fun _ => isQueryBoundP_pure _ _ _) (by omega)
      · refine isQueryBoundP_bind_le_mk (S.N_dh * 8 + 5)
          (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
            (fun _ => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (S.N_dh * 8 + 5)
          (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
            (fun _ => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (S.N_dh * 8 + 4)
          (isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ _)) (fun _ => ?_) (by omega)
        exact isQueryBoundP_bind_le_mk 0
          (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_finishAuthSendMkPrim S sid _ _
                                                     bundle m0 m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
          (fun _ => isQueryBoundP_pure _ _ _) (by omega)
theorem isQueryBoundP_finishAuthRecvUnmatchedSlotsReduction_prim (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (sentChal : Bool) :
    IsQueryBoundP
      (finishAuthRecvUnmatchedSlotsReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
        mkSaltCache slots' sentChal)
      (fun q => isPrimQuery q = true) (S.N_dh * 12 + 2) := by
  unfold finishAuthRecvUnmatchedSlotsReduction
  split
  · refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 2)
      (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
        (fun _ => ?_) (by omega)
    split
    · exact isQueryBoundP_bind_le_mk (S.N_dh * 12 + 1) (isQueryBoundP_deriveMkQ_prim spqrSalt? 0)
        (fun deriveMessageKeys => isQueryBoundP_embedPrim_isPrimQuery _ _
          (primBounded_finishAuthRecvMkSlotsPrim S msg prep drKey _ _ recvCount' mkSaltCache slots' deriveMessageKeys)) (
            by omega)
    · exact isQueryBoundP_bind_le_mk (S.N_dh * 12 + 1)
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleMessageKeys80 0))
        (fun deriveMessageKeys => isQueryBoundP_embedPrim_isPrimQuery _ _
          (primBounded_finishAuthRecvMkSlotsPrim S msg prep drKey _ _ recvCount' mkSaltCache slots' deriveMessageKeys)) (
            by omega)
  · split
    · refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 2)
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
          (fun _ => ?_) (by omega)
      exact isQueryBoundP_bind_le_mk (S.N_dh * 12 + 1)
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleMessageKeys80 0))
        (fun deriveMessageKeys => isQueryBoundP_embedPrim_isPrimQuery _ _
          (primBounded_finishAuthRecvMkSlotsPrim S msg prep drKey _ _ recvCount' mkSaltCache slots' deriveMessageKeys)) (
            by omega)
    · refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 2)
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
          (fun _ => ?_) (by omega)
      refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 2)
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
          (fun _ => ?_) (by omega)
      exact isQueryBoundP_bind_le_mk (S.N_dh * 12 + 1)
        (isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ _))
        (fun deriveMessageKeys => isQueryBoundP_embedPrim_isPrimQuery _ _
          (primBounded_finishAuthRecvMkSlotsPrim S msg prep drKey _ _ recvCount' mkSaltCache slots' deriveMessageKeys)) (
            by omega)
theorem isQueryBoundP_finishAuthRecvUnmatchedReduction_prim (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) (sentChal : Bool) :
    IsQueryBoundP
      (finishAuthRecvUnmatchedReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
        mkSaltCache sentChal)
      (fun q => isPrimQuery q = true) (S.N_dh * 12 + 2) :=
  isQueryBoundP_finishAuthRecvUnmatchedSlotsReduction_prim S idx msg prep drKey rk1 spqrSalt? rSlot
    recvCount' mkSaltCache {} sentChal
theorem isQueryBoundP_matchedSameEphMkSlotsReduction_prim (S : Setup) (idx : Nat)
    (s : IdealAuthSession S) (sIdx : Nat)
    (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    IsQueryBoundP (matchedSameEphMkSlotsReduction S idx s sIdx spqrSalt? recvCount mkSaltCache)
      (fun q => isPrimQuery q = true) 1 := by
  unfold matchedSameEphMkSlotsReduction; dsimp only
  split
  · split
    · exact isQueryBoundP_pure _ _ _
    · split
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_deriveMkQ_prim spqrSalt? 0)
          (fun _ => isQueryBoundP_pure _ _ _) (by omega)
  · split
    · split
      · exact isQueryBoundP_pure _ _ _
      · split
        · exact isQueryBoundP_pure _ _ _
        · exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isPrimQuery _ 0
                                             (primBounded_embedUnif sampleMessageKeys80 0))
                                               (fun _ => isQueryBoundP_pure _ _ _) (by omega)
    · exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isPrimQuery _ 1
                                         (primBounded_primQ _)) (fun _ => isQueryBoundP_pure _ _ _)
                                           (by omega)
theorem isQueryBoundP_matchedSameEphMkReduction_prim (S : Setup) (idx : Nat)
  (s : IdealAuthSession S)
    (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    IsQueryBoundP (matchedSameEphMkReduction S idx s spqrSalt? recvCount mkSaltCache)
      (fun q => isPrimQuery q = true) 1 :=
  isQueryBoundP_matchedSameEphMkSlotsReduction_prim S idx s (sessionSlotIndex s.sid) spqrSalt?
    recvCount mkSaltCache
theorem isQueryBoundP_authMkRecvReduction_prim (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    IsQueryBoundP (authMkRecvReduction S idx msg prep? hst sentChal)
      (fun q => isPrimQuery q = true) (S.N_dh * 12 + 5) := by
  unfold authMkRecvReduction
  cases prep? with
  | none => exact isQueryBoundP_pure _ _ _
  | some prep =>
    dsimp only; split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only; split
        · refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 4)
            (isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ _)) (fun spqr? => ?_) (
              by omega)
          cases spqr? with
          | none =>
            exact isQueryBoundP_bind_le_mk 0
              (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_recvFinishTag_runPrim S true
                                                         prep.finishTag none))
              (fun _ => isQueryBoundP_pure _ _ _) (by omega)
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩; dsimp only
            exact isQueryBoundP_bind_le_mk (S.N_dh * 12 + 1)
              (isQueryBoundP_matchedSameEphMkSlotsReduction_prim S idx s _ spqrSalt? hst.recvCount
                hst.mkSaltCache)
              (fun p => isQueryBoundP_embedPrim_isPrimQuery _ _
                (primBounded_finishAuthRecvMkSlotsPrim S msg prep s.drKey s.rk1 s.ck1_1 _ p.2 _ p.1))
              (by omega)
        · refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 4)
            (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
              (fun rk1 => ?_) (by omega)
          refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 2)
            (isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ _)) (fun spqr? => ?_) (
              by omega)
          cases spqr? with
          | none =>
            exact isQueryBoundP_bind_le_mk 0
              (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_recvFinishTag_runPrim S true
                                                         prep.finishTag none))
              (fun _ => isQueryBoundP_pure _ _ _) (by omega)
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact isQueryBoundP_finishAuthRecvUnmatchedSlotsReduction_prim S idx msg prep s.drKey rk1
              spqrSalt? _ _ hst.mkSaltCache _ sentChal
      | none =>
        dsimp only
        refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 4)
          (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleDRKey96 0))
            (fun drKey => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 4)
          (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif sampleBytes32 0))
            (fun rk1 => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 2)
          (isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ _)) (fun spqr? => ?_) (
            by omega)
        cases spqr? with
        | none =>
          exact isQueryBoundP_bind_le_mk 0
            (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_recvFinishTag_runPrim S true
                                                       prep.finishTag none))
            (fun _ => isQueryBoundP_pure _ _ _) (by omega)
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          exact isQueryBoundP_finishAuthRecvUnmatchedSlotsReduction_prim S idx msg prep drKey rk1
            spqrSalt? _ _ hst.mkSaltCache _ sentChal
    · refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 5)
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif _ 0)) (fun _ => ?_) (
          by omega)
      refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 5)
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif _ 0)) (fun _ => ?_) (
          by omega)
      refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 4)
        (isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ _)) (fun _ => ?_) (by omega)
      refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 3)
        (isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ _)) (fun _ => ?_) (by omega)
      refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 2)
        (isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ _)) (fun spqr? => ?_) (by omega)
      cases spqr? with
      | none =>
        exact isQueryBoundP_bind_le_mk 0
          (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_recvFinishTag_runPrim S true
                                                     prep.finishTag none))
          (fun _ => isQueryBoundP_pure _ _ _) (by omega)
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩; dsimp only
        refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 1)
          (isQueryBoundP_embedPrim_isPrimQuery _ 1 (primBounded_primQ _)) (fun _ => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (S.N_dh * 12) (isQueryBoundP_embedPrim_isPrimQuery _ 1
                                                        (primBounded_primQ _)) (fun _ => ?_) (
                                                          by omega)
        exact isQueryBoundP_bind_le_mk 0
          (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_recvFinishTag_runPrim S true
                                                     prep.finishTag _))
          (fun _ => isQueryBoundP_pure _ _ _) (by omega)
theorem isQueryBoundP_authMkStepReduction_prim (S : Setup) (idx : Nat)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    IsQueryBoundP (authMkStepReduction S idx q hst sentChal)
      (fun q => isPrimQuery q = true) (S.N_dh * 30 + 26) := by
  unfold authMkStepReduction
  cases q with
  | sendOPK u i bundle m0 m1 =>
    dsimp only; split
    · exact isQueryBoundP_pure _ _ _
    · exact (isQueryBoundP_authMkSendReduction_prim S idx (.sendOPK u i) u bundle m0 m1 hst
              sentChal).mono (by omega)
  | sendNoOPK u i bundle m0 m1 =>
    dsimp only; split
    · exact isQueryBoundP_pure _ _ _
    · exact (isQueryBoundP_authMkSendReduction_prim S idx (.sendNoOPK u i) u bundle m0 m1 hst
              sentChal).mono (by omega)
  | recvOPK k j o msg =>
    dsimp only
    refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 5)
      (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_prepareAuthHybridRecvOPKPrim S k j o msg
                                                 hst.toAuthHybridState))
      (fun prep? => ?_) (by omega)
    exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_authMkRecvReduction_prim S idx msg prep? hst
                                       sentChal) (fun _ => isQueryBoundP_pure _ _ _) (by omega)
  | recvNoOPK k j l msg =>
    dsimp only
    refine isQueryBoundP_bind_le_mk (S.N_dh * 12 + 5)
      (isQueryBoundP_embedPrim_isPrimQuery _ _ (primBounded_prepareAuthHybridRecvNoOPKPrim S k j l
                                                 msg hst.toAuthHybridState))
      (fun prep? => ?_) (by omega)
    exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_authMkRecvReduction_prim S idx msg prep? hst
                                       sentChal) (fun _ => isQueryBoundP_pure _ _ _) (by omega)
  | _ =>
    dsimp only
    exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isPrimQuery _ _
                                       (primBounded_stepAuthOtherPrim S _ hst))
                                         (fun _ => isQueryBoundP_pure _ _ _) (by omega)
theorem isQueryBoundP_runWithPrfMkStep_prim {S : Setup} {α : Type} (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) α) (N : Nat)
    (hN : IsQueryBoundP mx (fun q => isGameQuery q = true) N)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    IsQueryBoundP (runWithPrfMkStep (authMkStepReduction S idx) mx hst sentChal)
      (fun q => isPrimQuery q = true) (N * (S.N_dh * 30 + 26)) := by
  induction mx using OracleComp.inductionOn generalizing N hst sentChal with
  | pure a => rw [runWithPrfMkStep_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hN
    rcases q with uq | gq
    · rw [runWithPrfMkStep_query_bind_inl]
      have hk : ∀ u, IsQueryBoundP (k u) (fun q => isGameQuery q = true) N :=
        hN.2
      exact isQueryBoundP_bind_le_mk (N * (S.N_dh * 30 + 26))
        (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif _ 0))
        (fun u => ih u N (hk u) hst sentChal) (by omega)
    · rw [runWithPrfMkStep_query_bind_inr]
      have hPos : 0 < N := hN.1.resolve_left (not_not.mpr rfl)
      have hk : ∀ resp, IsQueryBoundP (k resp) (fun q => isGameQuery q = true) (N - 1) :=
        hN.2
      have hMul : (S.N_dh * 30 + 26) + (N - 1) * (S.N_dh * 30 + 26) ≤ N * (S.N_dh * 30 + 26) := by
        have h1 : 1 + (N - 1) = N := Nat.add_sub_of_le hPos
        calc (S.N_dh * 30 + 26) + (N - 1) * (S.N_dh * 30 + 26)
          _ = (1 + (N - 1)) * (S.N_dh * 30 + 26) := by ring
          _ = N * (S.N_dh * 30 + 26) := by rw [h1]
          _ ≤ N * (S.N_dh * 30 + 26) := Nat.le_refl _
      exact isQueryBoundP_bind_le_mk ((N - 1) * (S.N_dh * 30 + 26))
        (isQueryBoundP_authMkStepReduction_prim S idx gq hst sentChal)
        (fun ⟨⟨resp, s'⟩, c'⟩ => ih resp (N - 1) (hk resp) s' c') hMul
theorem isQueryBoundP_finishAuthRecvUnmatchedSlotsReduction_prf (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState) (sentChal : Bool) :
    IsQueryBoundP
      (finishAuthRecvUnmatchedSlotsReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
        mkSaltCache slots' sentChal)
      (fun q => q.isRight = true) 1 := by
  unfold finishAuthRecvUnmatchedSlotsReduction
  split
  · refine isQueryBoundP_bind_le_mk 1 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (by omega)
    split
    · exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_deriveMkQ_prf spqrSalt?)
        (fun _ => isQueryBoundP_embedPrim_isRight _ 0) (by omega)
    · exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
        (fun _ => isQueryBoundP_embedPrim_isRight _ 0) (by omega)
  · split
    · refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
        by omega)
      exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
        (fun _ => isQueryBoundP_embedPrim_isRight _ 0) (by omega)
    · refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
        by omega)
      refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
        by omega)
      exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
        (fun _ => isQueryBoundP_embedPrim_isRight _ 0) (by omega)
theorem isQueryBoundP_finishAuthRecvUnmatchedReduction_prf (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) (sentChal : Bool) :
    IsQueryBoundP
      (finishAuthRecvUnmatchedReduction S idx msg prep drKey rk1 spqrSalt? rSlot recvCount'
        mkSaltCache sentChal)
      (fun q => q.isRight = true) 1 :=
  isQueryBoundP_finishAuthRecvUnmatchedSlotsReduction_prf S idx msg prep drKey rk1 spqrSalt? rSlot
    recvCount' mkSaltCache {} sentChal
theorem isQueryBoundP_matchedSameEphMkSlotsReduction_prf (S : Setup) (idx : Nat)
    (s : IdealAuthSession S) (sIdx : Nat)
    (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    IsQueryBoundP (matchedSameEphMkSlotsReduction S idx s sIdx spqrSalt? recvCount mkSaltCache)
      (fun q => q.isRight = true) 1 := by
  unfold matchedSameEphMkSlotsReduction; dsimp only
  split
  · split
    · exact isQueryBoundP_pure _ _ _
    · split
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_deriveMkQ_prf spqrSalt?)
          (fun _ => isQueryBoundP_pure _ _ _) (by omega)
  · split
    · split
      · exact isQueryBoundP_pure _ _ _
      · split
        · exact isQueryBoundP_pure _ _ _
        · exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
            (fun _ => isQueryBoundP_pure _ _ _) (by omega)
    · exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
        (fun _ => isQueryBoundP_pure _ _ _) (by omega)
theorem isQueryBoundP_matchedSameEphMkReduction_prf (S : Setup) (idx : Nat) (s : IdealAuthSession S)
    (spqrSalt? : Option Bytes) (recvCount : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    IsQueryBoundP (matchedSameEphMkReduction S idx s spqrSalt? recvCount mkSaltCache)
      (fun q => q.isRight = true) 1 :=
  isQueryBoundP_matchedSameEphMkSlotsReduction_prf S idx s (sessionSlotIndex s.sid) spqrSalt?
    recvCount mkSaltCache
theorem isQueryBoundP_authMkRecvReduction_prf (S : Setup) (idx : Nat)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecvPrim S))
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    IsQueryBoundP (authMkRecvReduction S idx msg prep? hst sentChal)
      (fun q => q.isRight = true) 1 := by
  unfold authMkRecvReduction
  cases prep? with
  | none => exact isQueryBoundP_pure _ _ _
  | some prep =>
    dsimp only; split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only; split
        · refine isQueryBoundP_bind_le_mk 1 (isQueryBoundP_embedPrim_isRight _ 0) (fun spqr? => ?_)
            (by omega)
          cases spqr? with
          | none =>
            exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
              (fun _ => isQueryBoundP_pure _ _ _) (by omega)
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩; dsimp only
            exact isQueryBoundP_bind_le_mk 0
              (isQueryBoundP_matchedSameEphMkSlotsReduction_prf S idx s _ spqrSalt? hst.recvCount
                hst.mkSaltCache)
              (fun _ => isQueryBoundP_embedPrim_isRight _ 0)
              (by omega)
        · refine isQueryBoundP_bind_le_mk 1 (isQueryBoundP_embedPrim_isRight _ 0) (fun rk1 => ?_) (
            by omega)
          refine isQueryBoundP_bind_le_mk 1 (isQueryBoundP_embedPrim_isRight _ 0) (fun spqr? => ?_)
            (by omega)
          cases spqr? with
          | none =>
            exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
              (fun _ => isQueryBoundP_pure _ _ _) (by omega)
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            exact isQueryBoundP_finishAuthRecvUnmatchedSlotsReduction_prf S idx msg prep s.drKey rk1
              spqrSalt? _ _ hst.mkSaltCache _ sentChal
      | none =>
        dsimp only
        refine isQueryBoundP_bind_le_mk 1 (isQueryBoundP_embedPrim_isRight _ 0) (fun drKey => ?_) (
          by omega)
        refine isQueryBoundP_bind_le_mk 1 (isQueryBoundP_embedPrim_isRight _ 0) (fun rk1 => ?_) (
          by omega)
        refine isQueryBoundP_bind_le_mk 1 (isQueryBoundP_embedPrim_isRight _ 0) (fun spqr? => ?_) (
          by omega)
        cases spqr? with
        | none =>
          exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
            (fun _ => isQueryBoundP_pure _ _ _) (by omega)
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          exact isQueryBoundP_finishAuthRecvUnmatchedSlotsReduction_prf S idx msg prep drKey rk1
            spqrSalt? _ _ hst.mkSaltCache _ sentChal
    · refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
        by omega)
      refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
        by omega)
      refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
        by omega)
      refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
        by omega)
      refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun spqr? => ?_) (
        by omega)
      cases spqr? with
      | none =>
        exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
          (fun _ => isQueryBoundP_pure _ _ _) (by omega)
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩; dsimp only
        refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
          by omega)
        refine isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
          by omega)
        exact isQueryBoundP_bind_le_mk 0 (isQueryBoundP_embedPrim_isRight _ 0)
          (fun _ => isQueryBoundP_pure _ _ _) (by omega)
theorem isQueryBoundP_authMkSendReduction_prf_cont {S : Setup} {α : Type} (idx : Nat)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) (R : Nat)
    (f : ((AuthResponse × AuthHybridStateFixed S) × Bool) → OracleComp PrfMkSimSpec α)
    (hf : ∀ x, IsQueryBoundP (f x) (fun q => q.isRight = true) (R + if x.2 then 0 else 1)) :
    IsQueryBoundP (authMkSendReduction S idx sid u bundle m0 m1 hst sentChal >>= f)
      (fun q => q.isRight = true) (R + if sentChal then 0 else 1) := by
  unfold authMkSendReduction
  rw [bind_assoc]
  refine isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
    (isQueryBoundP_embedPrim_isRight _ 0) (fun prep => ?_) (by omega)
  cases prep with
  | done resp hst' => rw [pure_bind]; exact hf ((resp, hst'), sentChal)
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
    pqRatchetMsg msgPlain =>
    dsimp only
    by_cases hChal : (!sentChal && ((hst.slots.allocSend sid).1 == idx)) = true
    · have hSentF : sentChal = false := by cases sentChal <;> simp at hChal ⊢
      subst hSentF
      simp only [hChal, Bool.false_eq_true, ↓reduceIte, bind_assoc]
      refine isQueryBoundP_bind_le_mk (R + 1) (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (
        by omega)
      refine isQueryBoundP_bind_le_mk R (isQueryBoundP_deriveMkQ_prf spqrSalt?) (fun _ => ?_) (
        by omega)
      refine isQueryBoundP_bind_le_mk R (isQueryBoundP_embedPrim_isRight _ 0) (fun res => ?_) (
        by omega)
      rw [pure_bind]; simpa using hf (res, true)
    · simp only [hChal, Bool.false_eq_true, ↓reduceIte]
      split
      · simp only [bind_assoc]
        refine isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
          (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
          (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
          (isQueryBoundP_embedPrim_isRight _ 0) (fun res => ?_) (by omega)
        rw [pure_bind]; exact hf (res, sentChal)
      · simp only [bind_assoc]
        refine isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
          (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
          (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
          (isQueryBoundP_embedPrim_isRight _ 0) (fun _ => ?_) (by omega)
        refine isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
          (isQueryBoundP_embedPrim_isRight _ 0) (fun res => ?_) (by omega)
        rw [pure_bind]; exact hf (res, sentChal)
theorem isQueryBoundP_runWithPrfMkStep_prf {S : Setup} {α : Type} (idx : Nat)
    (mx : OracleComp (unifSpec + authSpec S) α) (R : Nat) (hR : IsQueryBoundP mx isAuthRecvQuery R)
    (hst : AuthHybridStateFixed S) (sentChal : Bool) :
    IsQueryBoundP (runWithPrfMkStep (authMkStepReduction S idx) mx hst sentChal)
      (fun q => q.isRight = true) (R + if sentChal then 0 else 1) := by
  induction mx using OracleComp.inductionOn generalizing R hst sentChal with
  | pure a => rw [runWithPrfMkStep_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    rw [isQueryBoundP_query_bind_iff] at hR
    rcases q with uq | gq
    · rw [runWithPrfMkStep_query_bind_inl]
      have hk : ∀ u, IsQueryBoundP (k u) isAuthRecvQuery R := fun u =>
        by simpa [isAuthRecvQuery] using hR.2 u
      exact isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
        (isQueryBoundP_embedPrim_isRight _ 0) (fun u => ih u R (hk u) hst sentChal) (by omega)
    · rw [runWithPrfMkStep_query_bind_inr]
      cases gq with
      | sendOPK u i bundle m0 m1 =>
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery R := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction; dsimp only; split
        · rw [pure_bind]; exact ih _ R (hk _) hst sentChal
        · exact isQueryBoundP_authMkSendReduction_prf_cont idx (.sendOPK u i) u bundle m0 m1 hst
            sentChal R
            (fun ((resp, s'), c') => runWithPrfMkStep (authMkStepReduction S idx) (k resp) s' c')
            (fun ⟨⟨resp, s'⟩, c'⟩ => ih resp R (hk resp) s' c')
      | sendNoOPK u i bundle m0 m1 =>
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery R := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction; dsimp only; split
        · rw [pure_bind]; exact ih _ R (hk _) hst sentChal
        · exact isQueryBoundP_authMkSendReduction_prf_cont idx (.sendNoOPK u i) u bundle m0 m1 hst
            sentChal R
            (fun ((resp, s'), c') => runWithPrfMkStep (authMkStepReduction S idx) (k resp) s' c')
            (fun ⟨⟨resp, s'⟩, c'⟩ => ih resp R (hk resp) s' c')
      | recvOPK k' j o msg =>
        have hPos : 0 < R := hR.1.resolve_left (not_not.mpr trivial)
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery (R - 1) := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction; dsimp only; simp only [bind_assoc, pure_bind]
        refine isQueryBoundP_bind_le_mk (1 + ((R - 1) + if sentChal then 0 else 1))
          (isQueryBoundP_embedPrim_isRight _ 0) (fun prep? => ?_) (by omega)
        exact isQueryBoundP_bind_le_mk ((R - 1) + if sentChal then 0 else 1)
          (isQueryBoundP_authMkRecvReduction_prf S idx msg prep? hst sentChal)
          (fun ⟨resp, s'⟩ => ih resp (R - 1) (hk resp) s' sentChal) (by omega)
      | recvNoOPK k' j l msg =>
        have hPos : 0 < R := hR.1.resolve_left (not_not.mpr trivial)
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery (R - 1) := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction; dsimp only; simp only [bind_assoc, pure_bind]
        refine isQueryBoundP_bind_le_mk (1 + ((R - 1) + if sentChal then 0 else 1))
          (isQueryBoundP_embedPrim_isRight _ 0) (fun prep? => ?_) (by omega)
        exact isQueryBoundP_bind_le_mk ((R - 1) + if sentChal then 0 else 1)
          (isQueryBoundP_authMkRecvReduction_prf S idx msg prep? hst sentChal)
          (fun ⟨resp, s'⟩ => ih resp (R - 1) (hk resp) s' sentChal) (by omega)
      | _ =>
        have hk : ∀ resp, IsQueryBoundP (k resp) isAuthRecvQuery R := fun resp =>
          by simpa [isAuthRecvQuery] using hR.2 resp
        unfold authMkStepReduction; dsimp only; simp only [bind_assoc, pure_bind]
        exact isQueryBoundP_bind_le_mk (R + if sentChal then 0 else 1)
          (isQueryBoundP_embedPrim_isRight _ 0) (fun ⟨resp, s'⟩ => ih resp R (hk resp) s' sentChal)
            (by omega)
theorem isQueryBoundP_authMkReductionRun_prf (S : Setup) (idx : Nat)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    IsQueryBoundP (authMkReductionRun S idx A.1) (fun q => q.isRight = true) (S.N_recv_tot + 1) :=
      by
  unfold authMkReductionRun
  refine isQueryBoundP_bind_le_mk (S.N_recv_tot + 1)
    (isQueryBoundP_embedPrim_isRight _ 0) (fun secb => ?_) (by omega)
  exact isQueryBoundP_bind_le_mk 0
    (isQueryBoundP_runWithPrfMkStep_prf idx A.1.run S.N_recv_tot A.2.2.2.1
      (AuthHybridStateFixed.empty S secb) false)
    (fun _ => isQueryBoundP_embedPrim_isRight _ 0) (by simp)
theorem isQueryBoundP_authMkReductionRun_prim (S : Setup) (idx : Nat)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    IsQueryBoundP (authMkReductionRun S idx A.1)
      (fun q => isPrimQuery q = true) (b.q_total * (S.N_dh * 30 + 26) + S.N_dh * 5) := by
  unfold authMkReductionRun
  refine isQueryBoundP_bind_le_mk (b.q_total * (S.N_dh * 30 + 26) + S.N_dh * 5)
    (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif _ 0)) (fun secb => ?_) (
      by omega)
  exact isQueryBoundP_bind_le_mk (S.N_dh * 5)
    (isQueryBoundP_runWithPrfMkStep_prim idx A.1.run b.q_total
      (SignalPqxdh.QueryBounded.auth_total A.2)
      (AuthHybridStateFixed.empty S secb) false)
    (fun ⟨⟨b', finalSt⟩, _⟩ => isQueryBoundP_embedPrim_isPrimQuery _ _
      (primBounded_finalizeAuthFixedPrim S secb b' finalSt.toAuthHybridState))
    (by omega)
theorem prfMsgKeysReductionAuthFixed_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeysReductionAuthFixed S b A).Bounded :=
  ⟨isQueryBoundP_bind_le_mk (S.N_recv_tot + 1)
     (isQueryBoundP_embedPrim_isRight _ 0)
     (fun idx => isQueryBoundP_authMkReductionRun_prf S idx b A)
     (by dsimp [prfMsgKeysReductionAuthFixed]; omega),
   isQueryBoundP_bind_le_mk (b.q_total * (S.N_dh * 30 + 26) + S.N_dh * 5)
     (isQueryBoundP_embedPrim_isPrimQuery _ 0 (primBounded_embedUnif _ 0))
     (fun idx => isQueryBoundP_authMkReductionRun_prim S idx b A)
     (by dsimp [prfMsgKeysReductionAuthFixed]; omega)⟩
theorem prfMsgKeysReductionAuthFixed_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeysReductionAuthFixed S b A).q_prf ≤ S.N_recv_tot + 1 :=
  Nat.le_refl _
theorem prfMsgKeysReductionAuthFixed_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeysReductionAuthFixed S b A).q_prim ≤ primQueryBudget S b := by
  dsimp [prfMsgKeysReductionAuthFixed, primQueryBudget]
  nlinarith
end SignalPqxdh.Security.AuthSubHops1to3
