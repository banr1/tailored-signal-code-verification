/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c
import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingB
import VCVio.EvalDist.Monad.Basic

/-!
# `Auth` hybrid hop `G3 → G3.5`: `.recvOPK` and `.recvNoOPK` step couplings

Couples the receiver key schedule and `.recvOPK`/`.recvNoOPK` transitions between `.g3_5` and `.g3`
up to `badAuthFgAnyLatchedMono`, given the subcase premises.
-/

@[expose] public section

set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security

/-! ## Responder random-oracle origin -/

theorem respAuthCand_eraseSpkBundlesFg_eq_of_ne {S : Setup} (P : Primitives)
    {spkBundles : List ((Nat × Nat) × SpkBundleEntry)} (hVS : ValidSpkBundles S spkBundles)
    (hLen : spkBundles.length ≤ S.N_dh)
    {bKey : Nat × Nat} {k_s j_s : Nat} {b_r b_s : SpkBundleEntry}
    (hrMem : (bKey, b_r) ∈ spkBundles) (hsMem : ((k_s, j_s), b_s) ∈ spkBundles)
    (hNe : bKey ≠ (k_s, j_s)) (pk : Bytes) :
    respAuthCand S P (eraseSpkBundlesFg S (spkBundleFlatIdxVal S (k_s, j_s)) spkBundles)
      bKey pk = P.x25519 b_r.spkSk pk ∧
    (b_r.spkSk.length = 32 →
      respAuthCandGuard S (eraseSpkBundlesFg S (spkBundleFlatIdxVal S (k_s, j_s)) spkBundles)
        bKey = true) := by
  have hrLt : bKey.2 < S.N_recv := (hVS.1 (bKey, b_r) hrMem).2
  have hsLt : j_s < S.N_recv := (hVS.1 ((k_s, j_s), b_s) hsMem).2
  have hFlatNe : spkBundleFlatIdxVal S bKey ≠ spkBundleFlatIdxVal S (k_s, j_s) := by
    intro hEq
    exact hNe (spkSlotFlatIdx_inj S hrLt hsLt hEq)
  have hEraseLen :
      (eraseSpkBundlesFg S (spkBundleFlatIdxVal S (k_s, j_s)) spkBundles).length ≤ S.N_dh := by
    unfold eraseSpkBundlesFg; rw [List.length_map]; exact hLen
  have hFind : (eraseSpkBundlesFg S (spkBundleFlatIdxVal S (k_s, j_s)) spkBundles).find?
        (fun (idx, _) => idx == bKey) =
      some (bKey, b_r) := by
    rcases hVS with ⟨hBounds, hNodup⟩
    clear hsMem hLen hEraseLen
    induction spkBundles with
    | nil => nomatch hrMem
    | cons hd tl ih =>
      rcases hd with ⟨k0, b0⟩
      rw [List.map_cons, List.nodup_cons] at hNodup
      rcases List.mem_cons.mp hrMem with hEq | hTl
      · injection hEq with hk0 hb0; subst hk0; subst hb0
        unfold eraseSpkBundlesFg eraseSpkBundleEntryFg; rw [List.map_cons, List.find?_cons]
        dsimp only
        have hBeqSelf : (bKey == bKey) = true := beq_self_eq_true bKey
        have hBeqF : (FgGapDh.spkBundleFlatIdxVal S bKey ==
            spkBundleFlatIdxVal S (k_s, j_s)) = false :=
          beq_eq_false_iff_ne.mpr hFlatNe
        rw [hBeqSelf, hBeqF]; rfl
      · have hNe0 : (k0 == bKey) = false := by
          cases hBeq0 : (k0 == bKey)
          · rfl
          · have hk0Eq : k0 = bKey := beq_iff_eq.mp hBeq0
            subst hk0Eq; exact False.elim (hNodup.1 (List.mem_map.mpr ⟨(k0, b_r), hTl, rfl⟩))
        unfold eraseSpkBundlesFg; rw [List.map_cons, List.find?_cons]; dsimp only; rw [hNe0]
        exact ih hTl (fun e he => hBounds e (List.mem_cons_of_mem _ he)) hNodup.2
  unfold respAuthCand respAuthCandGuard
  rw [List.take_of_length_le hEraseLen, hFind]; dsimp only
  exact ⟨rfl, fun h32 => by cases hE : b_r.spkSk <;> simp_all⟩

/-- Witness that an RO input `secrets : Bytes` was constructed by an earlier responder
    handshake recorded in `s3.adv.respRecs`. -/
def AuthRespRoOrigin {S : Setup} (P : Primitives) (s3 : AuthAdvLatchedState S)
    (secrets : Bytes) : Prop :=
  ∃ (r : AuthRespRecord) (rKem : _root_.SignalPqxdh.Security.RecvKemRecord) (b_r : SpkBundleEntry),
    r ∈ s3.adv.respRecs ∧
    rKem ∈ s3.hyb.recvKemRecs ∧
    (r.bKey, b_r) ∈ s3.hyb.base.spkBundles ∧
    r.bKey = (rKem.k, rKem.j) ∧
    rKem.pqspkPk = b_r.pqspkPk ∧
    rKem.pqspkSk = b_r.pqspkSk ∧
    P.kemDecaps b_r.pqspkSk rKem.kemCt = some rKem.kemSs ∧
    P.isCanonical r.ekAPk = true ∧
    r.ekAPk.length = 32 ∧
    r.ikAPk.length = 32 ∧
    (r.bKey.1, UInt32.ofNat r.bKey.2, UInt32.ofNat r.bKey.2, r.ekAPk) ∈
      s3.hyb.base.seenKyberBaseKeys ∧
    extractDh1 secrets = P.x25519 b_r.spkSk r.ikAPk ∧
    extractDh3 secrets = P.x25519 b_r.spkSk r.ekAPk ∧
    (extractKemSsOPK secrets = rKem.kemSs ∨ extractKemSsNoOPK secrets = rKem.kemSs)

theorem authRespRoOrigin_of_traceSub {S : Setup} (P : Primitives)
    {s3 s3' : AuthAdvLatchedState S} {secrets : Bytes} (hSub : AuthHybridTraceSub s3.hyb s3'.hyb)
    (hRespSub : s3.adv.respRecs.Sublist s3'.adv.respRecs)
    (hKybSub : s3.hyb.base.seenKyberBaseKeys.Sublist s3'.hyb.base.seenKyberBaseKeys)
    (hOrig : AuthRespRoOrigin P s3 secrets) : AuthRespRoOrigin P s3' secrets := by
  rcases hOrig with ⟨r, rKem, b_r, hrMem, hrKemMem, hbMem, hbKey, hPqPk, hPqSk, hDec,
    hCanon, hEkLen, hIkLen, hKybMem, hDh1, hDh3, hSs⟩
  exact ⟨r, rKem, b_r, hRespSub.subset hrMem, hSub.recvRecs_sub.subset hrKemMem,
    hSub.base_sub.spkBundles_sub.subset hbMem, hbKey, hPqPk, hPqSk, hDec,
    hCanon, hEkLen, hIkLen, hKybSub.subset hKybMem, hDh1, hDh3, hSs⟩

/-! ## Bad-event firing on receiver queries -/

theorem badAuthFgDh1At_of_recv_mem_advRoLog {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (hV : ValidAuthKeyStoresFull S P st)
    {u_r k j : Nat} {senderEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {ikAPk_hdr secrets : Bytes} (huMem : (u_r, senderEntry) ∈ st.principals)
    (huNotCorr : (!senderEntry.corrupted) = true)
    (hPowIk : P.pow8 ikAPk_hdr = P.pow8 senderEntry.ikAPk)
    (hbMem : ((k, j), bEntry) ∈ st.spkBundles) (hRoMem : secrets ∈ advRoLog)
    (hRoLen : advRoLog.length ≤ maxRo)
    (hDh1 : extractDh1 secrets = P.x25519 bEntry.spkSk ikAPk_hdr) :
    badAuthFgDh1AtMono P maxRo u_r (spkBundleFlatIdxVal S (k, j)) st advRoLog respRecs = true := by
  have hFindU := find_principals_eq_some_of_mem hV.1.1 huMem
  have hFindB := find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbMem
  have huIk := hV.1.2.2.2.1 (u_r, senderEntry) huMem
  have hbSpk := (hV.1.2.2.2.2.1 ((k, j), bEntry) hbMem)
  have hPowBase : P.pow8 ikAPk_hdr = P.pow8 (P.x25519Base senderEntry.secIKA0) := by
    rw [hPowIk, huIk.2]
  have hTargetEq : P.x25519 bEntry.spkSk ikAPk_hdr = P.x25519 senderEntry.secIKA0 bEntry.spkPk := by
    rw [x25519_comm_of_pow8_eq_auth P hP bEntry.spkSk senderEntry.secIKA0 ikAPk_hdr hPowBase,
        ← hbSpk.2.1]
  have hTakeMem : secrets ∈ advRoLog.take maxRo := by
    rw [List.take_of_length_le hRoLen]; exact hRoMem
  unfold badAuthFgDh1AtMono; rw [hFindU, hFindB]; dsimp only
  rw [huNotCorr, Bool.true_and, Bool.or_eq_true, Bool.or_eq_true]
  left; left; exact List.any_eq_true.mpr ⟨secrets, hTakeMem, beq_iff_eq.mpr (hDh1.trans hTargetEq)⟩

theorem badAuthFgAnyLatched_of_recv_mem_advRoLog {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (s : AuthFgCutoffState S) (hV : ValidAuthKeyStoresFull S P s.base)
    {u_r k j : Nat} {senderEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {ikAPk_hdr secrets : Bytes} (huMem : (u_r, senderEntry) ∈ s.base.principals)
    (huNotCorr : (!senderEntry.corrupted) = true)
    (hPowIk : P.pow8 ikAPk_hdr = P.pow8 senderEntry.ikAPk)
    (hbMem : ((k, j), bEntry) ∈ s.base.spkBundles) (hRoMem : secrets ∈ s.advRoLog)
    (hRoLen : s.advRoLog.length ≤ maxRo)
    (hDh1 : extractDh1 secrets = P.x25519 bEntry.spkSk ikAPk_hdr) :
    badAuthFgAnyLatchedMono P maxRo s = true := by
  have huLt : u_r < S.N_id := hV.1.1.1 (u_r, senderEntry) huMem
  have hbRange := spkBundleFlatIdxVal_mem_range hV.1.2.1 hbMem
  exact badAuthFgAnyLatchedMono_of_exists_badAuthFgDh1AtMono P maxRo s
    ⟨⟨u_r, huLt⟩, spkBundleFlatIdxVal S (k, j), hbRange,
      badAuthFgDh1At_of_recv_mem_advRoLog P hP maxRo s.base s.advRoLog s.respRecs hV
        huMem huNotCorr hPowIk hbMem hRoMem hRoLen hDh1⟩

theorem recv_matched_none_imp_abort_of_idealSession_pqspkHonest {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (hst : AuthHybridState S)
    (hKS : ValidAuthKeyStores S P hst.base)
    {s : IdealAuthSession S} {sessEntry : AuthInitiatorEntry S}
    {u : Nat} {uEntry : PrincipalEntry} {kemCoins ss_s : Bytes}
    {initRec : _root_.SignalPqxdh.Security.InitKemRecord S} (hsMem : s ∈ hst.idealSessions)
    (hs : ValidIdealAuthSession S P hst s sessEntry u uEntry kemCoins ss_s initRec)
    {k : Fin S.N_id} {j : Fin S.N_recv} {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {opkPk? dh4? : Option Bytes} {ss_r : Bytes}
    {recEntry : _root_.SignalPqxdh.Security.RecvKemRecord} {hdr : HandshakeHdr}
    (hr : ValidAuthRespHandshake S P hst k j kEntry bEntry opkPk? dh4? ss_r recEntry hdr)
    (hPqHon : ∃ k_s j_s k_s_Entry b_s, (k_s, k_s_Entry) ∈ hst.base.principals ∧
      ((k_s, j_s), b_s) ∈ hst.base.spkBundles ∧ P.pow8 s.peerIkPk = P.pow8 k_s_Entry.ikAPk ∧
      s.peerPqspkPk = b_s.pqspkPk) (hMatchedNone : hst.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk hdr) = none)
    (hSecEq : idealSessionSecrets P uEntry sessEntry.ekASk ss_s s =
      recvHandshakeSecrets P kEntry bEntry dh4? ss_r hdr) : isAuthG3Abort P hst = true := by
  cases hAb : isAuthG3Abort P hst
  · have hNoBadKem : hasBadKemShCrAuth P hst = false := by
      unfold isAuthG3Abort at hAb
      rcases Bool.or_eq_false_iff.mp hAb with ⟨_, h4⟩
      exact h4
    have hNoKemColl : hasKemPkCollisionAuth hst = false := by
      unfold isAuthG3Abort at hAb
      rcases Bool.or_eq_false_iff.mp hAb with ⟨h123, _⟩
      rcases Bool.or_eq_false_iff.mp h123 with ⟨_, h3⟩
      exact h3
    have hMatch := secrets_eq_imp_matchIdealAuthHandshake_of_pqspkHonest P hP hst hKS
      hNoBadKem hNoKemColl hs hr hPqHon hSecEq
    exact False.elim (List.find?_eq_none.mp hMatchedNone s hsMem hMatch)
  · rfl

theorem badAuthFgDh1At_of_recv_respRoOrigin {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (s3 : AuthAdvLatchedState S) (hV : ValidAuthKeyStoresFull S P s3.hyb.base)
    {u_r k j : Nat} {senderEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {hdr : HandshakeHdr} {secrets : Bytes} (huMem : (u_r, senderEntry) ∈ s3.hyb.base.principals)
    (huNotCorr : (!senderEntry.corrupted) = true)
    (hPowIk : P.pow8 hdr.ikAPk = P.pow8 senderEntry.ikAPk)
    (hbMem : ((k, j), bEntry) ∈ s3.hyb.base.spkBundles) (hSpkId : hdr.spkId = UInt32.ofNat j)
    (hPqspkId : hdr.pqspkId = UInt32.ofNat j) (hEkLen : hdr.ekAPk.length = 32)
    (hEkCanon : P.isCanonical hdr.ekAPk = true) (hReplayOk :
      (checkAndMarkKyberBaseKeySeen s3.hyb.base.seenKyberBaseKeys k hdr.pqspkId hdr.spkId hdr.ekAPk).1 =
        true) (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot)
    (hOrig : AuthRespRoOrigin P s3 secrets)
    (hDh1 : extractDh1 secrets = P.x25519 bEntry.spkSk hdr.ikAPk)
    (hDh3 : extractDh3 secrets = P.x25519 bEntry.spkSk hdr.ekAPk) :
    badAuthFgDh1AtMono P maxRo u_r (spkBundleFlatIdxVal S (k, j))
      s3.hyb.base s3.adv.advRoLog s3.adv.respRecs = true := by
  rcases hOrig with ⟨r, _rKem, b_r, hrMem, _, hbrMem, _, _, _, _, hrCanon, hrEkLen, _,
    hKybMem, hOrigDh1, hOrigDh3, _⟩
  by_cases hbKeyEq : r.bKey = (k, j)
  · exfalso
    rw [hbKeyEq] at hbrMem hKybMem
    have hFB1 := find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbrMem
    have hFB2 := find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbMem
    rw [hFB1] at hFB2
    injection hFB2 with hPair; injection hPair with _ hbEq; subst hbEq
    have hbSpk := hV.1.2.2.2.2.1 ((k, j), b_r) hbrMem
    have hDh3Eq : P.x25519 b_r.spkSk hdr.ekAPk = P.x25519 b_r.spkSk r.ekAPk := by
      rw [← hDh3, hOrigDh3]
    have hPowEk := hP.x25519_inj_pow8 b_r.spkSk hdr.ekAPk r.ekAPk hbSpk.1 hEkLen hrEkLen hDh3Eq
    have hEkEq : hdr.ekAPk = r.ekAPk :=
      eq_of_isCanonical_of_pow8_eq_auth P hP hEkCanon hrCanon hPowEk
    unfold checkAndMarkKyberBaseKeySeen at hReplayOk
    dsimp (config := { zetaHave := true }) only at hReplayOk
    rw [hSpkId, hPqspkId, hEkEq] at hReplayOk
    have hCont : s3.hyb.base.seenKyberBaseKeys.contains
          (k, UInt32.ofNat j, UInt32.ofNat j, r.ekAPk) = true :=
      List.contains_iff_mem.mpr hKybMem
    rw [hCont] at hReplayOk
    simp at hReplayOk
  · have hFindU := find_principals_eq_some_of_mem hV.1.1 huMem
    have hFindB := find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbMem
    have huIk := hV.1.2.2.2.1 (u_r, senderEntry) huMem
    have hbSpk := hV.1.2.2.2.2.1 ((k, j), bEntry) hbMem
    have hbrSpk := (hV.1.2.2.2.2.1 (r.bKey, b_r) hbrMem).1
    have hSpkLen := (validAuthKeyStoresFull_lengths_le S P s3.hyb.base hV).2.1
    have hPowBase : P.pow8 hdr.ikAPk = P.pow8 (P.x25519Base senderEntry.secIKA0) := by
      rw [hPowIk, huIk.2]
    have hTargetEq :
        P.x25519 bEntry.spkSk hdr.ikAPk = P.x25519 senderEntry.secIKA0 bEntry.spkPk := by
      rw [x25519_comm_of_pow8_eq_auth P hP bEntry.spkSk senderEntry.secIKA0 hdr.ikAPk hPowBase,
          ← hbSpk.2.1]
    rcases respAuthCand_eraseSpkBundlesFg_eq_of_ne P hV.1.2.1 hSpkLen hbrMem hbMem hbKeyEq r.ikAPk
      with ⟨hCand, hGuard⟩
    have hCandEq : respAuthDh1Cand S P
          (eraseSpkBundlesFg S (spkBundleFlatIdxVal S (k, j)) s3.hyb.base.spkBundles) r =
        P.x25519 senderEntry.secIKA0 bEntry.spkPk := by
      unfold respAuthDh1Cand; rw [hCand, ← hOrigDh1, hDh1, hTargetEq]
    have hrTake : r ∈ s3.adv.respRecs.take S.N_sess_tot := by
      rw [List.take_of_length_le hRespLen]; exact hrMem
    unfold badAuthFgDh1AtMono; rw [hFindU, hFindB]; dsimp only
    rw [huNotCorr, Bool.true_and, Bool.or_eq_true]
    right; refine List.any_eq_true.mpr ⟨r, hrTake, ?_⟩
    rw [Bool.and_eq_true, beq_iff_eq]; exact ⟨hGuard hbrSpk, hCandEq⟩

theorem badAuthFgAnyLatched_of_recv_respRoOrigin {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (s3 : AuthAdvLatchedState S) (hV : ValidAuthKeyStoresFull S P s3.hyb.base)
    {u_r k j : Nat} {senderEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {hdr : HandshakeHdr} {secrets : Bytes} (huMem : (u_r, senderEntry) ∈ s3.hyb.base.principals)
    (huNotCorr : (!senderEntry.corrupted) = true)
    (hPowIk : P.pow8 hdr.ikAPk = P.pow8 senderEntry.ikAPk)
    (hbMem : ((k, j), bEntry) ∈ s3.hyb.base.spkBundles) (hSpkId : hdr.spkId = UInt32.ofNat j)
    (hPqspkId : hdr.pqspkId = UInt32.ofNat j) (hEkLen : hdr.ekAPk.length = 32)
    (hEkCanon : P.isCanonical hdr.ekAPk = true) (hReplayOk :
      (checkAndMarkKyberBaseKeySeen s3.hyb.base.seenKyberBaseKeys k hdr.pqspkId hdr.spkId hdr.ekAPk).1 =
        true) (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot)
    (hOrig : AuthRespRoOrigin P s3 secrets)
    (hDh1 : extractDh1 secrets = P.x25519 bEntry.spkSk hdr.ikAPk)
    (hDh3 : extractDh3 secrets = P.x25519 bEntry.spkSk hdr.ekAPk) :
    badAuthFgAnyLatchedMono P maxRo s3.toFg = true := by
  have huLt : u_r < S.N_id := hV.1.1.1 (u_r, senderEntry) huMem
  have hbRange := spkBundleFlatIdxVal_mem_range hV.1.2.1 hbMem
  exact badAuthFgAnyLatchedMono_of_exists_badAuthFgDh1AtMono P maxRo s3.toFg
    ⟨⟨u_r, huLt⟩, spkBundleFlatIdxVal S (k, j), hbRange,
      badAuthFgDh1At_of_recv_respRoOrigin P hP maxRo s3 hV huMem huNotCorr hPowIk hbMem
        hSpkId hPqspkId hEkLen hEkCanon hReplayOk hRespLen hOrig hDh1 hDh3⟩

/-! ## Receiver schedule and step coupling -/

theorem evalAuthHybridRecvDrKey_g3_eq {S : Setup} (P : Primitives)
    (roCache : List (Bytes × DRKey)) (matchedSess? : Option (IdealAuthSession S))
    (hon : Bool) (secrets : Bytes) :
    evalAuthHybridRecvDrKey .g3 true P roCache matchedSess? hon secrets =
      evalHkdfOrRo true P roCache secrets := by
  unfold evalAuthHybridRecvDrKey AuthHybridStage.idealDrKey
  simp

theorem evalAuthHybridRecvDrKey_g3_5_some {S : Setup} (P : Primitives)
    (roCache : List (Bytes × DRKey)) (s : IdealAuthSession S) (hon : Bool) (secrets : Bytes) :
    evalAuthHybridRecvDrKey .g3_5 true P roCache (some s) hon secrets =
      pure (s.drKey, roCache) := by
  unfold evalAuthHybridRecvDrKey AuthHybridStage.idealDrKey
  simp

theorem evalAuthHybridRecvDrKey_g3_5_none_of_false (S : Setup) (P : Primitives)
    (roCache : List (Bytes × DRKey)) {hon : Bool} (hHon : hon = false) (secrets : Bytes) :
    evalAuthHybridRecvDrKey (.g3_5 : AuthHybridStage) true P roCache
      (none : Option (IdealAuthSession S)) hon secrets = evalHkdfOrRo true P roCache secrets := by
  subst hHon
  unfold evalAuthHybridRecvDrKey AuthHybridStage.idealDrKey
  simp

theorem evalAuthHybridRecvDrKey_g3_5_none_of_true (S : Setup) (P : Primitives)
    (roCache : List (Bytes × DRKey)) {hon : Bool} (hHon : hon = true) (secrets : Bytes) :
    evalAuthHybridRecvDrKey (.g3_5 : AuthHybridStage) true P roCache
      (none : Option (IdealAuthSession S)) hon secrets =
      (sampleDRKey96 >>= fun dk => pure (dk, roCache)) := by
  subst hHon
  unfold evalAuthHybridRecvDrKey AuthHybridStage.idealDrKey
  simp

theorem evalHkdfOrRo_true_of_find_some (P : Primitives)
    (roCache : List (Bytes × DRKey)) (secrets sec : Bytes) (dk : DRKey)
    (hFind : roCache.find? (fun (inp, _) => inp == secrets) = some (sec, dk)) :
    evalHkdfOrRo true P roCache secrets = pure (dk, roCache) := by
  unfold evalHkdfOrRo
  simp [hFind]

theorem evalHkdfOrRo_true_of_find_none (P : Primitives)
    (roCache : List (Bytes × DRKey)) (secrets : Bytes)
    (hFind : roCache.find? (fun (inp, _) => inp == secrets) = none) :
    evalHkdfOrRo true P roCache secrets =
      (sampleDRKey96 >>= fun dk => pure (dk, (secrets, dk) :: roCache)) := by
  unfold evalHkdfOrRo
  simp [hFind]

/-- Couples `evalAuthHybridRecvSchedule` at `.g3_5` against `.g3` up to `bad`. -/
theorem relProbUpToBad_evalAuthHybridRecvSchedule_bind {S : Setup} {α : Type}
    (R : α → α → Prop) (bad : α → Bool) (P : Primitives) (hst35 hst3 : AuthHybridState S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg)
    (k35 k3 : Option (DRKey × Bytes × Bytes × Bytes ×
      List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes))) → ProbComp α)
    (hPrinEq : hst35.base.principals = hst3.base.principals)
    (hRootEq : hst35.base.rootRoCache = hst3.base.rootRoCache)
    (hIdealEq : hst35.idealSessions = hst3.idealSessions)
    (hNone : RelProbUpToBad R bad (k35 none) (k3 none)) (hSubA : ∀ s, hst3.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) =
        some s →
      hst3.base.roCache.find? (fun (inp, _) => inp == secrets) = some (secrets, s.drKey) ∧
      ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
          support (evalAuthHybridRecvCore true P hst3.base.rootRoCache kEntry bEntry msg s.drKey) →
        RelProbUpToBad R bad
          (k35 (some (s.drKey, rk1, ck1_1, pt, hst35.base.roCache, rootRoCache')))
          (k3 (some (s.drKey, rk1, ck1_1, pt, hst3.base.roCache, rootRoCache')))) (hSubB :
      hst3.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) =
        none → (match findHonestPrincipal P hst3.base.principals msg.hdr.ikAPk with
       | some (_, sEntry) => !sEntry.corrupted
       | none             => false) = false → ((∃ sec35 sec3 dk,
          hst35.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec35, dk) ∧
          hst3.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec3, dk) ∧
          ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P hst3.base.rootRoCache kEntry bEntry msg dk) →
            RelProbUpToBad R bad
              (k35 (some (dk, rk1, ck1_1, pt, hst35.base.roCache, rootRoCache')))
              (k3 (some (dk, rk1, ck1_1, pt, hst3.base.roCache, rootRoCache')))) ∨
       (hst35.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        hst3.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
            some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P hst3.base.rootRoCache kEntry bEntry msg dk) →
            RelProbUpToBad R bad
              (k35 (some (dk, rk1, ck1_1, pt, (secrets, dk) :: hst35.base.roCache, rootRoCache')))
              (k3 (some (dk, rk1, ck1_1, pt, (secrets, dk) :: hst3.base.roCache, rootRoCache'))))))
    (hSubC : hst3.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) =
        none → (match findHonestPrincipal P hst3.base.principals msg.hdr.ikAPk with
       | some (_, sEntry) => !sEntry.corrupted
       | none             => false) = true →
      hst3.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
      ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
          some (rk1, ck1_1, pt, rootRoCache') ∈
            support (evalAuthHybridRecvCore true P hst3.base.rootRoCache kEntry bEntry msg dk) →
          RelProbUpToBad R bad (k35 (some (dk, rk1, ck1_1, pt, hst35.base.roCache, rootRoCache')))
            (k3 (some (dk, rk1, ck1_1, pt, (secrets, dk) :: hst3.base.roCache, rootRoCache')))) :
    RelProbUpToBad R bad
      (evalAuthHybridRecvSchedule .g3_5 true P hst35 kEntry bEntry opkPk? secrets msg >>= k35)
      (evalAuthHybridRecvSchedule .g3 true P hst3 kEntry bEntry opkPk? secrets msg >>= k3) := by
  rw [evalAuthHybridRecvSchedule_g3_5_eq, evalAuthHybridRecvSchedule_g3_eq]
  dsimp (config := { zetaHave := true }) only
  rw [hPrinEq, hRootEq, hIdealEq, evalAuthHybridRecvDrKey_g3_eq, bind_assoc, bind_assoc]
  cases hMatch : hst3.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) with
  | some s =>
    rcases hSubA s hMatch with ⟨hFindRo, hPostA⟩
    rw [evalAuthHybridRecvDrKey_g3_5_some, evalHkdfOrRo_true_of_find_some P _ _ _ _ hFindRo,
        pure_bind, pure_bind]
    exact relProbUpToBad_evalAuthHybridRecvPost_bind R bad true P hst3.base.rootRoCache
      kEntry bEntry msg s.drKey hst35.base.roCache hst3.base.roCache k35 k3 hNone hPostA
  | none =>
    rcases hFp : findHonestPrincipal P hst3.base.principals msg.hdr.ikAPk with _ | ⟨_u, sEntry⟩
    · rw [hFp] at hSubB
      dsimp only at hSubB ⊢; rw [evalAuthHybridRecvDrKey_g3_5_none_of_false S P _ rfl]
      rcases hSubB hMatch rfl with ⟨sec35, sec3, dk, hF35, hF3, hPostHit⟩ | ⟨hF35, hF3, hPostMiss⟩
      · rw [evalHkdfOrRo_true_of_find_some P _ _ _ _ hF35,
            evalHkdfOrRo_true_of_find_some P _ _ _ _ hF3, pure_bind, pure_bind]
        exact relProbUpToBad_evalAuthHybridRecvPost_bind R bad true P hst3.base.rootRoCache
          kEntry bEntry msg dk hst35.base.roCache hst3.base.roCache k35 k3 hNone hPostHit
      · rw [evalHkdfOrRo_true_of_find_none P _ _ hF35, evalHkdfOrRo_true_of_find_none P _ _ hF3,
            bind_assoc, bind_assoc]
        refine RelProbUpToBad.bind_same_support sampleDRKey96 (fun dk hdk => ?_)
        rw [pure_bind, pure_bind]
        exact relProbUpToBad_evalAuthHybridRecvPost_bind R bad true P hst3.base.rootRoCache
          kEntry bEntry msg dk ((secrets, dk) :: hst35.base.roCache)
          ((secrets, dk) :: hst3.base.roCache) k35 k3 hNone (hPostMiss dk hdk)
    · rw [hFp] at hSubB hSubC
      dsimp only at hSubB hSubC ⊢
      cases hCorr : sEntry.corrupted
      · rw [hCorr] at hSubC
        rcases hSubC hMatch rfl with ⟨hF3, hPostC⟩
        rw [Bool.not_false, evalAuthHybridRecvDrKey_g3_5_none_of_true S P _ rfl,
            evalHkdfOrRo_true_of_find_none P _ _ hF3,
            bind_assoc, bind_assoc]
        refine RelProbUpToBad.bind_same_support sampleDRKey96 (fun dk hdk => ?_)
        rw [pure_bind, pure_bind]
        exact relProbUpToBad_evalAuthHybridRecvPost_bind R bad true P hst3.base.rootRoCache
          kEntry bEntry msg dk hst35.base.roCache ((secrets, dk) :: hst3.base.roCache)
          k35 k3 hNone (hPostC dk hdk)
      · rw [hCorr] at hSubB
        rw [Bool.not_true, evalAuthHybridRecvDrKey_g3_5_none_of_false S P _ rfl]
        rcases hSubB hMatch rfl with ⟨sec35, sec3, dk, hF35, hF3, hPostHit⟩ |
            ⟨hF35, hF3, hPostMiss⟩
        · rw [evalHkdfOrRo_true_of_find_some P _ _ _ _ hF35,
              evalHkdfOrRo_true_of_find_some P _ _ _ _ hF3, pure_bind, pure_bind]
          exact relProbUpToBad_evalAuthHybridRecvPost_bind R bad true P hst3.base.rootRoCache
            kEntry bEntry msg dk hst35.base.roCache hst3.base.roCache k35 k3 hNone hPostHit
        · rw [evalHkdfOrRo_true_of_find_none P _ _ hF35, evalHkdfOrRo_true_of_find_none P _ _ hF3,
              bind_assoc, bind_assoc]
          refine RelProbUpToBad.bind_same_support sampleDRKey96 (fun dk hdk => ?_)
          rw [pure_bind, pure_bind]
          exact relProbUpToBad_evalAuthHybridRecvPost_bind R bad true P hst3.base.rootRoCache
            kEntry bEntry msg dk ((secrets, dk) :: hst35.base.roCache)
            ((secrets, dk) :: hst3.base.roCache) k35 k3 hNone (hPostMiss dk hdk)

/-- Pure pre-schedule validation for `.recvOPK k j o msg` on `st : AuthState S`. -/
def parseAuthRecvOPKPre {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg) (st : AuthState S) :
    Option (PrincipalEntry × SpkBundleEntry × OpkEntry ×
      List (Nat × KeyId × KeyId × Bytes) × Bytes) :=
  if true && st.hasWonAuth then none
  else if !(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then none
  else if st.usedRecvOPK.contains (k.val, j.val, o.val) then none
  else if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then none
  else match st.principals.find? (fun (idx, _) => idx == k.val) with
  | none => none
  | some (_, kEntry) => match st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => none
    | some (_, bEntry) =>
      match st.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
      | none => none
      | some (_, oEntry) => if oEntry.consumed then none else
          let (replayOk, usedTriples') :=
            checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val
              msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
          if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then none
          else match P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
          | none => none
          | some ss => some (kEntry, bEntry, oEntry, usedTriples', ss)

/-- Pure pre-schedule validation for `.recvNoOPK k j l msg` on `st : AuthState S`. -/
def parseAuthRecvNoOPKPre {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg) (st : AuthState S) :
    Option (PrincipalEntry × SpkBundleEntry × List (Nat × KeyId × KeyId × Bytes) × Bytes) :=
  if true && st.hasWonAuth then none
  else if !(msg.hdr.spkId == UInt32.ofNat j.val && msg.hdr.pqspkId == UInt32.ofNat j.val &&
       msg.hdr.opkId? == none &&
       msg.hdr.ikAPk.length == 32 &&
       msg.hdr.ekAPk.length == 32 &&
       msg.ephAPk.length == 32) then none
  else if st.usedRecvNoOPK.contains (k.val, j.val, l.val) then none
  else if !koskSenderOk P st.principals st.advKeys msg.hdr.ikAPk then none
  else match st.principals.find? (fun (idx, _) => idx == k.val) with
  | none => none
  | some (_, kEntry) => match st.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
    | none => none
    | some (_, bEntry) =>
      let (replayOk, usedTriples') :=
        checkAndMarkKyberBaseKeySeen st.seenKyberBaseKeys k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk
      if !replayOk || !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk then none
      else match P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
      | none => none
      | some ss => some (kEntry, bEntry, usedTriples', ss)

@[simp]
theorem parseAuthRecvOPKPre_withAuthBaseRoCache {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (c : List (Bytes × DRKey)) (st : AuthState S) :
    parseAuthRecvOPKPre P k j o msg (withAuthBaseRoCache c st) =
      parseAuthRecvOPKPre P k j o msg st := rfl

@[simp]
theorem parseAuthRecvNoOPKPre_withAuthBaseRoCache {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (c : List (Bytes × DRKey)) (st : AuthState S) :
    parseAuthRecvNoOPKPre P k j l msg (withAuthBaseRoCache c st) =
      parseAuthRecvNoOPKPre P k j l msg st := rfl

def wrapAuthAdvLatchedRecv {S : Setup} (k : Fin S.N_id) (j : Fin S.N_recv)
    (msg : PreKeyMsg) (s : AuthAdvLatchedState S) (p : AuthResponse × AuthHybridState S) :
    AuthResponse × AuthAdvLatchedState S :=
  let rRec : AuthRespRecord :=
    { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk }
  (p.1, { s with adv := { s.adv with hyb := p.2, respRecs := rRec :: s.adv.respRecs } })

def finishLatchedRecvOPK {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes ×
      List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    AuthResponse × AuthAdvLatchedState S :=
  wrapAuthAdvLatchedRecv k j msg s
    (finishAuthHybridRecvOPK true P k j o kEntry bEntry oEntry usedTriples' msg hstDec res?)

def finishLatchedRecvNoOPK {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes ×
      List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes)))) :
    AuthResponse × AuthAdvLatchedState S :=
  wrapAuthAdvLatchedRecv k j msg s
    (finishAuthHybridRecvNoOPK true P k j l kEntry bEntry usedTriples' msg hstDec res?)

theorem pqxdhAuthAdvLatchedStageImpl_recvOPK_run_eq {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (msg : PreKeyMsg) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl stage S P (.recvOPK k j o msg)).run s =
      match parseAuthRecvOPKPre P k j o msg s.hyb.base with
      | none => pure (wrapAuthAdvLatchedRecv k j msg s (.noneResp, s.hyb))
      | some (kEntry, bEntry, oEntry, usedTriples', ss) =>
        let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
          k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
          pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
        let hstDec := { s.hyb with recvKemRecs := rRec :: s.hyb.recvKemRecs }
        let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
        let secrets := recvHandshakeSecrets P kEntry bEntry (some dh4) ss msg.hdr
        evalAuthHybridRecvSchedule stage true P hstDec kEntry bEntry
            (some oEntry.opkPk) secrets msg >>= fun res? =>
          pure (finishLatchedRecvOPK P k j o kEntry bEntry oEntry
            usedTriples' msg s hstDec res?) := by
  unfold pqxdhAuthAdvLatchedStageImpl pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl
    parseAuthRecvOPKPre finishLatchedRecvOPK wrapAuthAdvLatchedRecv
    recvHandshakeSecrets AuthAdvLatchedState.hyb
  simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hWon h1 h2 h3 h5
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · cases s.adv.hyb.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp [StateT.run_pure]
    | some pk =>
      rcases pk with ⟨_, kEntry⟩
      cases s.adv.hyb.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp [StateT.run_pure]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        cases s.adv.hyb.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => simp [StateT.run_pure]
        | some po =>
          rcases po with ⟨_, oEntry⟩
          dsimp only; split_ifs <;> simp [StateT.run_pure]
  · cases s.adv.hyb.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp [StateT.run_pure]
    | some pk =>
      rcases pk with ⟨_, kEntry⟩
      cases s.adv.hyb.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp [StateT.run_pure]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        cases s.adv.hyb.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        | none => simp [StateT.run_pure]
        | some po =>
          rcases po with ⟨_, oEntry⟩
          dsimp (config := { zetaHave := true }) only
          split_ifs with h4
          · simp [StateT.run_pure]
          · cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
            | none => simp [StateT.run_pure]
            | some ss =>
              simp only [Bool.true_and] at hWon
              simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift,
                monadLift_self, pure_bind, bind_assoc]
              congr 1
              funext res?
              cases res? with
              | none => simp [finishAuthHybridRecvOPK, StateT.run_pure]
              | some r =>
                rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
                dsimp only [finishAuthHybridRecvOPK]
                rcases findHonestPrincipal P s.adv.hyb.base.principals msg.hdr.ikAPk with
                  _ | ⟨_, senderEntry⟩
                · simp [StateT.run_set, hWon]
                · dsimp only
                  split_ifs <;> simp [StateT.run_set, hWon]

theorem pqxdhAuthAdvLatchedStageImpl_recvNoOPK_run_eq {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (msg : PreKeyMsg) (s : AuthAdvLatchedState S) :
    (pqxdhAuthAdvLatchedStageImpl stage S P (.recvNoOPK k j l msg)).run s =
      match parseAuthRecvNoOPKPre P k j l msg s.hyb.base with
      | none => pure (wrapAuthAdvLatchedRecv k j msg s (.noneResp, s.hyb))
      | some (kEntry, bEntry, usedTriples', ss) =>
        let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
          k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
          pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
        let hstDec := { s.hyb with recvKemRecs := rRec :: s.hyb.recvKemRecs }
        let secrets := recvHandshakeSecrets P kEntry bEntry none ss msg.hdr
        evalAuthHybridRecvSchedule stage true P hstDec kEntry bEntry none secrets msg >>=
          fun res? =>
            pure (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s hstDec res?) := by
  unfold pqxdhAuthAdvLatchedStageImpl pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl
    parseAuthRecvNoOPKPre finishLatchedRecvNoOPK wrapAuthAdvLatchedRecv
    recvHandshakeSecrets AuthAdvLatchedState.hyb
  simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hWon h1 h2 h3 h4
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · simp [StateT.run_pure]
  · cases s.adv.hyb.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp [StateT.run_pure]
    | some pk =>
      rcases pk with ⟨_, kEntry⟩
      cases s.adv.hyb.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp [StateT.run_pure]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        simp [StateT.run_pure]
  · cases s.adv.hyb.base.principals.find? (fun (idx, _) => idx == k.val) with
    | none => simp [StateT.run_pure]
    | some pk =>
      rcases pk with ⟨_, kEntry⟩
      cases s.adv.hyb.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      | none => simp [StateT.run_pure]
      | some pb =>
        rcases pb with ⟨_, bEntry⟩
        dsimp (config := { zetaHave := true }) only
        cases P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
        | none => simp [StateT.run_pure]
        | some ss =>
          simp only [Bool.true_and] at hWon
          simp only [StateT.run_bind, StateT.run_set, StateT.run_monadLift,
            monadLift_self, pure_bind, bind_assoc]
          congr 1
          funext res?
          cases res? with
          | none => simp [finishAuthHybridRecvNoOPK, StateT.run_pure]
          | some r =>
            rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
            dsimp only [finishAuthHybridRecvNoOPK]
            rcases findHonestPrincipal P s.adv.hyb.base.principals msg.hdr.ikAPk with
              _ | ⟨_, senderEntry⟩
            · simp [StateT.run_set, hWon]
            · dsimp only
              split_ifs <;> simp [StateT.run_set, hWon]


theorem finishLatchedRecvOPK_withAuthAdvLatchedRoCache_none {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S) :
    finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
        (withAuthAdvLatchedRoCache c s) (withAuthHybRoCache c hstDec) none =
      Prod.map id (withAuthAdvLatchedRoCache c)
        (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s hstDec none) := rfl

theorem finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (c c35' c3' : List (Bytes × DRKey)) (s : AuthAdvLatchedState S)
    (hstDec : AuthHybridState S) (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
        (withAuthAdvLatchedRoCache c s) (withAuthHybRoCache c hstDec)
        (some (dk, rk1, ck1_1, pt, c35', rootRoCache')) =
      Prod.map id (withAuthAdvLatchedRoCache c35')
        (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s hstDec
          (some (dk, rk1, ck1_1, pt, c3', rootRoCache'))) := by
  unfold finishLatchedRecvOPK finishAuthHybridRecvOPK wrapAuthAdvLatchedRecv
    withAuthAdvLatchedRoCache withAuthAdvRoCache withAuthHybRoCache withAuthBaseRoCache
  dsimp only
  rcases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    _ | ⟨_, senderEntry⟩
  · rfl
  · dsimp only
    cases !senderEntry.corrupted <;> rfl

theorem finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_none {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (c : List (Bytes × DRKey)) (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S) :
    finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
        (withAuthAdvLatchedRoCache c s) (withAuthHybRoCache c hstDec) none =
      Prod.map id (withAuthAdvLatchedRoCache c)
        (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s hstDec none) := rfl

theorem finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_some {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (c c35' c3' : List (Bytes × DRKey)) (s : AuthAdvLatchedState S)
    (hstDec : AuthHybridState S) (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
        (withAuthAdvLatchedRoCache c s) (withAuthHybRoCache c hstDec)
        (some (dk, rk1, ck1_1, pt, c35', rootRoCache')) =
      Prod.map id (withAuthAdvLatchedRoCache c35')
        (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s hstDec
          (some (dk, rk1, ck1_1, pt, c3', rootRoCache'))) := by
  unfold finishLatchedRecvNoOPK finishAuthHybridRecvNoOPK wrapAuthAdvLatchedRecv
    withAuthAdvLatchedRoCache withAuthAdvRoCache withAuthHybRoCache withAuthBaseRoCache
  dsimp only
  rcases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    _ | ⟨_, senderEntry⟩
  · rfl
  · dsimp only
    cases !senderEntry.corrupted <;> rfl

private theorem map_pow8_opkPk_mark_consumed {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) : (opkEntries.map (fun (idx, e) =>
      if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))).map
        (fun (_, e) => P.pow8 e.opkPk) = opkEntries.map (fun (_, e) => P.pow8 e.opkPk) := by
  rw [List.map_map]; refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_); dsimp only [Function.comp]
  split_ifs <;> rfl

@[simp]
theorem isAuthG3Abort_finishLatchedRecvOPK {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes ×
      List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes)))) : isAuthG3Abort P
      (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s hstDec res?).2.hyb =
    isAuthG3Abort P hstDec := by
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨dk, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    unfold finishLatchedRecvOPK finishAuthHybridRecvOPK wrapAuthAdvLatchedRecv
      AuthAdvLatchedState.hyb
    dsimp only
    rcases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
      _ | ⟨_, senderEntry⟩
    · unfold isAuthG3Abort hasBadSigAuth hasEcPkCollisionAuth hasKemPkCollisionAuth
        hasBadKemShCrAuth allHonestEcPksAuth allHonestKemPksAuth
        HasAuthState.toAuthState HasAuthState.toInitKemRecs HasAuthState.toRecvKemRecs
        instHasAuthStateAuthHybridState
      dsimp only; rw [map_pow8_opkPk_mark_consumed]
    · dsimp only
      split_ifs <;> {
        unfold isAuthG3Abort hasBadSigAuth hasEcPkCollisionAuth hasKemPkCollisionAuth
          hasBadKemShCrAuth allHonestEcPksAuth allHonestKemPksAuth
          HasAuthState.toAuthState HasAuthState.toInitKemRecs HasAuthState.toRecvKemRecs
          instHasAuthStateAuthHybridState
        dsimp only; rw [map_pow8_opkPk_mark_consumed]
      }

@[simp]
theorem isAuthG3Abort_finishLatchedRecvNoOPK {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes ×
      List (Bytes × DRKey) × List ((Bytes × Bytes) × (Bytes × Bytes)))) : isAuthG3Abort P
      (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s hstDec res?).2.hyb =
    isAuthG3Abort P hstDec := by
  cases res? with
  | none => rfl
  | some r =>
    rcases r with ⟨dk, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    unfold finishLatchedRecvNoOPK finishAuthHybridRecvNoOPK wrapAuthAdvLatchedRecv
      AuthAdvLatchedState.hyb
    dsimp only
    rcases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
      _ | ⟨_, senderEntry⟩
    · rfl
    · dsimp only
      split_ifs <;> rfl

theorem parseAuthRecvOPKPre_some_props {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S)
    {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry} {oEntry : OpkEntry}
    {usedTriples' : List (Nat × KeyId × KeyId × Bytes)} {ss : Bytes}
    (hPre : parseAuthRecvOPKPre P k j o msg hst.base =
      some (kEntry, bEntry, oEntry, usedTriples', ss)) :
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
    msg.hdr.spkId = UInt32.ofNat j.val ∧ msg.hdr.pqspkId = UInt32.ofNat j.val ∧
    msg.hdr.opkId? = some (UInt32.ofNat o.val) ∧ msg.hdr.ikAPk.length = 32 ∧
    msg.hdr.ekAPk.length = 32 ∧ msg.ephAPk.length = 32 ∧ (k.val, kEntry) ∈ hst.base.principals ∧
    ((k.val, j.val), bEntry) ∈ hst.base.spkBundles ∧
    ((k.val, j.val, o.val), oEntry) ∈ hst.base.opkEntries ∧
    (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
      msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk) = (true, usedTriples') ∧
    (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val, msg.hdr.ekAPk) ∈ usedTriples' ∧
    hst.base.seenKyberBaseKeys.Sublist usedTriples' ∧ P.isCanonical msg.hdr.ekAPk = true ∧
    P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt = some ss ∧
    ValidAuthRespHandshake S P hstDec k j kEntry bEntry (some oEntry.opkPk)
      (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss rRec msg.hdr := by
  unfold parseAuthRecvOPKPre at hPre
  split_ifs at hPre with hWon hHdr hUsed hKosk
  rcases hPK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    _ | ⟨kIdx, kEntry'⟩
  · rw [hPK] at hPre; nomatch hPre
  · rw [hPK] at hPre
    rcases hPB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      _ | ⟨bIdx, bEntry'⟩
    · rw [hPB] at hPre; nomatch hPre
    · rw [hPB] at hPre
      rcases hPO : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
        _ | ⟨oIdx, oEntry'⟩
      · rw [hPO] at hPre; nomatch hPre
      · rw [hPO] at hPre
        dsimp (config := { zetaHave := true }) only at hPre
        split_ifs at hPre with hCons hRep
        rcases hDec : P.kemDecaps bEntry'.pqspkSk msg.hdr.kemCt with _ | ss'
        · rw [hDec] at hPre; nomatch hPre
        · simp only [hDec, Option.some.injEq, Prod.mk.injEq] at hPre
          rcases hPre with ⟨hkEq, hbEq, hoEq, hTriplesEq, hSsEq⟩; subst kEntry' bEntry' oEntry' ss'
          simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hHdr
          rcases hHdr with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, hOpkId⟩, hIkLen⟩, hEkLen⟩, hEphLen⟩
          simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hRep
          rcases hRep with ⟨⟨hReplayOk, hEkCanon⟩, _⟩
          have hkIdx : kIdx = k.val :=
            beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × _) => x.1 == k.val) hPK)
          have hbIdx : bIdx = (k.val, j.val) :=
            beq_iff_eq.mp (List.find?_some (p := fun (x : (Nat × Nat) × _) =>
              x.1 == (k.val, j.val)) hPB)
          have hoIdx : oIdx = (k.val, j.val, o.val) :=
            beq_iff_eq.mp (List.find?_some (p := fun (x : (Nat × Nat × Nat) × _) =>
              x.1 == (k.val, j.val, o.val)) hPO)
          subst hkIdx hbIdx hoIdx
          have hkMem : (k.val, kEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hPK
          have hbMem : ((k.val, j.val), bEntry) ∈ hst.base.spkBundles :=
            List.mem_of_find?_eq_some hPB
          have hoMem : ((k.val, j.val, o.val), oEntry) ∈ hst.base.opkEntries :=
            List.mem_of_find?_eq_some hPO
          have hMark : checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
              msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk = (true, usedTriples') :=
            Prod.ext hReplayOk hTriplesEq
          have hMarkDef := hMark
          unfold checkAndMarkKyberBaseKeySeen at hMarkDef; dsimp only at hMarkDef
          split_ifs at hMarkDef with hCont
          · nomatch hMarkDef
          · injection hMarkDef with _ hUt
            subst hUt
            refine ⟨hSpkId, hPqspkId, hOpkId, hIkLen, hEkLen, hEphLen, hkMem, hbMem, hoMem,
              hMark, ?_, List.sublist_cons_self _ _, hEkCanon, hDec, ?_⟩
            · rw [hSpkId, hPqspkId]
              exact List.mem_cons_self
            · exact ⟨hkMem, hbMem, hIkLen, hEkLen, hEkCanon, hDec, List.mem_cons_self,
                rfl, rfl, rfl, rfl, Or.inr ⟨o.val, oEntry, hoMem, rfl, rfl⟩⟩

theorem parseAuthRecvNoOPKPre_some_props {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (hst : AuthHybridState S) {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {usedTriples' : List (Nat × KeyId × KeyId × Bytes)} {ss : Bytes}
    (hPre : parseAuthRecvNoOPKPre P k j l msg hst.base = some (kEntry, bEntry, usedTriples', ss)) :
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec := { hst with recvKemRecs := rRec :: hst.recvKemRecs }
    msg.hdr.spkId = UInt32.ofNat j.val ∧ msg.hdr.pqspkId = UInt32.ofNat j.val ∧
    msg.hdr.opkId? = none ∧ msg.hdr.ikAPk.length = 32 ∧ msg.hdr.ekAPk.length = 32 ∧
    msg.ephAPk.length = 32 ∧ (k.val, kEntry) ∈ hst.base.principals ∧
    ((k.val, j.val), bEntry) ∈ hst.base.spkBundles ∧
    (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
      msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk) = (true, usedTriples') ∧
    (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val, msg.hdr.ekAPk) ∈ usedTriples' ∧
    hst.base.seenKyberBaseKeys.Sublist usedTriples' ∧ P.isCanonical msg.hdr.ekAPk = true ∧
    P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt = some ss ∧
    ValidAuthRespHandshake S P hstDec k j kEntry bEntry none none ss rRec msg.hdr := by
  unfold parseAuthRecvNoOPKPre at hPre
  split_ifs at hPre with hWon hHdr hUsed hKosk
  rcases hPK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
    _ | ⟨kIdx, kEntry'⟩
  · rw [hPK] at hPre; nomatch hPre
  · rw [hPK] at hPre
    rcases hPB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
      _ | ⟨bIdx, bEntry'⟩
    · rw [hPB] at hPre; nomatch hPre
    · rw [hPB] at hPre
      dsimp (config := { zetaHave := true }) only at hPre
      split_ifs at hPre with hRep
      rcases hDec : P.kemDecaps bEntry'.pqspkSk msg.hdr.kemCt with _ | ss'
      · rw [hDec] at hPre; nomatch hPre
      · simp only [hDec, Option.some.injEq, Prod.mk.injEq] at hPre
        rcases hPre with ⟨hkEq, hbEq, hTriplesEq, hSsEq⟩; subst kEntry' bEntry' ss'
        simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq] at hHdr
        rcases hHdr with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, hOpkId⟩, hIkLen⟩, hEkLen⟩, hEphLen⟩
        simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hRep
        rcases hRep with ⟨⟨hReplayOk, hEkCanon⟩, _⟩
        have hkIdx : kIdx = k.val :=
          beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × _) => x.1 == k.val) hPK)
        have hbIdx : bIdx = (k.val, j.val) :=
          beq_iff_eq.mp (List.find?_some (p := fun (x : (Nat × Nat) × _) =>
            x.1 == (k.val, j.val)) hPB)
        subst hkIdx hbIdx
        have hkMem : (k.val, kEntry) ∈ hst.base.principals := List.mem_of_find?_eq_some hPK
        have hbMem : ((k.val, j.val), bEntry) ∈ hst.base.spkBundles :=
          List.mem_of_find?_eq_some hPB
        have hMark : checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
            msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk = (true, usedTriples') :=
          Prod.ext hReplayOk hTriplesEq
        have hMarkDef := hMark
        unfold checkAndMarkKyberBaseKeySeen at hMarkDef; dsimp only at hMarkDef
        split_ifs at hMarkDef with hCont
        · nomatch hMarkDef
        · injection hMarkDef with _ hUt
          subst hUt
          refine ⟨hSpkId, hPqspkId, hOpkId, hIkLen, hEkLen, hEphLen, hkMem, hbMem,
            hMark, ?_, List.sublist_cons_self _ _, hEkCanon, hDec, ?_⟩
          · rw [hSpkId, hPqspkId]
            exact List.mem_cons_self
          · exact ⟨hkMem, hbMem, hIkLen, hEkLen, hEkCanon, hDec, List.mem_cons_self,
              rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem finishLatchedRecvOPK_some_fields {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S) (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey)) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    let y := finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s hstDec
      (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))
    y.2.adv.respRecs =
      { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk } ::
        s.adv.respRecs ∧ y.2.hyb.recvKemRecs = hstDec.recvKemRecs ∧
    y.2.hyb.base.spkBundles = hstDec.base.spkBundles ∧
    y.2.hyb.base.seenKyberBaseKeys = usedTriples' := by
  unfold finishLatchedRecvOPK finishAuthHybridRecvOPK wrapAuthAdvLatchedRecv
    AuthAdvLatchedState.hyb
  dsimp only
  rcases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    _ | ⟨_, senderEntry⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · dsimp only
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem finishLatchedRecvNoOPK_some_fields {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S) (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey)) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    let y := finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s hstDec
      (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))
    y.2.adv.respRecs =
      { bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk } ::
        s.adv.respRecs ∧ y.2.hyb.recvKemRecs = hstDec.recvKemRecs ∧
    y.2.hyb.base.spkBundles = hstDec.base.spkBundles ∧
    y.2.hyb.base.seenKyberBaseKeys = usedTriples' := by
  unfold finishLatchedRecvNoOPK finishAuthHybridRecvNoOPK wrapAuthAdvLatchedRecv
    AuthAdvLatchedState.hyb
  dsimp only
  rcases findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    _ | ⟨_, senderEntry⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · dsimp only
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem authRespRoOrigin_finishLatchedRecvOPK {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (s3 : AuthAdvLatchedState S)
    {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry} {oEntry : OpkEntry}
    {usedTriples' : List (Nat × KeyId × KeyId × Bytes)} {ss : Bytes}
    (hPre : parseAuthRecvOPKPre P k j o msg s3.hyb.base =
      some (kEntry, bEntry, oEntry, usedTriples', ss)) (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey)) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
    let secrets := recvHandshakeSecrets P kEntry bEntry (some dh4) ss msg.hdr
    let y3 := finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
      s3 hstDec (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))
    AuthRespRoOrigin P y3.2 secrets ∧
    (∀ sec', AuthRespRoOrigin P s3 sec' → AuthRespRoOrigin P y3.2 sec') := by
  have hw := hP.toWellFormedPrimitivesδ
  rcases parseAuthRecvOPKPre_some_props P k j o msg s3.hyb hPre with
    ⟨_, _, _, hIkLen, hEkLen, _, _, hbMem, _, _, hUtMem, hUtSub, hEkCanon, hDec, _⟩
  let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
    k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
    pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
  let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
  rcases finishLatchedRecvOPK_some_fields P k j o kEntry bEntry oEntry usedTriples' msg
      s3 hstDec dk rk1 ck1_1 pt roCache' rootRoCache' with
    ⟨hRespEq, hKemEq, hSpkEq, hKybEq⟩
  have hSsLen : ss.length = 32 := hw.kemDecaps_len bEntry.pqspkSk msg.hdr.kemCt ss hDec
  refine ⟨?_, fun sec' hOrig => ?_⟩
  · refine ⟨{ bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk },
      rRec, bEntry, ?_, ?_, ?_, rfl, rfl, rfl, hDec, hEkCanon, hEkLen, hIkLen, ?_, ?_, ?_, ?_⟩
    · rw [hRespEq]; exact List.mem_cons_self
    · rw [hKemEq]; exact List.mem_cons_self
    · rw [hSpkEq]; exact hbMem
    · rw [hKybEq]; exact hUtMem
    · exact extractDh1_buildSecrets (hw.x25519_len _ _)
    · exact extractDh3_buildSecrets (hw.x25519_len _ _) (hw.x25519_len _ _) (hw.x25519_len _ _)
    · left
      exact extractKemSsOPK_buildSecrets (hw.x25519_len _ _) (hw.x25519_len _ _)
        (hw.x25519_len _ _) (hw.x25519_len _ _) hSsLen
  · rcases hOrig with ⟨r, rKem, b_r, hrMem, hrKemMem, hbrMem, hbKey, hPqPk, hPqSk,
      hrDec, hrCanon, hrEkLen, hrIkLen, hKybMem, hDh1, hDh3, hSs⟩
    refine ⟨r, rKem, b_r, ?_, ?_, ?_, hbKey, hPqPk, hPqSk, hrDec, hrCanon, hrEkLen, hrIkLen,
      ?_, hDh1, hDh3, hSs⟩
    · rw [hRespEq]; exact List.mem_cons_of_mem _ hrMem
    · rw [hKemEq]; exact List.mem_cons_of_mem _ hrKemMem
    · rw [hSpkEq]; exact hbrMem
    · rw [hKybEq]; exact hUtSub.subset hKybMem

theorem authRespRoOrigin_finishLatchedRecvNoOPK {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (s3 : AuthAdvLatchedState S) {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {usedTriples' : List (Nat × KeyId × KeyId × Bytes)} {ss : Bytes}
    (hPre : parseAuthRecvNoOPKPre P k j l msg s3.hyb.base =
      some (kEntry, bEntry, usedTriples', ss)) (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey)) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    let secrets := recvHandshakeSecrets P kEntry bEntry none ss msg.hdr
    let y3 := finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
      s3 hstDec (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))
    AuthRespRoOrigin P y3.2 secrets ∧
    (∀ sec', AuthRespRoOrigin P s3 sec' → AuthRespRoOrigin P y3.2 sec') := by
  have hw := hP.toWellFormedPrimitivesδ
  rcases parseAuthRecvNoOPKPre_some_props P k j l msg s3.hyb hPre with
    ⟨_, _, _, hIkLen, hEkLen, _, _, hbMem, _, hUtMem, hUtSub, hEkCanon, hDec, _⟩
  let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
    k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
    pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
  let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
  rcases finishLatchedRecvNoOPK_some_fields P k j l kEntry bEntry usedTriples' msg
      s3 hstDec dk rk1 ck1_1 pt roCache' rootRoCache' with
    ⟨hRespEq, hKemEq, hSpkEq, hKybEq⟩
  have hSsLen : ss.length = 32 := hw.kemDecaps_len bEntry.pqspkSk msg.hdr.kemCt ss hDec
  refine ⟨?_, fun sec' hOrig => ?_⟩
  · refine ⟨{ bKey := (k.val, j.val), ikAPk := msg.hdr.ikAPk, ekAPk := msg.hdr.ekAPk },
      rRec, bEntry, ?_, ?_, ?_, rfl, rfl, rfl, hDec, hEkCanon, hEkLen, hIkLen, ?_, ?_, ?_, ?_⟩
    · rw [hRespEq]; exact List.mem_cons_self
    · rw [hKemEq]; exact List.mem_cons_self
    · rw [hSpkEq]; exact hbMem
    · rw [hKybEq]; exact hUtMem
    · exact extractDh1_buildSecrets (hw.x25519_len _ _)
    · exact extractDh3_buildSecrets (hw.x25519_len _ _) (hw.x25519_len _ _) (hw.x25519_len _ _)
    · right
      exact extractKemSsNoOPK_buildSecrets (hw.x25519_len _ _) (hw.x25519_len _ _)
        (hw.x25519_len _ _) hSsLen
  · rcases hOrig with ⟨r, rKem, b_r, hrMem, hrKemMem, hbrMem, hbKey, hPqPk, hPqSk,
      hrDec, hrCanon, hrEkLen, hrIkLen, hKybMem, hDh1, hDh3, hSs⟩
    refine ⟨r, rKem, b_r, ?_, ?_, ?_, hbKey, hPqPk, hPqSk, hrDec, hrCanon, hrEkLen, hrIkLen,
      ?_, hDh1, hDh3, hSs⟩
    · rw [hRespEq]; exact List.mem_cons_of_mem _ hrMem
    · rw [hKemEq]; exact List.mem_cons_of_mem _ hrKemMem
    · rw [hSpkEq]; exact hbrMem
    · rw [hKybEq]; exact hUtSub.subset hKybMem

/-- Step coupling for `.recvOPK k j o msg` between `.g3_5` and `.g3`, given the subcase premises. -/
theorem fgAuthStepCoupling_cutoff_latched_recvOPK {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (Inv : AuthAdvLatchedState S → AuthAdvLatchedState S → Prop)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (s35 s3 : AuthAdvLatchedState S) (_hInv : Inv s35 s3) (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (hRunInv : ValidAuthHybridRunInv S P s3.hyb) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hbF : badAuthFgAnyLatchedMono P maxRo s3.toFg = false)
    (hRej : parseAuthRecvOPKPre P k j o msg s3.hyb.base = none →
      Inv (wrapAuthAdvLatchedRecv k j msg s35 (.noneResp, s35.hyb)).2
          (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2 ∨
      badAuthFgAnyLatchedMono P maxRo
        (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2.toFg = true)
    (hSchedNone : ∀ kEntry bEntry oEntry usedTriples' ss,
      parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      isAuthG3Abort P hstDec = false →
      Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
            s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec) none).2
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec none).2 ∨
      badAuthFgAnyLatchedMono P maxRo
        (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
          s3 hstDec none).2.toFg = true) (hSubA : ∀ kEntry bEntry oEntry usedTriples' ss s,
      parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
      let secrets := recvHandshakeSecrets P kEntry bEntry (some dh4) ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
          bEntry.pqspkPk msg.hdr) = some s →
      s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (secrets, s.drKey) ∧
      ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
          support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache
            kEntry bEntry msg s.drKey) →
        Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
              s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
              (some (s.drKey, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
            (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
              (some (s.drKey, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2 ∨
        badAuthFgAnyLatchedMono P maxRo
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
            (some (s.drKey, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2.toFg = true)
    (hSubB : ∀ kEntry bEntry oEntry usedTriples' ss, parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
      let secrets := recvHandshakeSecrets P kEntry bEntry (some dh4) ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
          bEntry.pqspkPk msg.hdr) = none →
      (match findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk with
       | some (_, sEntry) => !sEntry.corrupted
       | none             => false) = false → ((∃ sec35 sec3 dk,
          s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec35, dk) ∧
          s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec3, dk) ∧
          ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
            Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
                  s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
                  (some (dk, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
                (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                  (some (dk, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2 ∨
            badAuthFgAnyLatchedMono P maxRo
              (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2.toFg = true) ∨
       (s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
            some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
            Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
                  s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec) (some (dk, rk1, ck1_1, pt,
                    (secrets, dk) :: s35.hyb.base.roCache, rootRoCache'))).2
                (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                  (some (dk, rk1, ck1_1, pt,
                    (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2 ∨
            badAuthFgAnyLatchedMono P maxRo
              (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt,
                  (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2.toFg = true)))
    (hSubC : ∀ kEntry bEntry oEntry usedTriples' ss u_r senderEntry,
      parseAuthRecvOPKPre P k j o msg s3.hyb.base =
        some (kEntry, bEntry, oEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let dh4 := P.x25519 oEntry.opkSk msg.hdr.ekAPk
      let secrets := recvHandshakeSecrets P kEntry bEntry (some dh4) ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk)
          bEntry.pqspkPk msg.hdr) = none →
      findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk = some (u_r, senderEntry) →
      (!senderEntry.corrupted) = true →
      s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
      ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
          some (rk1, ck1_1, pt, rootRoCache') ∈
            support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
          let recvEv : RecvdOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
          (consumeMatchingSentOPK P recvEv s3.hyb.base.sentOPKEvents).1 = false →
          Inv (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
                s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
                (some (dk, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
              (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt,
                  (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2 ∨
          badAuthFgAnyLatchedMono P maxRo
            (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
              (some (dk, rk1, ck1_1, pt,
                (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2.toFg = true) :
    RelProbUpToBad (fun y35 y3 => (y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.recvOPK k j o msg)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.recvOPK k j o msg)).run s3) := by
  rw [pqxdhAuthAdvLatchedStageImpl_recvOPK_run_eq, pqxdhAuthAdvLatchedStageImpl_recvOPK_run_eq]
  have hBase35 : s35.hyb.base = withAuthBaseRoCache s35.hyb.base.roCache s3.hyb.base := by
    conv_lhs => rw [hAg]
    rfl
  have hPreEq : parseAuthRecvOPKPre P k j o msg s35.hyb.base =
      parseAuthRecvOPKPre P k j o msg s3.hyb.base := by
    rw [hBase35, parseAuthRecvOPKPre_withAuthBaseRoCache]
  rw [hPreEq]
  cases hPre : parseAuthRecvOPKPre P k j o msg s3.hyb.base with
  | none =>
    rcases hRej hPre with hInv' | hBad'
    · exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hInv'⟩)
    · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
        rw [mem_support_pure_iff] at hy; subst hy; exact hBad')
  | some p =>
    rcases p with ⟨kEntry, bEntry, oEntry, usedTriples', ss⟩
    dsimp only
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec3 := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    have hDecEq : ({
        base := s35.hyb.base, initKemRecs := s35.hyb.initKemRecs,
        recvKemRecs := rRec :: s35.hyb.recvKemRecs,
        idealSessions := s35.hyb.idealSessions } : AuthHybridState S) =
        withAuthHybRoCache s35.hyb.base.roCache hstDec3 := by
      change { s35.hyb with recvKemRecs := rRec :: s35.hyb.recvKemRecs } = _
      conv_lhs => rw [hAg]
      rfl
    by_cases hAbDec : isAuthG3Abort P hstDec3 = true
    · refine RelProbUpToBad.of_support_rel _ _ (fun y35 hy35 y3 hy3 _ => ?_)
      simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy35 hy3
      rcases hy35 with ⟨res35, _, rfl⟩
      rcases hy3 with ⟨res3, _, rfl⟩
      refine Or.inr ?_
      rw [isAuthG3Abort_finishLatchedRecvOPK, isAuthG3Abort_finishLatchedRecvOPK,
          hDecEq, isAuthG3Abort_withBaseRoCache]
      exact ⟨hAbDec, hAbDec⟩
    · have hAbDecF : isAuthG3Abort P hstDec3 = false := Bool.eq_false_iff.mpr hAbDec
      rw [hDecEq]
      refine relProbUpToBad_evalAuthHybridRecvSchedule_bind _ _ P
        (withAuthHybRoCache s35.hyb.base.roCache hstDec3) hstDec3 kEntry bEntry
        (some oEntry.opkPk) _ msg _ _ rfl rfl rfl ?_ ?_ ?_ ?_
      · rcases hSchedNone kEntry bEntry oEntry usedTriples' ss hPre hAbDecF with hI | hB
        · exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hI⟩)
        · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
            rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro s hMatch
        rcases hSubA kEntry bEntry oEntry usedTriples' ss s hPre hAbDecF hMatch with
          ⟨hRoFind, hPostA⟩
        refine ⟨hRoFind, fun rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
        rcases hPostA rk1 ck1_1 pt rootRoCache' hCore with hI | hB
        · have hFst := congrArg Prod.fst
            (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some P k j o kEntry bEntry oEntry
              usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache s3.hyb.base.roCache
              s3 hstDec3 s.drKey rk1 ck1_1 pt rootRoCache')
          rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
        · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
            rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro hMatchNone hNotHon
        rcases hSubB kEntry bEntry oEntry usedTriples' ss hPre hAbDecF hMatchNone hNotHon with
          ⟨sec35, sec3, dk, hF35, hF3, hHit⟩ | ⟨hF35, hF3, hMiss⟩
        · left
          refine ⟨sec35, sec3, dk, hF35, hF3, fun rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          rcases hHit rk1 ck1_1 pt rootRoCache' hCore with hI | hB
          · have hFst := congrArg Prod.fst
              (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some P k j o kEntry bEntry oEntry
                usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache s3.hyb.base.roCache
                s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
            rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
          · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
              rw [mem_support_pure_iff] at hy; subst hy; exact hB)
        · right
          refine ⟨hF35, hF3, fun dk hdk rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          rcases hMiss dk hdk rk1 ck1_1 pt rootRoCache' hCore with hI | hB
          · have hFst := congrArg Prod.fst
              (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some P k j o kEntry bEntry oEntry
                usedTriples' msg s35.adv.hyb.base.roCache
                ((recvHandshakeSecrets P kEntry bEntry
                  (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss msg.hdr, dk) ::
                    s35.hyb.base.roCache)
                ((recvHandshakeSecrets P kEntry bEntry
                  (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss msg.hdr, dk) ::
                    s3.hyb.base.roCache)
                s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
            rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
          · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
              rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro hMatchNone hHon
        rcases hFp : findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk with
          _ | ⟨u_r, senderEntry⟩
        · rw [hFp] at hHon; nomatch hHon
        · rw [hFp] at hHon; dsimp only at hHon
          rcases hSubC kEntry bEntry oEntry usedTriples' ss u_r senderEntry
              hPre hAbDecF hMatchNone hFp hHon with ⟨hF3, hPostC⟩
          refine ⟨hF3, fun dk hdk rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          let recvEv : RecvdOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
          cases hCons : (consumeMatchingSentOPK P recvEv s3.hyb.base.sentOPKEvents).1
          · rcases hPostC dk hdk rk1 ck1_1 pt rootRoCache' hCore hCons with hI | hB
            · have hFst := congrArg Prod.fst
                (finishLatchedRecvOPK_withAuthAdvLatchedRoCache_some P k j o kEntry bEntry oEntry
                  usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache
                  ((recvHandshakeSecrets P kEntry bEntry
                    (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk)) ss msg.hdr, dk) ::
                      s3.hyb.base.roCache)
                  s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
              rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
            · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
                rw [mem_support_pure_iff] at hy; subst hy; exact hB)
          · exfalso
            rcases parseAuthRecvOPKPre_some_props P k j o msg s3.hyb hPre with
              ⟨_, _, _, _, _, _, hkMem, hbMem, _, _⟩
            rcases consumeMatchingSentOPK_true_imp_abort_or_badLatchedMono_of_matched_none P hP
                maxRo s3 hRunInv hMatchNone hkMem hbMem
                ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hFp hHon hCons with hAb | hBad
            · rw [hAbF] at hAb; nomatch hAb
            · rw [hbF] at hBad; nomatch hBad

/-- Step coupling for `.recvNoOPK k j l msg` between `.g3_5` and `.g3`, given the subcase premises. -/
theorem fgAuthStepCoupling_cutoff_latched_recvNoOPK {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (Inv : AuthAdvLatchedState S → AuthAdvLatchedState S → Prop)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (s35 s3 : AuthAdvLatchedState S) (_hInv : Inv s35 s3) (hAg : AuthAdvLatchedAgreeOffRo s35 s3)
    (hRunInv : ValidAuthHybridRunInv S P s3.hyb) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hbF : badAuthFgAnyLatchedMono P maxRo s3.toFg = false)
    (hRej : parseAuthRecvNoOPKPre P k j l msg s3.hyb.base = none →
      Inv (wrapAuthAdvLatchedRecv k j msg s35 (.noneResp, s35.hyb)).2
          (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2 ∨
      badAuthFgAnyLatchedMono P maxRo
        (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2.toFg = true)
    (hSchedNone : ∀ kEntry bEntry usedTriples' ss, parseAuthRecvNoOPKPre P k j l msg s3.hyb.base =
        some (kEntry, bEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      isAuthG3Abort P hstDec = false →
      Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
            s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec) none).2
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec none).2 ∨
      badAuthFgAnyLatchedMono P maxRo (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
          s3 hstDec none).2.toFg = true) (hSubA : ∀ kEntry bEntry usedTriples' ss s,
      parseAuthRecvNoOPKPre P k j l msg s3.hyb.base = some (kEntry, bEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let secrets := recvHandshakeSecrets P kEntry bEntry none ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none
          bEntry.pqspkPk msg.hdr) = some s →
      s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (secrets, s.drKey) ∧
      ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
          support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache
            kEntry bEntry msg s.drKey) →
        Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
              s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
              (some (s.drKey, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
            (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
              (some (s.drKey, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2 ∨
        badAuthFgAnyLatchedMono P maxRo
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
            (some (s.drKey, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2.toFg = true)
    (hSubB : ∀ kEntry bEntry usedTriples' ss, parseAuthRecvNoOPKPre P k j l msg s3.hyb.base =
        some (kEntry, bEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let secrets := recvHandshakeSecrets P kEntry bEntry none ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr) = none →
      (match findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk with
       | some (_, sEntry) => !sEntry.corrupted
       | none             => false) = false → ((∃ sec35 sec3 dk,
          s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec35, dk) ∧
          s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec3, dk) ∧
          ∀ rk1 ck1_1 pt rootRoCache', some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
            Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
                  s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
                  (some (dk, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
                (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                  (some (dk, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2 ∨
            badAuthFgAnyLatchedMono P maxRo
              (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt, s3.hyb.base.roCache, rootRoCache'))).2.toFg = true) ∨
       (s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
        ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
            some (rk1, ck1_1, pt, rootRoCache') ∈
              support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
            Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
                  s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec) (some (dk, rk1, ck1_1, pt,
                    (secrets, dk) :: s35.hyb.base.roCache, rootRoCache'))).2
                (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                  (some (dk, rk1, ck1_1, pt,
                    (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2 ∨
            badAuthFgAnyLatchedMono P maxRo
              (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt,
                  (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2.toFg = true)))
    (hSubC : ∀ kEntry bEntry usedTriples' ss u_r senderEntry,
      parseAuthRecvNoOPKPre P k j l msg s3.hyb.base = some (kEntry, bEntry, usedTriples', ss) →
      let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
        k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
        pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
      let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      let secrets := recvHandshakeSecrets P kEntry bEntry none ss msg.hdr
      isAuthG3Abort P hstDec = false → s3.hyb.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr) = none →
      findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk = some (u_r, senderEntry) →
      (!senderEntry.corrupted) = true →
      s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
      ∀ dk ∈ support sampleDRKey96, ∀ rk1 ck1_1 pt rootRoCache',
          some (rk1, ck1_1, pt, rootRoCache') ∈
            support (evalAuthHybridRecvCore true P s3.hyb.base.rootRoCache kEntry bEntry msg dk) →
          let recvEv : RecvdNoOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
          (consumeMatchingSentNoOPK P recvEv s3.hyb.base.sentNoOPKEvents).1 = false →
          Inv (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
                s35 (withAuthHybRoCache s35.hyb.base.roCache hstDec)
                (some (dk, rk1, ck1_1, pt, s35.hyb.base.roCache, rootRoCache'))).2
              (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
                (some (dk, rk1, ck1_1, pt,
                  (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2 ∨
          badAuthFgAnyLatchedMono P maxRo
            (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
              (some (dk, rk1, ck1_1, pt,
                (secrets, dk) :: s3.hyb.base.roCache, rootRoCache'))).2.toFg = true) :
    RelProbUpToBad (fun y35 y3 => (y35.1 = y3.1 ∧ Inv y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.recvNoOPK k j l msg)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.recvNoOPK k j l msg)).run s3) := by
  rw [pqxdhAuthAdvLatchedStageImpl_recvNoOPK_run_eq, pqxdhAuthAdvLatchedStageImpl_recvNoOPK_run_eq]
  have hBase35 : s35.hyb.base = withAuthBaseRoCache s35.hyb.base.roCache s3.hyb.base := by
    conv_lhs => rw [hAg]
    rfl
  have hPreEq : parseAuthRecvNoOPKPre P k j l msg s35.hyb.base =
      parseAuthRecvNoOPKPre P k j l msg s3.hyb.base := by
    rw [hBase35, parseAuthRecvNoOPKPre_withAuthBaseRoCache]
  rw [hPreEq]
  cases hPre : parseAuthRecvNoOPKPre P k j l msg s3.hyb.base with
  | none =>
    rcases hRej hPre with hInv' | hBad'
    · exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hInv'⟩)
    · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
        rw [mem_support_pure_iff] at hy; subst hy; exact hBad')
  | some p =>
    rcases p with ⟨kEntry, bEntry, usedTriples', ss⟩
    dsimp only
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec3 := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    have hDecEq : ({
        base := s35.hyb.base, initKemRecs := s35.hyb.initKemRecs,
        recvKemRecs := rRec :: s35.hyb.recvKemRecs,
        idealSessions := s35.hyb.idealSessions } : AuthHybridState S) =
        withAuthHybRoCache s35.hyb.base.roCache hstDec3 := by
      change { s35.hyb with recvKemRecs := rRec :: s35.hyb.recvKemRecs } = _
      conv_lhs => rw [hAg]
      rfl
    by_cases hAbDec : isAuthG3Abort P hstDec3 = true
    · refine RelProbUpToBad.of_support_rel _ _ (fun y35 hy35 y3 hy3 _ => ?_)
      simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy35 hy3
      rcases hy35 with ⟨res35, _, rfl⟩
      rcases hy3 with ⟨res3, _, rfl⟩
      refine Or.inr ?_
      rw [isAuthG3Abort_finishLatchedRecvNoOPK, isAuthG3Abort_finishLatchedRecvNoOPK,
          hDecEq, isAuthG3Abort_withBaseRoCache]
      exact ⟨hAbDec, hAbDec⟩
    · have hAbDecF : isAuthG3Abort P hstDec3 = false := Bool.eq_false_iff.mpr hAbDec
      rw [hDecEq]
      refine relProbUpToBad_evalAuthHybridRecvSchedule_bind _ _ P
        (withAuthHybRoCache s35.hyb.base.roCache hstDec3) hstDec3 kEntry bEntry
        none _ msg _ _ rfl rfl rfl ?_ ?_ ?_ ?_
      · rcases hSchedNone kEntry bEntry usedTriples' ss hPre hAbDecF with hI | hB
        · exact RelProbUpToBad.of_pure (Or.inl ⟨rfl, hI⟩)
        · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
            rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro s hMatch
        rcases hSubA kEntry bEntry usedTriples' ss s hPre hAbDecF hMatch with
          ⟨hRoFind, hPostA⟩
        refine ⟨hRoFind, fun rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
        rcases hPostA rk1 ck1_1 pt rootRoCache' hCore with hI | hB
        · have hFst := congrArg Prod.fst
            (finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_some P k j l kEntry bEntry
              usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache s3.hyb.base.roCache
              s3 hstDec3 s.drKey rk1 ck1_1 pt rootRoCache')
          rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
        · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
            rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro hMatchNone hNotHon
        rcases hSubB kEntry bEntry usedTriples' ss hPre hAbDecF hMatchNone hNotHon with
          ⟨sec35, sec3, dk, hF35, hF3, hHit⟩ | ⟨hF35, hF3, hMiss⟩
        · left
          refine ⟨sec35, sec3, dk, hF35, hF3, fun rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          rcases hHit rk1 ck1_1 pt rootRoCache' hCore with hI | hB
          · have hFst := congrArg Prod.fst
              (finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_some P k j l kEntry bEntry
                usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache s3.hyb.base.roCache
                s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
            rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
          · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
              rw [mem_support_pure_iff] at hy; subst hy; exact hB)
        · right
          refine ⟨hF35, hF3, fun dk hdk rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          rcases hMiss dk hdk rk1 ck1_1 pt rootRoCache' hCore with hI | hB
          · have hFst := congrArg Prod.fst
              (finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_some P k j l kEntry bEntry
                usedTriples' msg s35.adv.hyb.base.roCache
                ((recvHandshakeSecrets P kEntry bEntry none ss msg.hdr, dk) ::
                  s35.hyb.base.roCache)
                ((recvHandshakeSecrets P kEntry bEntry none ss msg.hdr, dk) :: s3.hyb.base.roCache)
                s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
            rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
          · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
              rw [mem_support_pure_iff] at hy; subst hy; exact hB)
      · intro hMatchNone hHon
        rcases hFp : findHonestPrincipal P s3.hyb.base.principals msg.hdr.ikAPk with
          _ | ⟨u_r, senderEntry⟩
        · rw [hFp] at hHon; nomatch hHon
        · rw [hFp] at hHon; dsimp only at hHon
          rcases hSubC kEntry bEntry usedTriples' ss u_r senderEntry
              hPre hAbDecF hMatchNone hFp hHon with ⟨hF3, hPostC⟩
          refine ⟨hF3, fun dk hdk rk1 ck1_1 pt rootRoCache' hCore => ?_⟩
          let recvEv : RecvdNoOPKEvent := {
            bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
            sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
            pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
          cases hCons : (consumeMatchingSentNoOPK P recvEv s3.hyb.base.sentNoOPKEvents).1
          · rcases hPostC dk hdk rk1 ck1_1 pt rootRoCache' hCore hCons with hI | hB
            · have hFst := congrArg Prod.fst
                (finishLatchedRecvNoOPK_withAuthAdvLatchedRoCache_some P k j l kEntry bEntry
                  usedTriples' msg s35.adv.hyb.base.roCache s35.hyb.base.roCache
                  ((recvHandshakeSecrets P kEntry bEntry none ss msg.hdr, dk) ::
                    s3.hyb.base.roCache)
                  s3 hstDec3 dk rk1 ck1_1 pt rootRoCache')
              rw [← hAg] at hFst; exact RelProbUpToBad.of_pure (Or.inl ⟨hFst, hI⟩)
            · exact RelProbUpToBad.bad6 _ _ (fun y hy => by
                rw [mem_support_pure_iff] at hy; subst hy; exact hB)
          · exfalso
            rcases parseAuthRecvNoOPKPre_some_props P k j l msg s3.hyb hPre with
              ⟨_, _, _, _, _, _, hkMem, hbMem, _⟩
            rcases consumeMatchingSentNoOPK_true_imp_abort_or_badLatchedMono_of_matched_none P hP
                maxRo s3 hRunInv hMatchNone hkMem hbMem
                ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hFp hHon hCons with hAb | hBad
            · rw [hAbF] at hAb; nomatch hAb
            · rw [hbF] at hBad; nomatch hBad

end Proofs.SignalPqxdh.Security
