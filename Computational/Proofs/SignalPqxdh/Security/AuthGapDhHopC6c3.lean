/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c2
public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopC6c1
import Computational.Proofs.SignalPqxdh.Security.FgGapDh
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import VCVio.EvalDist.Monad.Basic
/-!
# `Auth` hybrid hop `G3 → G3.5`: `.recvOPK` and `.recvNoOPK` premise discharge

Discharges the subcase premises of `fgAuthStepCoupling_cutoff_latched_recvOPK` and
`fgAuthStepCoupling_cutoff_latched_recvNoOPK` and assembles the full step couplings under
`AuthFullG3G3_5CoupledInv` and `AuthWinGuardedG3G3_5CoupledInv`.
-/

@[expose] public section
set_option autoImplicit false
open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp
open scoped ENNReal
open Proofs.SignalPqxdh.Security.FgGapDh
namespace Proofs.SignalPqxdh.Security
/-! ## Initiator random-oracle origin -/
/-- Witness that `secrets` was constructed by an earlier initiator handshake on a trace prefix. -/
def AuthSendRoOrigin (S : Setup) (P : Primitives) (hst : AuthHybridState S)
    (secrets : Bytes) : Prop :=
  ∃ (st0 : AuthState S) (u : Fin S.N_id) (uEntry0 uEntry : PrincipalEntry)
    (bundle : PreKeyBundleInput) (kemCoins ss_s : Bytes)
    (sessEntry : AuthInitiatorEntry S) (s_ideal : IdealAuthSession S)
    (initRec : _root_.SignalPqxdh.Security.InitKemRecord S),
    ValidAuthKeyStores S P st0 ∧
    AuthBaseTraceSub st0 hst.base ∧
    st0.principals.find? (fun (idx, _) => idx == u.val) = some (u.val, uEntry0) ∧
    uEntry.ikAPk = uEntry0.ikAPk ∧
    (isGameSpk P st0.spkBundles bundle.spkB || isAdvRegistered P st0.advKeys bundle.spkB) = true ∧
    s_ideal.peerIkPk = bundle.ikB ∧
    s_ideal.peerSpkPk = bundle.spkB ∧
    s_ideal.peerPqspkPk = bundle.pqspkB ∧
    ValidIdealAuthSession S P hst s_ideal sessEntry u.val uEntry kemCoins ss_s initRec ∧
    secrets = idealSessionSecrets P uEntry sessEntry.ekASk ss_s s_ideal ∧
    ((let peerPrincipal? := findHonestPrincipal P st0.principals bundle.ikB
      let isFreshPeer := match peerPrincipal? with | some (_, p) => !p.corrupted | none => false
      let pqspkHon :=
        (checkBundleProvenanceExact P st0.principals st0.spkBundles st0.opkEntries bundle).2.2
      let spkHonIdeal := checkBundleSpkHonIdeal P st0.principals st0.spkBundles bundle
      isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)) = true →
     s_ideal ∈ hst.idealSessions)
theorem authSendRoOrigin_of_traceSub {S : Setup} (P : Primitives)
    {hst1 hst2 : AuthHybridState S} {secrets : Bytes}
    (hSub : AuthHybridTraceSub hst1 hst2)
    (hOrig : AuthSendRoOrigin S P hst1 secrets) :
    AuthSendRoOrigin S P hst2 secrets := by
  rcases hOrig with ⟨st0, u, uEntry0, uEntry1, bundle, kemCoins, ss_s,
    sessEntry, s_ideal, initRec, hKS0, hSub0, hFU0, hIkEq1, hKosk0,
    hPeerIk, hPeerSpk, hPeerPq, hVi1, hSec1, hMemId⟩
  rcases validIdealAuthSession_of_traceSub P hSub hVi1 with ⟨uEntry2, hSecEq, hIkEq2, hVi2⟩
  have hIdealSecEq : idealSessionSecrets P uEntry2 sessEntry.ekASk ss_s s_ideal =
      idealSessionSecrets P uEntry1 sessEntry.ekASk ss_s s_ideal := by
    unfold idealSessionSecrets; rw [hSecEq]
  exact ⟨st0, u, uEntry0, uEntry2, bundle, kemCoins, ss_s, sessEntry, s_ideal, initRec,
    hKS0, hSub0.trans hSub.base_sub, hFU0, hIkEq2.trans hIkEq1, hKosk0,
    hPeerIk, hPeerSpk, hPeerPq, hVi2, hSec1.trans hIdealSecEq.symm,
    fun hCond => hSub.idealSessions_sub.subset (hMemId hCond)⟩
theorem dh1_eq_imp_initAuthDh1Cand_eq_of_pow8_spk_ne_any_sender {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (bIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows advKeys : List (Bytes × Bytes))
    (sessEntry : AuthInitiatorEntry S) (u_s : ℕ) (uEntry_s senderEntry : PrincipalEntry)
    (bEntry : SpkBundleEntry) (ikAPk_hdr : Bytes)
    (huIk_s : uEntry_s.secIKA0.length = 32 ∧ uEntry_s.ikAPk = P.x25519Base uEntry_s.secIKA0)
    (huIk_r : senderEntry.secIKA0.length = 32 ∧
      senderEntry.ikAPk = P.x25519Base senderEntry.secIKA0)
    (hbSpk : bEntry.spkSk.length = 32 ∧ bEntry.spkPk = P.x25519Base bEntry.spkSk)
    (hFindU_s : principals.find? (fun (idx, _) => idx == sessionSenderIdx sessEntry.sid) =
      some (u_s, uEntry_s))
    (hSpks : ∀ kv ∈ spkBundles,
      kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
      ((spkBundleFlatIdxVal S kv.1 == bIdx) = true → kv.2.spkSk = bEntry.spkSk))
    (hS : spkBundles.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk') => (sk, P.pow8 pk')))
    (hAdvSkLen : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hSpkReg : (isGameSpk P spkBundles sessEntry.peerSpkPk ||
      isAdvRegistered P advKeys sessEntry.peerSpkPk) = true)
    (hPowHdr : P.pow8 ikAPk_hdr = P.pow8 senderEntry.ikAPk)
    (hNeV : P.pow8 sessEntry.peerSpkPk ≠ P.pow8 bEntry.spkPk)
    (hDh1Eq : P.x25519 uEntry_s.secIKA0 sessEntry.peerSpkPk = P.x25519 bEntry.spkSk ikAPk_hdr) :
    initAuthDh1CandGuard S P principals (eraseSpkBundlesFg S bIdx spkBundles) advKeyPows sessEntry =
      true ∧
    initAuthDh1Cand S P principals (eraseSpkBundlesFg S bIdx spkBundles) advKeyPows sessEntry =
      P.x25519 senderEntry.secIKA0 bEntry.spkPk := by
  have hw := hP.toWellFormedPrimitivesδ
  have hNeBase : P.pow8 sessEntry.peerSpkPk ≠ P.pow8 (P.x25519Base bEntry.spkSk) := by
    rw [← hbSpk.2]; exact hNeV
  have hLookupEq :
      lookupAuthSpkSkTake S P (eraseSpkBundlesFg S bIdx spkBundles) advKeyPows sessEntry.peerSpkPk =
      lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx spkBundles) advKeyPows sessEntry.peerSpkPk := by
    unfold lookupAuthSpkSkTake lookupSpkSkTake
    have hFindEq :
        ∀ (L : List ((Nat × Nat) × SpkBundleEntry)),
          (∀ x ∈ L, x ∈ eraseSpkBundlesFg S bIdx spkBundles) →
          L.find? (fun (_, b) => !b.spkSk.isEmpty && P.pow8 b.spkPk == P.pow8 sessEntry.peerSpkPk) =
          L.find? (fun (_, b) => P.pow8 b.spkPk == P.pow8 sessEntry.peerSpkPk) := by
      intro L hL
      induction L with
      | nil => rfl
      | cons hd tl ih =>
        have hMem : hd ∈ eraseSpkBundlesFg S bIdx spkBundles := hL hd (List.mem_cons_self ..)
        unfold eraseSpkBundlesFg at hMem
        rcases List.mem_map.mp hMem with ⟨⟨k0, b0⟩, hb0Mem, hEq⟩
        rcases hSpks (k0, b0) hb0Mem with ⟨hb0Len, hb0Pk, hb0Tgt⟩
        have hPredEq :
            (!hd.2.spkSk.isEmpty && P.pow8 hd.2.spkPk == P.pow8 sessEntry.peerSpkPk) =
            (P.pow8 hd.2.spkPk == P.pow8 sessEntry.peerSpkPk) := by
          rw [← hEq]; dsimp only [eraseSpkBundleEntryFg]
          cases hHit : (FgGapDh.spkBundleFlatIdxVal S k0 == bIdx)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hNE : (!b0.spkSk.isEmpty) = true := by cases hE : b0.spkSk <;> simp_all
            rw [hNE, Bool.true_and]
          · simp only [↓reduceIte]
            have hSkEq : b0.spkSk = bEntry.spkSk := hb0Tgt hHit
            have hPowF : (P.pow8 b0.spkPk == P.pow8 sessEntry.peerSpkPk) = false :=
              beq_eq_false_iff_ne.mpr (fun h => hNeBase (by rw [← h, hb0Pk, hSkEq]))
            rw [hPowF, Bool.and_false]
        simp only [List.find?_cons, hPredEq]
        cases (P.pow8 hd.2.spkPk == P.pow8 sessEntry.peerSpkPk)
        · exact ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
        · rfl
    dsimp only
    rw [hFindEq _ (fun x hx => List.mem_of_mem_take hx)]
    rfl
  rcases lookupSpkSkTake_eraseSpk_dichotomy S P bIdx bEntry.spkSk spkBundles advKeyPows advKeys
    sessEntry.peerSpkPk hSpks hS hAdvPows hAdvSkLen hSpkReg with ⟨_, _, hPow⟩ | ⟨hLen, hPow⟩
  · exfalso; exact hNeBase hPow
  · refine ⟨?_, ?_⟩
    · unfold initAuthDh1CandGuard; rw [hLookupEq, hFindU_s, Bool.and_eq_true]
      refine ⟨?_, rfl⟩
      revert hLen
      generalize lookupSpkSkTake S P (eraseSpkBundlesFg S bIdx spkBundles)
        advKeyPows sessEntry.peerSpkPk = sk
      intro hLen; cases sk <;> simp_all
    · unfold initAuthDh1Cand lookupSenderIkPk
      have hPowHdrBase : P.pow8 ikAPk_hdr = P.pow8 (P.x25519Base senderEntry.secIKA0) := by
        rw [hPowHdr, huIk_r.2]
      rw [hFindU_s, hLookupEq]; dsimp only
      rw [huIk_s.2, ← hw.x25519_comm uEntry_s.secIKA0,
          ← hP.x25519_pow8_congr uEntry_s.secIKA0 sessEntry.peerSpkPk _
              (hP.pow8_base_len sessEntry.peerSpkPk _ hPow) (hw.x25519Base_len _) hPow,
          hDh1Eq,
          hP.x25519_pow8_congr bEntry.spkSk ikAPk_hdr (P.x25519Base senderEntry.secIKA0)
            (hP.pow8_base_len ikAPk_hdr senderEntry.secIKA0 hPowHdrBase)
            (hw.x25519Base_len senderEntry.secIKA0) hPowHdrBase,
          ← hw.x25519_comm senderEntry.secIKA0 bEntry.spkSk, ← hbSpk.2]
theorem badAuthFgDh1At_of_recv_mem_sessions_spk_ne_any_sender {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (st : AuthState S) (advRoLog : List Bytes) (respRecs : List AuthRespRecord)
    (hV : ValidAuthKeyStoresFull S P st)
    {u_r u_s k j : Nat} {senderEntry uEntry_s : PrincipalEntry} {bEntry : SpkBundleEntry}
    {sessEntry : AuthInitiatorEntry S} {ikAPk_hdr : Bytes}
    (huMem_r : (u_r, senderEntry) ∈ st.principals) (huNotCorr : (!senderEntry.corrupted) = true)
    (hPowIk : P.pow8 ikAPk_hdr = P.pow8 senderEntry.ikAPk)
    (huMem_s : (u_s, uEntry_s) ∈ st.principals)
    (hbMem : ((k, j), bEntry) ∈ st.spkBundles) (hsMem : sessEntry ∈ st.sessions)
    (hsSender : sessionSenderIdx sessEntry.sid = u_s)
    (hSpkReg : (isGameSpk P st.spkBundles sessEntry.peerSpkPk ||
      isAdvRegistered P st.advKeys sessEntry.peerSpkPk) = true)
    (hSpkNe : P.pow8 sessEntry.peerSpkPk ≠ P.pow8 bEntry.spkPk)
    (hDh1Eq : P.x25519 uEntry_s.secIKA0 sessEntry.peerSpkPk = P.x25519 bEntry.spkSk ikAPk_hdr) :
    badAuthFgDh1AtMono P maxRo u_r (spkBundleFlatIdxVal S (k, j)) st advRoLog respRecs = true := by
  have hFindU_r := find_principals_eq_some_of_mem hV.1.1 huMem_r
  have hFindU_s := find_principals_eq_some_of_mem hV.1.1 huMem_s
  have hFindB := find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hbMem
  have huIk_r := hV.1.2.2.2.1 (u_r, senderEntry) huMem_r
  have huIk_s := hV.1.2.2.2.1 (u_s, uEntry_s) huMem_s
  have hbSpk := hV.1.2.2.2.2.1 ((k, j), bEntry) hbMem
  have hLengths := validAuthKeyStoresFull_lengths_le S P st hV
  have hSpkUnique : ∀ kv ∈ st.spkBundles,
      kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
      ((spkBundleFlatIdxVal S kv.1 == spkBundleFlatIdxVal S (k, j)) = true →
        kv.2.spkSk = bEntry.spkSk) := by
    intro kv hkv
    have hkvSpk := hV.1.2.2.2.2.1 kv hkv
    refine ⟨hkvSpk.1, hkvSpk.2.1, fun hFlatEq => ?_⟩
    have hFB1 := find_spkBundles_flatIdx_eq_some_of_mem hV.1.2.1 hkv
    rw [beq_iff_eq.mp hFlatEq, hFindB] at hFB1
    injection hFB1 with hPair; injection hPair with _ hbEq; rw [hbEq]
  rcases dh1_eq_imp_initAuthDh1Cand_eq_of_pow8_spk_ne_any_sender P hP
    (spkBundleFlatIdxVal S (k, j)) st.principals st.spkBundles
    (st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) st.advKeys
    sessEntry u_s uEntry_s senderEntry bEntry ikAPk_hdr huIk_s huIk_r ⟨hbSpk.1, hbSpk.2.1⟩
    (by rw [hsSender]; exact hFindU_s) hSpkUnique hLengths.2.1 rfl hV.1.2.2.2.2.2.2
    hSpkReg hPowIk hSpkNe hDh1Eq with ⟨hGuard, hCandEq⟩
  have hsTake : sessEntry ∈ st.sessions.take S.N_dh := by
    rw [List.take_of_length_le hLengths.2.2.2]; exact hsMem
  unfold badAuthFgDh1AtMono; rw [hFindU_r, hFindB]; dsimp only
  rw [huNotCorr, Bool.true_and, Bool.or_eq_true, Bool.or_eq_true]
  left; right; refine List.any_eq_true.mpr ⟨sessEntry, hsTake, ?_⟩
  rw [Bool.and_eq_true, beq_iff_eq]; exact ⟨hGuard, hCandEq⟩
theorem badAuthFgAnyLatched_of_recv_mem_sessions_spk_ne_any_sender {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (s : AuthFgCutoffState S) (hV : ValidAuthKeyStoresFull S P s.base)
    {u_r u_s k j : Nat} {senderEntry uEntry_s : PrincipalEntry} {bEntry : SpkBundleEntry}
    {sessEntry : AuthInitiatorEntry S} {ikAPk_hdr : Bytes}
    (huMem_r : (u_r, senderEntry) ∈ s.base.principals) (huNotCorr : (!senderEntry.corrupted) = true)
    (hPowIk : P.pow8 ikAPk_hdr = P.pow8 senderEntry.ikAPk)
    (huMem_s : (u_s, uEntry_s) ∈ s.base.principals)
    (hbMem : ((k, j), bEntry) ∈ s.base.spkBundles) (hsMem : sessEntry ∈ s.base.sessions)
    (hsSender : sessionSenderIdx sessEntry.sid = u_s)
    (hSpkReg : (isGameSpk P s.base.spkBundles sessEntry.peerSpkPk ||
      isAdvRegistered P s.base.advKeys sessEntry.peerSpkPk) = true)
    (hSpkNe : P.pow8 sessEntry.peerSpkPk ≠ P.pow8 bEntry.spkPk)
    (hDh1Eq : P.x25519 uEntry_s.secIKA0 sessEntry.peerSpkPk = P.x25519 bEntry.spkSk ikAPk_hdr) :
    badAuthFgAnyLatchedMono P maxRo s = true := by
  have huLt : u_r < S.N_id := hV.1.1.1 (u_r, senderEntry) huMem_r
  have hbRange := spkBundleFlatIdxVal_mem_range hV.1.2.1 hbMem
  exact badAuthFgAnyLatchedMono_of_exists_badAuthFgDh1AtMono P maxRo s
    ⟨⟨u_r, huLt⟩, spkBundleFlatIdxVal S (k, j), hbRange,
      badAuthFgDh1At_of_recv_mem_sessions_spk_ne_any_sender P hP maxRo s.base s.advRoLog s.respRecs
        hV huMem_r huNotCorr hPowIk huMem_s hbMem hsMem hsSender hSpkReg hSpkNe hDh1Eq⟩
theorem subcase4A_sendRoOrigin_imp_idealSend {S : Setup} (P : Primitives)
    (st0 : AuthState S) (hst : AuthHybridState S)
    (hKS0 : ValidAuthKeyStores S P st0) (hSub0 : AuthBaseTraceSub st0 hst.base)
    (hKS : ValidAuthKeyStores S P hst.base) (hNoEc : hasEcPkCollisionAuth P hst = false)
    {k j : Nat} {kEntry : PrincipalEntry} {b0 bEntry : SpkBundleEntry}
    {bundle : PreKeyBundleInput}
    (hkMem : (k, kEntry) ∈ hst.base.principals)
    (hbMem : ((k, j), bEntry) ∈ hst.base.spkBundles)
    (hb0Mem0 : ((k, j), b0) ∈ st0.spkBundles)
    (hPowIkB : P.pow8 kEntry.ikAPk = P.pow8 bundle.ikB)
    (hPowSpk : P.pow8 bEntry.spkPk = P.pow8 bundle.spkB)
    (hPqEq : bEntry.pqspkPk = bundle.pqspkB) :
    (let peerPrincipal? := findHonestPrincipal P st0.principals bundle.ikB
     let isFreshPeer := match peerPrincipal? with | some (_, p) => !p.corrupted | none => false
     let pqspkHon :=
       (checkBundleProvenanceExact P st0.principals st0.spkBundles st0.opkEntries bundle).2.2
     let spkHonIdeal := checkBundleSpkHonIdeal P st0.principals st0.spkBundles bundle
     isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && pqspkHon)) = true := by
  have hb0Mem1 : ((k, j), b0) ∈ hst.base.spkBundles := hSub0.spkBundles_sub.subset hb0Mem0
  have hFB0 := find_spkBundles_flatIdx_eq_some_of_mem hKS.2.1 hb0Mem1
  have hFB1 := find_spkBundles_flatIdx_eq_some_of_mem hKS.2.1 hbMem
  rw [hFB1] at hFB0; injection hFB0 with hPair; injection hPair with _ hbEq; subst hbEq
  rcases (hKS0.2.2.2.2.1 ((k, j), bEntry) hb0Mem0).2.2.1 with ⟨kEntry0, hk0Mem⟩
  rcases hSub0.exists_prin hk0Mem with ⟨kEntry1, hk1Mem, _, hkIkEq1⟩
  have hFK1 := find_principals_eq_some_of_mem hKS.1 hk1Mem
  have hFK := find_principals_eq_some_of_mem hKS.1 hkMem
  rw [hFK] at hFK1; injection hFK1 with hKP; injection hKP with _ hkEq; subst hkEq
  dsimp only
  cases hFP0 : findHonestPrincipal P st0.principals bundle.ikB with
  | none =>
    exfalso
    have hFP0' :
        st0.principals.find? (fun (_, e) => P.pow8 bundle.ikB == P.pow8 e.ikAPk) = none := hFP0
    refine List.find?_eq_none.mp hFP0' (k, kEntry0) hk0Mem ?_
    dsimp only; rw [beq_iff_eq, ← hPowIkB, hkIkEq1]
  | some kp =>
    rcases kp with ⟨k_s, pEntry0⟩
    have hFP0' :
        st0.principals.find? (fun (_, e) => P.pow8 bundle.ikB == P.pow8 e.ikAPk) =
          some (k_s, pEntry0) := hFP0
    have hPeerMem0 : (k_s, pEntry0) ∈ st0.principals := List.mem_of_find?_eq_some hFP0'
    have hPeerPow : P.pow8 bundle.ikB = P.pow8 pEntry0.ikAPk :=
      beq_iff_eq.mp (List.find?_some
        (p := fun (x : Nat × PrincipalEntry) => P.pow8 bundle.ikB == P.pow8 x.2.ikAPk) hFP0')
    rcases hSub0.exists_prin hPeerMem0 with ⟨pEntry1, hPeerMem1, _, hpIkEq1⟩
    have hNodupPrin := nodup_principals_of_hasEcPkCollisionAuth_false P hst hNoEc
    have hPrinEq : (k, kEntry) = (k_s, pEntry1) :=
      eq_of_nodup_map_auth (fun (_, e) => P.pow8 e.ikAPk) hNodupPrin hkMem hPeerMem1
        (by dsimp only; rw [hPowIkB, hPeerPow, ← hpIkEq1])
    have hksEq : k = k_s := congrArg Prod.fst hPrinEq
    dsimp only
    cases hC0 : pEntry0.corrupted
    · rfl
    · simp only [Bool.not_true, Bool.false_or, Option.isSome, Bool.true_and, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · unfold checkBundleSpkHonIdeal; rw [hFP0]; dsimp only
        refine List.any_eq_true.mpr ⟨((k, j), bEntry), hb0Mem0, ?_⟩
        simp only [hksEq, beq_self_eq_true, hC0, Bool.true_and, Bool.or_eq_true, beq_iff_eq]
        exact Or.inl hPowSpk
      · unfold checkBundleProvenanceExact; rw [hFP0]; dsimp only
        refine List.any_eq_true.mpr ⟨((k, j), bEntry), hb0Mem0, ?_⟩
        simp only [hksEq, beq_self_eq_true, Bool.true_and, beq_iff_eq]
        exact hPqEq
/-- Unmatched honest-sender receiver handshakes whose `secrets` satisfy `AuthSendRoOrigin` trigger
    an abort or `badAuthFgAnyLatchedMono`. -/
theorem recv_matched_none_imp_abort_or_badLatched_of_sendRoOrigin {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ) (s3 : AuthAdvLatchedState S)
    (hRun : ValidAuthHybridRunInv S P s3.hyb)
    {k : Fin S.N_id} {j : Fin S.N_recv} {u_r : Nat}
    {kEntry senderEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {opkPk? dh4? : Option Bytes} {ss_r : Bytes}
    {rRec : _root_.SignalPqxdh.Security.RecvKemRecord} {hdr : HandshakeHdr}
    (hr : ValidAuthRespHandshake S P { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      k j kEntry bEntry opkPk? dh4? ss_r rRec hdr)
    (hMatchNone : s3.hyb.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk hdr) = none)
    (hFp : findHonestPrincipal P s3.hyb.base.principals hdr.ikAPk = some (u_r, senderEntry))
    (hHon : (!senderEntry.corrupted) = true)
    (hOrig : AuthSendRoOrigin S P s3.hyb (recvHandshakeSecrets P kEntry bEntry dh4? ss_r hdr)) :
    isAuthG3Abort P { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } = true ∨
    isAuthG3Abort P s3.hyb = true ∨
    badAuthFgAnyLatchedMono P maxRo s3.toFg = true := by
  let hstDec := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
  by_cases hAbDec : isAuthG3Abort P hstDec = true
  · exact Or.inl hAbDec
  · by_cases hAb : isAuthG3Abort P s3.hyb = true
    · exact Or.inr (Or.inl hAb)
    · right; right
      have hAbDecF : isAuthG3Abort P hstDec = false := Bool.eq_false_iff.mpr hAbDec
      have hAbF : isAuthG3Abort P s3.hyb = false := Bool.eq_false_iff.mpr hAb
      have hNoBadKem : hasBadKemShCrAuth P hstDec = false := by
        unfold isAuthG3Abort at hAbDecF
        exact (Bool.or_eq_false_iff.mp hAbDecF).2
      have hNoEc : hasEcPkCollisionAuth P s3.hyb = false := by
        unfold isAuthG3Abort at hAbF
        exact (Bool.or_eq_false_iff.mp
          (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp hAbF).1).1).1
      rcases hOrig with ⟨st0, u, uEntry0, uEntry, bundle, kemCoins, ss_s,
        sessEntry, s_ideal, initRec, hKS0, hSub0, hFU0, hIkEq, hKosk0,
        hPeerIk, hPeerSpk, hPeerPq, hVi, hSecEq, hMemId⟩
      have hViDec : ValidIdealAuthSession S P hstDec s_ideal sessEntry u.val uEntry
          kemCoins ss_s initRec := hVi
      rcases secrets_eq_imp_components P hP hstDec hNoBadKem hViDec hr hSecEq.symm with
        ⟨_, hDh1, _, _, _, _, _⟩
      have hFp' :
          s3.hyb.base.principals.find? (fun (_, e) => P.pow8 hdr.ikAPk == P.pow8 e.ikAPk) =
            some (u_r, senderEntry) := hFp
      have huMem_r : (u_r, senderEntry) ∈ s3.hyb.base.principals := List.mem_of_find?_eq_some hFp'
      have hPowIk_r : P.pow8 hdr.ikAPk = P.pow8 senderEntry.ikAPk :=
        beq_iff_eq.mp (List.find?_some
          (p := fun (x : Nat × PrincipalEntry) => P.pow8 hdr.ikAPk == P.pow8 x.2.ikAPk) hFp')
      have hr' := hr
      rcases hr' with ⟨hkMem, hbMem, _⟩
      by_cases hPowSpk : P.pow8 bEntry.spkPk = P.pow8 s_ideal.peerSpkPk
      · have hMatch := secrets_eq_imp_matchIdealAuthHandshake_of_pow8_spk_eq P hP hstDec
          hRun.1.1 hNoBadKem hViDec hr hPowSpk hSecEq.symm
        by_cases hIn0 : ∃ b0, ((k.val, j.val), b0) ∈ st0.spkBundles
        · exfalso
          rcases hIn0 with ⟨b0, hb0Mem0⟩
          have hMatch' := hMatch
          unfold matchIdealAuthHandshake at hMatch'
          simp only [Bool.and_eq_true, beq_iff_eq] at hMatch'
          rcases hMatch' with ⟨⟨⟨⟨⟨⟨_, hPowIkB⟩, _⟩, _⟩, _⟩, hPqEq⟩, _⟩
          have hCond := subcase4A_sendRoOrigin_imp_idealSend P st0 s3.hyb hKS0 hSub0
            hRun.1.1 hNoEc hkMem hbMem hb0Mem0
            (by rw [hPowIkB, hPeerIk]) (by rw [hPowSpk, hPeerSpk]) (by rw [hPqEq, hPeerPq])
          exact List.find?_eq_none.mp hMatchNone s_ideal (hMemId hCond) hMatch
        · have hNotIn0 : ∀ b0, ((k.val, j.val), b0) ∉ st0.spkBundles :=
            fun b0 hb0 => hIn0 ⟨b0, hb0⟩
          unfold matchIdealAuthHandshake at hMatch
          simp only [Bool.and_eq_true, beq_iff_eq] at hMatch
          rcases hMatch with ⟨⟨⟨⟨⟨⟨hPowIkA, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
          have huMem_s : (u.val, uEntry) ∈ s3.hyb.base.principals :=
            hVi.2.2.2.2.2.2.2.2.1
          have hsIkPk : s_ideal.ikAPk = uEntry.ikAPk := hVi.2.2.2.2.2.2.2.2.2.2.1
          have hNodupPrin := nodup_principals_of_hasEcPkCollisionAuth_false P s3.hyb hNoEc
          have hPrinEq : (u_r, senderEntry) = (u.val, uEntry) :=
            eq_of_nodup_map_auth (fun (_, e) => P.pow8 e.ikAPk) hNodupPrin huMem_r huMem_s
              (by dsimp only; rw [← hPowIk_r, hPowIkA, hsIkPk])
          have huEntryEq : senderEntry = uEntry := congrArg Prod.snd hPrinEq
          rw [huEntryEq] at hHon
          have hFindU := find_principals_eq_some_of_mem hRun.1.1.1 huMem_s
          have hFindB := find_spkBundles_flatIdx_eq_some_of_mem hRun.1.1.2.1 hbMem
          have hbRange := spkBundleFlatIdxVal_mem_range hRun.1.1.2.1 hbMem
          have hLenLe := (validAuthKeyStoresFull_lengths_le S P s3.hyb.base hRun.1).2.2.2
          have hsMemTake : sessEntry ∈ s3.hyb.base.sessions.take S.N_dh := by
            rw [List.take_of_length_le hLenLe]; exact hVi.1
          have hSendIdx : sessionSenderIdx sessEntry.sid = u.val := by
            rw [hVi.2.1, hVi.2.2.2.2.2.2.2.2.2.1]
          have hSessSpk : sessEntry.peerSpkPk = bundle.spkB := by
            rw [hVi.2.2.2.2.2.1, hPeerSpk]
          have hKoskSpk0 :
              (isGameSpk P st0.spkBundles sessEntry.peerSpkPk ||
                isAdvRegistered P st0.advKeys sessEntry.peerSpkPk) = true := by
            rw [hSessSpk]; exact hKosk0
          have hPowSpkSess : P.pow8 bEntry.spkPk = P.pow8 sessEntry.peerSpkPk := by
            rw [hVi.2.2.2.2.2.1]; exact hPowSpk
          rcases subcase4B_kosk_imp_ecColl_or_badDh1Mono P hP maxRo u.val
              (spkBundleFlatIdxVal S (k.val, j.val)) st0 s3.hyb s3.adv.advRoLog s3.adv.respRecs
              hNotIn0 (hSub0.subSpk P) hSub0.subAdv hFindU hFindB hHon
              (hRun.1.1.2.2.2.1 (u.val, uEntry) huMem_s) hRun.1.1.2.2.2.2.2.2
              hsMemTake hSendIdx hKoskSpk0 hPowSpkSess with ⟨hEcT, _⟩ | hBad
          · rw [hNoEc] at hEcT; nomatch hEcT
          · exact badAuthFgAnyLatchedMono_of_exists_badAuthFgDh1AtMono P maxRo s3.toFg
              ⟨u, spkBundleFlatIdxVal S (k.val, j.val), hbRange, hBad⟩
      · have hSessSpk : sessEntry.peerSpkPk = s_ideal.peerSpkPk := hVi.2.2.2.2.2.1
        have hSpkReg0 :
            (isGameSpk P st0.spkBundles sessEntry.peerSpkPk ||
              isAdvRegistered P st0.advKeys sessEntry.peerSpkPk) = true := by
          rw [hSessSpk, hPeerSpk]; exact hKosk0
        have hSpkReg := isGameSpk_or_isAdvRegistered_mono_of_traceSub P hSub0
          sessEntry.peerSpkPk hSpkReg0
        have hSendIdx : sessionSenderIdx sessEntry.sid = u.val := by
          rw [hVi.2.1, hVi.2.2.2.2.2.2.2.2.2.1]
        exact badAuthFgAnyLatched_of_recv_mem_sessions_spk_ne_any_sender P hP maxRo
          s3.toFg hRun.1 huMem_r hHon hPowIk_r hVi.2.2.2.2.2.2.2.2.1 hbMem hVi.1 hSendIdx
          hSpkReg (fun h => hPowSpk (hSessSpk ▸ h.symm)) (hSessSpk ▸ hDh1)
/-! ## Random-oracle origin invariant -/
/-- Invariant that every `.g3` `roCache` entry came from `advRoLog`, an initiator `send` query, or
    a responder `recv` query. -/
def AuthRecvOriginInv (S : Setup) (P : Primitives) (s3 : AuthAdvLatchedState S) : Prop :=
  ∀ secrets p,
    s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = some p →
    p.1 = secrets ∧
    (secrets ∈ s3.adv.advRoLog ∨
     AuthSendRoOrigin S P s3.hyb secrets ∨
     AuthRespRoOrigin P s3 secrets)
theorem authRecvOriginInv_empty (S : Setup) (P : Primitives) (secb : Bool) :
    AuthRecvOriginInv S P (AuthAdvLatchedState.empty S secb) := by
  intro _ _ h
  cases h
theorem authRecvOriginInv_of_traceSub_eq_roCache {S : Setup} (P : Primitives)
    {s3 y3 : AuthAdvLatchedState S} (hOrig : AuthRecvOriginInv S P s3)
    (hSub : AuthHybridTraceSub s3.hyb y3.hyb)
    (hRoEq : y3.adv.hyb.base.roCache = s3.adv.hyb.base.roCache)
    (hLogSub : ∀ x ∈ s3.adv.advRoLog, x ∈ y3.adv.advRoLog)
    (hRespSub : s3.adv.respRecs.Sublist y3.adv.respRecs)
    (hKybSub : s3.hyb.base.seenKyberBaseKeys.Sublist y3.hyb.base.seenKyberBaseKeys) :
    AuthRecvOriginInv S P y3 := by
  intro secrets p hF
  rw [hRoEq] at hF
  rcases hOrig secrets p hF with ⟨hp1, hInLog | hSend | hResp⟩
  · exact ⟨hp1, Or.inl (hLogSub secrets hInLog)⟩
  · exact ⟨hp1, Or.inr (Or.inl (authSendRoOrigin_of_traceSub P hSub hSend))⟩
  · exact ⟨hp1, Or.inr (Or.inr (authRespRoOrigin_of_traceSub P hSub hRespSub hKybSub hResp))⟩
theorem authRecvOriginInv_of_traceSub_cons_roCache {S : Setup} (P : Primitives)
    {s3 y3 : AuthAdvLatchedState S} (hOrig : AuthRecvOriginInv S P s3)
    {secrets : Bytes} {dk : DRKey}
    (hSub : AuthHybridTraceSub s3.hyb y3.hyb)
    (hRoEq : y3.adv.hyb.base.roCache = (secrets, dk) :: s3.adv.hyb.base.roCache)
    (hLogSub : ∀ x ∈ s3.adv.advRoLog, x ∈ y3.adv.advRoLog)
    (hRespSub : s3.adv.respRecs.Sublist y3.adv.respRecs)
    (hKybSub : s3.hyb.base.seenKyberBaseKeys.Sublist y3.hyb.base.seenKyberBaseKeys)
    (hNew : secrets ∈ y3.adv.advRoLog ∨
      AuthSendRoOrigin S P y3.hyb secrets ∨
      AuthRespRoOrigin P y3 secrets) :
    AuthRecvOriginInv S P y3 := by
  intro sec' p' hF
  rw [hRoEq, List.find?_cons] at hF
  dsimp only at hF
  cases hBeq : (secrets == sec')
  · rw [hBeq] at hF
    rcases hOrig sec' p' hF with ⟨hp1, hInLog | hSend | hResp⟩
    · exact ⟨hp1, Or.inl (hLogSub sec' hInLog)⟩
    · exact ⟨hp1, Or.inr (Or.inl (authSendRoOrigin_of_traceSub P hSub hSend))⟩
    · exact ⟨hp1, Or.inr (Or.inr (authRespRoOrigin_of_traceSub P hSub hRespSub hKybSub hResp))⟩
  · rw [hBeq] at hF
    injection hF with hpEq
    subst hpEq
    have hSecEq : secrets = sec' := beq_iff_eq.mp hBeq
    subst hSecEq
    exact ⟨rfl, hNew⟩
/-- Under `AuthRecvOriginInv` with no abort and `badAuthFgAnyLatchedMono = false`, an unmatched
    honest-sender receiver secret misses `s3.hyb.base.roCache`. -/
theorem roCache_find_eq_none_of_recv_unmatched_honest {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxRo : ℕ)
    (s3 : AuthAdvLatchedState S) (hRunInv : ValidAuthHybridRunInv S P s3.hyb)
    (hOrig : AuthRecvOriginInv S P s3)
    {k : Fin S.N_id} {j : Fin S.N_recv} {u_r : Nat}
    {kEntry senderEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {opkPk? dh4? : Option Bytes} {ss_r : Bytes}
    {rRec : _root_.SignalPqxdh.Security.RecvKemRecord} {hdr : HandshakeHdr}
    (hAbF : isAuthG3Abort P s3.hyb = false)
    (hAbDecF : isAuthG3Abort P { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } = false)
    (hbF : badAuthFgAnyLatchedMono P maxRo s3.toFg = false)
    (hRoLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot)
    (hRespV : ValidAuthRespHandshake S P
      { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      k j kEntry bEntry opkPk? dh4? ss_r rRec hdr)
    (hMatchNone : s3.hyb.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk hdr) = none)
    (hFp : findHonestPrincipal P s3.hyb.base.principals hdr.ikAPk = some (u_r, senderEntry))
    (hHon : (!senderEntry.corrupted) = true)
    (hSpkId : hdr.spkId = UInt32.ofNat j.val)
    (hPqspkId : hdr.pqspkId = UInt32.ofNat j.val)
    (hReplayOk : (checkAndMarkKyberBaseKeySeen s3.hyb.base.seenKyberBaseKeys k.val
      hdr.pqspkId hdr.spkId hdr.ekAPk).1 = true) :
    let secrets := recvHandshakeSecrets P kEntry bEntry dh4? ss_r hdr
    s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none := by
  have hw := hP.toWellFormedPrimitivesδ
  intro secrets
  cases hF : s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) with
  | none => rfl
  | some p =>
    exfalso
    have hV : ValidAuthKeyStoresFull S P s3.hyb.base := hRunInv.1
    have huMem : (u_r, senderEntry) ∈ s3.hyb.base.principals :=
      List.mem_of_find?_eq_some hFp
    have hPowIk : P.pow8 hdr.ikAPk = P.pow8 senderEntry.ikAPk :=
      beq_iff_eq.mp (List.find?_some
        (p := fun (x : Nat × PrincipalEntry) => P.pow8 hdr.ikAPk == P.pow8 x.2.ikAPk) hFp)
    have hbMem : ((k.val, j.val), bEntry) ∈ s3.hyb.base.spkBundles := hRespV.2.1
    have hEkLen : hdr.ekAPk.length = 32 := hRespV.2.2.2.1
    have hEkCanon : P.isCanonical hdr.ekAPk = true := hRespV.2.2.2.2.1
    have hDh1 : extractDh1 secrets = P.x25519 bEntry.spkSk hdr.ikAPk :=
      extractDh1_buildSecrets (hw.x25519_len bEntry.spkSk hdr.ikAPk)
    have hDh3 : extractDh3 secrets = P.x25519 bEntry.spkSk hdr.ekAPk :=
      extractDh3_buildSecrets (hw.x25519_len bEntry.spkSk hdr.ikAPk)
        (hw.x25519_len kEntry.secIKA0 hdr.ekAPk)
        (hw.x25519_len bEntry.spkSk hdr.ekAPk)
    rcases (hOrig secrets p hF).2 with hInLog | hSendOrig | hRespOrig
    · have hBad := badAuthFgAnyLatched_of_recv_mem_advRoLog P hP maxRo s3.toFg hV
        huMem hHon hPowIk hbMem hInLog hRoLen hDh1
      rw [hbF] at hBad; nomatch hBad
    · rcases recv_matched_none_imp_abort_or_badLatched_of_sendRoOrigin P hP maxRo s3 hRunInv
        hRespV hMatchNone hFp hHon hSendOrig with hAbDec | hAb | hBad
      · rw [hAbDecF] at hAbDec; nomatch hAbDec
      · rw [hAbF] at hAb; nomatch hAb
      · rw [hbF] at hBad; nomatch hBad
    · have hBad := badAuthFgAnyLatched_of_recv_respRoOrigin P hP maxRo s3 hV
        huMem hHon hPowIk hbMem hSpkId hPqspkId hEkLen hEkCanon hReplayOk hRespLen
        hRespOrig hDh1 hDh3
      rw [hbF] at hBad; nomatch hBad
private theorem map_opk_keys_consume_c6c3 (key : Nat × Nat × Nat)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) :
    (opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e))).map
        (fun (idx, o) => (idx, o.opkSk, o.opkPk)) =
    opkEntries.map (fun (idx, o) => (idx, o.opkSk, o.opkPk)) := by
  rw [List.map_map]
  congr 1; funext ⟨idx, e⟩
  dsimp only [Function.comp_apply]
  split_ifs <;> rfl
theorem finishLatchedRecvOPK_some_ext {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (rRec : _root_.SignalPqxdh.Security.RecvKemRecord)
    (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey)) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    let hstDec := { s.hyb with recvKemRecs := rRec :: s.hyb.recvKemRecs }
    let y := finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s hstDec
      (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))
    AuthHybridTraceSub s.hyb y.2.hyb ∧
    y.2.adv.hyb.base.roCache = roCache' ∧
    y.2.hyb.idealSessions = s.hyb.idealSessions ∧
    y.2.adv.advRoLog = s.adv.advRoLog ∧
    y.2.hyb.base.usedSendSessions = s.hyb.base.usedSendSessions ∧
    s.adv.respRecs.Sublist y.2.adv.respRecs ∧
    y.2.hyb.base.seenKyberBaseKeys = usedTriples' := by
  unfold finishLatchedRecvOPK finishAuthHybridRecvOPK wrapAuthAdvLatchedRecv
    AuthAdvLatchedState.hyb
  dsimp only
  have hOpkSub :
      (s.adv.hyb.base.opkEntries.map (fun (idx, o) => (idx, o.opkSk, o.opkPk))).Sublist
        ((s.adv.hyb.base.opkEntries.map (fun (idx, e) =>
          if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true })
          else (idx, e))).map (fun (idx, o) => (idx, o.opkSk, o.opkPk))) := by
    rw [map_opk_keys_consume_c6c3]
  rcases findHonestPrincipal P s.adv.hyb.base.principals msg.hdr.ikAPk with
    _ | ⟨_, senderEntry⟩
  · exact ⟨⟨⟨List.Sublist.refl _, List.Sublist.refl _, hOpkSub,
      List.Sublist.refl _, List.Sublist.refl _⟩,
      List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩,
      rfl, rfl, rfl, rfl, List.sublist_cons_self _ _, rfl⟩
  · dsimp only
    split_ifs <;>
      exact ⟨⟨⟨List.Sublist.refl _, List.Sublist.refl _, hOpkSub,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩,
        rfl, rfl, rfl, rfl, List.sublist_cons_self _ _, rfl⟩
theorem finishLatchedRecvNoOPK_some_ext {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (rRec : _root_.SignalPqxdh.Security.RecvKemRecord)
    (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey)) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))) :
    let hstDec := { s.hyb with recvKemRecs := rRec :: s.hyb.recvKemRecs }
    let y := finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s hstDec
      (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))
    AuthHybridTraceSub s.hyb y.2.hyb ∧
    y.2.adv.hyb.base.roCache = roCache' ∧
    y.2.hyb.idealSessions = s.hyb.idealSessions ∧
    y.2.adv.advRoLog = s.adv.advRoLog ∧
    y.2.hyb.base.usedSendSessions = s.hyb.base.usedSendSessions ∧
    s.adv.respRecs.Sublist y.2.adv.respRecs ∧
    y.2.hyb.base.seenKyberBaseKeys = usedTriples' := by
  unfold finishLatchedRecvNoOPK finishAuthHybridRecvNoOPK wrapAuthAdvLatchedRecv
    AuthAdvLatchedState.hyb
  dsimp only
  rcases findHonestPrincipal P s.adv.hyb.base.principals msg.hdr.ikAPk with
    _ | ⟨_, senderEntry⟩
  · exact ⟨⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
      List.Sublist.refl _, List.Sublist.refl _⟩,
      List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩,
      rfl, rfl, rfl, rfl, List.sublist_cons_self _ _, rfl⟩
  · dsimp only
    split_ifs <;>
      exact ⟨⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩,
        rfl, rfl, rfl, rfl, List.sublist_cons_self _ _, rfl⟩
theorem authSendRoOrigin_finishSend_of_spqr_some {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (hSender : sessionSenderIdx sid = u.val)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (uEntry : PrincipalEntry) (ekASk kemCoins ephASk spqrCoins ss kemCt : Bytes)
    (hEkLen : ekASk.length = 32) (s3 : AuthAdvLatchedState S)
    (hKS : ValidAuthKeyStores S P s3.hyb.base)
    (hFU : s3.hyb.base.principals.find? (fun (idx, _) => idx == u.val) = some (u.val, uEntry))
    (hKosk : koskBundleOk P s3.hyb.base.principals s3.hyb.base.spkBundles
      s3.hyb.base.opkEntries s3.hyb.base.advKeys bundle = true)
    (hKem : P.kemEncaps bundle.pqspkB kemCoins = some (ss, kemCt))
    (drKey : DRKey) (roCache3' : List (Bytes × DRKey))
    (rk1 ck1_0 : Bytes) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    {pqrStA : Bytes} {spqrSalt? : Option Bytes} {pqRatchetMsg : Bytes}
    (hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins = some (pqrStA, spqrSalt?, pqRatchetMsg)) :
    let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
    let dh2 := P.x25519 ekASk bundle.ikB
    let dh3 := P.x25519 ekASk bundle.spkB
    let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
    let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
    let y3 := withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
      ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache3' rk1 ck1_0 rootRoCache').2
    AuthSendRoOrigin S P y3.hyb secrets := by
  intro dh1 dh2 dh3 dh4? secrets y3
  have huMem : (u.val, uEntry) ∈ s3.hyb.base.principals := List.mem_of_find?_eq_some hFU
  have hPeerKeys := koskBundleOk_imp_validPeerKeys P s3.hyb.base hKS bundle hKosk
  have hKoskSpk :
      (isGameSpk P s3.hyb.base.spkBundles bundle.spkB ||
        isAdvRegistered P s3.hyb.base.advKeys bundle.spkB) = true := by
    unfold koskBundleOk at hKosk
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hKosk).1).2
  let peerPrincipal? := findHonestPrincipal P s3.hyb.base.principals bundle.ikB
  let isFreshPeer : Bool :=
    match peerPrincipal? with | some (_, p) => !p.corrupted | none => false
  let msgPlain := if isFreshPeer then (if s3.hyb.base.secb then m1 else m0) else m0
  let sessEntry := mkSendSessEntry P s3.hyb.base sid bundle m0 m1 isFreshPeer ekASk ephASk
  let s_ideal := buildSendIdealSession P sid bundle uEntry ekASk ephASk kemCt msgPlain
    drKey rk1 ck1_0 (P.chainKdfNext ck1_0) spqrSalt? pqRatchetMsg
  let initRec : _root_.SignalPqxdh.Security.InitKemRecord S :=
    { sid := sid, pqspkPk := bundle.pqspkB, kemCt := kemCt, kemSs := ss }
  have hBaseSub : AuthBaseTraceSub s3.hyb.base y3.hyb.base := by
    dsimp only [y3]
    unfold finishAuthHybridSendPure; rw [hSpqr]
    exact ⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
      List.Sublist.refl _, List.sublist_cons_self _ _⟩
  have hSessMem : sessEntry ∈ y3.hyb.base.sessions := by
    dsimp only [y3]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.mem_cons_self
  have hInitMem : initRec ∈ y3.hyb.initKemRecs := by
    dsimp only [y3]; unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.mem_cons_self
  have hPrinEq : y3.hyb.base.principals = s3.hyb.base.principals := by
    dsimp only [y3]; unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
  have hVi : ValidIdealAuthSession S P y3.hyb s_ideal sessEntry u.val uEntry
      kemCoins ss initRec :=
    ⟨hSessMem, rfl, hEkLen, rfl, rfl, rfl, rfl, rfl,
     hPrinEq ▸ huMem, hSender, rfl, hKem, hInitMem, rfl, rfl, rfl,
     hPeerKeys.1, hPeerKeys.2.1, hPeerKeys.2.2⟩
  have hSecNew : secrets = idealSessionSecrets P uEntry sessEntry.ekASk ss s_ideal := by
    unfold secrets idealSessionSecrets dh1 dh2 dh3 dh4? s_ideal buildSendIdealSession sessEntry
      mkSendSessEntry
    cases bundle.opkB? <;> rfl
  refine ⟨s3.hyb.base, u, uEntry, uEntry, bundle, kemCoins, ss, sessEntry, s_ideal, initRec,
    hKS, hBaseSub, hFU, rfl, hKoskSpk, rfl, rfl, rfl, hVi, hSecNew, ?_⟩
  intro hId
  dsimp only [y3]
  unfold finishAuthHybridSendPure; rw [hSpqr]
  dsimp only [withLatchedHyb, AuthAdvLatchedState.hyb]
  change s_ideal ∈ if _ then s_ideal :: s3.hyb.idealSessions else s3.hyb.idealSessions
  split_ifs with hIf
  · exact List.mem_cons_self
  · exact False.elim (hIf hId)
private theorem prop_of_liftAuthBase_c6c3 {S : Setup} (Q : AuthHybridState S → Prop)
    (m : StateT (AuthState S) ProbComp AuthResponse) (hst : AuthHybridState S)
    (h : ∀ p ∈ support (m.run hst.base), Q { hst with base := p.2 })
    {y : AuthResponse × AuthHybridState S}
    (hy : y ∈ support ((liftAuthBase m).run hst)) :
    Q y.2 := by
  unfold liftAuthBase at hy
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
    support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy
  rcases hy with ⟨⟨resp, base'⟩, hp, _, rfl⟩
  exact h (resp, base') hp
theorem nonRo_query_usedKyberTriples_eq_of_mem_support {S : Setup} (stage : AuthHybridStage)
    (P : Primitives) (q : AuthQuery S) (s : AuthAdvLatchedState S) (hq : isAuthNonRoQuery q = true)
    {y : AuthResponse × AuthAdvLatchedState S}
    (hy : y ∈ support ((pqxdhAuthAdvLatchedStageImpl stage S P q).run s)) :
    y.2.hyb.base.seenKyberBaseKeys = s.hyb.base.seenKyberBaseKeys ∧
    y.2.hyb.base.hasWonAuth = s.hyb.base.hasWonAuth := by
  have hyHyb := mem_support_hyb_of_mem_support_pqxdhAuthAdvLatchedStageImpl stage P q s hy
  let Q : AuthHybridState S → Prop :=
    fun h' => h'.base.seenKyberBaseKeys = s.hyb.base.seenKyberBaseKeys ∧
      h'.base.hasWonAuth = s.hyb.base.hasWonAuth
  unfold pqxdhAuthHybridKoskImpl at hyHyb
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hyHyb
  by_cases hWon : (true && s.hyb.base.hasWonAuth) = true
  · simp only [hWon, ↓reduceIte, StateT.run_pure, mem_support_pure_iff] at hyHyb
    injection hyHyb with _ hEq; rw [hEq]; exact ⟨rfl, rfl⟩
  simp only [hWon, Bool.false_eq_true, ↓reduceIte] at hyHyb
  cases q with
  | roQuery _ => nomatch hq
  | sendOPK _ _ _ _ _ => nomatch hq
  | sendNoOPK _ _ _ _ _ => nomatch hq
  | recvOPK _ _ _ _ => nomatch hq
  | recvNoOPK _ _ _ _ => nomatch hq
  | initPrin u =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨_, _, _, _, _, rfl⟩; exact ⟨rfl, rfl⟩
  | corruptIK u =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    cases hF : s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    | some ue =>
      rcases ue with ⟨_, entry⟩; rw [hF] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
  | genSPK u j =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    · cases hF : s.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [hF] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
        rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
      | some ue =>
        rcases ue with ⟨_, uEntry⟩; rw [hF] at hp; dsimp only at hp
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
          support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
        rcases hp with ⟨_, _, _, _, ⟨_, _⟩, _, _, _, _, rfl⟩; exact ⟨rfl, rfl⟩
  | genOPK u j o =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨_, _, _, rfl⟩; exact ⟨rfl, rfl⟩
  | registerKey sk =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    cases hReg : registerAdvKey P s.hyb.base.advKeys sk with
    | none =>
      rw [hReg] at hp; dsimp only at hp; rw [StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    | some pa =>
      rcases pa with ⟨pk, advKeys'⟩; rw [hReg] at hp; dsimp only at hp
      rw [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, mem_support_pure_iff] at hp
      rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
  | roRootQuery rk dh =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp
    · rw [StateT.run_pure, mem_support_pure_iff] at hp; rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩
    · simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        support_bind, Set.mem_iUnion, mem_support_pure_iff] at hp
      rcases hp with ⟨⟨_, _⟩, _, _, rfl⟩; exact ⟨rfl, rfl⟩
  | revealDhSecrets =>
    refine prop_of_liftAuthBase_c6c3 Q _ s.hyb (fun p hp => ?_) hyHyb
    unfold pqxdhAuthImpl at hp
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hp; dsimp only at hp
    split_ifs at hp <;>
      (rw [StateT.run_pure, mem_support_pure_iff] at hp;
       rcases hp with ⟨_, rfl⟩; exact ⟨rfl, rfl⟩)
theorem authRecvOriginInv_of_nonRo_query {S : Setup} (P : Primitives)
    (q : AuthQuery S) (s3 : AuthAdvLatchedState S) (hq : isAuthNonRoQuery q = true)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl .g3 S P q).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  have hSub := authHybridTraceSub_pqxdhAuthAdvLatchedStageImpl .g3 P q s3 hy3
  rcases nonRo_query_fields_eq_of_mem_support .g3 P q s3 hq hy3 with
    ⟨hRo, _, hLog, hResp, _⟩
  have hKyb := (nonRo_query_usedKyberTriples_eq_of_mem_support .g3 P q s3 hq hy3).1
  exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub hRo
    (fun x hx => hLog ▸ hx) (hResp ▸ List.Sublist.refl _) (hKyb ▸ List.Sublist.refl _)
theorem authRecvOriginInv_of_roQuery {S : Setup} (P : Primitives)
    (secrets : Bytes) (s3 : AuthAdvLatchedState S)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.roQuery secrets)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  have hSub : ∀ c', AuthHybridTraceSub s3.hyb (updateRoQueryLatched secrets c' s3).hyb :=
    fun _ => ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
      List.Sublist.refl _, List.Sublist.refl _⟩,
      List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
  cases hWon : s3.adv.hyb.base.hasWonAuth
  · rw [pqxdhAuthAdvLatchedStageImpl_roQuery_run_eq _ _ _ _ hWon,
        evalHkdfOrRo_true_bind_eq] at hy3
    cases hF : s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
    | some p =>
      rw [hF] at hy3; rcases p with ⟨_, dk⟩; dsimp only at hy3
      rw [mem_support_pure_iff] at hy3; subst hy3
      exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig (hSub _) rfl
        (fun _ hx => List.mem_cons_of_mem _ hx) (List.Sublist.refl _) (List.Sublist.refl _)
    | none =>
      rw [hF] at hy3; dsimp only at hy3
      simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy3
      rcases hy3 with ⟨dk, _, rfl⟩
      exact authRecvOriginInv_of_traceSub_cons_roCache P hOrig (hSub _) rfl
        (fun _ hx => List.mem_cons_of_mem _ hx) (List.Sublist.refl _) (List.Sublist.refl _)
        (Or.inl List.mem_cons_self)
  · rw [pqxdhAuthAdvLatchedStageImpl_roQuery_run_of_hasWonAuth _ _ _ _ hWon,
        mem_support_pure_iff] at hy3
    subst hy3
    exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig (hSub _) rfl
      (fun _ hx => List.mem_cons_of_mem _ hx) (List.Sublist.refl _) (List.Sublist.refl _)
private theorem authRecvOriginInv_of_runAuthHybridSendLatched {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (hSender : sessionSenderIdx sid = u.val)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s3 : AuthAdvLatchedState S)
    (hKS : ValidAuthKeyStores S P s3.hyb.base)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support (runAuthHybridSendLatched .g3 S P sid u bundle m0 m1 s3)) :
    AuthRecvOriginInv S P y3.2 := by
  revert hy3
  rw [runAuthHybridSendLatched_eq .g3 P sid u bundle m0 m1 s3]
  dsimp only
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, mem_support_pure_iff]; rintro rfl; exact hOrig
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : s3.hyb.base.usedSendSessions.contains sid = true
    · simp only [h2, ↓reduceIte, mem_support_pure_iff]; rintro rfl; exact hOrig
    · rw [Bool.not_eq_true] at h2
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases hFU : s3.hyb.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        dsimp only; rw [mem_support_pure_iff]; rintro rfl; exact hOrig
      | some ue =>
        rcases ue with ⟨uIdx, uEntry⟩; dsimp only
        have huEq : uIdx = u.val :=
          beq_iff_eq.mp (List.find?_some (p := fun (x : Nat × PrincipalEntry) => x.1 == u.val) hFU)
        subst huEq
        split_ifs with h3 h4 h5
        · rw [mem_support_pure_iff]; rintro rfl; exact hOrig
        · rw [mem_support_pure_iff]; rintro rfl; exact hOrig
        · intro hy3
          simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy3
          rcases hy3 with ⟨_, _, _, _, _, _, _, _, rfl⟩; exact hOrig
        · have hKosk : koskBundleOk P s3.hyb.base.principals s3.hyb.base.spkBundles
              s3.hyb.base.opkEntries s3.hyb.base.advKeys bundle = true := by
            revert h4; simp
          intro hy3
          simp only [support_bind, Set.mem_iUnion] at hy3
          rcases hy3 with ⟨ekASk, hek, kemCoins, _, ephASk, _, spqrCoins, _, hy3⟩
          have hEkLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32 hek
          cases hKem : P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              rw [hKem] at hy3; dsimp only at hy3
              rw [mem_support_pure_iff] at hy3; subst hy3; exact hOrig
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              rw [hKem] at hy3; dsimp only at hy3
              simp only [support_bind, Set.mem_iUnion] at hy3
              rcases hy3 with ⟨⟨drKey, roCache'⟩, hDr, hyPost⟩
              unfold finishAuthHybridSendPost at hyPost
              simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hyPost
              rcases hyPost with ⟨⟨⟨rk1, ck1_0⟩, rootRoCache'⟩, _, rfl⟩
              cases hSpqr : P.spqrInitSend drKey.pqrKey spqrCoins with
              | none =>
                dsimp only [finishAuthHybridSendPure]; rw [hSpqr]; exact hOrig
              | some pqr =>
                rcases pqr with ⟨pqrStA, spqrSalt?, pqRatchetMsg⟩
                have hSub : AuthHybridTraceSub s3.hyb
                    (withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
                      ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache'
                      rk1 ck1_0 rootRoCache').2).hyb := by
                  unfold finishAuthHybridSendPure; rw [hSpqr]
                  dsimp only [withLatchedHyb, AuthAdvLatchedState.hyb]
                  refine ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
                    List.Sublist.refl _, List.sublist_cons_self _ _⟩,
                    List.sublist_cons_self _ _, List.Sublist.refl _, ?_⟩
                  dsimp only
                  split_ifs <;> first | exact List.sublist_cons_self _ _ | exact List.Sublist.refl _
                have hSendOrig := authSendRoOrigin_finishSend_of_spqr_some P sid u hSender
                  bundle m0 m1 uEntry ekASk kemCoins ephASk spqrCoins ss kemCt hEkLen s3
                  hKS hFU hKosk hKem drKey roCache' rk1 ck1_0 rootRoCache' hSpqr
                have hRoEq : (withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1
                    uEntry ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache'
                    rk1 ck1_0 rootRoCache').2).adv.hyb.base.roCache = roCache' := by
                  unfold finishAuthHybridSendPure; rw [hSpqr]; rfl
                have hKybSub : s3.hyb.base.seenKyberBaseKeys.Sublist
                    (withLatchedHyb s3 (finishAuthHybridSendPure P sid bundle m0 m1 uEntry
                      ekASk ephASk spqrCoins ss kemCt s3.hyb drKey roCache'
                      rk1 ck1_0 rootRoCache').2).hyb.base.seenKyberBaseKeys := by
                  unfold finishAuthHybridSendPure; rw [hSpqr]; exact List.Sublist.refl _
                unfold evalAuthHybridSendDrKey AuthHybridStage.idealDrKey evalHkdfOrRo at hDr
                simp only [Bool.and_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hDr
                let secrets := buildSecrets (P.x25519 uEntry.secIKA0 bundle.spkB)
                  (P.x25519 ekASk bundle.ikB) (P.x25519 ekASk bundle.spkB)
                  (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) ss
                cases hF : s3.hyb.base.roCache.find? (fun (s, _) => s == secrets) with
                | some p =>
                  rw [hF] at hDr; rcases p with ⟨_, dk⟩; dsimp only at hDr
                  rw [mem_support_pure_iff] at hDr
                  injection hDr with _ hRcEq; subst hRcEq
                  exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub hRoEq
                    (fun _ hx => hx) (List.Sublist.refl _) hKybSub
                | none =>
                  rw [hF] at hDr; dsimp only at hDr
                  simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hDr
                  rcases hDr with ⟨dk, _, hEq⟩
                  injection hEq with hDkEq hRcEq; subst hDkEq hRcEq
                  exact authRecvOriginInv_of_traceSub_cons_roCache P hOrig hSub hRoEq
                    (fun _ hx => hx) (List.Sublist.refl _) hKybSub (Or.inr (Or.inl hSendOrig))
theorem authRecvOriginInv_of_sendOPK {S : Setup} (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (s3 : AuthAdvLatchedState S) (hKS : ValidAuthKeyStores S P s3.hyb.base)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.sendOPK u i bundle m0 m1)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  unfold pqxdhAuthAdvLatchedStageImpl pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl at hy3
  simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind] at hy3
  split_ifs at hy3
  · rw [StateT.run_pure, pure_bind, mem_support_pure_iff] at hy3; subst hy3; exact hOrig
  · rw [StateT.run_pure, pure_bind, mem_support_pure_iff] at hy3; subst hy3; exact hOrig
  · exact authRecvOriginInv_of_runAuthHybridSendLatched P (.sendOPK u i) u rfl bundle m0 m1
      s3 hKS hOrig hy3
theorem authRecvOriginInv_of_sendNoOPK {S : Setup} (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (s3 : AuthAdvLatchedState S) (hKS : ValidAuthKeyStores S P s3.hyb.base)
    (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.sendNoOPK u i bundle m0 m1)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  unfold pqxdhAuthAdvLatchedStageImpl pqxdhAuthAdvStageImpl pqxdhAuthHybridKoskImpl at hy3
  simp only [StateT.run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind] at hy3
  split_ifs at hy3
  · rw [StateT.run_pure, pure_bind, mem_support_pure_iff] at hy3; subst hy3; exact hOrig
  · rw [StateT.run_pure, pure_bind, mem_support_pure_iff] at hy3; subst hy3; exact hOrig
  · exact authRecvOriginInv_of_runAuthHybridSendLatched P (.sendNoOPK u i) u rfl bundle m0 m1
      s3 hKS hOrig hy3
theorem roCache_of_mem_support_evalAuthHybridRecvSchedule_g3 {S : Setup} (P : Primitives)
    (hst : AuthHybridState S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg)
    {dk : DRKey} {rk1 ck1_1 pt : Bytes}
    {roCache' : List (Bytes × DRKey)} {rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes))}
    (hMem : some (dk, rk1, ck1_1, pt, roCache', rootRoCache') ∈
      support (evalAuthHybridRecvSchedule .g3 true P hst kEntry bEntry opkPk? secrets msg)) :
    roCache' = hst.base.roCache ∨ roCache' = (secrets, dk) :: hst.base.roCache := by
  rw [evalAuthHybridRecvSchedule_g3_eq] at hMem
  dsimp (config := { zetaHave := true }) only at hMem
  rw [evalAuthHybridRecvDrKey_g3_eq] at hMem
  simp only [support_bind, Set.mem_iUnion] at hMem
  rcases hMem with ⟨⟨drKey, roCache''⟩, hDr, hPost⟩
  unfold evalAuthHybridRecvPost at hPost
  simp only [support_bind, Set.mem_iUnion] at hPost
  rcases hPost with ⟨core?, _, hCore⟩
  cases core? with
  | none =>
    dsimp only at hCore
    rw [mem_support_pure_iff] at hCore
    nomatch hCore
  | some c =>
    rcases c with ⟨rk1', ck1_1', pt', rootRoCache''⟩
    dsimp only at hCore
    rw [mem_support_pure_iff] at hCore
    injection hCore with hTuple
    injection hTuple with hDk hRest
    injection hRest with _ hRest2
    injection hRest2 with _ hRest3
    injection hRest3 with _ hRest4
    injection hRest4 with hRc _
    subst hDk hRc
    unfold evalHkdfOrRo at hDr
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hDr
    cases hF : hst.base.roCache.find? (fun (s, _) => s == secrets) with
    | some p =>
      rw [hF] at hDr; rcases p with ⟨_, dk'⟩; dsimp only at hDr
      rw [mem_support_pure_iff] at hDr
      injection hDr with _ hRcEq
      exact Or.inl hRcEq
    | none =>
      rw [hF] at hDr; dsimp only at hDr
      simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hDr
      rcases hDr with ⟨dk', _, hEq⟩
      injection hEq with hDkEq hRcEq
      subst hDkEq
      exact Or.inr hRcEq
theorem authRecvOriginInv_of_recvOPK {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (msg : PreKeyMsg)
    (s3 : AuthAdvLatchedState S) (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.recvOPK k j o msg)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  rw [pqxdhAuthAdvLatchedStageImpl_recvOPK_run_eq] at hy3
  cases hPre : parseAuthRecvOPKPre P k j o msg s3.hyb.base with
  | none =>
    rw [hPre, mem_support_pure_iff] at hy3; subst hy3
    have hSub : AuthHybridTraceSub s3.hyb
        (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2.hyb :=
      ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
    exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub rfl
      (fun _ hx => hx) (List.sublist_cons_self _ _) (List.Sublist.refl _)
  | some pre =>
    rcases pre with ⟨kEntry, bEntry, oEntry, usedTriples', ss⟩
    rw [hPre] at hy3; dsimp only at hy3
    simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy3
    rcases hy3 with ⟨res?, hRes, rfl⟩
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec : AuthHybridState S := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    cases res? with
    | none =>
      have hSub : AuthHybridTraceSub s3.hyb
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg
            s3 hstDec none).2.hyb :=
        ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
          List.Sublist.refl _, List.Sublist.refl _⟩,
          List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
      exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub rfl
        (fun _ hx => hx) (List.sublist_cons_self _ _) (List.Sublist.refl _)
    | some r =>
      rcases r with ⟨dk, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      have hUtSub :=
        (parseAuthRecvOPKPre_some_props P k j o msg s3.hyb hPre).2.2.2.2.2.2.2.2.2.2.2.1
      rcases finishLatchedRecvOPK_some_ext P k j o kEntry bEntry oEntry usedTriples' msg
          s3 rRec dk rk1 ck1_1 pt roCache' rootRoCache' with
        ⟨hSub, hRoEq, _, hAdvEq, _, hRespSub, hKybEq⟩
      have hKybSub : s3.hyb.base.seenKyberBaseKeys.Sublist
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
            (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.hyb.base.seenKyberBaseKeys := by
        rw [hKybEq]; exact hUtSub
      have hLogSub : ∀ x ∈ s3.adv.advRoLog, x ∈
          (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s3 hstDec
            (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.adv.advRoLog := by
        intro x hx; rw [hAdvEq]; exact hx
      have hNewResp := (authRespRoOrigin_finishLatchedRecvOPK P hP k j o msg s3 hPre dk
          rk1 ck1_1 pt roCache' rootRoCache').1
      rcases roCache_of_mem_support_evalAuthHybridRecvSchedule_g3 P hstDec kEntry bEntry
          (some oEntry.opkPk)
          (recvHandshakeSecrets P kEntry bEntry (some (P.x25519 oEntry.opkSk msg.hdr.ekAPk))
            ss msg.hdr)
          msg hRes with hEq | hCons
      · exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub (hRoEq.trans hEq)
          hLogSub hRespSub hKybSub
      · exact authRecvOriginInv_of_traceSub_cons_roCache P hOrig hSub (hRoEq.trans hCons)
          hLogSub hRespSub hKybSub (Or.inr (Or.inr hNewResp))
theorem authRecvOriginInv_of_recvNoOPK {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg)
    (s3 : AuthAdvLatchedState S) (hOrig : AuthRecvOriginInv S P s3)
    {y3 : AuthResponse × AuthAdvLatchedState S}
    (hy3 : y3 ∈ support ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.recvNoOPK k j l msg)).run s3)) :
    AuthRecvOriginInv S P y3.2 := by
  rw [pqxdhAuthAdvLatchedStageImpl_recvNoOPK_run_eq] at hy3
  cases hPre : parseAuthRecvNoOPKPre P k j l msg s3.hyb.base with
  | none =>
    rw [hPre, mem_support_pure_iff] at hy3; subst hy3
    have hSub : AuthHybridTraceSub s3.hyb
        (wrapAuthAdvLatchedRecv k j msg s3 (.noneResp, s3.hyb)).2.hyb :=
      ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
        List.Sublist.refl _, List.Sublist.refl _⟩,
        List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _⟩
    exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub rfl
      (fun _ hx => hx) (List.sublist_cons_self _ _) (List.Sublist.refl _)
  | some pre =>
    rcases pre with ⟨kEntry, bEntry, usedTriples', ss⟩
    rw [hPre] at hy3; dsimp only at hy3
    simp only [support_bind, Set.mem_iUnion, mem_support_pure_iff] at hy3
    rcases hy3 with ⟨res?, hRes, rfl⟩
    let rRec : _root_.SignalPqxdh.Security.RecvKemRecord := {
      k := k.val, j := j.val, pqspkPk := bEntry.pqspkPk,
      pqspkSk := bEntry.pqspkSk, kemCt := msg.hdr.kemCt, kemSs := ss }
    let hstDec : AuthHybridState S := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
    cases res? with
    | none =>
      have hSub : AuthHybridTraceSub s3.hyb
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg
            s3 hstDec none).2.hyb :=
        ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
          List.Sublist.refl _, List.Sublist.refl _⟩,
          List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
      exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub rfl
        (fun _ hx => hx) (List.sublist_cons_self _ _) (List.Sublist.refl _)
    | some r =>
      rcases r with ⟨dk, rk1, ck1_1, pt, roCache', rootRoCache'⟩
      have hUtSub :=
        (parseAuthRecvNoOPKPre_some_props P k j l msg s3.hyb hPre).2.2.2.2.2.2.2.2.2.2.1
      rcases finishLatchedRecvNoOPK_some_ext P k j l kEntry bEntry usedTriples' msg
          s3 rRec dk rk1 ck1_1 pt roCache' rootRoCache' with
        ⟨hSub, hRoEq, _, hAdvEq, _, hRespSub, hKybEq⟩
      have hKybSub : s3.hyb.base.seenKyberBaseKeys.Sublist
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
            (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.hyb.base.seenKyberBaseKeys := by
        rw [hKybEq]; exact hUtSub
      have hLogSub : ∀ x ∈ s3.adv.advRoLog, x ∈
          (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s3 hstDec
            (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.adv.advRoLog := by
        intro x hx; rw [hAdvEq]; exact hx
      have hNewResp := (authRespRoOrigin_finishLatchedRecvNoOPK P hP k j l msg s3 hPre dk
          rk1 ck1_1 pt roCache' rootRoCache').1
      rcases roCache_of_mem_support_evalAuthHybridRecvSchedule_g3 P hstDec kEntry bEntry none
          (recvHandshakeSecrets P kEntry bEntry none ss msg.hdr) msg hRes with hEq | hCons
      · exact authRecvOriginInv_of_traceSub_eq_roCache P hOrig hSub (hRoEq.trans hEq)
          hLogSub hRespSub hKybSub
      · exact authRecvOriginInv_of_traceSub_cons_roCache P hOrig hSub (hRoEq.trans hCons)
          hLogSub hRespSub hKybSub (Or.inr (Or.inr hNewResp))
/-! ## Receiver subcase premises -/
theorem authRoCacheCoupled_of_traceSub_cons_both_resp {S : Setup} (P : Primitives)
    {s35 s3 y3 : AuthAdvLatchedState S} {secrets : Bytes} {dk : DRKey}
    (hRc : AuthRoCacheCoupled P s35 s3)
    (_hF35 : s35.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none)
    (hF3 : s3.adv.hyb.base.roCache.find? (fun (s, _) => s == secrets) = none)
    (hSub : AuthHybridTraceSub s3.hyb y3.hyb)
    (hRoEq : y3.adv.hyb.base.roCache = (secrets, dk) :: s3.adv.hyb.base.roCache)
    (hIdEq : y3.hyb.idealSessions = s3.hyb.idealSessions)
    (hLogSub : ∀ x ∈ s3.adv.advRoLog, x ∈ y3.adv.advRoLog)
    (hUsedSub : ∀ x ∈ s3.hyb.base.usedSendSessions, x ∈ y3.hyb.base.usedSendSessions)
    (hRespSub : ∀ x ∈ s3.adv.respRecs, x ∈ y3.adv.respRecs)
    (hNewResp : AuthRespRoOrigin P y3 secrets) :
    AuthRoCacheCoupled P
      (withAuthAdvLatchedRoCache ((secrets, dk) :: s35.adv.hyb.base.roCache) y3) y3 := by
  rcases hRc with ⟨h1, h2, h3, h4⟩
  have h35Ro :
      (withAuthAdvLatchedRoCache
        ((secrets, dk) :: s35.adv.hyb.base.roCache) y3).adv.hyb.base.roCache =
        (secrets, dk) :: s35.adv.hyb.base.roCache := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sec' p hF35'
    rw [h35Ro, List.find?_cons] at hF35'
    rw [hRoEq, List.find?_cons]
    dsimp only at hF35' ⊢
    cases hBeq : (secrets == sec')
    · rw [hBeq] at hF35'; exact h1 sec' p hF35'
    · rw [hBeq] at hF35'; exact hF35'
  · intro s hs
    rw [hIdEq] at hs
    rcases h2 s hs with ⟨sessEntry, u, uEntry1, kemCoins, ss_s, initRec, hVi1, hVh1, hFind1⟩
    rcases validIdealAuthSession_of_traceSub P hSub hVi1 with ⟨uEntry2, hSecEq, _, hVi2⟩
    have hVh2 := validIdealSessionHonesty_of_traceSub P hSub hVh1
    have hIdealSecEq : idealSessionSecrets P uEntry2 sessEntry.ekASk ss_s s =
          idealSessionSecrets P uEntry1 sessEntry.ekASk ss_s s := by
      unfold idealSessionSecrets; rw [hSecEq]
    refine ⟨sessEntry, u, uEntry2, kemCoins, ss_s, initRec, hVi2, hVh2, ?_⟩
    dsimp only at hFind1 ⊢
    rw [hRoEq, hIdealSecEq, List.find?_cons]
    dsimp only
    have hNe : (secrets == idealSessionSecrets P uEntry1 sessEntry.ekASk ss_s s) = false := by
      cases hBeq : (secrets == idealSessionSecrets P uEntry1 sessEntry.ekASk ss_s s)
      · rfl
      · rw [← beq_iff_eq.mp hBeq, hF3] at hFind1; nomatch hFind1
    rw [hNe]; exact hFind1
  · intro sec' p hF3'
    rw [hRoEq, List.find?_cons] at hF3'
    dsimp only at hF3'
    cases hBeq : (secrets == sec')
    · rw [hBeq] at hF3'
      rcases h3 sec' p hF3' with ⟨hp1, hInLog | ⟨s_old, hsMem, hsUsed, hsInit, hDh3⟩ |
        ⟨k_r, j_r, bEntry_r, r_rec, hbMem, hrMem, hrKey, hEkLen, hDh3⟩⟩
      · exact ⟨hp1, Or.inl (hLogSub sec' hInLog)⟩
      · exact ⟨hp1, Or.inr (Or.inl ⟨s_old, hSub.base_sub.sessions_sub.subset hsMem,
          hUsedSub s_old.sid hsUsed, hsInit, hDh3⟩)⟩
      · exact ⟨hp1, Or.inr (Or.inr ⟨k_r, j_r, bEntry_r, r_rec,
          hSub.base_sub.spkBundles_sub.subset hbMem, hRespSub r_rec hrMem, hrKey, hEkLen, hDh3⟩)⟩
    · rw [hBeq] at hF3'
      injection hF3' with hpEq; subst hpEq
      have hSecEq : secrets = sec' := beq_iff_eq.mp hBeq
      subst hSecEq
      rcases hNewResp with ⟨r, _, b_r, hrMem, _, hbrMem, _, _, _, _, _, hrEkLen, _, _, _, hDh3, _⟩
      exact ⟨rfl, Or.inr (Or.inr ⟨r.bKey.1, r.bKey.2, b_r, r, hbrMem, hrMem,
        Prod.ext rfl rfl, hrEkLen, hDh3⟩)⟩
  · intro sec' p hF35' hF3'
    rw [h35Ro, List.find?_cons] at hF35'
    rw [hRoEq, List.find?_cons] at hF3'
    dsimp only at hF35' hF3'
    cases hBeq : (secrets == sec')
    · rw [hBeq] at hF35' hF3'
      rcases h4 sec' p hF35' hF3' with
        ⟨s, hs, sessEntry, u, uEntry1, kemCoins, ss_s, initRec, hVi1, hVh1, hSec, hpEq⟩
      rcases validIdealAuthSession_of_traceSub P hSub hVi1 with ⟨uEntry2, hSecEq, _, hVi2⟩
      have hVh2 := validIdealSessionHonesty_of_traceSub P hSub hVh1
      have hIdealSecEq : idealSessionSecrets P uEntry2 sessEntry.ekASk ss_s s =
            idealSessionSecrets P uEntry1 sessEntry.ekASk ss_s s := by
        unfold idealSessionSecrets; rw [hSecEq]
      rw [← hIdealSecEq] at hSec; rw [← hIdEq] at hs
      exact ⟨s, hs, sessEntry, u, uEntry2, kemCoins, ss_s, initRec, hVi2, hVh2, hSec, hpEq⟩
    · rw [hBeq] at hF35'; nomatch hF35'
theorem recv_subcaseB_roCache_cases {S : Setup} (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) {s35 s3 : AuthAdvLatchedState S}
    (hRc : AuthRoCacheCoupled P s35 s3) (hKS : ValidAuthKeyStores S P s3.hyb.base)
    {k : Fin S.N_id} {j : Fin S.N_recv} {kEntry : PrincipalEntry} {bEntry : SpkBundleEntry}
    {opkPk? dh4? : Option Bytes} {ss : Bytes}
    {rRec : _root_.SignalPqxdh.Security.RecvKemRecord} {hdr : HandshakeHdr}
    (hAbDecF : isAuthG3Abort P { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs } = false)
    (hRespV : ValidAuthRespHandshake S P
      { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      k j kEntry bEntry opkPk? dh4? ss rRec hdr)
    (hMatchNone : s3.hyb.idealSessions.find?
      (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk hdr) = none) :
    let secrets := recvHandshakeSecrets P kEntry bEntry dh4? ss hdr
    (∃ sec35 sec3 dk,
      s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec35, dk) ∧
      s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = some (sec3, dk)) ∨
    (s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none ∧
     s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) = none) := by
  intro secrets
  cases hF35 : s35.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) with
  | some p =>
    rcases p with ⟨sec35, dk⟩
    exact Or.inl ⟨sec35, sec35, dk, rfl, hRc.1 secrets (sec35, dk) hF35⟩
  | none =>
    right; refine ⟨rfl, ?_⟩
    cases hF3 : s3.hyb.base.roCache.find? (fun (inp, _) => inp == secrets) with
    | none => rfl
    | some p =>
      exfalso
      rcases hRc.2.2.2 secrets p hF35 hF3 with
        ⟨s, hsMem, sessEntry, u, uEntry1, kemCoins, ss_s, initRec, hVi1, hVh1, hSecEq, _⟩
      let hstDec : AuthHybridState S := { s3.hyb with recvKemRecs := rRec :: s3.hyb.recvKemRecs }
      have hSubDec : AuthHybridTraceSub s3.hyb hstDec :=
        ⟨⟨List.Sublist.refl _, List.Sublist.refl _, List.Sublist.refl _,
          List.Sublist.refl _, List.Sublist.refl _⟩,
          List.Sublist.refl _, List.sublist_cons_self _ _, List.Sublist.refl _⟩
      rcases validIdealAuthSession_of_traceSub P hSubDec hVi1 with ⟨uEntry2, hSecIKA, _, hVi2⟩
      have hVh2 := validIdealSessionHonesty_of_traceSub P hSubDec hVh1
      have hNoBadSig : hasBadSigAuth hstDec = false := by
        unfold isAuthG3Abort at hAbDecF
        simp only [Bool.or_eq_false_iff] at hAbDecF
        exact hAbDecF.1.1.2
      rcases validIdealSessionHonesty_imp_spk_and_pqspk_of_hasBadSigAuth_false
          P hstDec hNoBadSig hVi2.1 hVh2 with ⟨_, hPqHon⟩
      have hIdealSecEq : idealSessionSecrets P uEntry2 sessEntry.ekASk ss_s s = secrets := by
        rw [hSecEq]; unfold idealSessionSecrets; rw [hSecIKA]
      have hAb := recv_matched_none_imp_abort_of_idealSession_pqspkHonest P hP hstDec hKS
        hsMem hVi2 hRespV hPqHon hMatchNone hIdealSecEq
      rw [hAbDecF] at hAb; nomatch hAb
theorem finishLatchedRecvOPK_hasWonAuth_true_of_consume_false {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S)
    (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey)) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    {u_r : Nat} {senderEntry : PrincipalEntry}
    (hFp : findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk = some (u_r, senderEntry))
    (hHon : (!senderEntry.corrupted) = true)
    (hConsF : (consumeMatchingSentOPK P
      { bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
        sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
        pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
      hstDec.base.sentOPKEvents).1 = false) :
    (finishLatchedRecvOPK P k j o kEntry bEntry oEntry usedTriples' msg s hstDec
      (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.hyb.base.hasWonAuth = true := by
  unfold finishLatchedRecvOPK finishAuthHybridRecvOPK wrapAuthAdvLatchedRecv
    AuthAdvLatchedState.hyb
  dsimp only
  rw [hFp]; dsimp only
  simp only [hHon, ↓reduceIte]
  revert hConsF
  cases consumeMatchingSentOPK P
      { bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
        sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
        pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
      hstDec.base.sentOPKEvents with
  | mk matchedOk sentOPK' =>
    dsimp only; rintro rfl; simp
theorem finishLatchedRecvNoOPK_hasWonAuth_true_of_consume_false {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (s : AuthAdvLatchedState S) (hstDec : AuthHybridState S)
    (dk : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey)) (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    {u_r : Nat} {senderEntry : PrincipalEntry}
    (hFp : findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk = some (u_r, senderEntry))
    (hHon : (!senderEntry.corrupted) = true)
    (hConsF : (consumeMatchingSentNoOPK P
      { bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
        sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
        pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
      hstDec.base.sentNoOPKEvents).1 = false) :
    (finishLatchedRecvNoOPK P k j l kEntry bEntry usedTriples' msg s hstDec
      (some (dk, rk1, ck1_1, pt, roCache', rootRoCache'))).2.hyb.base.hasWonAuth = true := by
  unfold finishLatchedRecvNoOPK finishAuthHybridRecvNoOPK wrapAuthAdvLatchedRecv
    AuthAdvLatchedState.hyb
  dsimp only
  rw [hFp]; dsimp only
  simp only [hHon, ↓reduceIte]
  revert hConsF
  cases consumeMatchingSentNoOPK P
      { bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
        sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
        pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt }
      hstDec.base.sentNoOPKEvents with
  | mk matchedOk sentNoOPK' =>
    dsimp only; rintro rfl; simp
/-! ## Full step couplings -/
def AuthRoCacheOrWon {S : Setup} (P : Primitives)
    (s35 s3 : AuthAdvLatchedState S) : Prop :=
  AuthAdvLatchedAgreeOffRo s35 s3 ∧
  (AuthRoCacheCoupled P s35 s3 ∨
   (s35.hyb.base.hasWonAuth = true ∧ s3.hyb.base.hasWonAuth = true))
/-- Coupled invariant between `.g3_5` and `.g3` combining `AuthG3G3_5CoupledInv` and
    `AuthRecvOriginInv`. -/
def AuthFullG3G3_5CoupledInv {S : Setup} (P : Primitives)
    (s35 s3 : AuthAdvLatchedState S) : Prop :=
  AuthG3G3_5CoupledInv P s35 s3 ∧
  AuthRecvOriginInv S P s3
/-- Win-guarded coupled invariant between `.g3_5` and `.g3` on `AuthAdvLatchedState S`. -/
def AuthWinGuardedG3G3_5CoupledInv {S : Setup} (P : Primitives)
    (s35 s3 : AuthAdvLatchedState S) : Prop :=
  AuthAdvLatchedAgreeOffRo s35 s3 ∧
  ValidAuthHybridRunInv S P s3.hyb ∧
  AuthRecvOriginInv S P s3 ∧
  (AuthRoCacheCoupled P s35 s3 ∨
   (s35.hyb.base.hasWonAuth = true ∧ s3.hyb.base.hasWonAuth = true))
theorem authWinGuardedG3G3_5CoupledInv_empty (S : Setup) (P : Primitives) (secb : Bool) :
    AuthWinGuardedG3G3_5CoupledInv P
      (AuthAdvLatchedState.empty S secb) (AuthAdvLatchedState.empty S secb) :=
  ⟨AuthAdvLatchedAgreeOffRo.refl _, validAuthHybridRunInv_empty S P secb,
   authRecvOriginInv_empty S P secb, Or.inl (authRoCacheCoupled_empty S P secb)⟩
theorem authWinGuardedG3G3_5CoupledInv_of_full {S : Setup} (P : Primitives)
    {s35 s3 : AuthAdvLatchedState S} (hFull : AuthFullG3G3_5CoupledInv P s35 s3) :
    AuthWinGuardedG3G3_5CoupledInv P s35 s3 :=
  ⟨hFull.1.1, hFull.1.2.1, hFull.2, Or.inl hFull.1.2.2⟩
theorem authFullG3G3_5CoupledInv_of_winGuarded_not_won {S : Setup} (P : Primitives)
    {s35 s3 : AuthAdvLatchedState S} (hWin : AuthWinGuardedG3G3_5CoupledInv P s35 s3)
    (hNotWon : s3.hyb.base.hasWonAuth = false) :
    AuthFullG3G3_5CoupledInv P s35 s3 := by
  rcases hWin with ⟨hAg, hRun, hOrig, hRc | ⟨_, hWon3⟩⟩
  · exact ⟨⟨hAg, hRun, hRc⟩, hOrig⟩
  · rw [hNotWon] at hWon3; nomatch hWon3
theorem fgAuthStepCoupling_cutoff_latched_roQuery_full
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (secrets : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hFull : AuthFullG3G3_5CoupledInv P s35 s3) (hAbF : isAuthG3Abort P s3.hyb = false)
    (hRoStep : s3.adv.advRoLog.length + 1 ≤ maxRo) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.roQuery secrets)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.roQuery secrets)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep := fgAuthStepCoupling_cutoff_latched_roQuery S P hP maxRo secrets s35 s3
    hFull.1 hAbF hRoStep
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hInv'⟩ | hAb
  · exact Or.inl ⟨hEq, hInv', authRecvOriginInv_of_roQuery P secrets s3 hFull.2 hy3⟩
  · exact Or.inr hAb
theorem fgAuthStepCoupling_cutoff_latched_sendOPK_or_respEkColl_full
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hFull : AuthFullG3G3_5CoupledInv P s35 s3)
    (hAbF : isAuthG3Abort P s3.hyb = false) (hLogLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.sendOPK u i bundle m0 m1)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.sendOPK u i bundle m0 m1)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep := fgAuthStepCoupling_cutoff_latched_sendOPK_or_respEkColl S P hP maxRo u i
    bundle m0 m1 s35 s3 hFull.1 hAbF hLogLen hRespLen
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hInv'⟩ | hAb
  · exact Or.inl ⟨hEq, hInv',
      authRecvOriginInv_of_sendOPK P u i bundle m0 m1 s3 hFull.1.2.1.1.1 hFull.2 hy3⟩
  · exact Or.inr hAb
theorem fgAuthStepCoupling_cutoff_latched_sendNoOPK_or_respEkColl_full
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (maxRo : ℕ) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (s35 s3 : AuthAdvLatchedState S)
    (hFull : AuthFullG3G3_5CoupledInv P s35 s3)
    (hAbF : isAuthG3Abort P s3.hyb = false) (hLogLen : s3.adv.advRoLog.length ≤ maxRo)
    (hRespLen : s3.adv.respRecs.length ≤ S.N_sess_tot) :
    RelProbUpToBad (fun y35 y3 =>
        (y35.1 = y3.1 ∧ AuthFullG3G3_5CoupledInv P y35.2 y3.2) ∨
        (isAuthG3Abort P y35.2.hyb = true ∧ isAuthG3Abort P y3.2.hyb = true))
      (fun y3 => badAuthFgAnyLatchedMono P maxRo y3.2.toFg ||
                 latchRespEkCollSendStep P s3 y3.2 false)
      ((pqxdhAuthAdvLatchedStageImpl .g3_5 S P (.sendNoOPK u i bundle m0 m1)).run s35)
      ((pqxdhAuthAdvLatchedStageImpl .g3 S P (.sendNoOPK u i bundle m0 m1)).run s3) := by
  refine relProbUpToBad_of_imp_support_right ?_
  have hStep := fgAuthStepCoupling_cutoff_latched_sendNoOPK_or_respEkColl S P hP maxRo u i
    bundle m0 m1 s35 s3 hFull.1 hAbF hLogLen hRespLen
  refine RelProbUpToBad.mono hStep (fun y35 y3 hRel _ hy3 => ?_) (fun _ h => h)
  rcases hRel with ⟨hEq, hInv'⟩ | hAb
  · exact Or.inl ⟨hEq, hInv',
      authRecvOriginInv_of_sendNoOPK P u i bundle m0 m1 s3 hFull.1.2.1.1.1 hFull.2 hy3⟩
  · exact Or.inr hAb
/-- Win-guarded coupled invariant on `AuthSendLatchedState S`. -/
def AuthSendWinGuardedCoupledInv {S : Setup} (P : Primitives)
    (s35 s3 : AuthSendLatchedState S) : Prop :=
  AuthWinGuardedG3G3_5CoupledInv P s35.toAuthAdvLatchedState s3.toAuthAdvLatchedState ∧
  s35.respEkCollLatched = s3.respEkCollLatched
end Proofs.SignalPqxdh.Security
