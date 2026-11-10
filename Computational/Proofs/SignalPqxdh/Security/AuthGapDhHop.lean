/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthGapDhHopA
import Computational.Proofs.SignalPqxdh.Security.SigHop
import VCVio.EvalDist.Monad.Basic

/-!
# `Auth` hop `G0 → G3`: signature reduction and provenance bridges

Instantiates `SigGameLens` (`authSigLens`) to bound the EUF-CMA reduction `sigReductionAuth`,
and establishes the provenance-rewriting bridges `G0 → G0.1 → G1 → G2.1` via `runAuthWithProv`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal
open MeasureTheory
open SignalPqxdh
open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security

/-! ## `SigGameLens` instantiation -/

def badPeersAuth {S : Setup} (st : AuthState S) : List Bytes :=
  (st.sessions.filter (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest))).map (fun s =>
    s.peerIkPk)

def authSigLens (S : Setup) : SigGameLens S (AuthState S) AuthResponse where
  prins        := fun st => st.principals
  putPrins     := fun st p => { st with principals := p }
  spks         := fun st => st.spkBundles
  putSpks      := fun st s => { st with spkBundles := s }
  badPeers     := badPeersAuth
  noneResp     := .noneResp
  initPrinResp := .initPrinResp
  corrResp     := .corrResp
  bundleResp   := .bundleResp
  prins_putPrins    := fun _ _ => rfl
  spks_putPrins     := fun _ _ => rfl
  badPeers_putPrins := fun _ _ => rfl
  putPrins_putPrins := fun _ _ _ => rfl
  prins_putSpks     := fun _ _ => rfl
  spks_putSpks      := fun _ _ => rfl
  badPeers_putSpks  := fun _ _ => rfl
  putPrins_putSpks  := fun _ _ _ => rfl

def eraseAuth (S : Setup) (k : Nat) (st : AuthState S) : AuthState S :=
  { st with principals := erasePrinSk k st.principals }

theorem runAuthSendSim_commutes (S : Setup) (P : Primitives) (k : Nat)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) :
    CommutesRel (eraseAuth S k) st
      (runAuthSendSim S P sid u bundle m0 m1)
      (runAuthSendSim S P sid u bundle m0 m1) := by
  unfold runAuthSendSim
  apply CommutesRel.get_bind
  dsimp only [eraseAuth]
  rw [koskBundleOk_erasePrinSk, find?_idx_erasePrinSk]
  cases st.principals.find? (fun (idx, _) => idx == u.val) with
  | none => prove_commutes_rel
  | some p =>
    rcases p with ⟨idx, uEntry⟩
    dsimp only [Option.map]
    simp only [eraseEntrySk_secIKA0, eraseEntrySk_ikAPk, resolveSigPk_erasePrinSk,
      findHonestPrincipal_erasePrinSk]
    cases findHonestPrincipal P st.principals bundle.ikB with
    | none => dsimp only [Option.map]; prove_commutes_rel
    | some pp =>
      rcases pp with ⟨pIdx, pEntry⟩
      dsimp only [Option.map]
      simp only [eraseEntrySk_corrupted]
      prove_commutes_rel

theorem pqxdhAuthSimImpl_other_commutes (S : Setup) (P : Primitives) (k : Nat)
    (q : AuthQuery S) (st : AuthState S)
    (h_not_init : ∀ u, q ≠ .initPrin u)
    (h_not_corr : ∀ u, q ≠ .corruptIK u)
    (h_not_spk : ∀ u j, q ≠ .genSPK u j) :
    CommutesRel (eraseAuth S k) st
      (pqxdhAuthSimImpl S P q)
      (pqxdhAuthSimImpl S P q) := by
  cases q with
  | initPrin u => exact False.elim (h_not_init u rfl)
  | corruptIK u => exact False.elim (h_not_corr u rfl)
  | genSPK u j => exact False.elim (h_not_spk u j rfl)
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthSimImpl; dsimp only
    by_cases h : bundle.opkB?.isNone = true
    · simp only [h, ↓reduceIte]; exact CommutesRel.pure _ st _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact runAuthSendSim_commutes S P k (.sendOPK u i) u bundle m0 m1 st
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthSimImpl; dsimp only
    by_cases h : bundle.opkB?.isSome = true
    · simp only [h, ↓reduceIte]; exact CommutesRel.pure _ st _
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact runAuthSendSim_commutes S P k (.sendNoOPK u i) u bundle m0 m1 st
  | recvOPK u j o msg =>
    unfold pqxdhAuthSimImpl; apply CommutesRel.get_bind; dsimp only [eraseAuth]
    rw [koskSenderOk_erasePrinSk, find?_idx_erasePrinSk]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => dsimp only [Option.map]; prove_commutes_rel
    | some p =>
      rcases p with ⟨idx, kEntry⟩
      dsimp only [Option.map]
      simp only [eraseEntrySk_secIKA0, eraseEntrySk_ikAPk, findHonestPrincipal_erasePrinSk]
      cases findHonestPrincipal P st.principals msg.hdr.ikAPk <;>
        (dsimp only [Option.map]; prove_commutes_rel)
  | recvNoOPK u j l msg =>
    unfold pqxdhAuthSimImpl; apply CommutesRel.get_bind; dsimp only [eraseAuth]
    rw [koskSenderOk_erasePrinSk, find?_idx_erasePrinSk]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => dsimp only [Option.map]; prove_commutes_rel
    | some p =>
      rcases p with ⟨idx, kEntry⟩
      dsimp only [Option.map]
      simp only [eraseEntrySk_secIKA0, eraseEntrySk_ikAPk, findHonestPrincipal_erasePrinSk]
      cases findHonestPrincipal P st.principals msg.hdr.ikAPk <;>
        (dsimp only [Option.map]; prove_commutes_rel)
  | genOPK _ _ _ | roQuery _ | roRootQuery _ _ | revealDhSecrets | registerKey _ =>
    unfold pqxdhAuthSimImpl pqxdhAuthImpl; apply CommutesRel.get_bind; dsimp only [eraseAuth];
      prove_commutes_rel

def InitPostAuth {S : Setup} (P : Primitives) (bundle : PreKeyBundleInput)
    (st st' : AuthState S) : Prop :=
  st'.principals = st.principals ∧
  st'.spkBundles = st.spkBundles ∧
  (badPeersAuth st' = badPeersAuth st ∨
   (badPeersAuth st' = bundle.ikB :: badPeersAuth st ∧
     P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC bundle.spkB) bundle.spkSig =
       true ∧
     P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB) bundle.pqspkSig
       = true ∧
     (isHonestUncorruptedPeer P st.principals bundle.ikB).isSome = true ∧
     !(let (spkHon, _, pqspkHon) :=
       checkBundleProvenanceNoOpk P st.principals st.spkBundles [] bundle; spkHon && pqspkHon) =
         true))

theorem initPostAuth_refl {S : Setup} (P : Primitives) (bundle : PreKeyBundleInput) (st : AuthState
  S) :
    InitPostAuth P bundle st st :=
  ⟨rfl, rfl, Or.inl rfl⟩

theorem isHonestUncorruptedPeer_isSome_eq_match (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    (match findHonestPrincipal P principals ikB with
     | some (_, pEntry) => !pEntry.corrupted
     | none             => false) =
    (isHonestUncorruptedPeer P principals ikB).isSome := by
  unfold isHonestUncorruptedPeer
  cases findHonestPrincipal P principals ikB with
  | none => rfl
  | some p =>
    rcases p with ⟨k, entry⟩
    dsimp only
    cases entry.corrupted <;> rfl

theorem initPostAuth_cons_session {S : Setup} (P : Primitives) (bundle : PreKeyBundleInput)
    (st : AuthState S) (sess : AuthInitiatorEntry S)
    (usedSendSessions' : List (SessionId S))
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (h_peer : sess.peerIkPk = bundle.ikB)
    (h_fresh : sess.fresh = (match findHonestPrincipal P st.principals bundle.ikB with
     | some (_, pEntry) => !pEntry.corrupted
     | none             => false))
    (h_spk : sess.spkHonest = (match findHonestPrincipal P st.principals bundle.ikB with
     | none => (false, false, false)
     | some (k, _) =>
       (st.spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB),
        false,
        st.spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB))).1)
    (h_pqspk : sess.pqspkHonest = (match findHonestPrincipal P st.principals bundle.ikB with
     | none => (false, false, false)
     | some (k, _) =>
       (st.spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB),
        false,
        st.spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB))).2.2)
    (h_sig : (!(P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC bundle.spkB)
      bundle.spkSig &&
       P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB)
         bundle.pqspkSig)) = false) :
    InitPostAuth P bundle st
      { st with
        sessions         := sess :: st.sessions
        usedSendSessions := usedSendSessions'
        roCache          := roCache'
        rootRoCache      := rootRoCache' } := by
  have h_fresh' : sess.fresh = (isHonestUncorruptedPeer P st.principals bundle.ikB).isSome :=
    h_fresh.trans (isHonestUncorruptedPeer_isSome_eq_match P st.principals bundle.ikB)
  have h_spk' : sess.spkHonest = (checkBundleProvenanceNoOpk P st.principals st.spkBundles []
    bundle).1 := by
    rw [h_spk]; unfold checkBundleProvenanceNoOpk checkBundleProvenanceExact checkBundleProvenance
    cases findHonestPrincipal P st.principals bundle.ikB <;> rfl
  have h_pqspk' : sess.pqspkHonest = (checkBundleProvenanceNoOpk P st.principals st.spkBundles []
    bundle).2.2 := by
    rw [h_pqspk]; unfold checkBundleProvenanceNoOpk checkBundleProvenanceExact checkBundleProvenance
    cases findHonestPrincipal P st.principals bundle.ikB <;> rfl
  refine ⟨rfl, rfl, ?_⟩
  unfold badPeersAuth
  dsimp only
  rw [List.filter_cons]
  by_cases hbad : (sess.fresh && (!sess.spkHonest || !sess.pqspkHonest)) = true
  · right
    have hmap : List.map (fun s => s.peerIkPk)
        (if (sess.fresh && (!sess.spkHonest || !sess.pqspkHonest)) = true then
          sess :: List.filter (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest)) st.sessions
        else List.filter (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest)) st.sessions) =
        bundle.ikB :: List.map (fun s => s.peerIkPk)
          (List.filter (fun s => s.fresh && (!s.spkHonest || !s.pqspkHonest)) st.sessions) := by
      simp [hbad, h_peer]
    simp only [Bool.not_eq_false', Bool.and_eq_true] at h_sig
    simp only [Bool.and_eq_true, h_fresh', h_spk', h_pqspk', ← Bool.not_and] at hbad
    exact ⟨hmap, h_sig.1, h_sig.2, hbad.1, by simpa using hbad.2⟩
  · left
    simp [hbad]

theorem runAuthSendSim_pres (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) :
    SatisfiesAt (InitPostAuth P bundle st) st (runAuthSendSim S P sid u bundle m0 m1) := by
  have h0 := initPostAuth_refl P bundle st
  unfold runAuthSendSim
  apply SatisfiesAt.get_bind
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
  split
  · apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    apply SatisfiesAt.ite_return _ _ _ _ h0; intro _
    apply SatisfiesAt.liftM_bind; intro _
    apply SatisfiesAt.liftM_bind; intro _
    apply SatisfiesAt.liftM_bind; intro _
    apply SatisfiesAt.liftM_bind; intro _
    apply SatisfiesAt.ite_return _ _ _ _ h0; intro h_sig
    split
    · apply SatisfiesAt.liftM_bind; rintro ⟨drKey, roCache'⟩; dsimp only
      apply SatisfiesAt.liftM_bind; rintro ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩; dsimp only
      split
      · refine SatisfiesAt.set_of_pres _ _ _
          (initPostAuth_cons_session P bundle st _ _ _ _ rfl rfl rfl rfl h_sig) ?_
        intro x hx; split at hx <;> simp at hx <;> rw [hx]
      · exact SatisfiesAt.pure _ _ _ h0
    · exact SatisfiesAt.pure _ _ _ h0
  · exact SatisfiesAt.pure _ _ _ h0

theorem pqxdhAuthSimImpl_sendOPK_pres (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes) (st : AuthState
      S) :
    SatisfiesAt (InitPostAuth P b st) st (pqxdhAuthSimImpl S P (.sendOPK u i b m0 m1)) := by
  unfold pqxdhAuthSimImpl; dsimp only
  by_cases h : b.opkB?.isNone = true
  · simp only [h, ↓reduceIte]; exact SatisfiesAt.pure _ _ _ (initPostAuth_refl P b st)
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact runAuthSendSim_pres S P (.sendOPK u i) u b m0 m1 st

theorem pqxdhAuthSimImpl_sendNoOPK_pres (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes) (st :
      AuthState S) :
    SatisfiesAt (InitPostAuth P b st) st (pqxdhAuthSimImpl S P (.sendNoOPK u i b m0 m1)) := by
  unfold pqxdhAuthSimImpl; dsimp only
  by_cases h : b.opkB?.isSome = true
  · simp only [h, ↓reduceIte]; exact SatisfiesAt.pure _ _ _ (initPostAuth_refl P b st)
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact runAuthSendSim_pres S P (.sendNoOPK u i) u b m0 m1 st

theorem pqxdhAuthSimImpl_other_pres (S : Setup) (P : Primitives)
    (q : AuthQuery S) (st : AuthState S)
    (h_not_init : ∀ u, q ≠ .initPrin u)
    (h_not_corr : ∀ u, q ≠ .corruptIK u)
    (h_not_spk : ∀ u j, q ≠ .genSPK u j)
    (h_not_sopk : ∀ u i b m0 m1, q ≠ .sendOPK u i b m0 m1)
    (h_not_snoopk : ∀ u i b m0 m1, q ≠ .sendNoOPK u i b m0 m1) :
    ∀ x ∈ support ((pqxdhAuthSimImpl S P q).run st),
      x.2.principals = st.principals ∧ SpksPreserved S st.spkBundles x.2.spkBundles ∧
      badPeersAuth x.2 = badPeersAuth st := by
  let proj := fun s : AuthState S => (s.principals, s.spkBundles, s.sessions)
  have h_from_proj : ∀ m : StateT (AuthState S) ProbComp AuthResponse,
      PreservesAt proj st m →
      ∀ x ∈ support (m.run st),
        x.2.principals = st.principals ∧ SpksPreserved S st.spkBundles x.2.spkBundles ∧
        badPeersAuth x.2 = badPeersAuth st := by
    intro m hP x hx
    have h := hP x hx
    have hs : x.2.sessions = st.sessions := congrArg (Prod.snd ∘ Prod.snd) h
    exact ⟨congrArg Prod.fst h, spksPreserved_of_eq S (congrArg (Prod.fst ∘ Prod.snd) h),
      by unfold badPeersAuth; rw [hs]⟩
  cases q with
  | initPrin u => exact False.elim (h_not_init u rfl)
  | corruptIK u => exact False.elim (h_not_corr u rfl)
  | genSPK u j => exact False.elim (h_not_spk u j rfl)
  | sendOPK u i b m0 m1 => exact False.elim (h_not_sopk u i b m0 m1 rfl)
  | sendNoOPK u i b m0 m1 => exact False.elim (h_not_snoopk u i b m0 m1 rfl)
  | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _
      | revealDhSecrets | registerKey _ =>
    apply h_from_proj; unfold pqxdhAuthSimImpl pqxdhAuthImpl; dsimp only; prove_preserves_at

theorem extractBundleForgery_complete_of_badSig_noOpk
    (P : Primitives) (targetParty : Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput) (prevForgery : Option (Bytes × Bytes))
    (h_peer : isHonestUncorruptedPeer P principals bundle.ikB = some targetParty)
    (h_sig_ec : P.sigVerify targetPk (encodeEC bundle.spkB) bundle.spkSig = true)
    (h_sig_kem : P.sigVerify targetPk (encodeKEM bundle.pqspkB) bundle.pqspkSig = true)
    (h_bad : !(let (spkHon, _, pqspkHon) :=
      checkBundleProvenanceNoOpk P principals spkBundles [] bundle; spkHon && pqspkHon) = true) :
    (extractBundleForgery P targetParty targetPk principals spkBundles bundle prevForgery).isSome =
      true := by
  cases prevForgery with
  | some fg => rfl
  | none =>
    obtain ⟨entry, h_find, _, _, _⟩ :=
      findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some P principals bundle.ikB h_peer
    unfold extractBundleForgery
    simp only [h_peer, beq_self_eq_true, ↓reduceIte, h_sig_ec, h_sig_kem, Bool.true_and]
    unfold checkBundleProvenanceNoOpk checkBundleProvenanceExact checkBundleProvenance at h_bad
    simp only [h_find] at h_bad
    cases h_se : spkBundles.any (fun ((u, _), b) => u == targetParty && b.spkPk == bundle.spkB) with
    | false => simp
    | true =>
      cases h_pe : spkBundles.any (fun ((u, _), b) => u == targetParty && b.pqspkPk ==
        bundle.pqspkB) with
      | false => simp
      | true => simp [h_se, h_pe] at h_bad

theorem cleanPeers_cons_of_extractBundleForgery_eq_none_auth
    (S : Setup) (P : Primitives) (k : Nat) (sk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (peers : List Bytes) (bundle : PreKeyBundleInput)
    (hPrin : ValidPrincipals S principals)
    (hk : ∃ e, (k, e) ∈ principals ∧ e.secIKAsign = sk ∧ e.ikSignPk = P.sigPkGen sk ∧ e.corrupted =
      false)
    (hClean : CleanPeers S P k principals peers)
    (hfg : extractBundleForgery P k (P.sigPkGen sk) principals spkBundles bundle none = none)
    (h_sig_ec : P.sigVerify (resolveSigPk P principals bundle.ikB) (encodeEC bundle.spkB)
      bundle.spkSig = true)
    (h_sig_kem : P.sigVerify (resolveSigPk P principals bundle.ikB) (encodeKEM bundle.pqspkB)
      bundle.pqspkSig = true)
    (h_fresh : (isHonestUncorruptedPeer P principals bundle.ikB).isSome = true)
    (h_bad : !(let (spkHon, _, pqspkHon) :=
      checkBundleProvenanceNoOpk P principals spkBundles [] bundle; spkHon && pqspkHon) = true) :
    CleanPeers S P k principals (bundle.ikB :: peers) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hmem
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h_fresh
    obtain ⟨e, hfind, hmem_p, hpow, _⟩ := findHonestPrincipal_of_isHonestUncorruptedPeer_eq_some P
      principals bundle.ikB hu
    have hne : u ≠ k := by
      intro rfl
      rcases hk with ⟨ek, hmem_k, _, hpk_k, _⟩
      have he_eq : e = ek := mem_principals_unique hPrin.2 hmem_p hmem_k
      subst he_eq
      have hres : resolveSigPk P principals bundle.ikB = P.sigPkGen sk := by
        unfold resolveSigPk; rw [hfind]; exact hpk_k
      rw [hres] at h_sig_ec h_sig_kem
      have h_some := extractBundleForgery_complete_of_badSig_noOpk P u (P.sigPkGen sk)
        principals spkBundles bundle none hu h_sig_ec h_sig_kem h_bad
      rw [hfg] at h_some
      cases h_some
    exact ⟨u, e, hmem_p, hPrin.1 (u, e) hmem_p, hne, hpow⟩
  · exact hClean x hmem

theorem safe_step_initiate_auth (S : Setup) (P : Primitives) (k : Nat) (bundle : PreKeyBundleInput)
    (realInit : StateT (AuthState S) ProbComp AuthResponse) (st : AuthState S)
    (h_pres : SatisfiesAt (InitPostAuth P bundle st) st realInit)
    (hSafe : (authSigLens S).Safe P k st) :
    ∀ x ∈ support (realInit.run st), (authSigLens S).Safe P k x.2 := by
  rcases hSafe with ⟨hVP, hek, hCorr, hClean⟩
  intro x hx
  rcases h_pres x hx with ⟨hp, _, hbp | ⟨hbp, _, _, hFresh, _⟩⟩
  · unfold SigGameLens.Safe; dsimp only [authSigLens] at *; rw [hp, hbp]; exact ⟨hVP, hek, hCorr,
      hClean⟩
  · unfold SigGameLens.Safe; dsimp only [authSigLens] at *; rw [hp, hbp]
    exact ⟨hVP, hek, hCorr, cleanPeers_cons_of_safe S P k st.principals (badPeersAuth st) bundle.ikB
      hVP.1 hCorr hClean hFresh⟩

theorem before_step_initiate_auth (S : Setup) (P : Primitives) (k : Nat) (bundle :
  PreKeyBundleInput)
    (realInit : StateT (AuthState S) ProbComp AuthResponse)
    (st : AuthState S) (budget : Nat)
    (fL : AuthResponse × AuthState S → ℝ≥0∞)
    (fR : Bytes → (AuthResponse × SigReductionState (AuthState S) × Nat) × List Bytes → ℝ≥0∞)
    (h_pres : SatisfiesAt (InitPostAuth P bundle st) st realInit)
    (hBefore : (authSigLens S).ActiveBefore P k st budget)
    (h_ih_before : ∀ out st' b', (authSigLens S).ActiveBefore P k st' b' →
      fL (out, st') ≤ probExpect sampleScalar32 (fun sk =>
        fR sk ((out, ⟨st', k, P.sigPkGen sk, none⟩, b'), []))) :
    probExpect (realInit.run st) fL ≤
      probExpect sampleScalar32 (fun sk =>
        probExpect (runSigStepSim P sk budget ((authSigLens S).stepInitiate P bundle realInit ⟨st,
          k, P.sigPkGen sk, none⟩) []) (fR sk)) := by
  rcases hBefore with ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
  refine before_step_of_eq_real P k (realInit.run st)
    (fun pk => (authSigLens S).stepInitiate P bundle realInit ⟨st, k, pk, none⟩)
    ((authSigLens S).ActiveBefore P k) budget fL fR ?_ ?_ h_ih_before
  · intro pk
    unfold SigGameLens.stepInitiate
    dsimp only [authSigLens] at *
    simp [extractBundleForgery_eq_none_of_not_mem P k pk st.principals st.spkBundles bundle hNotK]
  · intro x hx
    rcases h_pres x hx with ⟨hp, hs, hbp | ⟨hbp, _, _, hFresh, _⟩⟩
    · unfold SigGameLens.ActiveBefore; dsimp only [authSigLens] at *; rw [hp, hs, hbp]; exact
        ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, hClean⟩
    · unfold SigGameLens.ActiveBefore; dsimp only [authSigLens] at *; rw [hp, hs, hbp]
      refine ⟨hb_eq, hVP, hNotK, hVS, hSpkNotK, ?_⟩
      exact cleanPeers_cons_of_before S P k st.principals (badPeersAuth st) bundle.ikB
        (fun p hp => ⟨hVP.1 p hp, hNotK p hp⟩) hClean hFresh

theorem after_step_initiate_auth (S : Setup) (P : Primitives) (k : Nat) (sk : Bytes) (bundle :
  PreKeyBundleInput)
    (realInit : StateT (AuthState S) ProbComp AuthResponse)
    (st : AuthState S) (s : SigReductionState (AuthState S)) (budget : Nat) (signedMsgs : List
      Bytes)
    (fL : AuthResponse × AuthState S → ℝ≥0∞)
    (fR : (AuthResponse × SigReductionState (AuthState S) × Nat) × List Bytes → ℝ≥0∞)
    (h_erase : realInit.run ((authSigLens S).eraseSk k st) =
      (fun (out, st') => (out, (authSigLens S).eraseSk k st')) <$> realInit.run st)
    (h_pres : SatisfiesAt (InitPostAuth P bundle st) st realInit)
    (hAfter : (authSigLens S).ActiveAfter P k sk st s budget signedMsgs)
    (h_fL_le : ∀ x, fL x ≤ 1)
    (h_fL_zero : ∀ x, (authSigLens S).Safe P k x.2 → fL x = 0)
    (h_fR_ge : ∀ y, SigWon P sk y.1.2.1 y.2 → 1 ≤ fR y)
    (h_ih : ∀ out st' s' b' msgs', (authSigLens S).ActiveAfter P k sk st' s' b' msgs' →
      fL (out, st') ≤ fR ((out, s', b'), msgs')) :
    probExpect (realInit.run st) fL ≤
      probExpect (runSigStepSim P sk budget ((authSigLens S).stepInitiate P bundle realInit s)
        signedMsgs) fR := by
  rcases hAfter with ⟨rfl, hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget, hMsgs, hClean⟩
  dsimp only [authSigLens] at *
  cases hfg : extractBundleForgery P k (P.sigPkGen sk) st.principals st.spkBundles bundle none with
  | some p =>
    rcases p with ⟨mStar, sigStar⟩
    have ⟨_, hver, hnotmem_bundle⟩ :=
      extractBundleForgery_valid_euf_cma P k (P.sigPkGen sk) st.principals st.spkBundles
        bundle hfg
    have hnotmem_msgs : mStar ∉ signedMsgs :=
      fun hm => hnotmem_bundle (hMsgs mStar hm)
    refine after_step_of_won P sk budget (realInit.run st)
      ((authSigLens S).stepInitiate P bundle realInit ⟨(authSigLens S).eraseSk k st, k, P.sigPkGen
        sk, none⟩)
      signedMsgs fL fR ?_ h_fL_le h_fR_ge
    intro sr hsr
    unfold SigGameLens.stepInitiate at hsr
    simp only [SigGameLens.prins_eraseSk, SigGameLens.spks_eraseSk, authSigLens,
      extractBundleForgery_erasePrinSk, hfg,
      support_bind, Set.mem_iUnion, exists_prop,
      support_pure, Set.mem_singleton_iff] at hsr
    rcases hsr with ⟨⟨out, gs'⟩, _, rfl⟩
    exact ⟨out, ⟨gs', k, P.sigPkGen sk, some (mStar, sigStar)⟩, rfl,
      ⟨mStar, sigStar, rfl, hver, hnotmem_msgs⟩⟩
  | none =>
    refine after_step_of_erase P k sk budget ((authSigLens S).eraseSk k)
      (realInit.run st) ((authSigLens S).stepInitiate P bundle realInit ⟨(authSigLens S).eraseSk k
        st, k, P.sigPkGen sk, none⟩)
      signedMsgs ((authSigLens S).Safe P k) ((authSigLens S).ActiveAfter P k sk) fL fR ?_ ?_
        h_fL_zero h_ih
    · unfold SigGameLens.stepInitiate
      simp [authSigLens, hfg, h_erase, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    · intro x hx
      refine Or.inr ?_
      rcases h_pres x hx with ⟨hp, hs, hbp | ⟨hbp, hSig1, hSig2, hFresh, hProv⟩⟩
      · unfold SigGameLens.ActiveAfter; dsimp only [authSigLens]
        rw [hp, hs, hbp]
        exact ⟨by simp [SigGameLens.eraseSk, hp], hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget,
          hMsgs, hClean⟩
      · unfold SigGameLens.ActiveAfter; dsimp only [authSigLens]
        rw [hp, hs, hbp]
        refine ⟨by simp [SigGameLens.eraseSk, hp], hVP, ⟨ek, hek, hsk, hpk, hcorr⟩, hVS, hBudget,
          hMsgs, ?_⟩
        exact cleanPeers_cons_of_extractBundleForgery_eq_none_auth S P k sk
          st.principals st.spkBundles (badPeersAuth st) bundle
          hVP ⟨ek, hek, hsk, hpk, hcorr⟩ hClean hfg hSig1 hSig2 hFresh hProv

noncomputable def stepAuthForSig (S : Setup) (P : Primitives)
    (q : AuthQuery S) (s : SigReductionState (AuthState S)) :
    ProbComp (SigStepResult (SigReductionState (AuthState S)) AuthResponse) :=
  if s.forgery.isSome then
    pure (.done .noneResp s)
  else
    match q with
    | .initPrin u => (authSigLens S).stepInitPrin P u s
    | .corruptIK u => (authSigLens S).stepCorruptIK u s
    | .genSPK u j => (authSigLens S).stepGenSPK P u j s
    | .sendOPK u i bundle m0 m1 =>
      (authSigLens S).stepInitiate P bundle (pqxdhAuthSimImpl S P (.sendOPK u i bundle m0 m1)) s
    | .sendNoOPK u i bundle m0 m1 =>
      (authSigLens S).stepInitiate P bundle (pqxdhAuthSimImpl S P (.sendNoOPK u i bundle m0 m1)) s
    | q_other =>
      SigGameLens.stepOther (pqxdhAuthSimImpl S P q_other) s

theorem evalStepPrim_stepAuthForSigPrim (S : Setup) (P : Primitives)
    (q : AuthQuery S) (s : SigReductionState (AuthState S))
    (hPrin : s.gameState.principals.length ≤ S.N_dh)
    (hSpk : s.gameState.spkBundles.length ≤ S.N_dh)
    (hOpk : s.gameState.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P s.gameState.advKeys) :
    evalStepPrim P (stepAuthForSigPrim S) q s =
      stepAuthForSig S P q s := by
  unfold evalStepPrim stepAuthForSigPrim stepAuthForSig
  split_ifs with hSome
  · rfl
  · cases q with
    | initPrin u =>
      dsimp only [SigGameLens.stepInitPrin, authSigLens]
      split_ifs
      · rfl
      · simp only [simulateQ_bind, simulateQ_embedUnif,
          simulateQ_pure, map_bind, map_pure, SigStepResultPrim.toProbComp]
        rfl
      · rw [simulateQ_bind, map_bind,
          simulateQ_pqxdhAuthSimImplPrim S P (.initPrin u) s.gameState hPrin hSpk hOpk hAdv]
        rfl
    | corruptIK u =>
      dsimp only [SigGameLens.stepCorruptIK, authSigLens]
      split_ifs
      · cases s.gameState.principals.find? (fun (idx, _) => idx == u.val) <;> rfl
      · rw [simulateQ_bind, map_bind,
          simulateQ_pqxdhAuthSimImplPrim S P (.corruptIK u) s.gameState hPrin hSpk hOpk hAdv]
        rfl
    | genSPK u j =>
      dsimp only [SigGameLens.stepGenSPK, authSigLens]
      split_ifs
      · rfl
      · cases s.gameState.principals.find? (fun (idx, _) => idx == u.val) with
        | none => rfl
        | some p =>
          rcases p with ⟨_, uEntry⟩
          dsimp only
          simp only [simulateQ_bind, simulateQ_embedUnif,
            simulateQ_pure, map_bind, map_pure, SigStepResultPrim.toProbComp]
          rfl
      · rw [simulateQ_bind, map_bind,
          simulateQ_pqxdhAuthSimImplPrim S P (.genSPK u j) s.gameState hPrin hSpk hOpk hAdv]
        rfl
    | sendOPK u i bundle m0 m1 =>
      dsimp only [SigGameLens.stepInitiate, authSigLens]
      rw [simulateQ_bind, map_bind,
        simulateQ_extractBundleForgeryPrim S P s.targetParty s.targetPk s.gameState.principals
          s.gameState.spkBundles bundle s.forgery hPrin,
        pure_bind, simulateQ_bind, map_bind,
        simulateQ_pqxdhAuthSimImplPrim S P (.sendOPK u i bundle m0 m1) s.gameState hPrin hSpk hOpk
          hAdv]
      simp [SigStepResultPrim.toProbComp]
    | sendNoOPK u i bundle m0 m1 =>
      dsimp only [SigGameLens.stepInitiate, authSigLens]
      rw [simulateQ_bind, map_bind,
        simulateQ_extractBundleForgeryPrim S P s.targetParty s.targetPk s.gameState.principals
          s.gameState.spkBundles bundle s.forgery hPrin,
        pure_bind, simulateQ_bind, map_bind,
        simulateQ_pqxdhAuthSimImplPrim S P (.sendNoOPK u i bundle m0 m1) s.gameState hPrin hSpk hOpk
          hAdv]
      simp [SigStepResultPrim.toProbComp]
    | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _
        | revealDhSecrets | registerKey _ =>
      dsimp only [SigGameLens.stepOther]
      rw [simulateQ_bind, map_bind,
        simulateQ_pqxdhAuthSimImplPrim S P _ s.gameState hPrin hSpk hOpk hAdv]
      simp [SigStepResultPrim.toProbComp]

def ValidAuthSim (S : Setup) (P : Primitives) (st : AuthState S) : Prop :=
  ValidPrincipals S st.principals ∧
  ValidSpkBundles S st.spkBundles ∧
  ValidOpkEntries S st.opkEntries ∧
  ValidAdvKeysPow8 P st.advKeys

theorem validAuthSim_lengths_le (S : Setup) (P : Primitives) (st : AuthState S)
    (hV : ValidAuthSim S P st) :
    st.principals.length ≤ S.N_dh ∧
    st.spkBundles.length ≤ S.N_dh ∧
    st.opkEntries.length ≤ S.N_dh := by
  have hNil := validEcLists_nil S
  have hEc : ValidEcLists S st.principals st.spkBundles st.opkEntries [] :=
    ⟨hV.1, hV.2.1, hV.2.2.1, hNil.2.2.2⟩
  have hTag := validTaggedPks_ecTaggedFromLists S P
    st.principals st.spkBundles st.opkEntries [] hEc
  have hLen := validTaggedPks_length_le hTag
  unfold ecTaggedFromLists at hLen
  simp only [List.length_append, List.length_map] at hLen
  exact ⟨by omega, by omega, by omega⟩

theorem runAuthSendSim_pres_proj (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (st :
      AuthState S) :
    PreservesAt (fun s : AuthState S => (s.principals, s.spkBundles, s.opkEntries, s.advKeys)) st
      (runAuthSendSim S P sid u bundle m0 m1) := by
  unfold runAuthSendSim; prove_preserves_at

theorem pqxdhAuthSimImpl_recvNoOPK_pres_proj (S : Setup) (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (msg : PreKeyMsg) (st : AuthState S) :
    PreservesAt (fun s : AuthState S => (s.principals, s.spkBundles, s.opkEntries, s.advKeys)) st
      (pqxdhAuthSimImpl S P (.recvNoOPK k j l msg)) := by
  unfold pqxdhAuthSimImpl; dsimp only; prove_preserves_at

theorem pqxdhAuthSimImpl_validAuthSim_step (S : Setup) (P : Primitives)
    (q : AuthQuery S) (st : AuthState S) (hV : ValidAuthSim S P st) :
    ∀ x ∈ support ((pqxdhAuthSimImpl S P q).run st), ValidAuthSim S P x.2 := by
  rcases hV with ⟨hVP, hVS, hVO, hAdv⟩
  let proj := fun s : AuthState S => (s.principals, s.spkBundles, s.opkEntries, s.advKeys)
  have h_from_proj : ∀ m : StateT (AuthState S) ProbComp AuthResponse,
      PreservesAt proj st m →
      ∀ x ∈ support (m.run st), ValidAuthSim S P x.2 := by
    intro m hp x hx
    have hs := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst hs
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) hs
    have hp3 : x.2.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hs
    have hp4 : x.2.advKeys = st.advKeys := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hs
    exact ⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hp4 ▸ hAdv⟩
  cases q with
  | initPrin u =>
    unfold pqxdhAuthSimImpl pqxdhAuthImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨secIKA0, _, secIKAsign, _, rfl⟩
      exact ⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, hAdv⟩
    · simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
  | corruptIK u =>
    unfold pqxdhAuthSimImpl pqxdhAuthImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
    | some p =>
      rcases p with ⟨_, entry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
      have h_corr := validPrincipals_map_corrupted S P u.val st.principals hVP
      intro x hx
      simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
      exact ⟨h_corr.1, hVS, hVO, hAdv⟩
  | genSPK u j =>
    unfold pqxdhAuthSimImpl pqxdhAuthImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind]
        intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
        exact ⟨hVP, (validSpkBundles_cons S u j _ st.spkBundles hVS hFresh).1, hVO, hAdv⟩
    · simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
  | genOPK u j o =>
    unfold pqxdhAuthSimImpl pqxdhAuthImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      intro x hx
      simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
      rcases hx with ⟨opkSk, _, rfl⟩
      exact ⟨hVP, hVS, (validOpkEntries_cons S u j o _ st.opkEntries hVO hFresh).1, hAdv⟩
    · simp [StateT.run_pure, ValidAuthSim, hVP, hVS, hVO, hAdv]
  | recvOPK k j o msg =>
    let projOpk := fun s : AuthState S =>
      (s.principals, s.spkBundles, s.opkEntries.map Prod.fst, s.advKeys)
    have h_step : ∀ (s : AuthState S) u t rc rrc,
        projOpk { s with
          opkEntries := s.opkEntries.map (fun (idx, e) =>
            if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
          usedRecvOPK := u, seenKyberBaseKeys := t, roCache := rc, rootRoCache := rrc } = projOpk s
            := by
      intro s u t rc rrc
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
      dsimp only [projOpk]
      rw [List.map_map]
      refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
      simp only [Function.comp_def]; split_ifs <;> rfl
    have hp : PreservesAt projOpk st (pqxdhAuthSimImpl S P (.recvOPK k j o msg)) := by
      unfold pqxdhAuthSimImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _ _ _ _ _)
        | split)
    intro x hx
    have h_eq := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) h_eq
    have hp3 : x.2.opkEntries.map Prod.fst = st.opkEntries.map Prod.fst :=
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp4 : x.2.advKeys = st.advKeys :=
      congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
    refine ⟨hp1 ▸ hVP, hp2 ▸ hVS, ⟨?_, ?_⟩, hp4 ▸ hAdv⟩
    · intro e he
      have he_fst : e.1 ∈ st.opkEntries.map Prod.fst := by
        rw [← hp3]; exact List.mem_map_of_mem he
      rw [List.mem_map] at he_fst
      rcases he_fst with ⟨e', he', heq⟩
      rw [← heq]; exact hVO.1 e' he'
    · have h_slot : x.2.opkEntries.map (fun e => ecOpkSlotIdx S e.1) =
          st.opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map (ecOpkSlotIdx S)) hp3
      rw [h_slot]; exact hVO.2
  | registerKey sk =>
    unfold pqxdhAuthSimImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · intro x hx
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨hVP, hVS, hVO, hAdv⟩
    · intro x hx
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨hVP, hVS, hVO, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · rfl
      · exact hAdv e he'
  | sendOPK u i bnd m0 m1 =>
    apply h_from_proj
    unfold pqxdhAuthSimImpl; dsimp only
    split
    · exact PreservesAt.pure _ _ _
    · exact runAuthSendSim_pres_proj S P (.sendOPK u i) u bnd m0 m1 st
  | sendNoOPK u i bnd m0 m1 =>
    apply h_from_proj
    unfold pqxdhAuthSimImpl; dsimp only
    split
    · exact PreservesAt.pure _ _ _
    · exact runAuthSendSim_pres_proj S P (.sendNoOPK u i) u bnd m0 m1 st
  | recvNoOPK k j l msg =>
    exact h_from_proj _ (pqxdhAuthSimImpl_recvNoOPK_pres_proj S P k j l msg st)
  | roQuery _ | roRootQuery _ _ | revealDhSecrets =>
    apply h_from_proj
    unfold pqxdhAuthSimImpl pqxdhAuthImpl; dsimp only; prove_preserves_at

theorem sigReductionAuthRun_pos (S : Setup)
    (A : AuthAdversary S) (pk : Bytes) (hN : 0 < S.N_id) :
    haveI : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    sigReductionAuthRun S A pk = (do
      let k ← embedPrim (spec := sigOracleSpec) (embedUnif ($ᵗ (Fin S.N_id)))
      simulateAuthForSigPrim S k.val pk A) := by
  unfold sigReductionAuthRun
  split_ifs
  rfl

theorem evalDist_sigEufCmaExp_AuthRun (S : Setup) (P : Primitives)
    (A : AuthAdversary S) (hN : 0 < S.N_id) :
    haveI : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    probExpect (do
      let sk ← sampleScalar32
      let pk := P.sigPkGen sk
      let ((m, sig), signedMsgs) ←
        (simulateQ (sigEufCmaFullImpl P sk) (sigReductionAuthRun S A pk)).run []
      return (P.sigVerify pk m sig && decide (m ∉ signedMsgs)))
      (fun b => if b = true then 1 else 0) =
      ∑ k ∈ Finset.range S.N_id,
        probExpect (do
          let sk ← sampleScalar32
          let pk := P.sigPkGen sk
          let ((m, sig), signedMsgs) ←
            (simulateQ (sigEufCmaFullImpl P sk) (simulateAuthForSigPrim S k pk A)).run []
          return (P.sigVerify pk m sig && decide (m ∉ signedMsgs)))
          (fun b => if b = true then 1 else 0) * (S.N_id : ℝ≥0∞)⁻¹ := by
  have : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
  simp_rw [sigReductionAuthRun_pos S A _ hN]
  have h_emb : ∀ (sk : Bytes) (f : Fin S.N_id × List Bytes → ℝ≥0∞),
      probExpect ((simulateQ (sigEufCmaFullImpl P sk)
        (embedPrim (spec := sigOracleSpec) (embedUnif ($ᵗ (Fin S.N_id))))).run []) f =
        probExpect ($ᵗ (Fin S.N_id)) (fun k => f (k, [])) := by
    intro sk f
    unfold sigEufCmaFullImpl
    rw [simulateQ_embedPrim_run, simulateQ_embedUnif, probExpect_map]
  simp only [simulateQ_bind, StateT.run_bind, probExpect_bind, h_emb]
  rw [probExpect_swap sampleScalar32 ($ᵗ (Fin S.N_id)),
      probExpect_uniformFin S.N_id (fun k =>
        probExpect sampleScalar32 (fun a =>
          probExpect ((simulateQ (sigEufCmaFullImpl P a) (simulateAuthForSigPrim S k (P.sigPkGen a)
            A)).run []) (fun x =>
            probExpect (pure (P.sigVerify (P.sigPkGen a) x.1.1 x.1.2 && decide (x.1.1 ∉ x.2))) (fun
              b =>
              if b = true then 1 else 0))))]

theorem evalDist_sigEufCmaExp_sigReductionAuth (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) (hN : 0 < S.N_id) :
    haveI : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    𝒟[sigEufCmaExp P (sigReductionAuth S b A)] {true} =
      ∑ k ∈ Finset.range S.N_id,
        𝒟[sigEufCmaExp P (sigReductionAuthAt S b k A)] {true} * (S.N_id : ℝ≥0∞)⁻¹ := by
  have : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
  rw [sigEufCmaExp_eq, evalDist_true_eq_probExpect]
  simp_rw [evalDist_pure_bool_true]
  change probExpect (do
      let sk ← sampleScalar32
      let pk := P.sigPkGen sk
      let ((m, sig), signedMsgs) ←
        (simulateQ (sigEufCmaFullImpl P sk) (sigReductionAuthRun S A.val pk)).run []
      return (P.sigVerify pk m sig && decide (m ∉ signedMsgs)))
      (fun b => if b = true then 1 else 0) = _
  rw [evalDist_sigEufCmaExp_AuthRun S P A.val hN]
  congr 1; ext k; congr 1
  rw [sigEufCmaExp_eq, evalDist_true_eq_probExpect]
  simp_rw [evalDist_pure_bool_true]
  rfl

theorem sum_sigReductionAuth_le (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (∑ k ∈ Finset.range S.N_id, SigEufCma P (sigReductionAuthAt S b k A)) ≤
      (S.N_id : ℝ) * SigEufCma P (sigReductionAuth S b A) := by
  by_cases hN : 0 < S.N_id
  · have : NeZero S.N_id := ⟨Nat.ne_of_gt hN⟩
    have h_core := evalDist_sigEufCmaExp_sigReductionAuth S P b A hN
    unfold SigEufCma
    rw [h_core]
    have hfin : ∀ k ∈ Finset.range S.N_id,
        𝒟[sigEufCmaExp P (sigReductionAuthAt S b k A)] {true} * (S.N_id : ℝ≥0∞)⁻¹ ≠ ⊤ := by
      intro k _
      exact ENNReal.mul_ne_top (MeasureTheory.measure_ne_top _ {true})
        (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne S.N_id)))
    rw [ENNReal.toReal_sum hfin]
    have hterm : ∀ k ∈ Finset.range S.N_id,
        (𝒟[sigEufCmaExp P (sigReductionAuthAt S b k A)] {true} * (S.N_id : ℝ≥0∞)⁻¹).toReal =
          (𝒟[sigEufCmaExp P (sigReductionAuthAt S b k A)] {true}).toReal * (S.N_id : ℝ)⁻¹ := by
      intro k _
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← mul_assoc,
      mul_comm (S.N_id : ℝ), mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne S.N_id)),
        mul_one]
  · have h0 : S.N_id = 0 := Nat.eq_zero_of_not_pos hN
    simp [h0]

/-! ## Provenance hybrid bridges -/

def hasBadSigAuthAt (S : Setup) (P : Primitives) (k : Nat) (st : AuthState S) : Bool :=
  (authSigLens S).badAt P k st

theorem hasBadSigAuth_eq_any_range (S : Setup) (P : Primitives) (st : AuthState S) :
    (hasBadSigAuth st && noPrinPkColl P st.principals) =
      (List.range S.N_id).any (fun k => hasBadSigAuthAt S P k st) := by
  apply Bool.eq_iff_iff.mpr
  simp only [hasBadSigAuth, hasBadSigAuthAt, SigGameLens.badAt, authSigLens, badPeersAuth,
    HasAuthState.toAuthState, List.any_eq_true, List.mem_range, List.mem_map, List.mem_filter,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨s, hs, hfresh, hbad⟩, hnp⟩
    have hN : 0 < S.N_id := sessionId_pos_N_id s.sid
    exact ⟨peerPartyIdx S P st.principals s.peerIkPk,
      peerPartyIdx_lt hN P st.principals s.peerIkPk,
      ⟨s.peerIkPk, ⟨s, ⟨hs, hfresh, hbad⟩, rfl⟩, rfl⟩, hnp⟩
  · rintro ⟨k, _, ⟨_, ⟨s, ⟨hs, hfresh, hbad⟩, rfl⟩, _⟩, hnp⟩
    exact ⟨⟨s, hs, hfresh, hbad⟩, hnp⟩

noncomputable def runAuthWithProv (prov : ProvFnType) (S : Setup) (P : Primitives)
    (A : AuthAdversary S) : ProbComp (Bool × Bool × AuthState S) := do
  let secb ← $ᵗ Bool
  let initSt := AuthState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthState S) ProbComp) +
    pqxdhAuthWithProvImpl S P prov
  let (b', finalSt) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalSt)

@[simp]
theorem runAuthWithProv_checkBundleProvenance (S : Setup) (P : Primitives) (A : AuthAdversary S) :
    runAuthWithProv (checkBundleProvenance P) S P A = runAuthSim true true S P A := by
  unfold runAuthWithProv runAuthSim
  rw [pqxdhAuthWithProvImpl_checkBundleProvenance]

noncomputable def contAuth (S : Setup) (P : Primitives)
    (a : Bool × Bool × AuthState S) : ProbComp Bool :=
  let (secb, b', finalSt) := a
  if finalSt.hasWonAuth then
    pure true
  else if !(finalSt.sessions.all (fun s =>
      !s.challenged || authInitCorruptionClause P true finalSt.principals s)) then
    $ᵗ Bool
  else
    pure (b' == secb)

@[simp]
theorem hasEcPkCollisionAuth_mapAuthSessions {S : Setup} (P : Primitives)
    (f : Bool × Bool × Bool → Bool × Bool × Bool) (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := f (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    hasEcPkCollisionAuth P (mapAuthSessions mapEntry st) = hasEcPkCollisionAuth P st := by
  intro mapEntry
  unfold hasEcPkCollisionAuth allHonestEcPksAuth mapAuthSessions
  dsimp only [HasAuthState.toAuthState]
  rw [List.map_map]
  rfl

@[simp]
theorem hasKemPkCollisionAuth_mapAuthSessions {S : Setup}
    (f : AuthInitiatorEntry S → AuthInitiatorEntry S) (st : AuthState S) :
    hasKemPkCollisionAuth (mapAuthSessions f st) = hasKemPkCollisionAuth st :=
  rfl

theorem contAuth_mapAuthSessions_squash (S : Setup) (P : Primitives)
    (secb b' : Bool) (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := squashTriples (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    contAuth S P (secb, b', mapAuthSessions mapEntry st) = contAuth S P (secb, b', st) := by
  intro mapEntry
  unfold contAuth mapAuthSessions
  dsimp only
  have hall : (List.map mapEntry st.sessions).all (fun s =>
      !s.challenged || authInitCorruptionClause P true st.principals s) =
      st.sessions.all (fun s =>
        !s.challenged || authInitCorruptionClause P true st.principals s) := by
    rw [List.all_map]
    refine list_all_congr (fun s _ => ?_)
    dsimp only [Function.comp_def, mapEntry, squashTriples, authInitCorruptionClause]
    cases s.spkHonest <;> cases s.opkHonest <;> simp
  rw [hall]

@[simp]
theorem hasBadSigAuth_mapAuthSessions_eraseOpk {S : Setup} (st : AuthState S) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := eraseOpkTriples (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    hasBadSigAuth (mapAuthSessions mapEntry st) = hasBadSigAuth st := by
  intro mapEntry
  unfold hasBadSigAuth mapAuthSessions
  dsimp only [HasAuthState.toAuthState]
  rw [List.any_map]
  rfl

theorem contAuth_mapAuthSessions_eraseOpk_of_not_badSig (S : Setup) (P : Primitives)
    (secb b' : Bool) (st : AuthState S)
    (h_ok : hasBadSigAuth st = false) :
    let mapEntry : AuthInitiatorEntry S → AuthInitiatorEntry S := fun s =>
      let (s', o', p') := eraseOpkTriples (s.spkHonest, s.opkHonest, s.pqspkHonest)
      { s with spkHonest := s', opkHonest := o', pqspkHonest := p' }
    contAuth S P (secb, b', mapAuthSessions mapEntry st) = contAuth S P (secb, b', st) := by
  intro mapEntry
  unfold contAuth mapAuthSessions
  dsimp only
  have hall : (List.map mapEntry st.sessions).all (fun s =>
      !s.challenged || authInitCorruptionClause P true st.principals s) =
      st.sessions.all (fun s =>
        !s.challenged || authInitCorruptionClause P true st.principals s) := by
    rw [List.all_map]
    refine list_all_congr (fun s hs => ?_)
    have h_not_bad : (s.fresh && (!s.spkHonest || !s.pqspkHonest)) = false := by
      unfold hasBadSigAuth at h_ok
      exact Bool.eq_false_iff.mpr (List.any_eq_false.mp h_ok s hs)
    dsimp only [Function.comp_def, mapEntry, eraseOpkTriples, authInitCorruptionClause]
    cases hfr : s.fresh with
    | false => simp
    | true =>
      simp only [hfr, Bool.true_and, Bool.or_eq_false_iff, Bool.not_eq_false'] at h_not_bad
      simp [h_not_bad.1]
  rw [hall]

end Proofs.SignalPqxdh.Security
