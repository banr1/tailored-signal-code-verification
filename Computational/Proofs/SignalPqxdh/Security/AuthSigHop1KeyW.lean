/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSigHop1KeyC0

/-!
# One-key `Auth` bad-signature hop: step lemmas for the pre-sampled real oracle

**Checked by Lean.** Proves `Safe` absorption, `authSigGood1Key` preservation, and
`bundleSignedMessages` monotonicity across one step of `pqxdhAuthSigPreImpl1Key`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open OracleSpec OracleComp

namespace Proofs.SignalPqxdh.Security

theorem initPostAuth_cons_session_exact {S : Setup} (P : Primitives) (bundle : PreKeyBundleInput)
    (st st' : AuthState S) (sess : AuthInitiatorEntry S)
    (h_prin : st'.principals = st.principals) (h_spks : st'.spkBundles = st.spkBundles)
    (h_sess : st'.sessions = sess :: st.sessions)
    (h_peer : sess.peerIkPk = bundle.ikB)
    (h_fresh : sess.fresh = (match findHonestPrincipal P st.principals bundle.ikB with
     | some (_, pEntry) => !pEntry.corrupted
     | none             => false))
    (h_spk : sess.spkHonest =
      (checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle).1)
    (h_pqspk : sess.pqspkHonest =
      (checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle).2.2)
    (h_sig : (!(P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC bundle.spkB)
      bundle.spkSig &&
       P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB)
         bundle.pqspkSig)) = false) :
    InitPostAuth P bundle st st' := by
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
  refine ⟨h_prin, h_spks, ?_⟩
  unfold badPeersAuth
  rw [h_sess, List.filter_cons]
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

theorem runAuthSendWithProv_exact_pres (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) :
    SatisfiesAt (InitPostAuth P bundle st) st
      (runAuthSendWithProv S P (checkBundleProvenanceExact P) sid u bundle m0 m1) := by
  have h0 := initPostAuth_refl P bundle st
  unfold runAuthSendWithProv
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
      · rcases hprov : checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries
            bundle with ⟨s1, o1, p1⟩
        dsimp only
        intro x hx
        simp only [StateT.run_bind, StateT.run_set, pure_bind] at hx
        split at hx <;>
        · split at hx <;>
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
            subst hx
            refine initPostAuth_cons_session_exact P bundle st _ _ rfl rfl rfl rfl
              (by first | rfl | simp only [*])
              (by rw [hprov]) (by rw [hprov]) h_sig
      · exact SatisfiesAt.pure _ _ _ h0
    · exact SatisfiesAt.pure _ _ _ h0
  · exact SatisfiesAt.pure _ _ _ h0

theorem pqxdhAuthWithProvImpl_exact_sendOPK_pres (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) :
    SatisfiesAt (InitPostAuth P b st) st
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) (.sendOPK u i b m0 m1)) := by
  unfold pqxdhAuthWithProvImpl; dsimp only
  by_cases h : b.opkB?.isNone = true
  · simp only [h, ↓reduceIte]; exact SatisfiesAt.pure _ _ _ (initPostAuth_refl P b st)
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact runAuthSendWithProv_exact_pres S P (.sendOPK u i) u b m0 m1 st

theorem pqxdhAuthWithProvImpl_exact_sendNoOPK_pres (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) :
    SatisfiesAt (InitPostAuth P b st) st
      (pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) (.sendNoOPK u i b m0 m1)) := by
  unfold pqxdhAuthWithProvImpl; dsimp only
  by_cases h : b.opkB?.isSome = true
  · simp only [h, ↓reduceIte]; exact SatisfiesAt.pure _ _ _ (initPostAuth_refl P b st)
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact runAuthSendWithProv_exact_pres S P (.sendNoOPK u i) u b m0 m1 st

theorem pqxdhAuthWithProvImpl_other_pres3 (S : Setup) (P : Primitives) (provFn : ProvFnType)
    (q : AuthQuery S) (st : AuthState S)
    (h_not_init : ∀ u, q ≠ .initPrin u)
    (h_not_corr : ∀ u, q ≠ .corruptIK u)
    (h_not_spk : ∀ u j, q ≠ .genSPK u j)
    (h_not_sopk : ∀ u i b m0 m1, q ≠ .sendOPK u i b m0 m1)
    (h_not_snoopk : ∀ u i b m0 m1, q ≠ .sendNoOPK u i b m0 m1) :
    ∀ x ∈ support ((pqxdhAuthWithProvImpl S P provFn q).run st),
      x.2.principals = st.principals ∧ x.2.spkBundles = st.spkBundles ∧
      x.2.sessions = st.sessions := by
  let proj := fun s : AuthState S => (s.principals, s.spkBundles, s.sessions)
  have h_from_proj : ∀ m : StateT (AuthState S) ProbComp AuthResponse,
      PreservesAt proj st m →
      ∀ x ∈ support (m.run st),
        x.2.principals = st.principals ∧ x.2.spkBundles = st.spkBundles ∧
        x.2.sessions = st.sessions := by
    intro m hP x hx
    have h := hP x hx
    exact ⟨congrArg Prod.fst h, congrArg (Prod.fst ∘ Prod.snd) h,
      congrArg (Prod.snd ∘ Prod.snd) h⟩
  cases q with
  | initPrin u => exact False.elim (h_not_init u rfl)
  | corruptIK u => exact False.elim (h_not_corr u rfl)
  | genSPK u j => exact False.elim (h_not_spk u j rfl)
  | sendOPK u i b m0 m1 => exact False.elim (h_not_sopk u i b m0 m1 rfl)
  | sendNoOPK u i b m0 m1 => exact False.elim (h_not_snoopk u i b m0 m1 rfl)
  | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _
      | revealDhSecrets | registerKey _ =>
    apply h_from_proj; unfold pqxdhAuthWithProvImpl pqxdhAuthImpl; dsimp only; prove_preserves_at

def prinEntry1Key (P : Primitives) (s : Bytes) : PrincipalEntry :=
  { secIKA0 := s, ikAPk := P.x25519Base s, secIKAsign := s, ikSignPk := P.x25519Base s,
    corrupted := false }

theorem mem_support_fgPreAuthInitPrin1Key (k : ℕ) (optSk : Option Bytes) (S : Setup)
    (P : Primitives) (u : Fin S.N_id) (st : AuthState S) (x : AuthResponse × AuthState S)
    (hx : x ∈ support ((fgPreAuthInitPrin1Key true k optSk S P u).run st)) :
    x.2 = st ∨
    (st.principals.any (fun (idx, _) => idx == u.val) = false ∧
      ∃ s : Bytes, (∀ sk, optSk = some sk → u.val = k → s = sk) ∧
        x.2 = { st with principals := (u.val, prinEntry1Key P s) :: st.principals }) := by
  unfold fgPreAuthInitPrin1Key at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  by_cases hFresh : st.principals.any (fun (idx, _) => idx == u.val) = true
  · simp only [hFresh, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hx
    exact Or.inl (by rw [hx])
  · have hFreshF : st.principals.any (fun (idx, _) => idx == u.val) = false :=
      Bool.eq_false_iff.mpr hFresh
    rw [hFreshF] at hx
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨s, hs, h_eq⟩
    refine Or.inr ⟨hFreshF, s, ?_, by rw [h_eq]; rfl⟩
    intro sk hsk hk
    subst hsk
    simp only [hk, beq_self_eq_true, Bool.and_self, ↓reduceIte, support_pure,
      Set.mem_singleton_iff] at hs
    exact hs

theorem mem_support_authSigPre1Key (k : ℕ) (optSk : Option Bytes) (S : Setup) (P : Primitives)
    (q : AuthQuery S) (st : AuthState S) (x : AuthResponse × AuthState S)
    (hx : x ∈ support ((pqxdhAuthSigPreImpl1Key k optSk S P q).run st)) :
    x.2 = st ∨
    (∃ u, q = .initPrin u ∧ x ∈ support ((fgPreAuthInitPrin1Key true k optSk S P u).run st)) ∨
    ((∀ u, q ≠ .initPrin u) ∧
      x ∈ support ((pqxdhAuthWithProvImpl S P (checkBundleProvenanceExact P) q).run st)) := by
  unfold pqxdhAuthSigPreImpl1Key freezeImpl at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  split_ifs at hx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    exact Or.inl (by rw [hx])
  · right
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl, hx⟩
    | corruptIK _ | genSPK _ _ | genOPK _ _ _ | sendOPK _ _ _ _ _ | sendNoOPK _ _ _ _ _
    | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _ | revealDhSecrets
    | registerKey _ => exact Or.inr ⟨fun _ h => (by cases h), hx⟩

theorem safe_of_eq_fields (S : Setup) (P : Primitives) (k : ℕ) (st st' : AuthState S)
    (hp : st'.principals = st.principals) (hs : st'.sessions = st.sessions)
    (h : (authSigLens S).Safe P k st) : (authSigLens S).Safe P k st' := by
  unfold SigGameLens.Safe at *
  dsimp only [authSigLens] at *
  unfold badPeersAuth at *
  rw [hp, hs]; exact h

theorem good_of_eq_fields (S : Setup) (P : Primitives) (k : ℕ) (sk : Bytes) (st st' : AuthState S)
    (hp : st'.principals = st.principals) (hs : st'.sessions = st.sessions)
    (h : authSigGood1Key S P k sk st) : authSigGood1Key S P k sk st' := by
  unfold authSigGood1Key at *
  unfold badPeersAuth at *
  rw [hp, hs]; exact h

theorem authSigPre1Key_safe_step (S : Setup) (P : Primitives) (k : ℕ) (optSk : Option Bytes)
    (q : AuthQuery S) (st : AuthState S) (hSafe : (authSigLens S).Safe P k st) :
    ∀ x ∈ support ((pqxdhAuthSigPreImpl1Key k optSk S P q).run st),
      (authSigLens S).Safe P k x.2 := by
  intro x hx
  rcases mem_support_authSigPre1Key k optSk S P q st x hx with h | ⟨u, rfl, hx'⟩ | ⟨hq, hx'⟩
  · rw [h]; exact hSafe
  · rcases mem_support_fgPreAuthInitPrin1Key k optSk S P u st x hx' with h | ⟨hFresh, s, _, h⟩
    · rw [h]; exact hSafe
    · rcases hSafe with ⟨hVP, ⟨ek, hek⟩, hCorr, hClean⟩
      have hCons := validPrincipals_cons S u (prinEntry1Key P s) st.principals hVP hFresh
      have hne : u.val ≠ k := by
        intro hk
        subst hk
        exact hCons.2 (List.mem_map_of_mem hek)
      unfold SigGameLens.Safe
      dsimp only [authSigLens]
      rw [h]
      refine ⟨hCons.1, ⟨ek, List.mem_cons_of_mem _ hek⟩, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with h_eq | hmem
        · injection h_eq with h1 _
          exact False.elim (hne h1.symm)
        · exact hCorr e hmem
      · exact cleanPeers_cons_principal S P k u.val _ st.principals (badPeersAuth st) hClean
  · cases q with
    | initPrin u => exact False.elim (hq u rfl)
    | corruptIK u => exact (authSigLens S).safe_step_corruptIK P k u st hSafe x hx'
    | genSPK u j => exact (authSigLens S).safe_step_genSPK P k u j st hSafe x hx'
    | sendOPK u i bnd m0 m1 =>
      exact safe_step_initiate_auth S P k bnd _ st
        (pqxdhAuthWithProvImpl_exact_sendOPK_pres S P u i bnd m0 m1 st) hSafe x hx'
    | sendNoOPK u i bnd m0 m1 =>
      exact safe_step_initiate_auth S P k bnd _ st
        (pqxdhAuthWithProvImpl_exact_sendNoOPK_pres S P u i bnd m0 m1 st) hSafe x hx'
    | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _
    | revealDhSecrets | registerKey _ =>
      obtain ⟨hp, _, hs⟩ := pqxdhAuthWithProvImpl_other_pres3 S P _ _ st
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) x hx'
      exact safe_of_eq_fields S P k st x.2 hp hs hSafe

theorem evalDist_authSigPre1Key_safe_eq_zero (S : Setup) (P : Primitives) (k : ℕ)
    (optSk : Option Bytes) {α : Type} (oa : OracleComp (unifSpec + authSpec S) α)
    (st : AuthState S) (hSafe : (authSigLens S).Safe P k st) :
    𝒟[(simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (AuthState S) ProbComp) + pqxdhAuthSigPreImpl1Key k optSk S P) oa).run st >>=
      fun (_, s) => pure (hasBadSigAuthAt S P k s)] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure x =>
    have hBadF : hasBadSigAuthAt S P k st = false :=
      (authSigLens S).safe_badAt_eq_false P k st hSafe
    simp [StateT.run_pure, hBadF]
  | query_bind q kont ih =>
    cases q with
    | inl n =>
      simp only [FgGapDh.simulateQ_run_query_inl, bind_assoc]
      exact FgGapDh.evalDist_bind_true_eq_zero_of_support _ _ (fun u _ => ih u st hSafe)
    | inr gq =>
      simp only [FgGapDh.simulateQ_run_query_inr, bind_assoc]
      exact FgGapDh.evalDist_bind_true_eq_zero_of_support _ _ (fun y hy =>
        ih y.1 y.2 (authSigPre1Key_safe_step S P k optSk gq st hSafe y hy))

theorem authSigGood1Key_step_of_not_send (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (k : ℕ) (sk : Bytes) (q : AuthQuery S)
    (hS1 : ∀ u i b m0 m1, q ≠ .sendOPK u i b m0 m1)
    (hS2 : ∀ u i b m0 m1, q ≠ .sendNoOPK u i b m0 m1)
    (st : AuthState S) (hG : authSigGood1Key S P k sk st) :
    ∀ x ∈ support ((pqxdhAuthSigPreImpl1Key k (some sk) S P q).run st),
      authSigGood1Key S P k sk x.2 ∨ (authSigLens S).Safe P k x.2 := by
  intro x hx
  rcases mem_support_authSigPre1Key k (some sk) S P q st x hx with h | ⟨u, rfl, hx'⟩ | ⟨hq, hx'⟩
  · rw [h]; exact Or.inl hG
  · rcases mem_support_fgPreAuthInitPrin1Key k (some sk) S P u st x hx' with
      h | ⟨hFresh, s, hs, h⟩
    · rw [h]; exact Or.inl hG
    · left
      rcases hG with ⟨hVP, hK, hClean⟩
      have hCons := validPrincipals_cons S u (prinEntry1Key P s) st.principals hVP hFresh
      unfold authSigGood1Key
      rw [h]
      refine ⟨hCons.1, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with h_eq | hmem
        · injection h_eq with h1 h2
          have hsk : s = sk := hs sk rfl h1.symm
          subst hsk
          subst h2
          exact ⟨rfl, (congrFun hP.sigPkGen_eq_x25519Base s).symm, rfl⟩
        · exact hK e hmem
      · exact cleanPeers_cons_principal S P k u.val _ st.principals (badPeersAuth st) hClean
  · cases q with
    | initPrin u => exact False.elim (hq u rfl)
    | sendOPK u i b m0 m1 => exact False.elim (hS1 u i b m0 m1 rfl)
    | sendNoOPK u i b m0 m1 => exact False.elim (hS2 u i b m0 m1 rfl)
    | genSPK u j =>
      rcases (authSigLens S).mem_support_realGenSPK P u j st x hx' with h | ⟨_, _, _, _, _, _, h⟩
      · rw [h]; exact Or.inl hG
      · rw [h]; exact Or.inl (good_of_eq_fields S P k sk st _ rfl rfl hG)
    | corruptIK u =>
      rcases hG with ⟨hVP, hK, hClean⟩
      rcases (authSigLens S).mem_support_realCorruptIK u st x hx' with ⟨_, h⟩ | ⟨idx, entry, hf, h⟩
      · rw [h]; exact Or.inl ⟨hVP, hK, hClean⟩
      · rw [h]
        dsimp only [authSigLens]
        by_cases hu : u.val = k
        ·
          right
          subst hu
          have hmem := List.mem_of_find?_eq_some hf
          have hidx : idx = u.val := by
            have := List.find?_some hf
            simpa using this
          subst hidx
          unfold SigGameLens.Safe
          dsimp only [authSigLens]
          refine ⟨validPrincipals_corrupt S u.val st.principals hVP,
            ⟨{ entry with corrupted := true },
              (mem_corrupt_map u.val u.val _ st.principals).mpr ⟨entry, hmem, by simp⟩⟩, ?_,
            cleanPeers_corrupt S P u.val u.val st.principals (badPeersAuth st) hClean⟩
          intro e he
          rcases (mem_corrupt_map u.val u.val e st.principals).mp he with ⟨e0, _, rfl⟩
          simp
        · left
          refine ⟨validPrincipals_corrupt S u.val st.principals hVP, ?_,
            cleanPeers_corrupt S P k u.val st.principals (badPeersAuth st) hClean⟩
          intro e he
          rcases (mem_corrupt_map u.val k e st.principals).mp he with ⟨e0, hmem, rfl⟩
          have hku : (k == u.val) = false := beq_eq_false_iff_ne.mpr (Ne.symm hu)
          simp only [hku, Bool.false_eq_true, ↓reduceIte]
          exact hK e0 hmem
    | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _
    | revealDhSecrets | registerKey _ =>
      obtain ⟨hp, _, hs⟩ := pqxdhAuthWithProvImpl_other_pres3 S P _ _ st
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) x hx'
      exact Or.inl (good_of_eq_fields S P k sk st x.2 hp hs hG)

theorem authSigGood1Key_of_initPostAuth (S : Setup) (P : Primitives) (k : ℕ) (sk : Bytes)
    (bundle : PreKeyBundleInput) (st st' : AuthState S) (hG : authSigGood1Key S P k sk st)
    (hfg : extractBundleForgery P k (P.sigPkGen sk) st.principals st.spkBundles bundle none = none)
    (hPost : InitPostAuth P bundle st st') : authSigGood1Key S P k sk st' := by
  rcases hG with ⟨hVP, hK, hClean⟩
  rcases hPost with ⟨hp, _, hbp | ⟨hbp, h_ec, h_kem, hFresh, hBad⟩⟩
  · unfold authSigGood1Key; rw [hp, hbp]; exact ⟨hVP, hK, hClean⟩
  · unfold authSigGood1Key; rw [hp, hbp]
    refine ⟨hVP, hK, ?_⟩
    by_cases hk : ∃ e, (k, e) ∈ st.principals
    · obtain ⟨e, he⟩ := hk
      obtain ⟨h1, h2, h3⟩ := hK e he
      exact cleanPeers_cons_of_extractBundleForgery_eq_none_auth S P k sk st.principals
        st.spkBundles (badPeersAuth st) bundle hVP ⟨e, he, h1, h2, h3⟩ hClean hfg h_ec h_kem
        hFresh hBad
    · refine cleanPeers_cons_of_before S P k st.principals (badPeersAuth st) bundle.ikB
        (fun p hp => ⟨hVP.1 p hp, fun hpk => hk ⟨p.2, by rw [← hpk]; exact hp⟩⟩) hClean hFresh

theorem authSigGood1Key_step_sendOPK (S : Setup) (P : Primitives) (k : ℕ) (sk : Bytes)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) (hG : authSigGood1Key S P k sk st)
    (hfg : extractBundleForgery P k (P.sigPkGen sk) st.principals st.spkBundles bundle none =
      none) :
    ∀ x ∈ support ((pqxdhAuthSigPreImpl1Key k (some sk) S P (.sendOPK u i bundle m0 m1)).run st),
      authSigGood1Key S P k sk x.2 := by
  intro x hx
  rcases mem_support_authSigPre1Key k (some sk) S P _ st x hx with h | ⟨_, h, _⟩ | ⟨_, hx'⟩
  · rw [h]; exact hG
  · cases h
  · exact authSigGood1Key_of_initPostAuth S P k sk bundle st x.2 hG hfg
      (pqxdhAuthWithProvImpl_exact_sendOPK_pres S P u i bundle m0 m1 st x hx')

theorem authSigGood1Key_step_sendNoOPK (S : Setup) (P : Primitives) (k : ℕ) (sk : Bytes)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (st : AuthState S) (hG : authSigGood1Key S P k sk st)
    (hfg : extractBundleForgery P k (P.sigPkGen sk) st.principals st.spkBundles bundle none =
      none) :
    ∀ x ∈ support
        ((pqxdhAuthSigPreImpl1Key k (some sk) S P (.sendNoOPK u i bundle m0 m1)).run st),
      authSigGood1Key S P k sk x.2 := by
  intro x hx
  rcases mem_support_authSigPre1Key k (some sk) S P _ st x hx with h | ⟨_, h, _⟩ | ⟨_, hx'⟩
  · rw [h]; exact hG
  · cases h
  · exact authSigGood1Key_of_initPostAuth S P k sk bundle st x.2 hG hfg
      (pqxdhAuthWithProvImpl_exact_sendNoOPK_pres S P u i bundle m0 m1 st x hx')

theorem bundleSignedMessages_mono_authSigPre1Key (S : Setup) (P : Primitives) (k : ℕ)
    (optSk : Option Bytes) (q : AuthQuery S) (st : AuthState S) :
    ∀ x ∈ support ((pqxdhAuthSigPreImpl1Key k optSk S P q).run st),
      ∀ m ∈ bundleSignedMessages k st.spkBundles, m ∈ bundleSignedMessages k x.2.spkBundles := by
  intro x hx m hm
  rcases mem_support_authSigPre1Key k optSk S P q st x hx with h | ⟨u, rfl, hx'⟩ | ⟨hq, hx'⟩
  · rw [h]; exact hm
  · rcases mem_support_fgPreAuthInitPrin1Key k optSk S P u st x hx' with h | ⟨_, _, _, h⟩
    · rw [h]; exact hm
    · rw [h]; exact hm
  · cases q with
    | initPrin u => exact False.elim (hq u rfl)
    | corruptIK u =>
      rcases (authSigLens S).mem_support_realCorruptIK u st x hx' with ⟨_, h⟩ | ⟨_, _, _, h⟩
      · rw [h]; exact hm
      · rw [h]; exact hm
    | genSPK u j =>
      rcases (authSigLens S).mem_support_realGenSPK P u j st x hx' with h | ⟨_, _, _, bE, _, _, h⟩
      · rw [h]; exact hm
      · rw [h]
        dsimp only [authSigLens]
        by_cases hu : (u.val == k) = true
        · have hu' : u.val = k := beq_iff_eq.mp hu
          rw [hu', bundleSignedMessages_cons_eq]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
        · rw [bundleSignedMessages_cons_of_ne k u.val j.val bE _ (Bool.eq_false_iff.mpr hu)]
          exact hm
    | sendOPK u i bnd m0 m1 =>
      obtain ⟨_, hs, _⟩ := pqxdhAuthWithProvImpl_exact_sendOPK_pres S P u i bnd m0 m1 st x hx'
      rw [hs]; exact hm
    | sendNoOPK u i bnd m0 m1 =>
      obtain ⟨_, hs, _⟩ := pqxdhAuthWithProvImpl_exact_sendNoOPK_pres S P u i bnd m0 m1 st x hx'
      rw [hs]; exact hm
    | genOPK _ _ _ | recvOPK _ _ _ _ | recvNoOPK _ _ _ _ | roQuery _ | roRootQuery _ _
    | revealDhSecrets | registerKey _ =>
      obtain ⟨_, hs, _⟩ := pqxdhAuthWithProvImpl_other_pres3 S P _ _ st
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h) x hx'
      rw [hs]; exact hm

end Proofs.SignalPqxdh.Security
