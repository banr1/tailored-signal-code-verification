/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliPqKeyIndStepCore
import Computational.Proofs.E2E.ComposedKeyIndHop
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# Per-arm preservation of `CliAdapterKeyIndInv` and `CliAdapterDrvRel` for 1-key `KeyInd`

**Checked by Lean.** Proves preservation of `CliAdapterKeyIndInv` and `CliAdapterDrvRel` across
each 1-key real-HKDF `KeyInd` query arm.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open ReductionDsl OracleComp OracleSpec MeasureTheory

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoGames.LibsignalSessionApi HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme
  MACScheme WireAEAD FSAEAD CryptoGames.Ratchet.LibsignalSim CryptoGames.FSAEAD.Thm5
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalSpqrV1 CryptoVerification.SignalSession

/-! ## Primitive, support, and list-update helpers -/

theorem modelPrims_x25519Base_eq_cli (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (sk : SignalPqxdh.Bytes) :
    (modelPrims X W).x25519Base sk = vecU8 (keyPairOf W.C (u8Vec 32 sk)).publicKey.bytes := rfl

theorem sigVerify_length_eq_64_cli {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P) {pk msg sig : SignalPqxdh.Bytes}
    (hv : P.sigVerify pk msg sig = true) : sig.length = 64 := by
  rw [hP.sigVerify_eq_xeddsaVerifyRef] at hv
  unfold SignalPqxdh.xeddsaVerifyRef at hv
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  split_ifs at hv with hif
  exact hif.1.2

theorem sigSign_length_eq_64_cli {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P) (sk msg r : SignalPqxdh.Bytes) :
    (P.sigSign sk msg r).length = 64 :=
  sigVerify_length_eq_64_cli hP (hP.sig_corr sk msg r)

theorem hkdfDerive96_lengths_of_wf_cli {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P) (secrets : SignalPqxdh.Bytes) :
    (P.hkdfDerive96 secrets).rootKey.length = 32 ∧
    (P.hkdfDerive96 secrets).chainKey.length = 32 ∧
    (P.hkdfDerive96 secrets).pqrKey.length = 32 := by
  rw [hP.hkdfDerive96_eq_ref]
  simp [SignalPqxdh.hkdfDerive96Ref, SignalPqxdh.hkdfExpand96Ref,
    SignalPqxdh.hmacSha256Ref, SignalPqxdh.sha256Ref, SignalPqxdh.fitBytesRef_length]

theorem sampleScalar32_length_of_mem_cli {sk : SignalPqxdh.Bytes}
    (hmem : sk ∈ support SignalPqxdh.sampleScalar32) : sk.length = 32 :=
  length_of_mem_support_sampleBytes32 hmem

theorem sampleKemKeyGen_lengths_of_mem_cli {P : SignalPqxdh.Primitives}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P)
    {p : SignalPqxdh.Bytes × SignalPqxdh.Bytes}
    (hmem : p ∈ support (SignalPqxdh.sampleKemKeyGen P)) :
    p.1.length = 1568 ∧ p.2.length = 3168 := by
  unfold SignalPqxdh.sampleKemKeyGen at hmem
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hmem
  rcases hmem with ⟨seed, _, rfl⟩
  exact hP.kemKeyGen_valid seed

theorem resolveSigPk_eq_ikB_of_1key_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S (ℓ := ℓ) P W st ds)
    {ikB : SignalPqxdh.Bytes}
    (hHon : (match SignalPqxdh.findHonestPrincipal P st.principals ikB with
             | some (_, e) => e.ikAPk == ikB
             | none => true) = true) :
    SignalPqxdh.resolveSigPk P st.principals ikB = ikB := by
  unfold SignalPqxdh.resolveSigPk
  rcases hfind : SignalPqxdh.findHonestPrincipal P st.principals ikB with _ | ⟨idx, e⟩
  · rfl
  · simp only [hfind, beq_iff_eq] at hHon
    have hmem := List.mem_of_find?_eq_some hfind
    exact (hInv.prins_wf idx e hmem).2.2.2.2.2.trans hHon

@[simp]
theorem bhBaseMirror_noneResp_cli {S : SignalPqxdh.Setup}
    (drv : ModelDriverBase S) (kq : SignalPqxdh.KeyIndQuery S) :
    bhBaseMirror drv kq .noneResp = drv := by
  cases kq <;> rfl

@[simp]
theorem bhDrvMirror_noneResp_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds : ModelDriverState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) :
    bhDrvMirror ds kq .noneResp = ds := by
  unfold bhDrvMirror
  rw [bhBaseMirror_noneResp_cli]
  cases kq <;> rfl

@[simp]
theorem bhE2EMirror_noneResp_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (σ : BHE2EDrvState S ℓ) (kq : SignalPqxdh.KeyIndQuery S) :
    bhE2EMirror σ kq .noneResp = σ := by
  unfold bhE2EMirror
  rw [bhBaseMirror_noneResp_cli]
  cases kq <;> rfl

theorem mem_principals_of_find?_eq_some_cli
    {principals : List (ℕ × SignalPqxdh.PrincipalEntry)} {u idx : ℕ}
    {e : SignalPqxdh.PrincipalEntry}
    (h : principals.find? (fun (i, _) => i == u) = some (idx, e)) :
    (u, e) ∈ principals ∧ idx = u := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  dsimp only at hp
  have hidx : idx = u := beq_iff_eq.mp hp
  subst hidx
  exact ⟨hm, rfl⟩

theorem mem_support_evalHkdfOrRo_false_cli
    (P : SignalPqxdh.Primitives)
    (roCache : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (secrets : SignalPqxdh.Bytes)
    {dk : SignalPqxdh.DRKey}
    {roCache' : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey)}
    (h : (dk, roCache') ∈ support (SignalPqxdh.evalHkdfOrRo false P roCache secrets)) :
    dk = P.hkdfDerive96 secrets ∧ roCache' = roCache := by
  unfold SignalPqxdh.evalHkdfOrRo at h
  simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
  exact h

theorem partnerRandKey_lengths_cli {S : SignalPqxdh.Setup}
    {P : SignalPqxdh.Primitives}
    {respSessions : List (SignalPqxdh.KeyIndRespEntry S)}
    (hRespWf : ∀ r ∈ respSessions,
      r.drKeyReal.rootKey.length = 32 ∧ r.drKeyReal.chainKey.length = 32 ∧
      r.drKeyReal.pqrKey.length = 32 ∧ r.drKeyRand.rootKey.length = 32 ∧
      r.drKeyRand.chainKey.length = 32 ∧ r.drKeyRand.pqrKey.length = 32)
    {sessEntry : SignalPqxdh.KeyIndInitiatorEntry S} {dk : SignalPqxdh.DRKey}
    (h : SignalPqxdh.keyIndPartnerRandKey? P respSessions sessEntry = some dk) :
    dk.rootKey.length = 32 ∧ dk.chainKey.length = 32 ∧ dk.pqrKey.length = 32 := by
  unfold SignalPqxdh.keyIndPartnerRandKey? at h
  rcases hfind : respSessions.find? (fun r => SignalPqxdh.keyIndPartner P sessEntry r) with _ | r
  · simp [hfind] at h
  · simp only [hfind, Option.map_some, Option.some.injEq] at h
    subst h
    have hw := hRespWf r (List.mem_of_find?_eq_some hfind)
    exact ⟨hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2⟩

theorem mem_support_recordKeyIndResp_cli {S : SignalPqxdh.Setup}
    {P : SignalPqxdh.Primitives} {st st₂ : SignalPqxdh.KeyIndState S}
    {rEntry : SignalPqxdh.KeyIndRespEntry S} {u : Unit}
    (hrec : (u, st₂) ∈ support ((SignalPqxdh.recordKeyIndResp S P rEntry).run st))
    (hSessWf : ∀ s ∈ st.sessions,
      s.drKeyReal.rootKey.length = 32 ∧ s.drKeyReal.chainKey.length = 32 ∧
      s.drKeyReal.pqrKey.length = 32 ∧ s.drKeyRand.rootKey.length = 32 ∧
      s.drKeyRand.chainKey.length = 32 ∧ s.drKeyRand.pqrKey.length = 32) :
    ∃ drKeyRand : SignalPqxdh.DRKey,
      (drKeyRand.rootKey.length = 32 ∧ drKeyRand.chainKey.length = 32 ∧
       drKeyRand.pqrKey.length = 32) ∧
      st₂ = { st with respSessions := { rEntry with drKeyRand := drKeyRand } :: st.respSessions } := by
  unfold SignalPqxdh.recordKeyIndResp at hrec
  rw [stateT_run_get_bind_cli] at hrec
  rcases hfind : st.sessions.find? (fun s => SignalPqxdh.keyIndPartner P s rEntry) with _ | s
  · rw [hfind] at hrec
    simp only [stateT_monadLift_run_cli, StateT.run_bind, StateT.run_set,
      bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff, Prod.mk.injEq] at hrec
    rcases hrec with ⟨dk, hdk, _, rfl⟩
    exact ⟨dk, lengths_of_mem_support_sampleDRKey96 hdk, rfl⟩
  · rw [hfind] at hrec; dsimp only at hrec
    simp only [pure_bind, StateT.run_set, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hrec
    rcases hrec with ⟨_, rfl⟩
    have hw := hSessWf s (List.mem_of_find?_eq_some hfind)
    exact ⟨s.drKeyRand, ⟨hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2⟩, rfl⟩

theorem mem_support_lift_modify_bhDrvMirror_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (m : StateT (SignalPqxdh.KeyIndState S) ProbComp SignalPqxdh.KeyIndResponse)
    (kq : SignalPqxdh.KeyIndQuery S)
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    {kr : SignalPqxdh.KeyIndResponse} {ds' : ModelDriverState S ℓ} {st' : SignalPqxdh.KeyIndState S}
    (hmem : ((kr, ds'), st') ∈ support
      (((StateT.lift m >>= fun r =>
          modify (fun d => bhDrvMirror d kq r) >>= fun _ => pure r :
            BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st)) :
    (kr, st') ∈ support (m.run st) ∧ ds' = bhDrvMirror ds kq kr := by
  simp only [stateT_lift_run_cli, StateT.run_bind, StateT.run_modify, StateT.run_pure,
    bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with ⟨⟨r, st1⟩, hm, ⟨rfl, rfl⟩, rfl⟩
  exact ⟨hm, rfl⟩

theorem mem_sessions_map_reveal_cli {S : SignalPqxdh.Setup}
    {sessions : List (SignalPqxdh.KeyIndInitiatorEntry S)}
    {sid : SignalPqxdh.SessionId S} {s' : SignalPqxdh.KeyIndInitiatorEntry S}
    (h : s' ∈ sessions.map (fun s => if s.sid == sid then { s with revealed := true } else s)) :
    ∃ s ∈ sessions,
      s'.sid = s.sid ∧ s'.peerSpkPk = s.peerSpkPk ∧ s'.drKeyReal = s.drKeyReal ∧
      s'.drKeyRand = s.drKeyRand ∧ s'.hdr = s.hdr ∧ s'.tested = s.tested := by
  rcases List.mem_map.mp h with ⟨s, hs, rfl⟩
  refine ⟨s, hs, ?_⟩
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem exists_mem_sessions_map_reveal_cli {S : SignalPqxdh.Setup}
    {sessions : List (SignalPqxdh.KeyIndInitiatorEntry S)}
    (sid : SignalPqxdh.SessionId S) {s : SignalPqxdh.KeyIndInitiatorEntry S}
    (hs : s ∈ sessions) :
    ∃ s' ∈ sessions.map (fun e => if e.sid == sid then { e with revealed := true } else e),
      s'.sid = s.sid ∧ s'.peerSpkPk = s.peerSpkPk ∧ s'.hdr = s.hdr := by
  refine ⟨if s.sid == sid then { s with revealed := true } else s,
    List.mem_map_of_mem hs, ?_⟩
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

theorem mem_principals_map_corrupt_cli
    {principals : List (ℕ × SignalPqxdh.PrincipalEntry)} {u : ℕ}
    {idx : ℕ} {e' : SignalPqxdh.PrincipalEntry}
    (h : (idx, e') ∈ principals.map (fun (i, e) =>
      if i == u then (i, { e with corrupted := true }) else (i, e))) :
    ∃ e, (idx, e) ∈ principals ∧ e'.secIKA0 = e.secIKA0 ∧ e'.ikAPk = e.ikAPk ∧
      e'.secIKAsign = e.secIKAsign ∧ e'.ikSignPk = e.ikSignPk := by
  rcases List.mem_map.mp h with ⟨⟨i, e⟩, he, heq⟩
  dsimp only at heq
  split_ifs at heq <;> {
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact ⟨e, he, rfl, rfl, rfl, rfl⟩
  }

theorem exists_mem_principals_map_corrupt_cli
    {principals : List (ℕ × SignalPqxdh.PrincipalEntry)} (u : ℕ)
    {idx : ℕ} {e : SignalPqxdh.PrincipalEntry} (he : (idx, e) ∈ principals) :
    ∃ e', (idx, e') ∈ principals.map (fun (i, x) =>
      if i == u then (i, { x with corrupted := true }) else (i, x)) ∧
      e'.secIKA0 = e.secIKA0 ∧ e'.ikAPk = e.ikAPk := by
  refine ⟨if idx == u then { e with corrupted := true } else e, ?_, ?_⟩
  · have hmem := List.mem_map_of_mem
      (f := fun ((i, x) : ℕ × SignalPqxdh.PrincipalEntry) =>
        if i == u then (i, { x with corrupted := true }) else (i, x)) he
    dsimp only at hmem
    split_ifs at hmem ⊢ <;> exact hmem
  · split_ifs <;> exact ⟨rfl, rfl⟩

theorem mem_spkBundles_map_reveal_cli
    {spks : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)} {target : ℕ × ℕ}
    {idx : ℕ × ℕ} {b' : SignalPqxdh.SpkBundleEntry}
    (h : (idx, b') ∈ spks.map (fun (i, b) =>
      if i == target then (i, { b with revealed := true }) else (i, b))) :
    ∃ b, (idx, b) ∈ spks ∧ b'.spkSk = b.spkSk ∧ b'.spkPk = b.spkPk ∧
      b'.pqspkPk = b.pqspkPk ∧ b'.pqspkSk = b.pqspkSk ∧
      b'.spkSig = b.spkSig ∧ b'.pqspkSig = b.pqspkSig := by
  rcases List.mem_map.mp h with ⟨⟨i, b⟩, hb, heq⟩
  dsimp only at heq
  split_ifs at heq <;> {
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact ⟨b, hb, rfl, rfl, rfl, rfl, rfl, rfl⟩
  }

theorem exists_mem_spkBundles_map_reveal_cli
    {spks : List ((ℕ × ℕ) × SignalPqxdh.SpkBundleEntry)} (target : ℕ × ℕ)
    {idx : ℕ × ℕ} {b : SignalPqxdh.SpkBundleEntry} (hb : (idx, b) ∈ spks) :
    ∃ b', (idx, b') ∈ spks.map (fun (i, x) =>
      if i == target then (i, { x with revealed := true }) else (i, x)) ∧
      b'.spkPk = b.spkPk ∧ b'.pqspkPk = b.pqspkPk := by
  refine ⟨if idx == target then { b with revealed := true } else b, ?_, ?_⟩
  · have hmem := List.mem_map_of_mem
      (f := fun ((i, x) : (ℕ × ℕ) × SignalPqxdh.SpkBundleEntry) =>
        if i == target then (i, { x with revealed := true }) else (i, x)) hb
    dsimp only at hmem
    split_ifs at hmem ⊢ <;> exact hmem
  · split_ifs <;> exact ⟨rfl, rfl⟩

theorem mem_opkEntries_map_consumed_cli
    {opks : List ((ℕ × ℕ × ℕ) × SignalPqxdh.OpkEntry)} {target : ℕ × ℕ × ℕ}
    {idx : ℕ × ℕ × ℕ} {o' : SignalPqxdh.OpkEntry}
    (h : (idx, o') ∈ opks.map (fun (i, o) =>
      if i == target then (i, { o with consumed := true }) else (i, o))) :
    ∃ o, (idx, o) ∈ opks ∧ o'.opkSk = o.opkSk ∧ o'.opkPk = o.opkPk := by
  rcases List.mem_map.mp h with ⟨⟨i, o⟩, ho, heq⟩
  dsimp only at heq
  split_ifs at heq <;> {
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact ⟨o, ho, rfl, rfl⟩
  }

theorem exists_mem_opkEntries_map_consumed_cli
    {opks : List ((ℕ × ℕ × ℕ) × SignalPqxdh.OpkEntry)} (target : ℕ × ℕ × ℕ)
    {idx : ℕ × ℕ × ℕ} {o : SignalPqxdh.OpkEntry} (ho : (idx, o) ∈ opks) :
    ∃ o', (idx, o') ∈ opks.map (fun (i, x) =>
      if i == target then (i, { x with consumed := true }) else (i, x)) ∧
      o'.opkPk = o.opkPk := by
  refine ⟨if idx == target then { o with consumed := true } else o, ?_, ?_⟩
  · have hmem := List.mem_map_of_mem
      (f := fun ((i, x) : (ℕ × ℕ × ℕ) × SignalPqxdh.OpkEntry) =>
        if i == target then (i, { x with consumed := true }) else (i, x)) ho
    dsimp only at hmem
    split_ifs at hmem ⊢ <;> exact hmem
  · split_ifs <;> rfl

/-! ## Per-arm `KeyInd` invariant preservation -/

theorem cliAdapterDrvRel_of_keyInd_step {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli st_cli' : SignalPqxdh.KeyIndState S} {ds_cli ds_cli' : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (kq : SignalPqxdh.KeyIndQuery S) (kr : SignalPqxdh.KeyIndResponse)
    (h_secb : st_cli'.secb = true)
    (h_spk : List.Forall₂ CliSpkBundleRel st_cli'.spkBundles
      (cliUpdateSpkBundlesForQuery kq σ_e2e.st.spkBundles kr st_cli'))
    (h_tested : ∀ s ∈ st_cli'.sessions, s.tested = true →
      SignalPqxdh.isSpkRevealed (modelPrims X W) st_cli'.spkBundles s.peerSpkPk = true ∧
      SignalPqxdh.isSpkRevealed (modelPrims X W)
        (cliUpdateSpkBundlesForQuery kq σ_e2e.st.spkBundles kr st_cli') s.peerSpkPk = true)
    (h_resp : ∀ r ∈ st_cli'.respSessions, r.tested = false)
    (h_ki_inv : CliAdapterKeyIndInv S (modelPrims X W) W st_cli' ds_cli')
    (h_base : ds_cli'.toModelDriverBase = bhBaseMirror ds_cli.toModelDriverBase kq kr)
    (h_corr : ds_cli'.corrPrins = (bhDrvMirror ds_cli kq kr).corrPrins)
    (h_revSpks : ds_cli'.revealedSpks = (bhDrvMirror ds_cli kq kr).revealedSpks)
    (h_insts : ds_cli'.bhInsts = ds_cli.bhInsts)
    (h_meta : ds_cli'.instMeta = ds_cli.instMeta)
    (h_inst_mono : ∀ {q_rem : ℕ} {bi : ModelDriverInstance S ℓ} {d : BHModelInst S ℓ}
      {im im_e2e : ModelDriverInstanceMeta S} {inst : BHAdapterInstMeta S} {ack : Bool},
      CliAdapterInstRel X W q_rem st_cli ds_cli bi d im im_e2e inst ack →
      CliAdapterInstRel X W q_rem st_cli' ds_cli' bi d im im_e2e inst ack) :
    CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli' ds_cli'
      (σ_ad.1, σ_ad.2.1, bhBaseMirror σ_ad.2.2 kq kr)
      (bhE2EMirror
        { σ_e2e with
          st := cliReplaceSpkBundles st_cli'
            (cliUpdateSpkBundlesForQuery kq σ_e2e.st.spkBundles kr st_cli') }
        kq kr) where
  b_eq := hRel.b_eq
  st_rel := ⟨h_secb, h_secb, rfl, h_spk, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h_tested, h_resp⟩
  ki_inv := h_ki_inv
  base_e2e_eq := by
    change ds_cli'.toModelDriverBase = bhBaseMirror σ_e2e.toModelDriverBase kq kr
    rw [h_base, hRel.base_e2e_eq]
  base_ad_eq := by
    change bhBaseMirror σ_ad.2.2 kq kr = ds_cli'.toModelDriverBase
    rw [h_base, hRel.base_ad_eq]
  corrPrins_eq := by
    rw [h_corr]
    cases kq <;> cases kr <;> simp [bhDrvMirror, bhE2EMirror, hRel.corrPrins_eq]
  revealedSpks_eq := by
    rw [h_revSpks]
    cases kq <;> cases kr <;> simp [bhDrvMirror, bhE2EMirror, hRel.revealedSpks_eq]
  insts_len_le := by rw [h_insts]; exact hRel.insts_len_le
  insts_len_eq := by
    change ds_cli'.bhInsts.length = σ_e2e.insts.length
    rw [h_insts, hRel.insts_len_eq]
  meta_cli_len_eq := by rw [h_meta, h_insts, hRel.meta_cli_len_eq]
  meta_e2e_len_eq := hRel.meta_e2e_len_eq
  ad_none_of_ge := hRel.ad_none_of_ge
  insts_rel := by
    intro i h_cli h_e2e h_mb h_me
    simp only [h_insts, h_meta] at h_cli h_mb ⊢
    obtain ⟨inst, hinst, hInstRel⟩ := hRel.insts_rel i h_cli h_e2e h_mb h_me
    exact ⟨inst, hinst, h_inst_mono hInstRel⟩

theorem cliAdapterDrvRel_of_keyInd_noneResp {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {b : Bool} {qStart : ℕ} {qs_rem : ℕ → ℕ}
    {st_cli : SignalPqxdh.KeyIndState S} {ds_cli : ModelDriverState S ℓ}
    {σ_ad : CliAdapterState S} {σ_e2e : BHE2EDrvState S ℓ}
    (hRel : CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli σ_ad σ_e2e)
    (kq : SignalPqxdh.KeyIndQuery S) :
    CliAdapterDrvRel S ℓ X W b qStart qs_rem st_cli ds_cli
      (σ_ad.1, σ_ad.2.1, bhBaseMirror σ_ad.2.2 kq .noneResp)
      (bhE2EMirror
        { σ_e2e with
          st := cliReplaceSpkBundles st_cli
            (cliUpdateSpkBundlesForQuery kq σ_e2e.st.spkBundles .noneResp st_cli) }
        kq .noneResp) := by
  exact cliAdapterDrvRel_of_keyInd_step hRel kq .noneResp
    hRel.st_rel.secb_cli
    (by simp [cliUpdateSpkBundlesForQuery_noneResp, hRel.st_rel.spkBundles_rel])
    (by
      intro s hs ht
      simpa [cliUpdateSpkBundlesForQuery_noneResp] using hRel.st_rel.tested_spkRevealed s hs ht)
    hRel.st_rel.resp_not_tested
    hRel.ki_inv
    (by simp) (by simp) (by simp) rfl rfl
    (fun h => cliAdapterInstRel_of_st_ds_unchanged h (fun _ hx => hx) rfl)

theorem cliAdapterKeyIndInv_of_initPrin {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P)
    (hXBase : ∀ sk, P.x25519Base sk = vecU8 (keyPairOf W.C (u8Vec 32 sk)).publicKey.bytes)
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (u : Fin S.N_id) (secIKA0 : SignalPqxdh.Bytes)
    (hany : st.principals.any (fun (idx, _) => idx == u.val) = false)
    (hsec : secIKA0.length = 32) :
    let ikAPk := P.x25519Base secIKA0
    let entry : SignalPqxdh.PrincipalEntry :=
      { secIKA0 := secIKA0, ikAPk := ikAPk,
        secIKAsign := secIKA0, ikSignPk := ikAPk, corrupted := false }
    CliAdapterKeyIndInv S P W
      { st with principals := (u.val, entry) :: st.principals }
      (bhDrvMirror ds (.initPrin u) (.initPrinResp ikAPk ikAPk)) := by
  intro ikAPk entry
  have hnot_mem : ∀ e, (u.val, e) ∉ st.principals := by
    intro e he
    simp only [List.any_eq_false] at hany
    exact hany (u.val, e) he (beq_self_eq_true _)
  refine
    { prins_wf := fun idx e he => by
        rcases List.mem_cons.mp he with ⟨rfl, rfl⟩ | htl
        · exact ⟨hsec, rfl, hXBase secIKA0, hP.x25519Base_len secIKA0, rfl, rfl⟩
        · exact hInv.prins_wf idx e htl
      prins_uniq := fun idx₁ idx₂ e₁ e₂ h1 h2 hidx => by
        subst hidx
        rcases List.mem_cons.mp h1 with hHead1 | htl1 <;>
          rcases List.mem_cons.mp h2 with hHead2 | htl2
        · cases hHead1; cases hHead2; exact ⟨rfl, rfl, rfl, rfl⟩
        · cases hHead1; exact False.elim (hnot_mem e₂ htl2)
        · cases hHead2; exact False.elim (hnot_mem e₁ htl1)
        · exact hInv.prins_uniq idx₁ idx₁ e₁ e₂ htl1 htl2 rfl
      spk_wf := hInv.spk_wf
      spk_uniq := hInv.spk_uniq
      opk_wf := hInv.opk_wf
      opk_uniq := hInv.opk_uniq
      ds_prins := fun u' ik hmem => by
        rcases List.mem_cons.mp hmem with ⟨rfl, rfl⟩ | htl
        · exact ⟨entry, List.mem_cons_self, rfl⟩
        · obtain ⟨e, he, hik⟩ := hInv.ds_prins u' ik htl
          exact ⟨e, List.mem_cons_of_mem _ he, hik⟩
      prins_ds := fun idx e he => by
        rcases List.mem_cons.mp he with ⟨rfl, rfl⟩ | htl
        · exact ⟨u, List.mem_cons_self⟩
        · obtain ⟨u', hu'⟩ := hInv.prins_ds idx e htl
          exact ⟨u', List.mem_cons_of_mem _ hu'⟩
      ds_bundles := fun slot spkB pqspkB hmem => by
        obtain ⟨e, b, he, hb, h1, h2⟩ := hInv.ds_bundles slot spkB pqspkB hmem
        exact ⟨e, b, List.mem_cons_of_mem _ he, hb, h1, h2⟩
      ds_opks := hInv.ds_opks
      sessions_wf := hInv.sessions_wf
      sessions_uniq := hInv.sessions_uniq
      roCache_nil := hInv.roCache_nil
      respSessions_wf := hInv.respSessions_wf
      initTapes_wf := fun sid u_init bnd t_init hmem => by
        obtain ⟨hs, ⟨uEntry, hu⟩, hrest⟩ := hInv.initTapes_wf sid u_init bnd t_init hmem
        exact ⟨hs, ⟨uEntry, List.mem_cons_of_mem _ hu⟩, hrest⟩
      initTapes_uniq := hInv.initTapes_uniq
      sends_wf := fun sid bnd hdr hmem => by
        obtain ⟨hs, ⟨u_init, t_init, uEntry, ht, hu, hik⟩, hspkid, hpqid, hopkid,
          hbs1, hbs2, hlen1, hlen2, hlen3, hsig, hall⟩ := hInv.sends_wf sid bnd hdr hmem
        refine ⟨hs, ⟨u_init, t_init, uEntry, ht, List.mem_cons_of_mem _ hu, hik⟩,
          hspkid, hpqid, hopkid, hbs1, hbs2, hlen1, hlen2, hlen3, hsig, ?_⟩
        intro sid' u_init' bnd' t_init' sEntry uIdx uEntry' ht' hsid' hsE hsEsid hu' huIdx
        rcases List.mem_cons.mp hu' with ⟨rfl, rfl⟩ | hu_tl
        · obtain ⟨_, ⟨uE₀, huE₀⟩, _⟩ := hInv.initTapes_wf sid' u_init' bnd' t_init' ht'
          exact False.elim (hnot_mem uE₀ (huIdx ▸ huE₀))
        · exact hall sid' u_init' bnd' t_init' sEntry uIdx uEntry' ht' hsid' hsE hsEsid hu_tl huIdx }

theorem cliAdapterKeyIndInv_of_genSPK {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P)
    (hXBase : ∀ sk, P.x25519Base sk = vecU8 (keyPairOf W.C (u8Vec 32 sk)).publicKey.bytes)
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (uEntry : SignalPqxdh.PrincipalEntry)
    (hu : (u.val, uEntry) ∈ st.principals)
    (hany : st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false)
    (spkSk rSpk pqspkPk pqspkSk rPq : SignalPqxdh.Bytes)
    (hspk : spkSk.length = 32)
    (hpq : pqspkPk.length = 1568 ∧ pqspkSk.length = 3168) :
    let spkPk := P.x25519Base spkSk
    let spkSig := P.sigSign uEntry.secIKAsign (SignalPqxdh.encodeEC spkPk) rSpk
    let pqspkSig := P.sigSign uEntry.secIKAsign (SignalPqxdh.encodeKEM pqspkPk) rPq
    let bEntry : SignalPqxdh.SpkBundleEntry :=
      { spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
        pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
    let bundleOut : SignalPqxdh.PreKeyBundleInput :=
      { ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig,
        opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
    CliAdapterKeyIndInv S P W
      { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles }
      (bhDrvMirror ds (.genSPK u j) (.bundleResp bundleOut)) := by
  intro spkPk spkSig pqspkSig bEntry bundleOut
  have hnot_mem : ∀ b, ((u.val, j.val), b) ∉ st.spkBundles := by
    intro b hb
    simp only [List.any_eq_false] at hany
    exact hany ((u.val, j.val), b) hb (beq_self_eq_true _)
  refine
    { prins_wf := hInv.prins_wf
      prins_uniq := hInv.prins_uniq
      spk_wf := fun idx b hb => by
        rcases List.mem_cons.mp hb with ⟨rfl, rfl⟩ | htl
        · exact ⟨hspk, rfl, hXBase spkSk, hP.x25519Base_len spkSk, hpq.1, hpq.2,
            sigSign_length_eq_64_cli hP _ _ _, sigSign_length_eq_64_cli hP _ _ _⟩
        · exact hInv.spk_wf idx b htl
      spk_uniq := fun idx₁ idx₂ b₁ b₂ h1 h2 hidx => by
        subst hidx
        rcases List.mem_cons.mp h1 with hHead1 | htl1 <;>
          rcases List.mem_cons.mp h2 with hHead2 | htl2
        · cases hHead1; cases hHead2; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        · cases hHead1; exact False.elim (hnot_mem b₂ htl2)
        · cases hHead2; exact False.elim (hnot_mem b₁ htl1)
        · exact hInv.spk_uniq idx₁ idx₁ b₁ b₂ htl1 htl2 rfl
      opk_wf := hInv.opk_wf
      opk_uniq := hInv.opk_uniq
      ds_prins := hInv.ds_prins
      prins_ds := hInv.prins_ds
      ds_bundles := fun slot spkB pqspkB hmem => by
        rcases List.mem_cons.mp hmem with ⟨rfl, rfl, rfl⟩ | htl
        · exact ⟨uEntry, bEntry, hu, List.mem_cons_self, rfl, rfl⟩
        · obtain ⟨e, b, he, hb, h1, h2⟩ := hInv.ds_bundles slot spkB pqspkB htl
          exact ⟨e, b, he, List.mem_cons_of_mem _ hb, h1, h2⟩
      ds_opks := hInv.ds_opks
      sessions_wf := hInv.sessions_wf
      sessions_uniq := hInv.sessions_uniq
      roCache_nil := hInv.roCache_nil
      respSessions_wf := hInv.respSessions_wf
      initTapes_wf := hInv.initTapes_wf
      initTapes_uniq := hInv.initTapes_uniq
      sends_wf := hInv.sends_wf }

theorem cliAdapterKeyIndInv_of_genOPK {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P)
    (hXBase : ∀ sk, P.x25519Base sk = vecU8 (keyPairOf W.C (u8Vec 32 sk)).publicKey.bytes)
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hany : st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) = false)
    (opkSk : SignalPqxdh.Bytes) (hopk : opkSk.length = 32) :
    let opkPk := P.x25519Base opkSk
    let oEntry : SignalPqxdh.OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    CliAdapterKeyIndInv S P W
      { st with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.opkEntries }
      (bhDrvMirror ds (.genOPK u j o) (.pkResp opkPk)) := by
  intro opkPk oEntry
  have hnot_mem : ∀ oe, ((u.val, j.val, o.val), oe) ∉ st.opkEntries := by
    intro oe hoe
    simp only [List.any_eq_false] at hany
    exact hany ((u.val, j.val, o.val), oe) hoe (beq_self_eq_true _)
  refine
    { prins_wf := hInv.prins_wf
      prins_uniq := hInv.prins_uniq
      spk_wf := hInv.spk_wf
      spk_uniq := hInv.spk_uniq
      opk_wf := fun idx oe hoe => by
        rcases List.mem_cons.mp hoe with ⟨rfl, rfl⟩ | htl
        · exact ⟨hopk, rfl, hXBase opkSk, hP.x25519Base_len opkSk⟩
        · exact hInv.opk_wf idx oe htl
      opk_uniq := fun idx₁ idx₂ o₁ o₂ h1 h2 hidx => by
        subst hidx
        rcases List.mem_cons.mp h1 with hHead1 | htl1 <;>
          rcases List.mem_cons.mp h2 with hHead2 | htl2
        · cases hHead1; cases hHead2; exact ⟨rfl, rfl⟩
        · cases hHead1; exact False.elim (hnot_mem o₂ htl2)
        · cases hHead2; exact False.elim (hnot_mem o₁ htl1)
        · exact hInv.opk_uniq idx₁ idx₁ o₁ o₂ htl1 htl2 rfl
      ds_prins := hInv.ds_prins
      prins_ds := hInv.prins_ds
      ds_bundles := hInv.ds_bundles
      ds_opks := fun slot pk hmem => by
        rcases List.mem_cons.mp hmem with ⟨rfl, rfl⟩ | htl
        · exact ⟨oEntry, List.mem_cons_self, rfl⟩
        · obtain ⟨oe, hoe, hpk⟩ := hInv.ds_opks slot pk htl
          exact ⟨oe, List.mem_cons_of_mem _ hoe, hpk⟩
      sessions_wf := hInv.sessions_wf
      sessions_uniq := hInv.sessions_uniq
      roCache_nil := hInv.roCache_nil
      respSessions_wf := hInv.respSessions_wf
      initTapes_wf := hInv.initTapes_wf
      initTapes_uniq := hInv.initTapes_uniq
      sends_wf := hInv.sends_wf }

theorem cliAdapterKeyIndInv_of_corruptIK {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (u : Fin S.N_id) (ikSk sigSk : SignalPqxdh.Bytes) :
    let principals' := st.principals.map (fun (idx, e) =>
      if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
    CliAdapterKeyIndInv S P W
      { st with principals := principals' }
      (bhDrvMirror ds (.corruptIK u) (.corrResp ikSk sigSk)) := by
  intro principals'
  refine
    { prins_wf := fun idx e' he' => by
        obtain ⟨e, he, h1, h2, h3, h4⟩ := mem_principals_map_corrupt_cli he'
        rw [h1, h2, h3, h4]
        exact hInv.prins_wf idx e he
      prins_uniq := fun idx₁ idx₂ e₁' e₂' h1 h2 hidx => by
        obtain ⟨e₁, he₁, hs₁, hp₁, hss₁, hsp₁⟩ := mem_principals_map_corrupt_cli h1
        obtain ⟨e₂, he₂, hs₂, hp₂, hss₂, hsp₂⟩ := mem_principals_map_corrupt_cli h2
        obtain ⟨hs, hp, hss, hsp⟩ := hInv.prins_uniq idx₁ idx₂ e₁ e₂ he₁ he₂ hidx
        exact ⟨hs₁.trans (hs.trans hs₂.symm), hp₁.trans (hp.trans hp₂.symm),
          hss₁.trans (hss.trans hss₂.symm), hsp₁.trans (hsp.trans hsp₂.symm)⟩
      spk_wf := hInv.spk_wf
      spk_uniq := hInv.spk_uniq
      opk_wf := hInv.opk_wf
      opk_uniq := hInv.opk_uniq
      ds_prins := fun u' ik hmem => by
        obtain ⟨e, he, hik⟩ := hInv.ds_prins u' ik hmem
        obtain ⟨e', he', _, hp⟩ := exists_mem_principals_map_corrupt_cli u.val he
        exact ⟨e', he', hik.trans hp.symm⟩
      prins_ds := fun idx e' he' => by
        obtain ⟨e, he, _, hp, _, _⟩ := mem_principals_map_corrupt_cli he'
        rw [hp]
        exact hInv.prins_ds idx e he
      ds_bundles := fun slot spkB pqspkB hmem => by
        obtain ⟨e, b, he, hb, h1, h2⟩ := hInv.ds_bundles slot spkB pqspkB hmem
        obtain ⟨e', he', _, _⟩ := exists_mem_principals_map_corrupt_cli u.val he
        exact ⟨e', b, he', hb, h1, h2⟩
      ds_opks := hInv.ds_opks
      sessions_wf := hInv.sessions_wf
      sessions_uniq := hInv.sessions_uniq
      roCache_nil := hInv.roCache_nil
      respSessions_wf := hInv.respSessions_wf
      initTapes_wf := fun sid u_init bnd t_init hmem => by
        obtain ⟨hs, ⟨uEntry, hu⟩, hrest⟩ := hInv.initTapes_wf sid u_init bnd t_init hmem
        obtain ⟨uEntry', hu', _, _⟩ := exists_mem_principals_map_corrupt_cli u.val hu
        exact ⟨hs, ⟨uEntry', hu'⟩, hrest⟩
      initTapes_uniq := hInv.initTapes_uniq
      sends_wf := fun sid bnd hdr hmem => by
        obtain ⟨hs, ⟨u_init, t_init, uEntry, ht, hu, hik⟩, hspkid, hpqid, hopkid,
          hbs1, hbs2, hlen1, hlen2, hlen3, hsig, hall⟩ := hInv.sends_wf sid bnd hdr hmem
        obtain ⟨uEntry', hu', _, hp⟩ := exists_mem_principals_map_corrupt_cli u.val hu
        refine ⟨hs, ⟨u_init, t_init, uEntry', ht, hu', hik.trans hp.symm⟩,
          hspkid, hpqid, hopkid, hbs1, hbs2, hlen1, hlen2, hlen3, hsig, ?_⟩
        intro sid' u_init' bnd' t_init' sEntry uIdx uEntry'' ht' hsid' hsE hsEsid hu'' huIdx
        obtain ⟨uEntry₀, hu₀, hsec₀, _, _, _⟩ := mem_principals_map_corrupt_cli hu''
        rw [hsec₀]
        exact hall sid' u_init' bnd' t_init' sEntry uIdx uEntry₀ ht' hsid' hsE hsEsid hu₀ huIdx }

theorem cliAdapterKeyIndInv_of_revealSpkSk {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (u : Fin S.N_id) (j : Fin S.N_recv) (spkSk : SignalPqxdh.Bytes) :
    let spks' := st.spkBundles.map (fun (idx, b) =>
      if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))
    CliAdapterKeyIndInv S P W
      { st with spkBundles := spks' }
      (bhDrvMirror ds (.revealSpkSk u j) (.spkSkResp spkSk)) := by
  intro spks'
  refine
    { prins_wf := hInv.prins_wf
      prins_uniq := hInv.prins_uniq
      spk_wf := fun idx b' hb' => by
        obtain ⟨b, hb, h1, h2, h3, h4, h5, h6⟩ := mem_spkBundles_map_reveal_cli hb'
        rw [h1, h2, h3, h4, h5, h6]
        exact hInv.spk_wf idx b hb
      spk_uniq := fun idx₁ idx₂ b₁' b₂' h1 h2 hidx => by
        obtain ⟨b₁, hb₁, hs₁, hp₁, hq₁, hk₁, hsg₁, hpsg₁⟩ := mem_spkBundles_map_reveal_cli h1
        obtain ⟨b₂, hb₂, hs₂, hp₂, hq₂, hk₂, hsg₂, hpsg₂⟩ := mem_spkBundles_map_reveal_cli h2
        obtain ⟨hs, hp, hq, hk, hsg, hpsg⟩ := hInv.spk_uniq idx₁ idx₂ b₁ b₂ hb₁ hb₂ hidx
        exact ⟨hs₁.trans (hs.trans hs₂.symm), hp₁.trans (hp.trans hp₂.symm),
          hq₁.trans (hq.trans hq₂.symm), hk₁.trans (hk.trans hk₂.symm),
          hsg₁.trans (hsg.trans hsg₂.symm), hpsg₁.trans (hpsg.trans hpsg₂.symm)⟩
      opk_wf := hInv.opk_wf
      opk_uniq := hInv.opk_uniq
      ds_prins := hInv.ds_prins
      prins_ds := hInv.prins_ds
      ds_bundles := fun slot spkB pqspkB hmem => by
        obtain ⟨e, b, he, hb, h1, h2⟩ := hInv.ds_bundles slot spkB pqspkB hmem
        obtain ⟨b', hb', hp, hq⟩ := exists_mem_spkBundles_map_reveal_cli (u.val, j.val) hb
        exact ⟨e, b', he, hb', h1.trans hp.symm, h2.trans hq.symm⟩
      ds_opks := hInv.ds_opks
      sessions_wf := hInv.sessions_wf
      sessions_uniq := hInv.sessions_uniq
      roCache_nil := hInv.roCache_nil
      respSessions_wf := hInv.respSessions_wf
      initTapes_wf := hInv.initTapes_wf
      initTapes_uniq := hInv.initTapes_uniq
      sends_wf := hInv.sends_wf }

theorem cliAdapterKeyIndInv_of_revealSessionKey {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (sid : SignalPqxdh.SessionId S) (dk : SignalPqxdh.DRKey) :
    let sessions' := st.sessions.map (fun s =>
      if s.sid == sid then { s with revealed := true } else s)
    CliAdapterKeyIndInv S P W
      { st with sessions := sessions' }
      (bhDrvMirror ds (.revealSessionKey sid) (.drKeyResp dk)) := by
  intro sessions'
  refine
    { prins_wf := hInv.prins_wf
      prins_uniq := hInv.prins_uniq
      spk_wf := hInv.spk_wf
      spk_uniq := hInv.spk_uniq
      opk_wf := hInv.opk_wf
      opk_uniq := hInv.opk_uniq
      ds_prins := hInv.ds_prins
      prins_ds := hInv.prins_ds
      ds_bundles := hInv.ds_bundles
      ds_opks := hInv.ds_opks
      sessions_wf := fun s' hs' => by
        obtain ⟨s, hs, _, _, hreal, hrand, _, _⟩ := mem_sessions_map_reveal_cli hs'
        rw [hreal, hrand]
        exact hInv.sessions_wf s hs
      sessions_uniq := fun s₁' s₂' h1 h2 hsid => by
        obtain ⟨s₁, hs₁, hsid₁, hspk₁, hreal₁, _, hhdr₁, _⟩ := mem_sessions_map_reveal_cli h1
        obtain ⟨s₂, hs₂, hsid₂, hspk₂, hreal₂, _, hhdr₂, _⟩ := mem_sessions_map_reveal_cli h2
        obtain ⟨hspk, hreal, hhdr⟩ :=
          hInv.sessions_uniq s₁ s₂ hs₁ hs₂ (hsid₁.symm.trans (hsid.trans hsid₂))
        exact ⟨hspk₁.trans (hspk.trans hspk₂.symm),
          hreal₁.trans (hreal.trans hreal₂.symm),
          hhdr₁.trans (hhdr.trans hhdr₂.symm)⟩
      roCache_nil := hInv.roCache_nil
      respSessions_wf := hInv.respSessions_wf
      initTapes_wf := fun sid' u_init bnd t_init hmem => by
        obtain ⟨⟨s, hs, rfl⟩, hrest⟩ := hInv.initTapes_wf sid' u_init bnd t_init hmem
        obtain ⟨s', hs', hsid', _, _⟩ := exists_mem_sessions_map_reveal_cli sid hs
        exact ⟨⟨s', hs', hsid'⟩, hrest⟩
      initTapes_uniq := hInv.initTapes_uniq
      sends_wf := fun sid' bnd hdr hmem => by
        obtain ⟨⟨s, hs, rfl, hspk, hhdr⟩, hu, hspkid, hpqid, hopkid,
          hbs1, hbs2, hlen1, hlen2, hlen3, hsig, hall⟩ := hInv.sends_wf sid' bnd hdr hmem
        obtain ⟨s', hs', hsid', hspk', hhdr'⟩ := exists_mem_sessions_map_reveal_cli sid hs
        refine ⟨⟨s', hs', hsid', hspk'.trans hspk, hhdr'.trans hhdr⟩,
          hu, hspkid, hpqid, hopkid, hbs1, hbs2, hlen1, hlen2, hlen3, hsig, ?_⟩
        intro sid'' u_init' bnd' t_init' sEntry' uIdx uEntry ht' hsid'' hsE' hsEsid' hu' huIdx
        obtain ⟨sEntry, hsE, hsid0, _, hreal0, _, _, _⟩ := mem_sessions_map_reveal_cli hsE'
        rw [hreal0]
        exact hall sid'' u_init' bnd' t_init' sEntry uIdx uEntry ht' hsid'' hsE
          (hsid0.symm.trans hsEsid') hu' huIdx }

theorem cliAdapterKeyIndInv_of_revealRespSessionKey {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (sid : SignalPqxdh.SessionId S) (dk : SignalPqxdh.DRKey) :
    let respSessions' := st.respSessions.map (fun r =>
      if r.sid == sid then { r with revealed := true } else r)
    CliAdapterKeyIndInv S P W
      { st with respSessions := respSessions' }
      (bhDrvMirror ds (.revealSessionKey sid) (.drKeyResp dk)) := by
  intro respSessions'
  refine { hInv with
    respSessions_wf := fun r' hr' => by
      rcases List.mem_map.mp hr' with ⟨r, hr, rfl⟩
      split_ifs <;> exact hInv.respSessions_wf r hr }

theorem cliAdapterKeyIndInv_of_accept {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    {st : SignalPqxdh.KeyIndState S} {ds : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (opkEntries' : List ((ℕ × ℕ × ℕ) × SignalPqxdh.OpkEntry))
    (hopk_back : ∀ idx o', (idx, o') ∈ opkEntries' →
      ∃ o, (idx, o) ∈ st.opkEntries ∧ o'.opkSk = o.opkSk ∧ o'.opkPk = o.opkPk)
    (hopk_fwd : ∀ idx o, (idx, o) ∈ st.opkEntries →
      ∃ o', (idx, o') ∈ opkEntries' ∧ o'.opkPk = o.opkPk)
    (rEntry : SignalPqxdh.KeyIndRespEntry S) (drKeyRand : SignalPqxdh.DRKey)
    (hreal : rEntry.drKeyReal.rootKey.length = 32 ∧ rEntry.drKeyReal.chainKey.length = 32 ∧
      rEntry.drKeyReal.pqrKey.length = 32)
    (hrand : drKeyRand.rootKey.length = 32 ∧ drKeyRand.chainKey.length = 32 ∧
      drKeyRand.pqrKey.length = 32)
    (roCache' : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (hro : roCache' = [])
    (usedRecvOPK' usedRecvNoOPK' : List (ℕ × ℕ × ℕ))
    (usedKyberTriples' : List (ℕ × SignalPqxdh.KeyId × SignalPqxdh.KeyId × SignalPqxdh.Bytes)) :
    CliAdapterKeyIndInv S P W
      { st with
        opkEntries := opkEntries'
        respSessions := { rEntry with drKeyRand := drKeyRand } :: st.respSessions
        usedRecvOPK := usedRecvOPK'
        usedRecvNoOPK := usedRecvNoOPK'
        seenKyberBaseKeys := usedKyberTriples'
        roCache := roCache' }
      ds where
  prins_wf := hInv.prins_wf
  prins_uniq := hInv.prins_uniq
  spk_wf := hInv.spk_wf
  spk_uniq := hInv.spk_uniq
  opk_wf := fun idx o' ho' => by
    obtain ⟨o, ho, h1, h2⟩ := hopk_back idx o' ho'
    rw [h1, h2]
    exact hInv.opk_wf idx o ho
  opk_uniq := fun idx₁ idx₂ o₁' o₂' h1 h2 hidx => by
    obtain ⟨o₁, ho₁, hs₁, hp₁⟩ := hopk_back idx₁ o₁' h1
    obtain ⟨o₂, ho₂, hs₂, hp₂⟩ := hopk_back idx₂ o₂' h2
    obtain ⟨hs, hp⟩ := hInv.opk_uniq idx₁ idx₂ o₁ o₂ ho₁ ho₂ hidx
    exact ⟨hs₁.trans (hs.trans hs₂.symm), hp₁.trans (hp.trans hp₂.symm)⟩
  ds_prins := hInv.ds_prins
  prins_ds := hInv.prins_ds
  ds_bundles := hInv.ds_bundles
  ds_opks := fun slot opkPk hmem => by
    obtain ⟨o, ho, hpk⟩ := hInv.ds_opks slot opkPk hmem
    obtain ⟨o', ho', hpk'⟩ := hopk_fwd _ o ho
    exact ⟨o', ho', hpk.trans hpk'.symm⟩
  sessions_wf := hInv.sessions_wf
  sessions_uniq := hInv.sessions_uniq
  roCache_nil := hro
  respSessions_wf := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | htl
    · exact ⟨hreal.1, hreal.2.1, hreal.2.2, hrand.1, hrand.2.1, hrand.2.2⟩
    · exact hInv.respSessions_wf r htl
  initTapes_wf := hInv.initTapes_wf
  initTapes_uniq := hInv.initTapes_uniq
  sends_wf := hInv.sends_wf

def bhInitiateMirror_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds : ModelDriverState S ℓ) (sid : SignalPqxdh.SessionId S)
    (bnd : SignalPqxdh.PreKeyBundleInput) (r : SignalPqxdh.KeyIndResponse) : ModelDriverState S ℓ :=
  match r with
  | .hdrResp hdr => { ds with sends := (sid, bnd, hdr) :: ds.sends }
  | _ => ds

theorem bhDrvMirror_initiateOPK_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds : ModelDriverState S ℓ) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (bnd : SignalPqxdh.PreKeyBundleInput) (r : SignalPqxdh.KeyIndResponse) :
    bhDrvMirror ds (.initiateOPK u i bnd) r = bhInitiateMirror_cli ds (.sendOPK u i) bnd r := by
  cases r <;> rfl

theorem bhDrvMirror_initiateNoOPK_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds : ModelDriverState S ℓ) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (bnd : SignalPqxdh.PreKeyBundleInput) (r : SignalPqxdh.KeyIndResponse) :
    bhDrvMirror ds (.initiateNoOPK u i bnd) r = bhInitiateMirror_cli ds (.sendNoOPK u i) bnd r := by
  cases r <;> rfl

theorem bhBaseMirror_initiateOPK_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds : ModelDriverState S ℓ) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (bnd : SignalPqxdh.PreKeyBundleInput) (r : SignalPqxdh.KeyIndResponse) :
    (bhInitiateMirror_cli ds (.sendOPK u i) bnd r).toModelDriverBase =
      bhBaseMirror ds.toModelDriverBase (.initiateOPK u i bnd) r := by
  cases r <;> rfl

theorem bhBaseMirror_initiateNoOPK_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds : ModelDriverState S ℓ) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (bnd : SignalPqxdh.PreKeyBundleInput) (r : SignalPqxdh.KeyIndResponse) :
    (bhInitiateMirror_cli ds (.sendNoOPK u i) bnd r).toModelDriverBase =
      bhBaseMirror ds.toModelDriverBase (.initiateNoOPK u i bnd) r := by
  cases r <;> rfl

private theorem bhDrv_run_lift_get_bind_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (k : SignalPqxdh.KeyIndState S → BHDrvM S ℓ SignalPqxdh.KeyIndResponse)
    (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (bnd : SignalPqxdh.PreKeyBundleInput) :
    ((((StateT.lift get >>= k) >>= fun r =>
        modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
          BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st) =
    (((k st >>= fun r =>
        modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
          BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st) := by
  simp only [bind_assoc, StateT.run_bind, stateT_lift_run_cli, StateT.run_get,
    StateT.run_pure, pure_bind]

private theorem mem_support_bhDrv_pure_noneResp_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (ds ds' : ModelDriverState S ℓ) (st st' : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (bnd : SignalPqxdh.PreKeyBundleInput)
    (kr : SignalPqxdh.KeyIndResponse)
    (h : ((kr, ds'), st') ∈ support
      ((((pure .noneResp : BHDrvM S ℓ SignalPqxdh.KeyIndResponse) >>= fun r =>
          modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
            BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st)) :
    kr = .noneResp ∧ ds' = ds ∧ st' = st := by
  simp only [pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq, bhInitiateMirror_cli] at h
  rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

private theorem stateT_run_ite_noneResp_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (cond : Bool) (m : BHDrvM S ℓ SignalPqxdh.KeyIndResponse)
    (ds ds' : ModelDriverState S ℓ) (st st' : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (bnd : SignalPqxdh.PreKeyBundleInput)
    (kr : SignalPqxdh.KeyIndResponse)
    (h : ((kr, ds'), st') ∈ support
      ((((if cond then pure .noneResp else m) >>= fun r =>
          modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
            BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st)) :
    (kr = .noneResp ∧ ds' = ds ∧ st' = st) ∨
    (cond = false ∧ ((kr, ds'), st') ∈ support
      (((m >>= fun r =>
          modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
            BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st)) := by
  cases cond
  · exact Or.inr ⟨rfl, h⟩
  · simp only [↓reduceIte] at h
    exact Or.inl (mem_support_bhDrv_pure_noneResp_cli ds ds' st st' sid bnd kr h)

private theorem mem_support_bhDrv_liftM_bind_cli {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    (c : ProbComp α) (k : α → BHDrvM S ℓ SignalPqxdh.KeyIndResponse)
    (ds ds' : ModelDriverState S ℓ) (st st' : SignalPqxdh.KeyIndState S)
    (sid : SignalPqxdh.SessionId S) (bnd : SignalPqxdh.PreKeyBundleInput)
    (kr : SignalPqxdh.KeyIndResponse)
    (h : ((kr, ds'), st') ∈ support
      ((((StateT.lift (liftM c : StateT (SignalPqxdh.KeyIndState S) ProbComp α) >>= k) >>= fun r =>
          modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
            BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st)) :
    ∃ a ∈ support c,
      ((kr, ds'), st') ∈ support
        (((k a >>= fun r =>
            modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
              BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st) := by
  have hrun :
      ((((StateT.lift (liftM c : StateT (SignalPqxdh.KeyIndState S) ProbComp α) >>= k) >>= fun r =>
          modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
            BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st) =
      (c >>= fun a =>
        (((k a >>= fun r =>
            modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
              BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st)) := by
    simp only [bind_assoc, StateT.run_bind, stateT_lift_run_cli, stateT_monadLift_run_cli,
      StateT.run_pure, pure_bind]
  rw [hrun] at h
  simp only [support_bind, Set.mem_iUnion] at h
  rcases h with ⟨a, ha, hmem⟩
  exact ⟨a, ha, hmem⟩

private theorem mem_support_bhDrv_set_modify_pure_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    (st1 st st' : SignalPqxdh.KeyIndState S)
    (f : ModelDriverState S ℓ → ModelDriverState S ℓ)
    (resp kr : SignalPqxdh.KeyIndResponse)
    (ds ds' : ModelDriverState S ℓ)
    (sid : SignalPqxdh.SessionId S) (bnd : SignalPqxdh.PreKeyBundleInput)
    (h : ((kr, ds'), st') ∈ support
      ((((do
            StateT.lift (set st1)
            modify f
            pure resp : BHDrvM S ℓ SignalPqxdh.KeyIndResponse) >>= fun r =>
          modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
            BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st)) :
    kr = resp ∧ ds' = bhInitiateMirror_cli (f ds) sid bnd resp ∧ st' = st1 := by
  simp only [bind_assoc, pure_bind, StateT.run_bind, stateT_lift_run_cli, StateT.run_set,
    StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

theorem cliAdapterKeyIndInv_of_initiate {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P)
    {st : SignalPqxdh.KeyIndState S} {ds ds' : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id)
    (bnd : SignalPqxdh.PreKeyBundleInput) (t_init : List.Vector (BitVec 8) 160)
    (uEntry : SignalPqxdh.PrincipalEntry) (hu : (u.val, uEntry) ∈ st.principals)
    (hsid_prin : bhDrvSessionInitPrin? sid = some u)
    (hany : st.sessions.any (fun e => e.sid == sid) = false)
    (hspkSig : bnd.spkSig.length = 64) (hpqspkSig : bnd.pqspkSig.length = 64)
    (hsigOk : (P.sigVerify bnd.ikB (SignalPqxdh.encodeEC bnd.spkB) bnd.spkSig &&
      P.sigVerify bnd.ikB (SignalPqxdh.encodeKEM bnd.pqspkB) bnd.pqspkSig) = true)
    (ss kemCt : SignalPqxdh.Bytes)
    (hEnc : P.kemEncaps bnd.pqspkB (tapeKemCoins t_init) = some (ss, kemCt))
    (hkemCt : kemCt.length = 1568)
    (drKeyReal drKeyRand : SignalPqxdh.DRKey)
    (hreal_eq : drKeyReal = P.hkdfDerive96 (SignalPqxdh.buildSecrets
      (P.x25519 uEntry.secIKA0 bnd.spkB)
      (P.x25519 (tapeEkASk t_init) bnd.ikB)
      (P.x25519 (tapeEkASk t_init) bnd.spkB)
      (bnd.opkB?.map (fun (_, opkPk) => P.x25519 (tapeEkASk t_init) opkPk)) ss))
    (hreal : drKeyReal.rootKey.length = 32 ∧ drKeyReal.chainKey.length = 32 ∧
      drKeyReal.pqrKey.length = 32)
    (hrand : drKeyRand.rootKey.length = 32 ∧ drKeyRand.chainKey.length = 32 ∧
      drKeyRand.pqrKey.length = 32)
    (roCache' : List (SignalPqxdh.Bytes × SignalPqxdh.DRKey))
    (hro : roCache' = [])
    (entry : SignalPqxdh.KeyIndInitiatorEntry S)
    (hentry_sid : entry.sid = sid)
    (hentry_spk : entry.peerSpkPk = bnd.spkB)
    (hentry_real : entry.drKeyReal = drKeyReal)
    (hentry_rand : entry.drKeyRand = drKeyRand)
    (hentry_hdr : entry.hdr =
      { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base (tapeEkASk t_init), spkId := bnd.spkId,
        opkId? := bnd.opkB?.map Prod.fst, pqspkId := bnd.pqspkId, kemCt := kemCt })
    (hds_prins : ds'.prins = ds.prins)
    (hds_bundles : ds'.bundles = ds.bundles)
    (hds_opks : ds'.opks = ds.opks)
    (hds_tapes : ds'.initTapes = (sid, u, bnd, t_init) :: ds.initTapes)
    (hds_sends : ∀ s b h, (s, b, h) ∈ ds'.sends →
      (s = sid ∧ b = bnd ∧ h = entry.hdr) ∨ (s, b, h) ∈ ds.sends) :
    CliAdapterKeyIndInv S P W
      { st with sessions := entry :: st.sessions, roCache := roCache' }
      ds' := by
  have hnot_mem : ∀ s ∈ st.sessions, s.sid ≠ sid := by
    intro s hs hEq
    simp only [List.any_eq_false] at hany
    exact hany s hs (beq_iff_eq.mpr hEq)
  have htape_not_sid : ∀ sid' u' b' t', (sid', u', b', t') ∈ ds.initTapes → sid' ≠ sid := by
    intro sid' u' b' t' ht hEq
    obtain ⟨⟨sE, hsE, hsEsid⟩, _⟩ := hInv.initTapes_wf sid' u' b' t' ht
    exact hnot_mem sE hsE (hsEsid.trans hEq)
  refine
    { prins_wf := hInv.prins_wf
      prins_uniq := hInv.prins_uniq
      spk_wf := hInv.spk_wf
      spk_uniq := hInv.spk_uniq
      opk_wf := hInv.opk_wf
      opk_uniq := hInv.opk_uniq
      ds_prins := fun u' ik hmem => hInv.ds_prins u' ik (hds_prins ▸ hmem)
      prins_ds := fun idx e he => by
        obtain ⟨u', hu'⟩ := hInv.prins_ds idx e he
        exact ⟨u', hds_prins.symm ▸ hu'⟩
      ds_bundles := fun slot spkB pqspkB hmem =>
        hInv.ds_bundles slot spkB pqspkB (hds_bundles ▸ hmem)
      ds_opks := fun slot opkPk hmem =>
        hInv.ds_opks slot opkPk (hds_opks ▸ hmem)
      sessions_wf := fun s hs => by
        rcases List.mem_cons.mp hs with rfl | htl
        · rw [hentry_real, hentry_rand]
          exact ⟨hreal.1, hreal.2.1, hreal.2.2, hrand.1, hrand.2.1, hrand.2.2⟩
        · exact hInv.sessions_wf s htl
      sessions_uniq := fun s₁ s₂ h1 h2 hsid => by
        rcases List.mem_cons.mp h1 with rfl | htl1 <;>
          rcases List.mem_cons.mp h2 with rfl | htl2
        · exact ⟨rfl, rfl, rfl⟩
        · exact False.elim (hnot_mem s₂ htl2 (hsid.symm.trans hentry_sid))
        · exact False.elim (hnot_mem s₁ htl1 (hsid.trans hentry_sid))
        · exact hInv.sessions_uniq s₁ s₂ htl1 htl2 hsid
      roCache_nil := hro
      respSessions_wf := hInv.respSessions_wf
      initTapes_wf := fun sid' u_init bnd' t_init' hmem => by
        rw [hds_tapes] at hmem
        rcases List.mem_cons.mp hmem with ⟨rfl, rfl, rfl, rfl⟩ | htl
        · exact ⟨⟨entry, List.mem_cons_self, hentry_sid⟩, ⟨uEntry, hu⟩,
            hsid_prin, hspkSig, hpqspkSig⟩
        · obtain ⟨⟨sE, hsE, hsid'⟩, hrest⟩ := hInv.initTapes_wf sid' u_init bnd' t_init' htl
          exact ⟨⟨sE, List.mem_cons_of_mem _ hsE, hsid'⟩, hrest⟩
      initTapes_uniq := fun sid' u₁ b₁ t₁ u₂ b₂ t₂ h1 h2 => by
        rw [hds_tapes] at h1 h2
        rcases List.mem_cons.mp h1 with hHead1 | htl1 <;>
          rcases List.mem_cons.mp h2 with hHead2 | htl2
        · rcases Prod.mk.inj hHead1 with ⟨_, h1'⟩
          rcases Prod.mk.inj h1' with ⟨rfl, h1''⟩
          rcases Prod.mk.inj h1'' with ⟨rfl, rfl⟩
          rcases Prod.mk.inj hHead2 with ⟨_, h2'⟩
          rcases Prod.mk.inj h2' with ⟨rfl, h2''⟩
          rcases Prod.mk.inj h2'' with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
        · rcases Prod.mk.inj hHead1 with ⟨rfl, _⟩
          exact False.elim (htape_not_sid sid' u₂ b₂ t₂ htl2 rfl)
        · rcases Prod.mk.inj hHead2 with ⟨rfl, _⟩
          exact False.elim (htape_not_sid sid' u₁ b₁ t₁ htl1 rfl)
        · exact hInv.initTapes_uniq sid' u₁ b₁ t₁ u₂ b₂ t₂ htl1 htl2
      sends_wf := fun sid' bnd' hdr' hmem => by
        rcases hds_sends sid' bnd' hdr' hmem with ⟨rfl, rfl, rfl⟩ | htl
        · refine ⟨⟨entry, List.mem_cons_self, hentry_sid, hentry_spk, rfl⟩,
            ⟨u, t_init, uEntry, by rw [hds_tapes]; exact List.mem_cons_self,
              hu, by rw [hentry_hdr]⟩, ?_⟩
          refine ⟨by rw [hentry_hdr], by rw [hentry_hdr], by rw [hentry_hdr],
            hspkSig, hpqspkSig,
            by rw [hentry_hdr]; exact (hInv.prins_wf u.val uEntry hu).2.2.2.1,
            by rw [hentry_hdr]; exact hP.x25519Base_len _,
            by rw [hentry_hdr]; exact hkemCt,
            hsigOk, ?_⟩
          intro sid'' u_init' bnd'' t_init' sE uIdx uE' ht' hsid'' hsE hsEsid huE' huIdx
          rw [hds_tapes] at ht'
          rcases List.mem_cons.mp ht' with hHead | htl_t
          · rcases Prod.mk.inj hHead with ⟨_, h1'⟩
            rcases Prod.mk.inj h1' with ⟨hu_eq, h1''⟩
            rcases Prod.mk.inj h1'' with ⟨rfl, rfl⟩
            rcases List.mem_cons.mp hsE with rfl | hsE_tl
            · have huIdx_u : uIdx = u.val := huIdx.trans (congrArg Fin.val hu_eq)
              have huE_eq := (hInv.prins_uniq uIdx u.val uE' uEntry huE' hu huIdx_u).1
              refine ⟨ss, ?_, ?_, ?_⟩
              · rw [hentry_hdr]; exact hEnc
              · rw [hentry_hdr]
              · dsimp only
                rw [hentry_real, huE_eq, hreal_eq]
            · exact False.elim (hnot_mem sE hsE_tl hsEsid)
          · exact False.elim (htape_not_sid sid'' u_init' bnd'' t_init' htl_t hsid'')
        · obtain ⟨⟨sOld, hsOld, hsOld_sid, h2, h3⟩, ⟨u_init, t', uE, ht', huE, hik⟩,
            hspkid, hpqid, hopkid, hbs1, hbs2, hlen1, hlen2, hlen3, hsig, hall⟩ :=
            hInv.sends_wf sid' bnd' hdr' htl
          have hsid'_ne : sid' ≠ sid := by
            intro hEq; exact hnot_mem sOld hsOld (hsOld_sid.trans hEq)
          refine ⟨⟨sOld, List.mem_cons_of_mem _ hsOld, hsOld_sid, h2, h3⟩,
            ⟨u_init, t', uE, by rw [hds_tapes]; exact List.mem_cons_of_mem _ ht', huE, hik⟩,
            hspkid, hpqid, hopkid, hbs1, hbs2, hlen1, hlen2, hlen3, hsig, ?_⟩
          intro sid'' u_init' bnd'' t_init' sE uIdx uE' ht'' hsid'' hsE hsEsid huE' huIdx
          rw [hds_tapes] at ht''
          have ht''_tl : (sid'', u_init', bnd'', t_init') ∈ ds.initTapes := by
            rcases List.mem_cons.mp ht'' with hHead | htl_t
            · rcases Prod.mk.inj hHead with ⟨rfl, _⟩
              exact False.elim (hsid'_ne hsid''.symm)
            · exact htl_t
          have hsE_tl : sE ∈ st.sessions := by
            rcases List.mem_cons.mp hsE with rfl | htl_s
            · exact False.elim (hsid'_ne (hsEsid.symm.trans hentry_sid))
            · exact htl_s
          exact hall sid'' u_init' bnd'' t_init' sE uIdx uE' ht''_tl hsid'' hsE_tl hsEsid huE' huIdx }

theorem bhRunInitiate_false_preserves_inv_cli {S : SignalPqxdh.Setup} {ℓ : ℕ}
    {P : SignalPqxdh.Primitives} {W : PEParams}
    (hP : SignalPqxdh.CryptoWellFormedPrimitivesδ P)
    {st st' : SignalPqxdh.KeyIndState S} {ds ds' : ModelDriverState S ℓ}
    (hInv : CliAdapterKeyIndInv S P W st ds)
    (sid : SignalPqxdh.SessionId S) (u : Fin S.N_id)
    (bnd : SignalPqxdh.PreKeyBundleInput) (kr : SignalPqxdh.KeyIndResponse)
    (hsid_prin : bhDrvSessionInitPrin? sid = some u)
    (hmem : ((kr, ds'), st') ∈ support
      (((bhRunInitiate S P sid u bnd false >>= fun r =>
          modify (fun d => bhInitiateMirror_cli d sid bnd r) >>= fun _ => pure r :
            BHDrvM S ℓ SignalPqxdh.KeyIndResponse).run ds).run st)) :
    (kr = .noneResp ∧ ds' = ds ∧ st' = st) ∨
    (st'.secb = st.secb ∧ st'.spkBundles = st.spkBundles ∧ st'.respSessions = st.respSessions ∧
     (∀ s ∈ st'.sessions, s.tested = true → s ∈ st.sessions) ∧
     (∀ x ∈ ds.initTapes, x ∈ ds'.initTapes) ∧ CliAdapterKeyIndInv S P W st' ds' ∧
     ds'.toModelDriverBase = (bhInitiateMirror_cli ds sid bnd kr).toModelDriverBase ∧
     ds'.corrPrins = ds.corrPrins ∧ ds'.revealedSpks = ds.revealedSpks ∧
     ds'.bhInsts = ds.bhInsts ∧ ds'.instMeta = ds.instMeta) := by
  unfold bhRunInitiate at hmem
  rw [bhDrv_run_lift_get_bind_cli] at hmem
  rcases stateT_run_ite_noneResp_cli _ _ ds ds' st st' sid bnd kr hmem with
    ⟨rfl, rfl, rfl⟩ | ⟨h1, hmem⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · rcases hFindU : st.principals.find? (fun (idx, _) => idx == u.val) with _ | ⟨idx_u, uEntry⟩
    · rw [hFindU] at hmem
      exact Or.inl (mem_support_bhDrv_pure_noneResp_cli ds ds' st st' sid bnd kr hmem)
    · rw [hFindU] at hmem; dsimp only at hmem
      obtain ⟨huEntry, _⟩ := mem_principals_of_find?_eq_some_cli hFindU
      rcases stateT_run_ite_noneResp_cli _ _ ds ds' st st' sid bnd kr hmem with
        ⟨rfl, rfl, rfl⟩ | ⟨hc1, hmem⟩
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · simp only [Bool.not_eq_false'] at hc1
        have hSigPk : SignalPqxdh.resolveSigPk P st.principals bnd.ikB = bnd.ikB :=
          resolveSigPk_eq_ikB_of_1key_cli hInv hc1
        rcases stateT_run_ite_noneResp_cli _ _ ds ds' st st' sid bnd kr hmem with
          ⟨rfl, rfl, rfl⟩ | ⟨_, hmem⟩
        · exact Or.inl ⟨rfl, rfl, rfl⟩
        · obtain ⟨t_init, _, hmem⟩ :=
            mem_support_bhDrv_liftM_bind_cli _ _ ds ds' st st' sid bnd kr hmem
          rcases stateT_run_ite_noneResp_cli _ _ ds ds' st st' sid bnd kr hmem with
            ⟨rfl, rfl, rfl⟩ | ⟨hc3, hmem⟩
          · exact Or.inl ⟨rfl, rfl, rfl⟩
          · simp only [Bool.not_eq_false'] at hc3
            rw [hSigPk] at hc3
            have hc3_and := Bool.and_eq_true _ _ |>.mp hc3
            have hspkSig : bnd.spkSig.length = 64 := sigVerify_length_eq_64_cli hP hc3_and.1
            have hpqspkSig : bnd.pqspkSig.length = 64 := sigVerify_length_eq_64_cli hP hc3_and.2
            rcases hEnc : P.kemEncaps bnd.pqspkB (tapeKemCoins t_init) with _ | ⟨ss, kemCt⟩
            · rw [hEnc] at hmem
              exact Or.inl (mem_support_bhDrv_pure_noneResp_cli ds ds' st st' sid bnd kr hmem)
            · rw [hEnc] at hmem; dsimp only at hmem
              have hkemCt : kemCt.length = 1568 :=
                (hP.kemEncaps_len bnd.pqspkB (tapeKemCoins t_init) ss kemCt hEnc).2
              obtain ⟨⟨drKeyReal, roCache'⟩, hro, hmem⟩ :=
                mem_support_bhDrv_liftM_bind_cli _ _ ds ds' st st' sid bnd kr hmem
              obtain ⟨hreal_eq, hro_eq⟩ := mem_support_evalHkdfOrRo_false_cli P st.roCache _ hro
              have hro_nil : roCache' = [] := hro_eq.trans hInv.roCache_nil
              have hreal : drKeyReal.rootKey.length = 32 ∧ drKeyReal.chainKey.length = 32 ∧
                  drKeyReal.pqrKey.length = 32 :=
                hreal_eq ▸ hkdfDerive96_lengths_of_wf_cli hP _
              let ekASk := tapeEkASk t_init
              let hdr : SignalPqxdh.HandshakeHdr :=
                { ikAPk := uEntry.ikAPk, ekAPk := P.x25519Base ekASk, spkId := bnd.spkId,
                  opkId? := bnd.opkB?.map Prod.fst, pqspkId := bnd.pqspkId, kemCt := kemCt }
              let honestPeer := SignalPqxdh.isHonestUncorruptedPeer P st.principals bnd.ikB
              let prov := SignalPqxdh.checkBundleProvenance P st.principals
                st.spkBundles st.opkEntries bnd
              let sessEntry : SignalPqxdh.KeyIndInitiatorEntry S :=
                { sid := sid, honestPeer := honestPeer, peerIkPk := bnd.ikB,
                  peerSpkPk := bnd.spkB, peerOpkPk? := bnd.opkB?.map Prod.snd,
                  peerPqspkPk := bnd.pqspkB, spkHonest := prov.1, opkHonest := prov.2.1,
                  pqspkHonest := prov.2.2, ekASk := ekASk, fresh := honestPeer.isSome,
                  drKeyReal := drKeyReal, drKeyRand := drKeyReal, hdr := hdr, tested := false }
              have hStep : ∃ drKeyRand : SignalPqxdh.DRKey,
                  (drKeyRand.rootKey.length = 32 ∧ drKeyRand.chainKey.length = 32 ∧
                   drKeyRand.pqrKey.length = 32) ∧
                  st' = { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions, roCache := roCache' } ∧
                  ds' = bhInitiateMirror_cli
                    { ds with initTapes := (sid, u, bnd, t_init) :: ds.initTapes } sid bnd kr ∧
                  (kr = .hdrResp hdr ∨ kr = .initUnfreshResp drKeyReal hdr) := by
                rcases hKPR : SignalPqxdh.keyIndPartnerRandKey? P st.respSessions sessEntry with _ | dk
                · rw [hKPR] at hmem; dsimp only at hmem
                  obtain ⟨dk, hdk, hmem⟩ :=
                    mem_support_bhDrv_liftM_bind_cli _ _ ds ds' st st' sid bnd kr hmem
                  refine ⟨dk, lengths_of_mem_support_sampleDRKey96 hdk, ?_⟩
                  rcases hFHP : SignalPqxdh.findHonestPrincipal P st.principals bnd.ikB with _ | _ <;>
                    rw [hFHP] at hmem
                  · obtain ⟨rfl, rfl, rfl⟩ := mem_support_bhDrv_set_modify_pure_cli _ st st' _ _ kr ds ds' sid bnd hmem; exact ⟨rfl, rfl, Or.inr rfl⟩
                  · obtain ⟨rfl, rfl, rfl⟩ := mem_support_bhDrv_set_modify_pure_cli _ st st' _ _ kr ds ds' sid bnd hmem; exact ⟨rfl, rfl, Or.inl rfl⟩
                · rw [hKPR] at hmem; dsimp only at hmem
                  refine ⟨dk, partnerRandKey_lengths_cli hInv.respSessions_wf hKPR, ?_⟩
                  rcases hFHP : SignalPqxdh.findHonestPrincipal P st.principals bnd.ikB with _ | _ <;>
                    rw [hFHP] at hmem
                  · obtain ⟨rfl, rfl, rfl⟩ := mem_support_bhDrv_set_modify_pure_cli _ st st' _ _ kr ds ds' sid bnd hmem; exact ⟨rfl, rfl, Or.inr rfl⟩
                  · obtain ⟨rfl, rfl, rfl⟩ := mem_support_bhDrv_set_modify_pure_cli _ st st' _ _ kr ds ds' sid bnd hmem; exact ⟨rfl, rfl, Or.inl rfl⟩
              rcases hStep with ⟨drKeyRand, hrand, rfl, rfl, hkr⟩
              right
              refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_,
                by rcases hkr with rfl | rfl <;> rfl, by rcases hkr with rfl | rfl <;> rfl,
                by rcases hkr with rfl | rfl <;> rfl, by rcases hkr with rfl | rfl <;> rfl⟩
              · intro s hs htest
                rcases List.mem_cons.mp hs with rfl | htl
                · simp [sessEntry] at htest
                · exact htl
              · intro x hx; rcases hkr with rfl | rfl <;> exact List.mem_cons_of_mem _ hx
              · refine cliAdapterKeyIndInv_of_initiate hP hInv sid u bnd t_init uEntry huEntry
                  hsid_prin h1 hspkSig hpqspkSig hc3 ss kemCt hEnc hkemCt drKeyReal drKeyRand
                  hreal_eq hreal hrand roCache' hro_nil { sessEntry with drKeyRand := drKeyRand }
                  rfl rfl rfl rfl rfl (by rcases hkr with rfl | rfl <;> rfl)
                  (by rcases hkr with rfl | rfl <;> rfl) (by rcases hkr with rfl | rfl <;> rfl)
                  (by rcases hkr with rfl | rfl <;> rfl) ?_
                intro s b h hmem_s; rcases hkr with rfl | rfl
                · rcases List.mem_cons.mp hmem_s with ⟨rfl, rfl, rfl⟩ | htl
                  · exact Or.inl ⟨rfl, rfl, rfl⟩
                  · exact Or.inr htl
                · exact Or.inr hmem_s
              · rcases hkr with rfl | rfl <;> rfl

end CryptoVerification.E2E
