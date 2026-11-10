/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhCouplingF
public import Computational.Proofs.SignalPqxdh.Security.Reductions
import Computational.Proofs.SignalPqxdh.Security.FgGapDh
import Computational.Proofs.SignalPqxdh.Security.FgGapDhIkCoupling
import Computational.Proofs.SignalPqxdh.Security.FgGapDhOpkCoupling
import Computational.Proofs.SpecLemmas.Assumptions.KemCorrect
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Hop 4 (`G3 → G3.5`): Fiedler–Günther `GapDH` Coupling

Combines the coupling of `FgGapDhCouplingA`–`F` with the per-index `GapDH` bounds to bound the
`G3` key-indistinguishability advantage and derive `pqxdh_key_ind_with`.
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

namespace Proofs.SignalPqxdh.Security

theorem isHonestUncorruptedPeer_some_imp (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) (v : ℕ)
    (h : isHonestUncorruptedPeer P principals ikB = some v) :
    ∃ vEntry, (v, vEntry) ∈ principals ∧ P.pow8 ikB = P.pow8 vEntry.ikAPk := by
  unfold isHonestUncorruptedPeer at h
  cases hFind : findHonestPrincipal P principals ikB with
  | none => rw [hFind] at h; nomatch h
  | some p =>
    rcases p with ⟨k, kEntry⟩
    rw [hFind] at h
    dsimp only at h
    split_ifs at h
    injection h with hk
    subst hk
    have h0 := List.find?_some hFind
    exact ⟨kEntry, List.mem_of_find?_eq_some hFind, beq_iff_eq.mp h0⟩

theorem checkBundleProvenance_imp (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    let (spkHon, opkHon, pqspkHon) := checkBundleProvenance P principals spkBundles opkEntries
      bundle
    (spkHon = true → ∃ k j bEntry, ((k, j), bEntry) ∈ spkBundles ∧ P.pow8 bEntry.spkPk = P.pow8
      bundle.spkB) ∧
    (opkHon = true → ∃ k j o oEntry opkPk, ((k, j, o), oEntry) ∈ opkEntries ∧
      bundle.opkB? = some opkPk ∧ P.pow8 oEntry.opkPk = P.pow8 opkPk.2) ∧
    (pqspkHon = true → ∃ k j kEntry bEntry, (k, kEntry) ∈ principals ∧
      ((k, j), bEntry) ∈ spkBundles ∧ P.pow8 bundle.ikB = P.pow8 kEntry.ikAPk ∧
      bEntry.pqspkPk = bundle.pqspkB) := by
  unfold checkBundleProvenance
  cases hFind : findHonestPrincipal P principals bundle.ikB with
  | none =>
    dsimp only
    exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  | some p =>
    rcases p with ⟨k, kEntry⟩
    have hkMem : (k, kEntry) ∈ principals := List.mem_of_find?_eq_some hFind
    have hkPow : P.pow8 bundle.ikB = P.pow8 kEntry.ikAPk := by
      have h0 := List.find?_some hFind
      exact beq_iff_eq.mp h0
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · intro hSpk
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hSpk
      rcases hSpk with ⟨⟨⟨u, j⟩, bEntry⟩, hbMem, rfl, hPow⟩
      exact ⟨u, j, bEntry, hbMem, hPow⟩
    · intro hOpk
      cases hOpt : bundle.opkB? with
      | none => rw [hOpt] at hOpk; nomatch hOpk
      | some pair =>
        rw [hOpt] at hOpk
        rcases pair with ⟨opkId, opkPk⟩
        simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hOpk
        rcases hOpk with ⟨⟨⟨u, j, o⟩, oEntry⟩, hoMem, rfl, hPow⟩
        exact ⟨u, j, o, oEntry, (opkId, opkPk), hoMem, rfl, hPow⟩
    · intro hPq
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hPq
      rcases hPq with ⟨⟨⟨u, j⟩, bEntry⟩, hbMem, rfl, hPqEq⟩
      exact ⟨u, j, kEntry, bEntry, hkMem, hbMem, hkPow, hPqEq⟩

def ValidTagStateCore {S : Setup} (P : Primitives) (adv : KeyIndAdvCutoffState S) : Prop :=
  ValidKeyStores S P adv.shCr.base ∧
  ValidLazyRand S P adv.shCr.base ∧
  (∀ s ∈ adv.shCr.base.sessions,
    ValidInitSession S P adv.shCr s ∧
    (isGameSpk P adv.shCr.base.spkBundles s.peerSpkPk || isAdvRegistered P adv.shCr.base.advKeys
      s.peerSpkPk) = true) ∧
  (∀ r ∈ adv.shCr.base.respSessions, ValidRespSession S P adv.shCr r)

theorem validKeyStores_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidKeyStores S P (KeyIndState.empty S secb) :=
  ⟨⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
   ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
   ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
   fun _ h => False.elim (List.not_mem_nil h),
   fun _ h => False.elim (List.not_mem_nil h),
   fun _ h => False.elim (List.not_mem_nil h),
   fun _ h => False.elim (List.not_mem_nil h)⟩

theorem validTagStateCore_empty (S : Setup) (P : Primitives) (secb : Bool) :
    ValidTagStateCore P { shCr := { base := KeyIndState.empty S secb }, advRoLog := [] } :=
  ⟨validKeyStores_empty S P secb,
   validLazyRand_empty S P secb,
   fun _ h => False.elim (List.not_mem_nil h),
   fun _ h => False.elim (List.not_mem_nil h)⟩

theorem validTagStateCore_of_map_flags {S : Setup} (P : Primitives)
    {adv adv' : KeyIndAdvCutoffState S} (hCore : ValidTagStateCore P adv)
    (fS : KeyIndInitiatorEntry S → KeyIndInitiatorEntry S)
    (fR : KeyIndRespEntry S → KeyIndRespEntry S)
    (hAdv : adv'.shCr = { adv.shCr with base := { adv.shCr.base with
      sessions := adv.shCr.base.sessions.map fS,
      respSessions := adv.shCr.base.respSessions.map fR } })
    (hfS : ∀ s, fS s = s ∨ fS s = { s with revealed := true } ∨ fS s = { s with tested := true })
    (hfR : ∀ r, fR r = r ∨ fR r = { r with revealed := true } ∨ fR r = { r with tested := true }) :
    ValidTagStateCore P adv' := by
  rcases hCore with ⟨hKS, hRand, hSess, hResp⟩
  refine ⟨by rw [hAdv]; exact hKS, ?_, ?_, ?_⟩
  · refine validLazyRand_of_map_flags P hRand fS fR
      (by rw [hAdv]) (by rw [hAdv]) (by rw [hAdv]) (by rw [hAdv]) (by rw [hAdv])
      (fun s => by rcases hfS s with h | h | h <;> rw [h])
      (fun s => by rcases hfS s with h | h | h <;> rw [h])
      (fun r => by rcases hfR r with h | h | h <;> rw [h])
      (fun r => by rcases hfR r with h | h | h <;> rw [h])
      (fun r => by rcases hfR r with h | h | h <;> rw [h])
      (fun s r =>
        by rcases hfS s with hs | hs | hs <;> rcases hfR r with hr | hr | hr <;> rw [hs, hr] <;>
        rfl)
  · intro s' hs'
    rw [hAdv] at hs' ⊢
    dsimp only at hs' ⊢
    rw [List.mem_map] at hs'
    rcases hs' with ⟨s, hs, rfl⟩
    have ⟨hV, hReg⟩ := hSess s hs
    rcases hfS s with h | h | h <;> rw [h] <;> exact ⟨hV, hReg⟩
  · intro r' hr'
    rw [hAdv] at hr' ⊢
    dsimp only at hr' ⊢
    rw [List.mem_map] at hr'
    rcases hr' with ⟨r, hr, rfl⟩
    have hV := hResp r hr
    rcases hfR r with h | h | h <;> rw [h] <;> exact hV

theorem validTagStateCore_of_shCrExtends_eq_sessions {S : Setup} (P : Primitives)
    {adv adv' : KeyIndAdvCutoffState S} (hCore : ValidTagStateCore P adv)
    (hKS' : ValidKeyStores S P adv'.shCr.base)
    (hExt : ShCrExtends adv.shCr adv'.shCr)
    (hSess : adv'.shCr.base.sessions = adv.shCr.base.sessions)
    (hResp : adv'.shCr.base.respSessions = adv.shCr.base.respSessions)
    (hOpk : ∀ x ∈ adv.shCr.base.usedRecvOPK, x ∈ adv'.shCr.base.usedRecvOPK)
    (hNoOpk : ∀ x ∈ adv.shCr.base.usedRecvNoOPK, x ∈ adv'.shCr.base.usedRecvNoOPK) :
    ValidTagStateCore P adv' := by
  rcases hCore with ⟨_, hRand, hSessV, hRespV⟩
  refine ⟨hKS', validLazyRand_of_eq_fields P hRand hSess hResp hExt.2.2.2.2 hOpk hNoOpk, ?_, ?_⟩
  · intro s hs
    rw [hSess] at hs
    have ⟨hV, hReg⟩ := hSessV s hs
    exact ⟨ValidInitSession.mono_shCrExtends P hExt hV,
      isGameSpk_or_isAdvRegistered_mono P hExt.1 hReg⟩
  · intro r hr
    rw [hResp] at hr
    exact ValidRespSession.mono_shCrExtends P hExt (hRespV r hr)

theorem validTagStateCore_of_tagStepRevealSessionKey {S : Setup} (P : Primitives)
    (sid : SessionId S) (adv : KeyIndAdvCutoffState S) (hCore : ValidTagStateCore P adv)
    {post : LazyPost} {adv' : KeyIndAdvCutoffState S}
    (hMem : (post, adv') ∈ support (tagStepRevealSessionKey S sid adv)) :
    ValidTagStateCore P adv' ∧ adv'.advRoLog = adv.advRoLog ∧
      adv'.shCr.sendCount = adv.shCr.sendCount := by
  unfold tagStepRevealSessionKey at hMem
  dsimp only at hMem
  cases h1 : adv.shCr.base.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    rw [h1] at hMem
    dsimp only at hMem
    split_ifs at hMem
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
      rcases hMem with ⟨_, rfl⟩
      exact ⟨hCore, rfl, rfl⟩
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
      rcases hMem with ⟨_, rfl⟩
      refine ⟨validTagStateCore_of_map_flags P hCore
        (fun s => if s.sid == sid then { s with revealed := true } else s) id
        (by simp) (fun s => by split_ifs <;> simp) (fun _ => Or.inl rfl), rfl, rfl⟩
  | none =>
    rw [h1] at hMem
    dsimp only at hMem
    cases h2 : adv.shCr.base.respSessions.find? (fun r => r.sid == sid) with
    | none =>
      rw [h2] at hMem
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
      rcases hMem with ⟨_, rfl⟩
      exact ⟨hCore, rfl, rfl⟩
    | some r =>
      rw [h2] at hMem
      dsimp only at hMem
      split_ifs at hMem
      · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
        rcases hMem with ⟨_, rfl⟩
        exact ⟨hCore, rfl, rfl⟩
      · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
        rcases hMem with ⟨_, rfl⟩
        refine ⟨validTagStateCore_of_map_flags P hCore id
          (fun x => if x.sid == sid then { x with revealed := true } else x)
          (by simp) (fun _ => Or.inl rfl) (fun x => by split_ifs <;> simp), rfl, rfl⟩

theorem validTagStateCore_of_tagStepTestSession {S : Setup} (P : Primitives)
    (testReal : Bool) (sid : SessionId S) (adv : KeyIndAdvCutoffState S)
    (hCore : ValidTagStateCore P adv)
    {post : LazyPost} {adv' : KeyIndAdvCutoffState S}
    (hMem : (post, adv') ∈ support (tagStepTestSession testReal S sid adv)) :
    ValidTagStateCore P adv' ∧ adv'.advRoLog = adv.advRoLog ∧
      adv'.shCr.sendCount = adv.shCr.sendCount := by
  unfold tagStepTestSession at hMem
  dsimp only at hMem
  cases hFresh : isKeyIndSessionTestable adv.shCr.base sid with
  | false =>
    rw [hFresh] at hMem
    simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
      at hMem
    rcases hMem with ⟨_, rfl⟩
    exact ⟨hCore, rfl, rfl⟩
  | true =>
    rw [hFresh] at hMem
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hMem
    cases h1 : adv.shCr.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      rw [h1] at hMem
      dsimp only at hMem
      have hAdvEq : adv' = { adv with shCr := { adv.shCr with base := { adv.shCr.base with
          sessions := adv.shCr.base.sessions.map (fun s =>
            if s.sid == sid then { s with tested := true } else s) } } } := by
        split_ifs at hMem <;>
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem <;>
          exact hMem.2
      rw [hAdvEq]
      refine ⟨validTagStateCore_of_map_flags P hCore
        (fun s => if s.sid == sid then { s with tested := true } else s) id
        (by simp) (fun s => by split_ifs <;> simp) (fun _ => Or.inl rfl), rfl, rfl⟩
    | none =>
      rw [h1] at hMem
      dsimp only at hMem
      cases h2 : adv.shCr.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        rw [h2] at hMem
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
        rcases hMem with ⟨_, rfl⟩
        exact ⟨hCore, rfl, rfl⟩
      | some r =>
        rw [h2] at hMem
        dsimp only at hMem
        have hAdvEq : adv' = { adv with shCr := { adv.shCr with base := { adv.shCr.base with
            respSessions := adv.shCr.base.respSessions.map (fun x =>
              if x.sid == sid then { x with tested := true } else x) } } } := by
          split_ifs at hMem <;>
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem <;>
            exact hMem.2
        rw [hAdvEq]
        refine ⟨validTagStateCore_of_map_flags P hCore id
          (fun x => if x.sid == sid then { x with tested := true } else x)
          (by simp) (fun _ => Or.inl rfl) (fun x => by split_ifs <;> simp), rfl, rfl⟩

theorem preCheckKeyInd_eq_some_imp {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S)
    {uEntry : PrincipalEntry}
    (h : preCheckKeyInd S P sid u bundle st = some uEntry) :
    sid ∉ st.sessions.map KeyIndInitiatorEntry.sid ∧
    (u.val, uEntry) ∈ st.principals ∧
    (isGameIdKey P st.principals bundle.ikB || isAdvRegistered P st.advKeys bundle.ikB) = true ∧
    (isGameSpk P st.spkBundles bundle.spkB || isAdvRegistered P st.advKeys bundle.spkB) = true ∧
    (match bundle.opkB? with
     | none => true
     | some (_, opkPk) => isGameOpk P st.opkEntries opkPk || isAdvRegistered P st.advKeys opkPk) =
         true := by
  unfold preCheckKeyInd at h
  cases hAny : st.sessions.any (fun e => e.sid == sid) with
  | true => rw [hAny] at h; nomatch h
  | false =>
    rw [hAny] at h
    dsimp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hFind : st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => rw [hFind] at h; nomatch h
    | some p =>
      rcases p with ⟨idx, e⟩
      rw [hFind] at h
      dsimp only at h
      cases hKosk : koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle with
      | false => rw [hKosk] at h; nomatch h
      | true =>
        rw [hKosk] at h
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        have h0 := List.find?_some hFind
        have hIdxEq : idx = u.val := beq_iff_eq.mp h0
        subst hIdxEq
        unfold koskBundleOk at hKosk
        simp only [Bool.and_eq_true] at hKosk
        refine ⟨?_, List.mem_of_find?_eq_some hFind, hKosk.1.1, hKosk.1.2, hKosk.2⟩
        intro hMem
        rw [List.mem_map] at hMem
        rcases hMem with ⟨s, hs, hSidEq⟩
        have hTrue : st.sessions.any (fun e => e.sid == sid) = true :=
          List.any_eq_true.mpr ⟨s, hs, beq_iff_eq.mpr hSidEq⟩
        rw [hAny] at hTrue; nomatch hTrue

theorem validTagStateCore_of_tagStepInitiate {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (adv : KeyIndAdvCutoffState S)
    (hCore : ValidTagStateCore P adv)
    (hSlot : initSessionSlotIdx sid < S.N_send_tot)
    (hSlotOpk : bundle.opkB?.isSome = true → initSessionSlotIdx sid < S.N_send_opk_tot)
    {post : LazyPost} {adv' : KeyIndAdvCutoffState S}
    (hMem : (post, adv') ∈ support (tagStepInitiate S P sid u bundle adv)) :
    ValidTagStateCore P adv' ∧ adv'.advRoLog = adv.advRoLog ∧
      adv'.shCr.sendCount ≤ adv.shCr.sendCount + 1 := by
  unfold tagStepInitiate at hMem
  dsimp only at hMem
  cases hPre : preCheckKeyInd S P sid u bundle adv.shCr.base with
  | none =>
    rw [hPre] at hMem
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
    rcases hMem with ⟨_, rfl⟩
    exact ⟨hCore, rfl, Nat.le_succ _⟩
  | some uEntry =>
    rw [hPre] at hMem
    dsimp only at hMem
    simp only [MonadAttach.mem_support_bind] at hMem
    rcases hMem with ⟨ekASk, hekASk, kemCoins, _, hMem⟩
    have hekLen : ekASk.length = 32 := length_of_mem_support_sampleScalar32_coll hekASk
    cases hSig : checkBundleSigs P adv.shCr.base.principals bundle with
    | false =>
      rw [hSig] at hMem
      simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
        at hMem
      rcases hMem with ⟨_, rfl⟩
      exact ⟨hCore, rfl, Nat.le_succ _⟩
    | true =>
      rw [hSig] at hMem
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hMem
      cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
      | none =>
        rw [hEnc] at hMem
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
        rcases hMem with ⟨_, rfl⟩
        have hExt : ShCrExtends adv.shCr { adv.shCr with sendCount := adv.shCr.sendCount + 1 } :=
          ⟨KeyStoreExtends.refl _, Nat.le_succ _, fun _ h => h, fun _ h => h, fun _ h => h⟩
        exact ⟨validTagStateCore_of_shCrExtends_eq_sessions P hCore hCore.1 hExt
          rfl rfl (fun _ h => h) (fun _ h => h), rfl, Nat.le_refl _⟩
      | some p =>
        rcases p with ⟨ss, kemCt⟩
        rw [hEnc] at hMem
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
        rcases hMem with ⟨_, hAdvEq⟩
        rcases preCheckKeyInd_eq_some_imp P sid u bundle adv.shCr.base hPre with
          ⟨hSidFresh, huMem, hKoskIk, hKoskSpk, hKoskOpk⟩
        rcases hCore with ⟨hKS, hRand, hSessV, hRespV⟩
        have hExt : ShCrExtends adv.shCr adv'.shCr := by
          rw [hAdvEq]
          exact ⟨⟨fun _ e h => ⟨e, h, rfl, rfl⟩,
            fun _ b h => ⟨b, h, rfl, rfl, rfl, rfl⟩,
            fun _ o h => ⟨o, h, rfl, rfl⟩,
            fun _ h => h⟩, Nat.le_succ _, fun _ h => List.mem_cons_of_mem _ h,
            fun _ h => h, fun _ h => h⟩
        rw [hAdvEq]
        refine ⟨⟨hKS, ?_, ?_, ?_⟩, rfl, Nat.le_refl _⟩
        · refine validLazyRand_cons_session P hRand _ rfl rfl (fun _ h => h) (fun _ h => h)
            (fun _ h => h) hSidFresh ?_
          cases hFindPart : adv.shCr.base.respSessions.find? (fun r => keyIndPartner P _ r) with
          | some r0 =>
            exact Or.inl ⟨r0, List.mem_of_find?_eq_some hFindPart,
              List.find?_some hFindPart, rfl⟩
          | none =>
            exact Or.inr ⟨fun r hr => Bool.eq_false_iff.mpr (List.find?_eq_none.mp hFindPart r hr),
              freshPidBytes_length adv.shCr.base⟩
        · intro s hs
          rcases List.mem_cons.mp hs with rfl | hsOld
          · refine ⟨⟨hSlot, hekLen, rfl, rfl,
              fun v hv => isHonestUncorruptedPeer_some_imp P _ _ v hv, ?_, ?_, ?_,
              exists_sk_of_isGameIdKey_or_isAdvRegistered P hKS hKoskIk,
              exists_sk_of_isGameSpk_or_isAdvRegistered P hKS hKoskSpk, ?_, ?_⟩, hKoskSpk⟩
            · exact (checkBundleProvenance_imp P adv.shCr.base.principals
                adv.shCr.base.spkBundles adv.shCr.base.opkEntries bundle).1
            · intro hOpkHon
              rcases (checkBundleProvenance_imp P adv.shCr.base.principals
                adv.shCr.base.spkBundles adv.shCr.base.opkEntries bundle).2.1 hOpkHon with
                ⟨k, j, o, oEntry, opkPair, hoMem, hOptEq, hPowEq⟩
              exact ⟨hSlotOpk (by simp [hOptEq]), k, j, o, oEntry, opkPair.2, hoMem,
                by simp [hOptEq], hPowEq⟩
            · exact (checkBundleProvenance_imp P adv.shCr.base.principals
                adv.shCr.base.spkBundles adv.shCr.base.opkEntries bundle).2.2
            · intro opkPk hOptEq
              cases hOpt : bundle.opkB? with
              | none => simp [hOpt] at hOptEq
              | some pair =>
                rcases pair with ⟨opkId, opkPk0⟩
                rw [hOpt] at hKoskOpk hOptEq
                injection hOptEq with hPkEq; subst hPkEq
                exact exists_sk_of_isGameOpk_or_isAdvRegistered P hKS hKoskOpk
            · refine ⟨u.val, uEntry, kemCoins, ss,
                { sendIdx := adv.shCr.sendCount, sid := sid, pqspkPk := bundle.pqspkB,
                  kemCt := kemCt, kemSs := ss },
                huMem, rfl, hEnc, List.mem_cons_self, Nat.lt_succ_self _,
                rfl, rfl, rfl, rfl, ?_⟩
              dsimp only [tagDRKey_rootKey]
              congr 1
              cases bundle.opkB? <;> rfl
          · have ⟨hV, hReg⟩ := hSessV s hsOld
            rw [← hAdvEq]
            exact ⟨ValidInitSession.mono_shCrExtends P hExt hV,
              isGameSpk_or_isAdvRegistered_mono P hExt.1 hReg⟩
        · intro r hr
          rw [← hAdvEq]
          exact ValidRespSession.mono_shCrExtends P hExt (hRespV r hr)

theorem validKeyStores_map_consumed {S : Setup} (P : Primitives) (key : Nat × Nat × Nat)
    {st st' : KeyIndState S} (hKS : ValidKeyStores S P st)
    (hPrins : st'.principals = st.principals)
    (hSpks : st'.spkBundles = st.spkBundles)
    (hOpks : st'.opkEntries = st.opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e)))
    (hAdvs : st'.advKeys = st.advKeys) :
    ValidKeyStores S P st' := by
  rcases hKS with ⟨hVP, hVS, hVO, hPrinV, hSpkV, hOpkV, hAdvV⟩
  refine ⟨hPrins ▸ hVP, hSpks ▸ hVS,
    hOpks ▸ (validOpkEntries_map_consumed S P key st.opkEntries hVO).1,
    hPrins ▸ hPrinV, ?_, ?_, hAdvs ▸ hAdvV⟩
  · intro kv hkv
    rw [hSpks] at hkv
    rw [hPrins]
    exact hSpkV kv hkv
  · intro kv hkv
    rw [hOpks, List.mem_map] at hkv
    rcases hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
    dsimp only at hEq
    split_ifs at hEq <;> (subst hEq; exact hOpkV (idx, e) heMem)

theorem keyStoreExtends_map_consumed {S : Setup} (key : Nat × Nat × Nat)
    {st st' : KeyIndState S}
    (hPrins : st'.principals = st.principals)
    (hSpks : st'.spkBundles = st.spkBundles)
    (hOpks : st'.opkEntries = st.opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e)))
    (hAdvs : st'.advKeys = st.advKeys) :
    KeyStoreExtends st st' := by
  refine ⟨fun u e h => ⟨e, hPrins ▸ h, rfl, rfl⟩,
    fun k b h => ⟨b, hSpks ▸ h, rfl, rfl, rfl, rfl⟩, ?_,
    fun kv h => hAdvs ▸ h⟩
  intro k o h
  rw [hOpks]
  refine ⟨if k == key then { o with consumed := true } else o, ?_,
    by split_ifs <;> rfl, by split_ifs <;> rfl⟩
  rw [List.mem_map]
  exact ⟨(k, o), h, by dsimp only; split_ifs <;> rfl⟩

theorem validTagStateCore_of_tagStepAcceptOPK {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (adv : KeyIndAdvCutoffState S)
    (hCore : ValidTagStateCore P adv)
    {post : LazyPost} {adv' : KeyIndAdvCutoffState S}
    (hMem : (post, adv') ∈ support (tagStepAcceptOPK S P k j o hdr adv)) :
    ValidTagStateCore P adv' ∧ adv'.advRoLog = adv.advRoLog ∧
      adv'.shCr.sendCount = adv.shCr.sendCount := by
  unfold tagStepAcceptOPK at hMem
  dsimp only at hMem
  cases hHdr : (hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) with
  | false =>
    rw [hHdr] at hMem
    simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
      at hMem
    rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
  | true =>
    rw [hHdr] at hMem
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hMem
    cases hUsed : adv.shCr.base.usedRecvOPK.contains (k.val, j.val, o.val) with
    | true =>
      rw [hUsed] at hMem
      simp only [↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
      rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
    | false =>
      rw [hUsed] at hMem
      simp only [Bool.false_eq_true, ↓reduceIte] at hMem
      cases hKosk : koskSenderOk P adv.shCr.base.principals adv.shCr.base.advKeys hdr.ikAPk with
      | false =>
        rw [hKosk] at hMem
        simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
          at hMem
        rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
      | true =>
        rw [hKosk] at hMem
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hMem
        cases hkFind : adv.shCr.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          rw [hkFind] at hMem
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
          rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
        | some pkPair =>
          rcases pkPair with ⟨kIdx, kEntry⟩
          rw [hkFind] at hMem; dsimp only at hMem
          cases hbFind : adv.shCr.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            rw [hbFind] at hMem
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
            rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
          | some pbPair =>
            rcases pbPair with ⟨bIdx, bEntry⟩
            rw [hbFind] at hMem; dsimp only at hMem
            cases hoFind : adv.shCr.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val,
              o.val)) with
            | none =>
              rw [hoFind] at hMem
              simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
              rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
            | some poPair =>
              rcases poPair with ⟨oIdx, oEntry⟩
              rw [hoFind] at hMem; dsimp only at hMem
              cases hCons : oEntry.consumed with
              | true =>
                rw [hCons] at hMem
                simp only [↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
                rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
              | false =>
                rw [hCons] at hMem
                simp only [Bool.false_eq_true, ↓reduceIte] at hMem
                cases hAcc : Model.acceptKeys P {
                  ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk,
                  spkBSk := bEntry.spkSk, spkBPk := bEntry.spkPk,
                  opkBSk? := some oEntry.opkSk,
                  pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
                  trustedPeer := true,
                  replayOk := (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val
                    hdr.pqspkId hdr.spkId hdr.ekAPk).1,
                  hdr := hdr } with
                | none =>
                  rw [hAcc] at hMem
                  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
                  rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
                | some dk =>
                  rw [hAcc] at hMem; dsimp only at hMem
                  cases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                  | none =>
                    rw [hDec] at hMem
                    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
                    rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
                  | some ss =>
                    rw [hDec] at hMem
                    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
                    rcases hMem with ⟨_, hAdvEq⟩
                    rcases hCore with ⟨hKS, hRand, hSessV, hRespV⟩
                    simp only [Bool.and_eq_true, beq_iff_eq] at hHdr
                    rcases hHdr with ⟨⟨⟨⟨hSpkId, hPqId⟩, hOpkId⟩, hIkLen⟩, hEkLen⟩
                    have ⟨hReplayOk, hEkCanon⟩ := acceptKeys_eq_some_imp P _ hAcc
                    have ⟨hNotKyber, hTriplesEq⟩ :
                        (k.val, hdr.pqspkId, hdr.spkId, hdr.ekAPk) ∉ adv.shCr.base.seenKyberBaseKeys
                          ∧
                        (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val
                          hdr.pqspkId hdr.spkId hdr.ekAPk).2 =
                          (k.val, hdr.pqspkId, hdr.spkId, hdr.ekAPk) ::
                            adv.shCr.base.seenKyberBaseKeys :=
                      checkAndMarkKyberUsed_eq_imp adv.shCr.base.seenKyberBaseKeys k.val
                        hdr.pqspkId hdr.spkId hdr.ekAPk (Prod.ext rfl rfl) hReplayOk
                    have hk0 := List.find?_some hkFind
                    have hkEq : kIdx = k.val := beq_iff_eq.mp hk0
                    subst hkEq
                    have hkMem : (k.val, kEntry) ∈ adv.shCr.base.principals :=
                      List.mem_of_find?_eq_some hkFind
                    have hb0 := List.find?_some hbFind
                    have hbEq : bIdx = (k.val, j.val) := beq_iff_eq.mp hb0
                    subst hbEq
                    have hbMem : ((k.val, j.val), bEntry) ∈ adv.shCr.base.spkBundles :=
                      List.mem_of_find?_eq_some hbFind
                    have ho0 := List.find?_some hoFind
                    have hoEq : oIdx = (k.val, j.val, o.val) := beq_iff_eq.mp ho0
                    subst hoEq
                    have hoMem : ((k.val, j.val, o.val), oEntry) ∈ adv.shCr.base.opkEntries :=
                      List.mem_of_find?_eq_some hoFind
                    have hKS' : ValidKeyStores S P adv'.shCr.base :=
                      validKeyStores_map_consumed P (k.val, j.val, o.val) hKS
                        (by rw [hAdvEq]) (by rw [hAdvEq]) (by rw [hAdvEq]) (by rw [hAdvEq])
                    have hExt : ShCrExtends adv.shCr adv'.shCr := by
                      refine ⟨keyStoreExtends_map_consumed (k.val, j.val, o.val)
                        (by rw [hAdvEq]) (by rw [hAdvEq]) (by rw [hAdvEq]) (by rw [hAdvEq]),
                        by rw [hAdvEq],
                        fun _ h => by rw [hAdvEq]; exact h,
                        fun _ h => by rw [hAdvEq]; exact List.mem_cons_of_mem _ h,
                        fun x hx => by
                          rw [hAdvEq]
                          change x ∈ (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val
                            hdr.pqspkId hdr.spkId hdr.ekAPk).2
                          rw [hTriplesEq]
                          exact List.mem_cons_of_mem _ hx⟩
                    rw [hAdvEq]
                    refine ⟨⟨by rw [← hAdvEq]; exact hKS', ?_, ?_, ?_⟩, rfl, rfl⟩
                    · refine validLazyRand_cons_respSession P hRand _ rfl rfl
                        (fun x hx => by
                          change x ∈ (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val
                            hdr.pqspkId hdr.spkId hdr.ekAPk).2
                          rw [hTriplesEq]
                          exact List.mem_cons_of_mem _ hx)
                        (fun x hx => List.mem_cons_of_mem _ hx)
                        (fun x hx => hx) ?_ ?_ ?_ ?_ (fun _ _ _ h => by nomatch h) ?_
                      · intro hInSid
                        rw [List.mem_map] at hInSid
                        rcases hInSid with ⟨r', hr', hSidEq⟩
                        have hInUsed := hRand.resp_used_opk r' hr' k j o hSidEq
                        rw [List.contains_iff_mem.mpr hInUsed] at hUsed
                        nomatch hUsed
                      · intro hInBundle
                        rw [List.mem_map] at hInBundle
                        rcases hInBundle with ⟨r', hr', hPairEq⟩
                        injection hPairEq with hIdxEq hEkEq
                        have hInKyber := hRand.resp_kyber_mem r' hr' k.val j.val hIdxEq
                        dsimp only at hEkEq
                        rw [hEkEq] at hInKyber
                        rw [hPqId, hSpkId] at hNotKyber
                        exact hNotKyber hInKyber
                      · intro k0 j0 hIdx0
                        dsimp only [respBundleIdx] at hIdx0
                        injection hIdx0 with hPair0
                        injection hPair0 with hk0 hj0
                        subst hk0; subst hj0
                        change (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val, hdr.ekAPk) ∈
                          (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId
                            hdr.spkId hdr.ekAPk).2
                        rw [hTriplesEq, hPqId, hSpkId]
                        exact List.mem_cons_self
                      · intro k0 j0 o0 hSid0
                        injection hSid0 with hk0 hj0 ho0
                        cases hk0; cases hj0; cases ho0
                        exact List.mem_cons_self
                      · cases hFindPart : adv.shCr.base.sessions.find? (fun s => keyIndPartner P s
                          _) with
                        | some s0 =>
                          have hPart0 := List.find?_some hFindPart
                          exact Or.inl ⟨s0, List.mem_of_find?_eq_some hFindPart, hPart0, rfl⟩
                        | none =>
                          exact Or.inr ⟨fun s hs => Bool.eq_false_iff.mpr (List.find?_eq_none.mp
                            hFindPart s hs),
                            freshPidBytes_length adv.shCr.base⟩
                    · intro s hs
                      have ⟨hV, hReg⟩ := hSessV s hs
                      rw [← hAdvEq]
                      exact ⟨ValidInitSession.mono_shCrExtends P hExt hV,
                        isGameSpk_or_isAdvRegistered_mono P hExt.1 hReg⟩
                    · intro r hr
                      rcases List.mem_cons.mp hr with rfl | hrOld
                      · refine ⟨k, j, kEntry, bEntry, ss,
                          { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                            pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
                            kemCt := hdr.kemCt, kemSs := ss },
                          rfl, hkMem, hbMem, ?_, rfl, rfl, rfl, hSpkId, hPqId, hIkLen, hEkLen,
                            hEkCanon,
                          exists_sk_of_isGameIdKey_or_isAdvRegistered P hKS hKosk,
                          hDec, List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, ?_⟩
                        · change (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val, hdr.ekAPk) ∈
                            (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId
                              hdr.spkId hdr.ekAPk).2
                          rw [hTriplesEq, hPqId, hSpkId]
                          exact List.mem_cons_self
                        · refine Or.inr ⟨o.val,
                            { oEntry with consumed := true }, ?_, rfl, hOpkId, rfl⟩
                          dsimp only
                          rw [List.mem_map]
                          exact ⟨((k.val, j.val, o.val), oEntry), hoMem, by simp⟩
                      · rw [← hAdvEq]
                        exact ValidRespSession.mono_shCrExtends P hExt (hRespV r hrOld)

theorem validTagStateCore_of_tagStepAcceptNoOPK {S : Setup} (P : Primitives)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (adv : KeyIndAdvCutoffState S)
    (hCore : ValidTagStateCore P adv)
    {post : LazyPost} {adv' : KeyIndAdvCutoffState S}
    (hMem : (post, adv') ∈ support (tagStepAcceptNoOPK S P k j l hdr adv)) :
    ValidTagStateCore P adv' ∧ adv'.advRoLog = adv.advRoLog ∧
      adv'.shCr.sendCount = adv.shCr.sendCount := by
  unfold tagStepAcceptNoOPK at hMem
  dsimp only at hMem
  cases hHdr : (hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) with
  | false =>
    rw [hHdr] at hMem
    simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
      at hMem
    rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
  | true =>
    rw [hHdr] at hMem
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hMem
    cases hUsed : adv.shCr.base.usedRecvNoOPK.contains (k.val, j.val, l.val) with
    | true =>
      rw [hUsed] at hMem
      simp only [↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
      rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
    | false =>
      rw [hUsed] at hMem
      simp only [Bool.false_eq_true, ↓reduceIte] at hMem
      cases hKosk : koskSenderOk P adv.shCr.base.principals adv.shCr.base.advKeys hdr.ikAPk with
      | false =>
        rw [hKosk] at hMem
        simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
          at hMem
        rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
      | true =>
        rw [hKosk] at hMem
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hMem
        cases hkFind : adv.shCr.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          rw [hkFind] at hMem
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
          rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
        | some pkPair =>
          rcases pkPair with ⟨kIdx, kEntry⟩
          rw [hkFind] at hMem; dsimp only at hMem
          cases hbFind : adv.shCr.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            rw [hbFind] at hMem
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
            rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
          | some pbPair =>
            rcases pbPair with ⟨bIdx, bEntry⟩
            rw [hbFind] at hMem; dsimp only at hMem
            cases hAcc : Model.acceptKeys P {
              ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk,
              spkBSk := bEntry.spkSk, spkBPk := bEntry.spkPk,
              opkBSk? := none,
              pqspkBSk := bEntry.pqspkSk, pqspkBPk := bEntry.pqspkPk,
              trustedPeer := true,
              replayOk := (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId
                hdr.spkId hdr.ekAPk).1,
              hdr := hdr } with
            | none =>
              rw [hAcc] at hMem
              simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
              rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
            | some dk =>
              rw [hAcc] at hMem; dsimp only at hMem
              cases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
              | none =>
                rw [hDec] at hMem
                simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
                rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, rfl, rfl⟩
              | some ss =>
                rw [hDec] at hMem
                simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
                rcases hMem with ⟨_, hAdvEq⟩
                rcases hCore with ⟨hKS, hRand, hSessV, hRespV⟩
                simp only [Bool.and_eq_true, beq_iff_eq] at hHdr
                rcases hHdr with ⟨⟨⟨⟨hSpkId, hPqId⟩, hOpkId⟩, hIkLen⟩, hEkLen⟩
                have ⟨hReplayOk, hEkCanon⟩ := acceptKeys_eq_some_imp P _ hAcc
                have ⟨hNotKyber, hTriplesEq⟩ :
                    (k.val, hdr.pqspkId, hdr.spkId, hdr.ekAPk) ∉ adv.shCr.base.seenKyberBaseKeys ∧
                    (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val
                      hdr.pqspkId hdr.spkId hdr.ekAPk).2 =
                      (k.val, hdr.pqspkId, hdr.spkId, hdr.ekAPk) :: adv.shCr.base.seenKyberBaseKeys
                        :=
                  checkAndMarkKyberUsed_eq_imp adv.shCr.base.seenKyberBaseKeys k.val
                    hdr.pqspkId hdr.spkId hdr.ekAPk (Prod.ext rfl rfl) hReplayOk
                have hk0 := List.find?_some hkFind
                have hkEq : kIdx = k.val := beq_iff_eq.mp hk0
                subst hkEq
                have hkMem : (k.val, kEntry) ∈ adv.shCr.base.principals :=
                  List.mem_of_find?_eq_some hkFind
                have hb0 := List.find?_some hbFind
                have hbEq : bIdx = (k.val, j.val) := beq_iff_eq.mp hb0
                subst hbEq
                have hbMem : ((k.val, j.val), bEntry) ∈ adv.shCr.base.spkBundles :=
                  List.mem_of_find?_eq_some hbFind
                have hExt : ShCrExtends adv.shCr adv'.shCr := by
                  rw [hAdvEq]
                  exact ⟨⟨fun _ e h => ⟨e, h, rfl, rfl⟩,
                    fun _ b h => ⟨b, h, rfl, rfl, rfl, rfl⟩,
                    fun _ o h => ⟨o, h, rfl, rfl⟩,
                    fun _ h => h⟩,
                    Nat.le_refl _,
                    fun _ h => h,
                    fun _ h => List.mem_cons_of_mem _ h,
                    fun x hx => by
                      change x ∈ (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val
                        hdr.pqspkId hdr.spkId hdr.ekAPk).2
                      rw [hTriplesEq]
                      exact List.mem_cons_of_mem _ hx⟩
                rw [hAdvEq]
                refine ⟨⟨hKS, ?_, ?_, ?_⟩, rfl, rfl⟩
                · refine validLazyRand_cons_respSession P hRand _ rfl rfl
                    (fun x hx => by
                      change x ∈ (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val
                        hdr.pqspkId hdr.spkId hdr.ekAPk).2
                      rw [hTriplesEq]
                      exact List.mem_cons_of_mem _ hx)
                    (fun x hx => hx)
                    (fun x hx => List.mem_cons_of_mem _ hx) ?_ ?_ ?_ (fun _ _ _ h => by nomatch h)
                      ?_ ?_
                  · intro hInSid
                    rw [List.mem_map] at hInSid
                    rcases hInSid with ⟨r', hr', hSidEq⟩
                    have hInUsed := hRand.resp_used_no_opk r' hr' k j l hSidEq
                    rw [List.contains_iff_mem.mpr hInUsed] at hUsed
                    nomatch hUsed
                  · intro hInBundle
                    rw [List.mem_map] at hInBundle
                    rcases hInBundle with ⟨r', hr', hPairEq⟩
                    injection hPairEq with hIdxEq hEkEq
                    have hInKyber := hRand.resp_kyber_mem r' hr' k.val j.val hIdxEq
                    dsimp only at hEkEq
                    rw [hEkEq] at hInKyber
                    rw [hPqId, hSpkId] at hNotKyber
                    exact hNotKyber hInKyber
                  · intro k0 j0 hIdx0
                    dsimp only [respBundleIdx] at hIdx0
                    injection hIdx0 with hPair0
                    injection hPair0 with hk0 hj0
                    subst hk0; subst hj0
                    change (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val, hdr.ekAPk) ∈
                      (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId
                        hdr.spkId hdr.ekAPk).2
                    rw [hTriplesEq, hPqId, hSpkId]
                    exact List.mem_cons_self
                  · intro k0 j0 l0 hSid0
                    injection hSid0 with hk0 hj0 hl0
                    cases hk0; cases hj0; cases hl0
                    exact List.mem_cons_self
                  · cases hFindPart : adv.shCr.base.sessions.find? (fun s => keyIndPartner P s _)
                      with
                    | some s0 =>
                      have hPart0 := List.find?_some hFindPart
                      exact Or.inl ⟨s0, List.mem_of_find?_eq_some hFindPart, hPart0, rfl⟩
                    | none =>
                      exact Or.inr ⟨fun s hs => Bool.eq_false_iff.mpr (List.find?_eq_none.mp
                        hFindPart s hs),
                        freshPidBytes_length adv.shCr.base⟩
                · intro s hs
                  have ⟨hV, hReg⟩ := hSessV s hs
                  rw [← hAdvEq]
                  exact ⟨ValidInitSession.mono_shCrExtends P hExt hV,
                    isGameSpk_or_isAdvRegistered_mono P hExt.1 hReg⟩
                · intro r hr
                  rcases List.mem_cons.mp hr with rfl | hrOld
                  · refine ⟨k, j, kEntry, bEntry, ss,
                      { bIdx := spkBundleFlatIdx S k j, k := k.val, j := j.val,
                        pqspkPk := bEntry.pqspkPk, pqspkSk := bEntry.pqspkSk,
                        kemCt := hdr.kemCt, kemSs := ss },
                      rfl, hkMem, hbMem, ?_, rfl, rfl, rfl, hSpkId, hPqId, hIkLen, hEkLen, hEkCanon,
                      exists_sk_of_isGameIdKey_or_isAdvRegistered P hKS hKosk,
                      hDec, List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, hOpkId, rfl⟩⟩
                    change (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val, hdr.ekAPk) ∈
                      (checkAndMarkKyberBaseKeySeen adv.shCr.base.seenKyberBaseKeys k.val hdr.pqspkId
                        hdr.spkId hdr.ekAPk).2
                    rw [hTriplesEq, hPqId, hSpkId]
                    exact List.mem_cons_self
                  · rw [← hAdvEq]
                    exact ValidRespSession.mono_shCrExtends P hExt (hRespV r hrOld)

theorem validTagStateCore_of_tagStepView {S : Setup} (P : Primitives)
    (testReal : Bool) (q : KeyIndQuery S) (adv : KeyIndAdvCutoffState S)
    (hCore : ValidTagStateCore P adv)
    {post : LazyPost} {adv' : KeyIndAdvCutoffState S}
    (hMem : (post, adv') ∈ support (tagStepView testReal S P q adv)) :
    ValidTagStateCore P adv' ∧
    adv'.advRoLog.length ≤ adv.advRoLog.length + (if isKeyIndRoQuery (.inr q) then 1 else 0) ∧
    adv'.shCr.sendCount ≤ adv.shCr.sendCount + (if isKeyIndSendQuery (.inr q) then 1 else 0) := by
  cases q with
  | initiateOPK u i bundle =>
    unfold tagStepView at hMem; dsimp only at hMem
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    split_ifs at hMem
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
      rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, Nat.le_refl _, Nat.le_succ _⟩
    · rcases validTagStateCore_of_tagStepInitiate P (.sendOPK u i) u bundle adv hCore
        (Nat.lt_of_lt_of_le (initSessionSlotIdx_sendOPK_lt u i) (Nat.le_add_right _ _))
        (fun _ => initSessionSlotIdx_sendOPK_lt u i) hMem with
        ⟨hC, hRo, hSend⟩
      exact ⟨hC, by rw [hRo], hSend⟩
  | initiateNoOPK u i bundle =>
    unfold tagStepView at hMem; dsimp only at hMem
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    split_ifs at hMem with hOpkSome
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
      rcases hMem with ⟨_, rfl⟩; exact ⟨hCore, Nat.le_refl _, Nat.le_succ _⟩
    · rcases validTagStateCore_of_tagStepInitiate P (.sendNoOPK u i) u bundle adv hCore
        (initSessionSlotIdx_sendNoOPK_lt u i) (fun h => False.elim (hOpkSome h)) hMem with
        ⟨hC, hRo, hSend⟩
      exact ⟨hC, by rw [hRo], hSend⟩
  | acceptOPK k j o hdr =>
    unfold tagStepView at hMem
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    rcases validTagStateCore_of_tagStepAcceptOPK P k j o hdr adv hCore hMem with ⟨hC, hRo, hSend⟩
    exact ⟨hC, by rw [hRo], by rw [hSend]⟩
  | acceptNoOPK k j l hdr =>
    unfold tagStepView at hMem
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    rcases validTagStateCore_of_tagStepAcceptNoOPK P k j l hdr adv hCore hMem with ⟨hC, hRo, hSend⟩
    exact ⟨hC, by rw [hRo], by rw [hSend]⟩
  | revealSessionKey sid =>
    unfold tagStepView at hMem
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    rcases validTagStateCore_of_tagStepRevealSessionKey P sid adv hCore hMem with ⟨hC, hRo, hSend⟩
    exact ⟨hC, by rw [hRo], by rw [hSend]⟩
  | testSession sid =>
    unfold tagStepView at hMem
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    rcases validTagStateCore_of_tagStepTestSession P testReal sid adv hCore hMem with ⟨hC, hRo,
      hSend⟩
    exact ⟨hC, by rw [hRo], by rw [hSend]⟩
  | roQuery sec =>
    unfold tagStepView at hMem
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
    rcases hMem with ⟨_, rfl⟩
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, List.length_cons, Nat.add_zero]
    exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
  | revealDhSecrets =>
    unfold tagStepView pqxdhKeyIndAdvG3Impl liftKeyIndAdvShCr pqxdhKeyIndShCrImpl
      liftKeyIndShCrBase liftShCrBase pqxdhKeyIndImpl at hMem
    simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, ↓reduceIte, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
    rcases hMem with ⟨_, ⟨_, rfl⟩, _, rfl⟩
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
  | initPrin u =>
    dsimp only [tagStepView] at hMem
    have hRun : (pqxdhKeyIndAdvG3Impl S P (.initPrin u)).run adv =
        (do
          let (r, base') ← (pqxdhKeyIndImpl true S P (.initPrin u)).run adv.shCr.base
          return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
      simp [pqxdhKeyIndAdvG3Impl, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl,
        liftKeyIndShCrBase, liftShCrBase, StateT.run]; rfl
    rw [hRun] at hMem
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
    rcases hMem with ⟨⟨r1, st1⟩, hSt1, _, rfl⟩
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    unfold pqxdhKeyIndImpl at hSt1; dsimp only at hSt1
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hSt1
    cases hFresh : adv.shCr.base.principals.any (fun (idx, _) => idx == u.val) with
    | true =>
      rw [hFresh] at hSt1
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
        at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
    | false =>
      rw [hFresh] at hSt1
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
      rcases hSt1 with ⟨sec0, hSec0, secSign, _, _, rfl⟩
      rcases hCore.1 with ⟨hVP, hVS, hVO, hPrinV, hSpkV, hOpkV, hAdvV⟩
      refine ⟨validTagStateCore_of_shCrExtends_eq_sessions P hCore ?_ ?_ rfl rfl
        (fun _ h => h) (fun _ h => h), Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨(validPrincipals_cons S u _ adv.shCr.base.principals hVP hFresh).1,
          hVS, hVO, ?_, ?_, hOpkV, hAdvV⟩
        · intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hOld
          · exact ⟨length_of_mem_support_sampleScalar32_coll hSec0, rfl⟩
          · exact hPrinV kv hOld
        · intro kv hkv
          rcases hSpkV kv hkv with ⟨h1, h2, ⟨uE, huE⟩, h4⟩
          exact ⟨h1, h2, ⟨uE, List.mem_cons_of_mem _ huE⟩, h4⟩
      · exact ⟨⟨fun _ e h => ⟨e, List.mem_cons_of_mem _ h, rfl, rfl⟩,
          fun _ b h => ⟨b, h, rfl, rfl, rfl, rfl⟩,
          fun _ o h => ⟨o, h, rfl, rfl⟩,
          fun _ h => h⟩, Nat.le_refl _, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | corruptIK u =>
    dsimp only [tagStepView] at hMem
    have hRun : (pqxdhKeyIndAdvG3Impl S P (.corruptIK u)).run adv =
        (do
          let (r, base') ← (pqxdhKeyIndImpl true S P (.corruptIK u)).run adv.shCr.base
          return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
      simp [pqxdhKeyIndAdvG3Impl, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl,
        liftKeyIndShCrBase, liftShCrBase, StateT.run]; rfl
    rw [hRun] at hMem
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
    rcases hMem with ⟨⟨r1, st1⟩, hSt1, _, rfl⟩
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    unfold pqxdhKeyIndImpl at hSt1; dsimp only at hSt1
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hSt1
    cases hFind : adv.shCr.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      rw [hFind] at hSt1
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
    | some p =>
      rcases p with ⟨_, entry⟩
      rw [hFind] at hSt1; dsimp only at hSt1
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      rcases hCore.1 with ⟨hVP, hVS, hVO, hPrinV, hSpkV, hOpkV, hAdvV⟩
      refine ⟨validTagStateCore_of_shCrExtends_eq_sessions P hCore ?_ ?_ rfl rfl
        (fun _ h => h) (fun _ h => h), Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨(validPrincipals_map_corrupted S P u.val adv.shCr.base.principals hVP).1,
          hVS, hVO, ?_, ?_, hOpkV, hAdvV⟩
        · intro kv hkv
          dsimp only at hkv; rw [List.mem_map] at hkv
          rcases hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
          dsimp only at hEq
          split_ifs at hEq <;> (subst hEq; exact hPrinV (idx, e) heMem)
        · intro kv hkv
          rcases hSpkV kv hkv with ⟨h1, h2, ⟨uE, huE⟩, h4⟩
          refine ⟨h1, h2, ⟨if kv.1.1 == u.val then { uE with corrupted := true } else uE, ?_⟩, h4⟩
          dsimp only; rw [List.mem_map]
          exact ⟨(kv.1.1, uE), huE, by dsimp only; split_ifs <;> rfl⟩
      · refine ⟨⟨?_, fun _ b h => ⟨b, h, rfl, rfl, rfl, rfl⟩,
          fun _ o h => ⟨o, h, rfl, rfl⟩, fun _ h => h⟩,
          Nat.le_refl _, fun _ h => h, fun _ h => h, fun _ h => h⟩
        intro idx e he
        refine ⟨if idx == u.val then { e with corrupted := true } else e, ?_,
          by split_ifs <;> rfl, by split_ifs <;> rfl⟩
        dsimp only; rw [List.mem_map]
        exact ⟨(idx, e), he, by dsimp only; split_ifs <;> rfl⟩
  | genSPK u j =>
    dsimp only [tagStepView] at hMem
    have hRun : (pqxdhKeyIndAdvG3Impl S P (.genSPK u j)).run adv =
        (do
          let (r, base') ← (genSpkBaseGeneric P KeyIndState.principals KeyIndState.spkBundles
            (fun st bs =>
              { st with spkBundles := bs }) KeyIndResponse.noneResp KeyIndResponse.bundleResp
            u j).run adv.shCr.base
          return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
      simp [pqxdhKeyIndAdvG3Impl, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl,
        runKeyIndShCrGenSPK, runShCrGenSPKGeneric, liftShCrBase, StateT.run]; rfl
    rw [hRun] at hMem
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
    rcases hMem with ⟨⟨r1, st1⟩, hSt1, _, rfl⟩
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    unfold genSpkBaseGeneric at hSt1; dsimp only at hSt1
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hSt1
    cases hFresh : adv.shCr.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) with
    | true =>
      rw [hFresh] at hSt1
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
        at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
    | false =>
      rw [hFresh] at hSt1
      simp only [Bool.false_eq_true, ↓reduceIte] at hSt1
      cases huFind : adv.shCr.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [huFind] at hSt1
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
        rcases hSt1 with ⟨_, rfl⟩
        exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
      | some puPair =>
        rcases puPair with ⟨uIdx, uEntry⟩
        rw [huFind] at hSt1; dsimp only at hSt1
        unfold sampleKemKeyGen at hSt1
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
        rcases hSt1 with ⟨spkSk, hSpkSk, rSpk, _, kpCoins, _, rPq, _, _, rfl⟩
        have hu0 := List.find?_some huFind
        have huEq : uIdx = u.val := beq_iff_eq.mp hu0
        subst huEq
        have huMem : (u.val, uEntry) ∈ adv.shCr.base.principals :=
          List.mem_of_find?_eq_some huFind
        rcases hCore.1 with ⟨hVP, hVS, hVO, hPrinV, hSpkV, hOpkV, hAdvV⟩
        refine ⟨validTagStateCore_of_shCrExtends_eq_sessions P hCore ?_ ?_ rfl rfl
          (fun _ h => h) (fun _ h => h), Nat.le_refl _, Nat.le_refl _⟩
        · refine ⟨hVP, (validSpkBundles_cons S u j _ adv.shCr.base.spkBundles hVS hFresh).1,
            hVO, hPrinV, ?_, hOpkV, hAdvV⟩
          intro kv hkv
          rcases List.mem_cons.mp hkv with rfl | hOld
          · exact ⟨length_of_mem_support_sampleScalar32_coll hSpkSk, rfl,
              ⟨uEntry, huMem⟩, kpCoins, rfl, rfl⟩
          · exact hSpkV kv hOld
        · exact ⟨⟨fun _ e h => ⟨e, h, rfl, rfl⟩,
            fun _ b h => ⟨b, List.mem_cons_of_mem _ h, rfl, rfl, rfl, rfl⟩,
            fun _ o h => ⟨o, h, rfl, rfl⟩,
            fun _ h => h⟩, Nat.le_refl _, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | genOPK u j o =>
    dsimp only [tagStepView] at hMem
    have hRun : (pqxdhKeyIndAdvG3Impl S P (.genOPK u j o)).run adv =
        (do
          let (r, base') ← (pqxdhKeyIndImpl true S P (.genOPK u j o)).run adv.shCr.base
          return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
      simp [pqxdhKeyIndAdvG3Impl, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl,
        liftKeyIndShCrBase, liftShCrBase, StateT.run]; rfl
    rw [hRun] at hMem
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
    rcases hMem with ⟨⟨r1, st1⟩, hSt1, _, rfl⟩
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    unfold pqxdhKeyIndImpl at hSt1; dsimp only at hSt1
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hSt1
    cases hFresh : adv.shCr.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) with
    | true =>
      rw [hFresh] at hSt1
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
        at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
    | false =>
      rw [hFresh] at hSt1
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
      rcases hSt1 with ⟨opkSk, hOpkSk, _, rfl⟩
      rcases hCore.1 with ⟨hVP, hVS, hVO, hPrinV, hSpkV, hOpkV, hAdvV⟩
      refine ⟨validTagStateCore_of_shCrExtends_eq_sessions P hCore ?_ ?_ rfl rfl
        (fun _ h => h) (fun _ h => h), Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨hVP, hVS, (validOpkEntries_cons S u j o _ adv.shCr.base.opkEntries hVO hFresh).1,
          hPrinV, hSpkV, ?_, hAdvV⟩
        intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hOld
        · exact ⟨length_of_mem_support_sampleScalar32_coll hOpkSk, rfl⟩
        · exact hOpkV kv hOld
      · exact ⟨⟨fun _ e h => ⟨e, h, rfl, rfl⟩,
          fun _ b h => ⟨b, h, rfl, rfl, rfl, rfl⟩,
          fun _ o h => ⟨o, List.mem_cons_of_mem _ h, rfl, rfl⟩,
          fun _ h => h⟩, Nat.le_refl _, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | revealSpkSk u j =>
    dsimp only [tagStepView] at hMem
    have hRun : (pqxdhKeyIndAdvG3Impl S P (.revealSpkSk u j)).run adv =
        (do
          let (r, base') ← (pqxdhKeyIndImpl true S P (.revealSpkSk u j)).run adv.shCr.base
          return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
      simp [pqxdhKeyIndAdvG3Impl, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl,
        liftKeyIndShCrBase, liftShCrBase, StateT.run]; rfl
    rw [hRun] at hMem
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
    rcases hMem with ⟨⟨r1, st1⟩, hSt1, _, rfl⟩
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    unfold pqxdhKeyIndImpl at hSt1; dsimp only at hSt1
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hSt1
    cases hFind : adv.shCr.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      rw [hFind] at hSt1
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
    | some pbPair =>
      rcases pbPair with ⟨_, bEntry⟩
      rw [hFind] at hSt1; dsimp only at hSt1
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      rcases hCore.1 with ⟨hVP, hVS, hVO, hPrinV, hSpkV, hOpkV, hAdvV⟩
      refine ⟨validTagStateCore_of_shCrExtends_eq_sessions P hCore ?_ ?_ rfl rfl
        (fun _ h => h) (fun _ h => h), Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨hVP, (validSpkBundles_map_revealed S P (u.val, j.val) adv.shCr.base.spkBundles
          hVS).1,
          hVO, hPrinV, ?_, hOpkV, hAdvV⟩
        intro kv hkv
        dsimp only at hkv; rw [List.mem_map] at hkv
        rcases hkv with ⟨⟨idx, b⟩, hbMem, hEq⟩
        dsimp only at hEq
        split_ifs at hEq <;> (subst hEq; exact hSpkV (idx, b) hbMem)
      · refine ⟨⟨fun _ e h => ⟨e, h, rfl, rfl⟩, ?_,
          fun _ o h => ⟨o, h, rfl, rfl⟩, fun _ h => h⟩,
          Nat.le_refl _, fun _ h => h, fun _ h => h, fun _ h => h⟩
        intro idx b hb
        refine ⟨if idx == (u.val, j.val) then { b with revealed := true } else b, ?_,
          by split_ifs <;> rfl, by split_ifs <;> rfl, by split_ifs <;> rfl, by split_ifs <;> rfl⟩
        dsimp only; rw [List.mem_map]
        exact ⟨(idx, b), hb, by dsimp only; split_ifs <;> rfl⟩
  | registerKey sk =>
    dsimp only [tagStepView] at hMem
    have hRun : (pqxdhKeyIndAdvG3Impl S P (.registerKey sk)).run adv =
        (do
          let (r, base') ← (pqxdhKeyIndImpl true S P (.registerKey sk)).run adv.shCr.base
          return (r, { adv with shCr := { adv.shCr with base := base' } })) := by
      simp [pqxdhKeyIndAdvG3Impl, liftKeyIndAdvShCr, pqxdhKeyIndShCrImpl,
        liftKeyIndShCrBase, liftShCrBase, StateT.run]; rfl
    rw [hRun] at hMem
    simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hMem
    rcases hMem with ⟨⟨r1, st1⟩, hSt1, _, rfl⟩
    simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte, Nat.add_zero]
    unfold pqxdhKeyIndImpl registerAdvKey at hSt1; dsimp only at hSt1
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hSt1
    cases hLen : (sk.length != 32) with
    | true =>
      rw [hLen] at hSt1
      simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
        at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      exact ⟨hCore, Nat.le_refl _, Nat.le_refl _⟩
    | false =>
      rw [hLen] at hSt1
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
        StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hSt1
      rcases hSt1 with ⟨_, rfl⟩
      have hSkLen : sk.length = 32 := bne_eq_false_iff_eq.mp hLen
      rcases hCore.1 with ⟨hVP, hVS, hVO, hPrinV, hSpkV, hOpkV, hAdvV⟩
      refine ⟨validTagStateCore_of_shCrExtends_eq_sessions P hCore ?_ ?_ rfl rfl
        (fun _ h => h) (fun _ h => h), Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨hVP, hVS, hVO, hPrinV, hSpkV, hOpkV, ?_⟩
        intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hOld
        · exact ⟨hSkLen, rfl⟩
        · exact hAdvV kv hOld
      · exact ⟨⟨fun _ e h => ⟨e, h, rfl, rfl⟩,
          fun _ b h => ⟨b, h, rfl, rfl, rfl, rfl⟩,
          fun _ o h => ⟨o, h, rfl, rfl⟩,
          fun _ h => List.mem_cons_of_mem _ h⟩,
          Nat.le_refl _, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem validTagStateCore_of_withAdvRoCache {S : Setup} (P : Primitives)
    (c : List (Bytes × DRKey)) {adv : KeyIndAdvCutoffState S}
    (hCore : ValidTagStateCore P adv) :
    ValidTagStateCore P (withAdvRoCache c adv) :=
  ⟨hCore.1, validLazyRand_of_eq_fields P hCore.2.1 rfl rfl (fun _ h => h) (fun _ h => h) (fun _ h =>
    h),
   hCore.2.2.1, hCore.2.2.2⟩

theorem validTagStateCore_of_roLens_eval {S : Setup} (P : Primitives)
    (lst : KeyIndLazyState S) (sec : Bytes)
    (hCore : ValidTagStateCore P lst.adv)
    {y : DRKey × KeyIndLazyState S}
    (hy : y ∈ support ((roLens S).eval lst sec)) :
    ValidTagStateCore P y.2.adv ∧
    y.2.adv.advRoLog = lst.adv.advRoLog ∧
    y.2.adv.shCr.sendCount = lst.adv.shCr.sendCount := by
  unfold CacheLens.eval at hy
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨dk, c'⟩, _, rfl⟩
  exact ⟨validTagStateCore_of_withAdvRoCache P c' hCore, rfl, rfl⟩

theorem validTagStateCore_of_randLens_eval {S : Setup} (P : Primitives)
    (lst : KeyIndLazyState S) (pid : Bytes)
    (hCore : ValidTagStateCore P lst.adv)
    {y : DRKey × KeyIndLazyState S}
    (hy : y ∈ support ((randLens S).eval lst pid)) :
    ValidTagStateCore P y.2.adv ∧
    y.2.adv.advRoLog = lst.adv.advRoLog ∧
    y.2.adv.shCr.sendCount = lst.adv.shCr.sendCount := by
  unfold CacheLens.eval at hy
  simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
  rcases hy with ⟨⟨dk, c'⟩, _, rfl⟩
  exact ⟨hCore, rfl, rfl⟩

theorem validTagStateCore_of_runLazyPost {S : Setup} (P : Primitives)
    (eagerRoHonest eagerRand : Bool) (post : LazyPost) (lst : KeyIndLazyState S)
    (hCore : ValidTagStateCore P lst.adv)
    {y : KeyIndResponse × KeyIndLazyState S}
    (hy : y ∈ support (runLazyPost eagerRoHonest eagerRand S post lst)) :
    ValidTagStateCore P y.2.adv ∧
    y.2.adv.advRoLog = lst.adv.advRoLog ∧
    y.2.adv.shCr.sendCount = lst.adv.shCr.sendCount := by
  have hRandIf : ∀ (pid : KeyIndLazyState S → Bytes) (lst1 : KeyIndLazyState S) (resp :
    KeyIndResponse),
      ValidTagStateCore P lst1.adv →
      y ∈ support (evalRandIf eagerRand pid lst1 (fun lst2 => pure (resp, lst2))) →
      ValidTagStateCore P y.2.adv ∧
      y.2.adv.advRoLog = lst1.adv.advRoLog ∧
      y.2.adv.shCr.sendCount = lst1.adv.shCr.sendCount := by
    intro pid lst1 resp hC1 hy1
    unfold evalRandIf at hy1
    split_ifs at hy1
    · simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy1
      rcases hy1 with ⟨⟨dk, lst2⟩, h2, rfl⟩
      exact validTagStateCore_of_randLens_eval P lst1 (pid lst1) hC1 h2
    · simp only [support_pure, Set.mem_singleton_iff] at hy1
      subst hy1; exact ⟨hC1, rfl, rfl⟩
  cases post with
  | done resp =>
    unfold runLazyPost at hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy; exact ⟨hCore, rfl, rfl⟩
  | evalRo sec mkResp =>
    unfold runLazyPost at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨dk, lst1⟩, h1, rfl⟩
    exact validTagStateCore_of_roLens_eval P lst sec hCore h1
  | evalRand pid mkResp =>
    unfold runLazyPost at hy
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hy
    rcases hy with ⟨⟨dk, lst1⟩, h1, rfl⟩
    exact validTagStateCore_of_randLens_eval P lst pid hCore h1
  | handshake isHonest freshResp unfreshResp secrets pid? =>
    unfold runLazyPost evalRoIf at hy; dsimp only at hy
    cases hRo : !isHonest || eagerRoHonest <;>
      simp only [hRo, ↓reduceIte, Bool.false_eq_true] at hy
    · cases pid? with
      | none =>
        rw [support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact ⟨hCore, rfl, rfl⟩
      | some pid =>
        exact hRandIf (fun _ => pid) lst _ hCore hy
    · simp only [MonadAttach.mem_support_bind] at hy
      rcases hy with ⟨⟨dk, lst1⟩, h1, hy1⟩
      rcases validTagStateCore_of_roLens_eval P lst secrets hCore h1 with ⟨hC1, hLog1, hSend1⟩
      cases pid? with
      | none =>
        rw [support_pure, Set.mem_singleton_iff] at hy1
        subst hy1; exact ⟨hC1, hLog1, hSend1⟩
      | some pid =>
        rcases hRandIf (fun _ => pid) lst1 _ hC1 hy1 with ⟨hC2, hLog2, hSend2⟩
        exact ⟨hC2, hLog2.trans hLog1, hSend2.trans hSend1⟩

theorem validTagStateCore_of_pqxdhKeyIndAdvTagImpl {S : Setup} (P : Primitives)
    (eagerRoHonest eagerRand testReal : Bool) (q : KeyIndQuery S)
    (lst : KeyIndLazyState S) (hCore : ValidTagStateCore P lst.adv)
    {y : KeyIndResponse × KeyIndLazyState S}
    (hy : y ∈ support ((pqxdhKeyIndAdvTagImpl eagerRoHonest eagerRand testReal S P q).run lst)) :
    ValidTagStateCore P y.2.adv ∧
    y.2.adv.advRoLog.length ≤ lst.adv.advRoLog.length + (if isKeyIndRoQuery (.inr q) then 1 else 0)
      ∧
    y.2.adv.shCr.sendCount ≤ lst.adv.shCr.sendCount + (if isKeyIndSendQuery (.inr q) then 1 else 0)
      := by
  dsimp only [pqxdhKeyIndAdvTagImpl, mkLazyKeyIndImpl, liftTagView, StateT.run_mk] at hy
  simp only [bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨⟨post, adv'⟩, hView, hyPost⟩
  rcases validTagStateCore_of_tagStepView P testReal q (getLazyView lst)
    (validTagStateCore_of_withAdvRoCache P [] hCore) hView with
    ⟨hCore', hLog', hSend'⟩
  rcases validTagStateCore_of_runLazyPost P eagerRoHonest eagerRand post (setLazyView adv' lst)
    (validTagStateCore_of_withAdvRoCache P _ hCore') hyPost with ⟨hCoreY, hLogY, hSendY⟩
  exact ⟨hCoreY,
    by simpa [hLogY, getLazyView, setLazyView, withAdvRoCache] using hLog',
    by simpa [hSendY, getLazyView, setLazyView, withAdvRoCache, withShCrRoCache] using hSend'⟩

theorem simulateQ_pqxdhKeyIndAdvTagImpl_validTagStateCore {S : Setup} {α : Type}
    (P : Primitives) (eagerRoHonest eagerRand testReal : Bool)
    (oa : OracleComp (unifSpec + keyIndSpec S) α)
    (lst : KeyIndLazyState S) (nRo nSend : Nat)
    (hCore : ValidTagStateCore P lst.adv)
    (hRo : OracleComp.IsQueryBoundP oa isKeyIndRoQuery nRo)
    (hSend : OracleComp.IsQueryBoundP oa isKeyIndSendQuery nSend) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl eagerRoHonest eagerRand
          testReal S P
    ∀ y ∈ support ((simulateQ full oa).run lst),
      ValidTagStateCore P y.2.adv ∧
      y.2.adv.advRoLog.length ≤ lst.adv.advRoLog.length + nRo ∧
      y.2.adv.shCr.sendCount ≤ lst.adv.shCr.sendCount + nSend := by
  intro full
  induction oa using OracleComp.inductionOn generalizing lst nRo nSend with
  | pure a =>
    intro y hy
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy; dsimp only; exact ⟨hCore, by omega, by omega⟩
  | query_bind t mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hRo hSend
    rcases t with uq | gq
    · intro y hy
      dsimp only [full] at hy
      rw [simulateQ_run_query_inl] at hy
      simp only [MonadAttach.mem_support_bind] at hy
      rcases hy with ⟨u, _, hy'⟩
      have hRo' := hRo.2 u
      have hSend' := hSend.2 u
      simp only [isKeyIndRoQuery, isKeyIndSendQuery, ↓reduceIte] at hRo' hSend'
      exact ih u lst nRo nSend hCore hRo' hSend' y hy'
    · intro y hy
      dsimp only [full] at hy
      rw [simulateQ_run_query_inr] at hy
      simp only [MonadAttach.mem_support_bind] at hy
      rcases hy with ⟨x, hstep, hy'⟩
      rcases validTagStateCore_of_pqxdhKeyIndAdvTagImpl P eagerRoHonest eagerRand testReal gq lst
        hCore hstep with
        ⟨hCoreX, hLogX, hSendX⟩
      rcases ih x.1 x.2
        (if isKeyIndRoQuery (.inr gq) then nRo - 1 else nRo)
        (if isKeyIndSendQuery (.inr gq) then nSend - 1 else nSend)
        hCoreX (hRo.2 x.1) (hSend.2 x.1) y hy' with ⟨hCoreY, hLogY, hSendY⟩
      have h1 := hRo.1
      have h2 := hSend.1
      refine ⟨hCoreY, ?_, ?_⟩
      · by_cases hro : isKeyIndRoQuery (.inr gq) <;>
          simp only [hro, not_true_eq_false, false_or, ↓reduceIte] at h1 hLogX hLogY <;> omega
      · by_cases hs : isKeyIndSendQuery (.inr gq) <;>
          simp only [hs, not_true_eq_false, false_or, ↓reduceIte] at h2 hSendX hSendY <;> omega

theorem validTagState_of_mem_support_simulateQ {S : Setup}
    (P : Primitives) (eagerRoHonest eagerRand testReal : Bool)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndLazyState S) ProbComp) + pqxdhKeyIndAdvTagImpl eagerRoHonest eagerRand
          testReal S P
    ∀ p ∈ support ((simulateQ full A.1.run).run (KeyIndLazyState.empty S)),
      ValidTagState P b.q_ro p.2.adv := by
  intro full p hp
  rcases simulateQ_pqxdhKeyIndAdvTagImpl_validTagStateCore P eagerRoHonest eagerRand testReal
    A.1.run (KeyIndLazyState.empty S) b.q_ro S.N_send_tot
    (validTagStateCore_empty S P true) A.2.1 A.2.2.1 p hp with
    ⟨hCore, hLog, hSend⟩
  exact ⟨by simpa [KeyIndLazyState.empty] using hLog,
    by simpa [KeyIndLazyState.empty, KeyIndState.empty] using hSend,
    hCore.1, hCore.2.1, hCore.2.2.1, hCore.2.2.2⟩

theorem prob_badKeyIndFgAny4_le_sum {S : Setup} (P : Primitives) (maxLen : ℕ)
    {α : Type} (mx : ProbComp α) (projSt : α → KeyIndState S) (projLog : α → List Bytes) :
    (𝒟[mx >>= fun x => pure (badKeyIndFgAny4 P maxLen (projSt x) (projLog x))] {true}).toReal ≤
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x => pure (badKeyIndFgDh1At P maxLen uIdx bIdx (projSt x) (projLog
          x))] {true}).toReal) +
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x => pure (badKeyIndFgDh3At P maxLen sIdx bIdx (projSt x) (projLog
          x))] {true}).toReal) +
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ kIdx ∈ Finset.range S.N_id,
        (𝒟[mx >>= fun x => pure (badKeyIndFgDh2At P maxLen sIdx kIdx (projSt x) (projLog
          x))] {true}).toReal) +
      (∑ sIdx ∈ Finset.range S.N_send_opk_tot, ∑ oIdx ∈ Finset.range S.N_opk_tot,
        (𝒟[mx >>= fun x => pure (badKeyIndFgDh4At P maxLen sIdx oIdx (projSt x) (projLog
          x))] {true}).toReal) := by
  unfold badKeyIndFgAny4
  have hOr1 := prob_or_le_add_fg mx
    (fun x => badKeyIndFgAny P maxLen (projSt x) (projLog x) ||
      (List.range S.N_send_tot).any (fun sIdx =>
        (List.range S.N_id).any (fun kIdx =>
          badKeyIndFgDh2At P maxLen sIdx kIdx (projSt x) (projLog x))))
    (fun x => (List.range S.N_send_opk_tot).any (fun sIdx =>
      (List.range S.N_opk_tot).any (fun oIdx =>
        badKeyIndFgDh4At P maxLen sIdx oIdx (projSt x) (projLog x))))
  have hOr2 := prob_or_le_add_fg mx
    (fun x => badKeyIndFgAny P maxLen (projSt x) (projLog x))
    (fun x => (List.range S.N_send_tot).any (fun sIdx =>
      (List.range S.N_id).any (fun kIdx =>
        badKeyIndFgDh2At P maxLen sIdx kIdx (projSt x) (projLog x))))
  have hAC := prob_badKeyIndFgAny_le_sum P maxLen mx projSt projLog
  have hB := toReal_any_double_range_le_sum2 mx S.N_send_tot S.N_id
    (fun sIdx kIdx x => badKeyIndFgDh2At P maxLen sIdx kIdx (projSt x) (projLog x))
  have hD := toReal_any_double_range_le_sum2 mx S.N_send_opk_tot S.N_opk_tot
    (fun sIdx oIdx x => badKeyIndFgDh4At P maxLen sIdx oIdx (projSt x) (projLog x))
  linarith

theorem evalDist_gapDhExp_fgKeyIndGapDhAdv4_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[gapDhExp P ddh pow8 (fgKeyIndGapDhAdv4 S b A)] =
    𝒟[FgGapDh.sampleIndexRange (fgTotalIndexCount S) >>= fun idx =>
        gapDhExp P ddh pow8 (fgKeyIndGapDhAdvAtFlat idx S b A)] := by
  have hStep1 :
      gapDhExp P ddh pow8 (fgKeyIndGapDhAdv4 S b A) =
      (do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let idx ← FgGapDh.sampleIndexRange (fgTotalIndexCount S)
        let Z ← simulateQ (gapDhFullImpl P ddh)
          (fgKeyIndGapDhRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) := by
    unfold gapDhExp fgKeyIndGapDhAdv4
    congr 1; ext u; congr 1; ext v
    change (simulateQ (gapDhFullImpl P ddh)
        (unifGdh (FgGapDh.sampleIndexRange (fgTotalIndexCount S)) >>= fun idx =>
          fgKeyIndGapDhRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v)) >>=
      fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
    rw [simulateQ_bind, FgGapDh.simulateQ_gapDhFullImpl_unifGdh, bind_assoc]
  rw [hStep1]
  have hSwap1 :
      𝒟[do
        let u ← sampleScalar32
        let v ← sampleScalar32
        let idx ← FgGapDh.sampleIndexRange (fgTotalIndexCount S)
        let Z ← simulateQ (gapDhFullImpl P ddh)
          (fgKeyIndGapDhRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] =
      𝒟[do
        let u ← sampleScalar32
        let idx ← FgGapDh.sampleIndexRange (fgTotalIndexCount S)
        let v ← sampleScalar32
        let Z ← simulateQ (gapDhFullImpl P ddh)
          (fgKeyIndGapDhRunAtFlat idx S b A (P.x25519Base u) (P.x25519Base v))
        return (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))] := by
    refine OracleComp.evalDist_bind_congr_of_support sampleScalar32 _ _ (fun u _ => ?_)
    exact OracleComp.evalDist_bind_bind_swap sampleScalar32
      (FgGapDh.sampleIndexRange (fgTotalIndexCount S)) _
  rw [hSwap1, OracleComp.evalDist_bind_bind_swap sampleScalar32
    (FgGapDh.sampleIndexRange (fgTotalIndexCount S))]
  rfl

theorem sum_range_mul_div_mod (M N : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ k ∈ Finset.range (M * N), f (k / N) (k % N) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, f i j := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hPos : 0 < N := by omega
    have hEq : m * N + j = j + m * N := Nat.add_comm _ _
    rw [hEq, Nat.add_mul_div_right j m hPos, Nat.div_eq_of_lt hj, Nat.zero_add,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem gapDh_congr_run (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    {adv1 adv2 : GapDhAdv} (h : adv1.run = adv2.run) :
    GapDH P ddh pow8 adv1 = GapDH P ddh pow8 adv2 := by
  unfold GapDH gapDhExp
  rw [h]

theorem sum_gapDh_fgKeyIndGapDhAdv4_eq (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    (∑ u ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
      GapDH P ddh pow8 (fgKeyIndGapDhAdvAt true u bIdx S b A)) +
    (∑ idx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
      GapDH P ddh pow8 (fgKeyIndGapDhAdvAt false idx bIdx S b A)) +
    (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ kIdx ∈ Finset.range S.N_id,
      GapDH P ddh pow8 (fgKeyIndGapDhAdvAtIk sIdx kIdx S b A)) +
    (∑ sIdx ∈ Finset.range S.N_send_opk_tot, ∑ oIdx ∈ Finset.range S.N_opk_tot,
      GapDH P ddh pow8 (fgKeyIndGapDhAdvAtOpk sIdx oIdx S b A)) =
    ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
      (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
      (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
      GapDH P ddh pow8 (fgKeyIndGapDhAdv4 S b A) := by
  have hExp := evalDist_gapDhExp_fgKeyIndGapDhAdv4_eq P ddh pow8 S b A
  have hSum := FgGapDh.mul_toReal_sampleIndexRange_bind_eq_sum_fg (fgTotalIndexCount S)
    (fun idx => gapDhExp P ddh pow8 (fgKeyIndGapDhAdvAtFlat idx S b A))
  have hRhs :
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDH P ddh pow8 (fgKeyIndGapDhAdv4 S b A) =
      ∑ idx ∈ Finset.range (fgTotalIndexCount S),
        GapDH P ddh pow8 (fgKeyIndGapDhAdvAtFlat idx S b A) := by
    unfold GapDH
    rw [hExp, ← hSum]
    unfold fgTotalIndexCount
    push_cast
    ring
  rw [hRhs]
  unfold fgTotalIndexCount
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range (S.N_id * S.N_spk_tot),
      GapDH P ddh pow8 (fgKeyIndGapDhAdvAtFlat x S b A) =
      ∑ u ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDH P ddh pow8 (fgKeyIndGapDhAdvAt true u bIdx S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => gapDh_congr_run P ddh pow8 ?_)
    rw [Finset.mem_range] at hx
    funext U V
    dsimp only [fgKeyIndGapDhAdvAtFlat, fgKeyIndGapDhAdvAt, fgKeyIndGapDhRunAtFlat]
    simp only [hx, ↓reduceIte]
  have h2 : ∑ x ∈ Finset.range (S.N_send_tot * S.N_spk_tot),
      GapDH P ddh pow8 (fgKeyIndGapDhAdvAtFlat (S.N_id * S.N_spk_tot + x) S b A) =
      ∑ idx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDH P ddh pow8 (fgKeyIndGapDhAdvAt false idx bIdx S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => gapDh_congr_run P ddh pow8 ?_)
    rw [Finset.mem_range] at hx
    funext U V
    dsimp only [fgKeyIndGapDhAdvAtFlat, fgKeyIndGapDhAdvAt, fgKeyIndGapDhRunAtFlat]
    have hNot1 : ¬ (S.N_id * S.N_spk_tot + x < S.N_id * S.N_spk_tot) := by omega
    have hlt2 : S.N_id * S.N_spk_tot + x < S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot := by
      omega
    simp only [hNot1, hlt2, ↓reduceIte, Nat.add_sub_cancel_left]
  have h3 : ∑ x ∈ Finset.range (S.N_send_tot * S.N_id),
      GapDH P ddh pow8 (fgKeyIndGapDhAdvAtFlat (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
        x) S b A) =
      ∑ sIdx ∈ Finset.range S.N_send_tot, ∑ kIdx ∈ Finset.range S.N_id,
        GapDH P ddh pow8 (fgKeyIndGapDhAdvAtIk sIdx kIdx S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => gapDh_congr_run P ddh pow8 ?_)
    rw [Finset.mem_range] at hx
    funext U V
    dsimp only [fgKeyIndGapDhAdvAtFlat, fgKeyIndGapDhAdvAtIk, fgKeyIndGapDhRunAtFlat]
    have hNot1 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + x < S.N_id * S.N_spk_tot) :=
      by omega
    have hNot2 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + x <
        S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) := by omega
    have hlt3 : S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + x <
        S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id := by omega
    simp only [hNot1, hNot2, hlt3, ↓reduceIte, Nat.add_sub_cancel_left]
  have h4 : ∑ x ∈ Finset.range (S.N_send_opk_tot * S.N_opk_tot),
      GapDH P ddh pow8 (fgKeyIndGapDhAdvAtFlat
        (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id + x) S b A) =
      ∑ sIdx ∈ Finset.range S.N_send_opk_tot, ∑ oIdx ∈ Finset.range S.N_opk_tot,
        GapDH P ddh pow8 (fgKeyIndGapDhAdvAtOpk sIdx oIdx S b A) := by
    rw [← sum_range_mul_div_mod]
    refine Finset.sum_congr rfl (fun x hx => gapDh_congr_run P ddh pow8 ?_)
    rw [Finset.mem_range] at hx
    funext U V
    dsimp only [fgKeyIndGapDhAdvAtFlat, fgKeyIndGapDhAdvAtOpk, fgKeyIndGapDhRunAtFlat]
    have hNot1 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id + x <
        S.N_id * S.N_spk_tot) := by omega
    have hNot2 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id + x <
        S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) := by omega
    have hNot3 : ¬ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id + x <
        S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) := by omega
    simp only [hNot1, hNot2, hNot3, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [h1, h2, h3, h4]

theorem prob_badKeyIndFgAny4_le_gapDh (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
        pure (badKeyIndFgAny4 P b.q_ro x.2.2.base x.2.2.advRoLog)] {true}).toReal ≤
      ((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
        (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
        (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
        GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdv4 S b A) := by
  have hUnion := prob_badKeyIndFgAny4_le_sum P b.q_ro (runKeyIndFgSim S P A.1)
    (fun x => x.2.2.base) (fun x => x.2.2.advRoLog)
  have hSumDh1 :
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
          pure (badKeyIndFgDh1At P b.q_ro uIdx bIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal) ≤
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdvAt true uIdx bIdx S b A)) :=
    Finset.sum_le_sum (fun uIdx huIdx =>
      Finset.sum_le_sum (fun bIdx hbIdx => prob_badKeyIndFgDh1At_le_gapDh S b P hP A uIdx huIdx bIdx
        hbIdx))
  have hSumDh3 :
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
          pure (badKeyIndFgDh3At P b.q_ro sIdx bIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal) ≤
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdvAt false sIdx bIdx S b A)) :=
    Finset.sum_le_sum (fun sIdx hsIdx =>
      Finset.sum_le_sum (fun bIdx hbIdx => prob_badKeyIndFgDh3At_le_gapDh S b P hP A sIdx hsIdx bIdx
        hbIdx))
  have hSumDh2 :
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ kIdx ∈ Finset.range S.N_id,
        (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
          pure (badKeyIndFgDh2At P b.q_ro sIdx kIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal) ≤
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ kIdx ∈ Finset.range S.N_id,
        GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdvAtIk sIdx kIdx S b A)) :=
    Finset.sum_le_sum (fun sIdx hsIdx =>
      Finset.sum_le_sum (fun kIdx hkIdx => prob_badKeyIndFgDh2At_le_gapDh S b P hP A sIdx hsIdx kIdx
        hkIdx))
  have hSumDh4 :
      (∑ sIdx ∈ Finset.range S.N_send_opk_tot, ∑ oIdx ∈ Finset.range S.N_opk_tot,
        (𝒟[runKeyIndFgSim S P A.1 >>= fun x =>
          pure (badKeyIndFgDh4At P b.q_ro sIdx oIdx x.2.2.base x.2.2.advRoLog)] {true}).toReal) ≤
      (∑ sIdx ∈ Finset.range S.N_send_opk_tot, ∑ oIdx ∈ Finset.range S.N_opk_tot,
        GapDH P P.isValidDhTriple P.pow8 (fgKeyIndGapDhAdvAtOpk sIdx oIdx S b A)) :=
    Finset.sum_le_sum (fun sIdx hsIdx =>
      Finset.sum_le_sum (fun oIdx hoIdx =>
        prob_badKeyIndFgDh4At_le_gapDh S b P hP A sIdx
          (Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hsIdx)
            (Nat.le_add_right _ _))) oIdx hoIdx))
  have hEq := sum_gapDh_fgKeyIndGapDhAdv4_eq S P P.isValidDhTriple P.pow8 b A
  linarith

theorem keyInd_hop_G0_G3_le
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    |KeyIndAdvantage S P A.1 - keyIndAdvG3 S P A.1| ≤
      (S.N_id : ℝ) * SigEufCma P (sigReductionKeyInd S b A) +
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
      (S.N_spk_tot : ℝ) * (S.N_send_tot : ℝ) * KemShCrReal P (shcrReductionKeyInd S b A) +
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  have h0_eq : KeyIndAdvantage S P A.1 = keyIndAdvG0 S P A.1 :=
    _root_.SignalPqxdh.Security.keyIndAdvG0_eq S P A.1
  have h02 := keyInd_hop_G0_G2_le S P b A hP
  have h23 := keyInd_hop_G2_G3_le S P hP b A
  have htri := abs_sub_le (KeyIndAdvantage S P A.1) (keyIndAdvG2 S P A.1) (keyIndAdvG3 S P A.1)
  rw [← h0_eq] at h02
  set_option exponentiation.threshold 512 in
  linarith

end Proofs.SignalPqxdh.Security

