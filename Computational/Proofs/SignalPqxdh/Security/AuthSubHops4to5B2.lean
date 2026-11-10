/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5B
import VCVio.EvalDist.Monad.Basic
import Computational.Proofs.SignalPqxdh.Security.FgGapDhA -- shake: keep
import Computational.Proofs.SignalPqxdh.Security.FgGapDhC -- shake: keep

/-!
# PQXDH authentication post-handshake sub-hops 4–5: clean-session invariant at `.g5`

Proves that `AuthCleanSessionInv` is preserved by every `Auth` oracle query under
`pqxdhAuthHybridSplitKoskImpl sendStage .g5`, keeping `hasWonAuth = false` absent bad signature or
KEM public-key collision events.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh (initSessionSlotIdx initSessionSlotIdx_sendOPK_lt
  initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt RelProbUpToBad
    simulateQ_relProbUpToBad evalDist_simulateQ_eq_of_step_or_bad)

theorem consumeMatchingSentOPK_fst_eq_true_of_mem (P : Primitives) (r : RecvdOPKEvent) :
    ∀ (xs : List SentOPKEvent) (ev : SentOPKEvent),
      ev ∈ xs → matchSentOPK P r ev = true →
      (consumeMatchingSentOPK P r xs).1 = true
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | x :: rest, ev, hmem, hmatch => by
    unfold consumeMatchingSentOPK
    by_cases hx : matchSentOPK P r x = true
    · simp [hx]
    · rcases List.mem_cons.mp hmem with rfl | hrest
      · exact False.elim (hx hmatch)
      · have ih := consumeMatchingSentOPK_fst_eq_true_of_mem P r rest ev hrest hmatch
        simp [hx, ih]

theorem mem_consumeMatchingSentOPK_or_match (P : Primitives) (r : RecvdOPKEvent) :
    ∀ (xs : List SentOPKEvent) (ev : SentOPKEvent),
      ev ∈ xs →
      matchSentOPK P r ev = true ∨ ev ∈ (consumeMatchingSentOPK P r xs).2
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | x :: rest, ev, hmem => by
    unfold consumeMatchingSentOPK
    by_cases hx : matchSentOPK P r x = true
    · rcases List.mem_cons.mp hmem with rfl | hrest
      · exact Or.inl hx
      · simp [hx, hrest]
    · rcases List.mem_cons.mp hmem with rfl | hrest
      · simp [hx]
      · rcases mem_consumeMatchingSentOPK_or_match P r rest ev hrest with hm | hmem'
        · exact Or.inl hm
        · right
          simp [hx, hmem']

theorem consumeMatchingSentNoOPK_fst_eq_true_of_mem (P : Primitives) (r : RecvdNoOPKEvent) :
    ∀ (xs : List SentNoOPKEvent) (ev : SentNoOPKEvent),
      ev ∈ xs → matchSentNoOPK P r ev = true →
      (consumeMatchingSentNoOPK P r xs).1 = true
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | x :: rest, ev, hmem, hmatch => by
    unfold consumeMatchingSentNoOPK
    by_cases hx : matchSentNoOPK P r x = true
    · simp [hx]
    · rcases List.mem_cons.mp hmem with rfl | hrest
      · exact False.elim (hx hmatch)
      · have ih := consumeMatchingSentNoOPK_fst_eq_true_of_mem P r rest ev hrest hmatch
        simp [hx, ih]

theorem mem_consumeMatchingSentNoOPK_or_match (P : Primitives) (r : RecvdNoOPKEvent) :
    ∀ (xs : List SentNoOPKEvent) (ev : SentNoOPKEvent),
      ev ∈ xs →
      matchSentNoOPK P r ev = true ∨ ev ∈ (consumeMatchingSentNoOPK P r xs).2
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | x :: rest, ev, hmem => by
    unfold consumeMatchingSentNoOPK
    by_cases hx : matchSentNoOPK P r x = true
    · rcases List.mem_cons.mp hmem with rfl | hrest
      · exact Or.inl hx
      · simp [hx, hrest]
    · rcases List.mem_cons.mp hmem with rfl | hrest
      · simp [hx]
      · rcases mem_consumeMatchingSentNoOPK_or_match P r rest ev hrest with hm | hmem'
        · exact Or.inl hm
        · right
          simp [hx, hmem']

theorem spkBundles_fst_eq_of_pqspkPk_eq :
    ∀ (xs : List ((Nat × Nat) × SpkBundleEntry)),
      (xs.map Prod.fst).Nodup →
      hasDuplicateBytes (xs.map (fun (_, b) => b.pqspkPk)) = false →
      ∀ kj1 b1 kj2 b2,
        (kj1, b1) ∈ xs → (kj2, b2) ∈ xs →
        b1.pqspkPk = b2.pqspkPk → kj1 = kj2
  | [], _, _, _, _, _, _, h1, _, _ => False.elim (List.not_mem_nil h1)
  | (kj0, b0) :: tl, hnodup, hdup, kj1, b1, kj2, b2, h1, h2, hpk => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.map_cons, hasDuplicateBytes, Bool.or_eq_false_iff] at hdup
    rcases List.mem_cons.mp h1 with h10 | h1tl <;> rcases List.mem_cons.mp h2 with h20 | h2tl
    · cases h10; cases h20; rfl
    · cases h10
      exfalso
      have hmem : b0.pqspkPk ∈ tl.map (fun (_, b) => b.pqspkPk) := by
        rw [hpk, List.mem_map]
        exact ⟨(kj2, b2), h2tl, rfl⟩
      have hcont : (tl.map (fun (_, b) => b.pqspkPk)).contains b0.pqspkPk = true :=
        List.contains_iff_mem.mpr hmem
      rw [hdup.1] at hcont
      cases hcont
    · cases h20
      exfalso
      have hmem : b0.pqspkPk ∈ tl.map (fun (_, b) => b.pqspkPk) := by
        rw [← hpk, List.mem_map]
        exact ⟨(kj1, b1), h1tl, rfl⟩
      have hcont : (tl.map (fun (_, b) => b.pqspkPk)).contains b0.pqspkPk = true :=
        List.contains_iff_mem.mpr hmem
      rw [hdup.1] at hcont
      cases hcont
    · exact spkBundles_fst_eq_of_pqspkPk_eq tl hnodup.2 hdup.2 kj1 b1 kj2 b2 h1tl h2tl hpk

theorem spkHonest_of_hasBadSigAuth_eq_false {S : Setup} (hst : AuthHybridState S)
    (hBad : hasBadSigAuth hst = false)
    (e : AuthInitiatorEntry S) (he : e ∈ hst.base.sessions) (hFresh : e.fresh = true) :
    e.spkHonest = true := by
  unfold hasBadSigAuth HasAuthState.toAuthState at hBad
  rw [List.any_eq_false] at hBad
  have h := hBad e he
  simp [hFresh] at h
  exact h.1

theorem exists_spkBundle_of_checkBundleProvenanceExact_fst (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput)
    (h : (checkBundleProvenanceExact P principals spkBundles opkEntries bundle).1 = true) :
    ∃ kj b, (kj, b) ∈ spkBundles ∧ b.spkPk = bundle.spkB := by
  unfold checkBundleProvenanceExact at h
  cases hfp : findHonestPrincipal P principals bundle.ikB with
  | none => simp [hfp] at h
  | some kp =>
    rcases kp with ⟨k, _⟩
    simp only [hfp, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Prod.exists] at h
    rcases h with ⟨u, j, b, hmem, _, hspk⟩
    exact ⟨(u, j), b, hmem, hspk⟩

theorem exists_spkBundle_of_checkBundleProvenanceExact_pq (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) {k : Nat} {pEntry : PrincipalEntry}
    (hfp : findHonestPrincipal P principals bundle.ikB = some (k, pEntry))
    (h : (checkBundleProvenanceExact P principals spkBundles opkEntries bundle).2.2 = true) :
    ∃ j b, ((k, j), b) ∈ spkBundles ∧ b.pqspkPk = bundle.pqspkB := by
  unfold checkBundleProvenanceExact at h
  simp only [hfp, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Prod.exists] at h
  rcases h with ⟨u, j, b, hmem, rfl, hpq⟩
  exact ⟨j, b, hmem, hpq⟩

theorem principals_eq_of_nodup {α β : Type} {xs : List (α × β)}
    (hNodup : (xs.map Prod.fst).Nodup) {k : α} {v1 v2 : β}
    (h1 : (k, v1) ∈ xs) (h2 : (k, v2) ∈ xs) : v1 = v2 := by
  induction xs with
  | nil => nomatch h1
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hNodup
    rcases List.mem_cons.mp h1 with rfl | h1' <;>
    rcases List.mem_cons.mp h2 with h2_eq | h2'
    · exact (Prod.mk.inj h2_eq).2.symm
    · exfalso; exact hNodup.1 (List.mem_map.mpr ⟨(k, v2), h2', rfl⟩)
    · subst h2_eq; exfalso; exact hNodup.1 (List.mem_map.mpr ⟨(k, v1), h1', rfl⟩)
    · exact ih hNodup.2 h1' h2'

theorem mem_of_find?_fst_beq {α β : Type} [BEq α] [LawfulBEq α]
    {xs : List (α × β)} {k k' : α} {v : β}
    (h : xs.find? (fun (idx, _) => idx == k) = some (k', v)) :
    (k, v) ∈ xs := by
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  simp only [beq_iff_eq] at hpred
  subst hpred
  exact hmem

theorem mem_support_evalAuthHybridRecvSchedule_g5_honest {S : Setup}
    (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg)
    (drKey : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hHon : (match findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
             | some (_, sEntry) => !sEntry.corrupted
             | none => false) = true)
    (hmem : some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') ∈
      support (evalAuthHybridRecvSchedule .g5 useRo P hst kEntry bEntry opkPk? secrets msg)) :
    ∃ s ∈ hst.idealSessions,
      matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr s = true ∧
      pt = s.msgPlain := by
  unfold evalAuthHybridRecvSchedule at hmem
  dsimp only at hmem
  cases hfp : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
  | none => simp [hfp] at hHon
  | some sp =>
    rcases sp with ⟨_, sEntry⟩
    simp only [hfp, Bool.not_eq_true'] at hHon
    simp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
      AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
      AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
      hfp, hHon, Bool.not_false, Bool.or_true, Bool.and_true, ↓reduceIte] at hmem
    cases hmatch : hst.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) with
    | none =>
      simp only [hmatch, Bool.not_false, ↓reduceIte, pure_bind] at hmem
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨dk, _, hmem⟩
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨_, _, hmem⟩
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨_, _, hmem⟩
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨_, _, hmem⟩
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨_, _, hspqr⟩
      cases hinit : P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with
      | none => simp [hinit] at hspqr
      | some pqrPair =>
        rcases pqrPair with ⟨_, spqrSalt?⟩
        simp [hinit] at hspqr
    | some s =>
      simp only [hmatch, pure_bind] at hmem
      by_cases hsameEph : (P.pow8 msg.ephAPk == P.pow8 s.ephAPk) = true
      · simp only [hsameEph, ↓reduceIte] at hmem
        cases hinit : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [hinit] at hmem
        | some pqrPair =>
          rcases pqrPair with ⟨_, spqrSalt?⟩
          simp only [hinit, Bool.true_and] at hmem
          by_cases hsalt : (spqrSalt? == s.spqrSalt?) = true
          · simp only [hsalt, ↓reduceIte] at hmem
            by_cases had : (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg ==
              s.ad &&
                msg.aeadCt == s.aeadCt) = true
            · simp [had] at hmem
              exact ⟨s, List.mem_of_find?_eq_some hmatch, List.find?_some hmatch, hmem.2.2.2.1⟩
            · simp [had] at hmem
          · simp [hsalt] at hmem
      · simp only [hsameEph, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false] at hmem
        rw [MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨_, _, hmem⟩
        rw [MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨_, _, hspqr⟩
        cases hinit : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [hinit] at hspqr
        | some pqrPair =>
          rcases pqrPair with ⟨_, spqrSalt?⟩
          simp [hinit] at hspqr

theorem mem_support_evalAuthFixedRecvScheduleCached_g5_honest {S : Setup}
    (useRo : Bool) (P : Primitives)
    (hst : AuthHybridState S) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (opkPk? : Option Bytes) (secrets : Bytes) (msg : PreKeyMsg)
    (drKey : DRKey) (rk1 ck1_1 pt : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (mkSaltCache' : AuthMkSaltCache S)
    (hHon : (match findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
             | some (_, sEntry) => !sEntry.corrupted
             | none => false) = true)
    (hmem : (some (drKey, rk1, ck1_1, pt, roCache', rootRoCache'), mkSaltCache') ∈
      support (evalAuthFixedRecvScheduleCached .g5 useRo P hst recvCount mkSaltCache
        kEntry bEntry opkPk? secrets msg)) :
    ∃ s ∈ hst.idealSessions,
      matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr s = true ∧
      pt = s.msgPlain := by
  unfold evalAuthFixedRecvScheduleCached at hmem
  dsimp only at hmem
  cases hfp : findHonestPrincipal P hst.base.principals msg.hdr.ikAPk with
  | none => simp [hfp] at hHon
  | some sp =>
    rcases sp with ⟨_, sEntry⟩
    simp only [hfp, Bool.not_eq_true'] at hHon
    simp only [AuthHybridStage.idealDrKey, AuthHybridStage.idealRk,
      AuthHybridStage.idealCk, AuthHybridStage.idealMsgKeys,
      AuthHybridStage.idealFreshAead, AuthHybridStage.idealUnmatchedRecvAead,
      hfp, hHon, Bool.not_false, Bool.or_true, Bool.and_true, ↓reduceIte] at hmem
    cases hmatch : hst.idealSessions.find?
        (matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk opkPk? bEntry.pqspkPk msg.hdr) with
    | none =>
      simp only [hmatch, Bool.not_false, ↓reduceIte, pure_bind] at hmem
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨dk, _, hmem⟩
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨_, _, hmem⟩
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨_, _, hmem⟩
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨_, _, hmem⟩
      rw [MonadAttach.mem_support_bind] at hmem
      rcases hmem with ⟨_, _, hspqr⟩
      cases hinit : P.spqrInitRecv dk.pqrKey msg.pqRatchetMsg with
      | none => simp [hinit] at hspqr
      | some pqrPair =>
        rcases pqrPair with ⟨_, spqrSalt?⟩
        simp [hinit] at hspqr
    | some s =>
      simp only [hmatch, pure_bind] at hmem
      by_cases hsameEph : (P.pow8 msg.ephAPk == P.pow8 s.ephAPk) = true
      · simp only [hsameEph, ↓reduceIte] at hmem
        cases hinit : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [hinit] at hmem
        | some pqrPair =>
          rcases pqrPair with ⟨_, spqrSalt?⟩
          simp only [hinit, Bool.true_and] at hmem
          by_cases hsalt : (sameSaltKey spqrSalt? s.spqrSalt?) = true
          · simp only [hsalt, ↓reduceIte] at hmem
            by_cases had : (firstMsgAD msg.hdr.ikAPk kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg ==
              s.ad &&
                msg.aeadCt == s.aeadCt) = true
            · simp [had] at hmem
              exact ⟨s, List.mem_of_find?_eq_some hmatch, List.find?_some hmatch, hmem.1.2.2.2.1⟩
            · simp [had] at hmem
          · simp only [hsalt, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hmem
            cases hcache : mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
            | none => simp [hcache] at hmem
            | some ce => rcases ce with ⟨_, _, _⟩; simp [hcache] at hmem
      · simp only [hsameEph, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false] at hmem
        rw [MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨_, _, hmem⟩
        rw [MonadAttach.mem_support_bind] at hmem
        rcases hmem with ⟨_, _, hspqr⟩
        cases hinit : P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [hinit] at hspqr
        | some pqrPair =>
          rcases pqrPair with ⟨_, spqrSalt?⟩
          simp [hinit] at hspqr

/-- Clean-session correspondence invariant for a recorded fresh session `s ∈ hst.idealSessions`. -/
structure IdealSessionClean (P : Primitives) (S : Setup)
    (hst : AuthHybridState S) (s : IdealAuthSession S) : Prop where
  canon_ek : P.isCanonical s.ekAPk = true
  has_sess_entry :
    (∃ e ∈ hst.base.sessions,
      (e.fresh = true ∨ e.spkHonest = true) ∧ e.peerSpkPk = s.peerSpkPk ∧
      (e.spkHonest = true → ∃ kj b, (kj, b) ∈ hst.base.spkBundles ∧ b.spkPk = s.peerSpkPk)) ∨
    (∃ kj b pE, (kj, b) ∈ hst.base.spkBundles ∧ b.pqspkPk = s.peerPqspkPk ∧
      (kj.1, pE) ∈ hst.base.principals ∧ pE.corrupted = true)
  event_or_replayed :
    (∃ kj b, (kj, b) ∈ hst.base.spkBundles ∧ b.pqspkPk = s.peerPqspkPk ∧
      (kj.1, UInt32.ofNat kj.2, UInt32.ofNat kj.2, s.ekAPk) ∈ hst.base.seenKyberBaseKeys) ∨
    (match s.peerOpkPk? with
     | some sOpk =>
       ∃ ev ∈ hst.base.sentOPKEvents,
         ev.matched = false ∧ ev.a0 = s.ikAPk ∧ P.pow8 ev.b0 = P.pow8 s.peerIkPk ∧
         ev.sb = s.peerSpkPk ∧ ev.ob = sOpk ∧ ev.a1 = s.ekAPk ∧
         ev.pk1 = s.peerPqspkPk ∧ ev.ct = s.kemCt ∧ ev.m = s.msgPlain
     | none =>
       ∃ ev ∈ hst.base.sentNoOPKEvents,
         ev.matched = false ∧ ev.a0 = s.ikAPk ∧ P.pow8 ev.b0 = P.pow8 s.peerIkPk ∧
         ev.sb = s.peerSpkPk ∧ ev.a1 = s.ekAPk ∧
         ev.pk1 = s.peerPqspkPk ∧ ev.ct = s.kemCt ∧ ev.m = s.msgPlain)

theorem IdealSessionClean.mono {P : Primitives} {S : Setup}
    {hst hst' : AuthHybridState S} {s : IdealAuthSession S}
    (hs : IdealSessionClean P S hst s)
    (hBundles : hst.base.spkBundles ⊆ hst'.base.spkBundles)
    (hSessions : hst.base.sessions ⊆ hst'.base.sessions)
    (hTriples : hst.base.seenKyberBaseKeys ⊆ hst'.base.seenKyberBaseKeys)
    (hSentOPK : hst.base.sentOPKEvents ⊆ hst'.base.sentOPKEvents)
    (hSentNoOPK : hst.base.sentNoOPKEvents ⊆ hst'.base.sentNoOPKEvents)
    (hPrinc : ∀ k pE, (k, pE) ∈ hst.base.principals → pE.corrupted = true →
      ∃ pE', (k, pE') ∈ hst'.base.principals ∧ pE'.corrupted = true :=
        by intros k pE hm hc; exact ⟨pE, hm, hc⟩) :
    IdealSessionClean P S hst' s where
  canon_ek := hs.canon_ek
  has_sess_entry := by
    rcases hs.has_sess_entry with ⟨e, he, hfresh, hspk, hhon⟩ | ⟨kj, b, pE, hmem_b, hpq, hmem_p,
      hcorr⟩
    · left
      refine ⟨e, hSessions he, hfresh, hspk, fun hh => ?_⟩
      rcases hhon hh with ⟨kj, b, hmem, hpk⟩
      exact ⟨kj, b, hBundles hmem, hpk⟩
    · right
      rcases hPrinc kj.1 pE hmem_p hcorr with ⟨pE', hmem_p', hcorr'⟩
      exact ⟨kj, b, pE', hBundles hmem_b, hpq, hmem_p', hcorr'⟩
  event_or_replayed := by
    rcases hs.event_or_replayed with ⟨kj, b, hmem, hpk, htr⟩ | hev
    · exact Or.inl ⟨kj, b, hBundles hmem, hpk, hTriples htr⟩
    · right
      cases hopk : s.peerOpkPk? with
      | some sOpk =>
        rw [hopk] at hev
        rcases hev with ⟨ev, hev_mem, hrest⟩
        exact ⟨ev, hSentOPK hev_mem, hrest⟩
      | none =>
        rw [hopk] at hev
        rcases hev with ⟨ev, hev_mem, hrest⟩
        exact ⟨ev, hSentNoOPK hev_mem, hrest⟩

/-- Clean-session state invariant for `pqxdhAuthHybridSplitKoskImpl sendStage .g5`. -/
structure AuthCleanSessionInv (P : Primitives) (S : Setup) (hst : AuthHybridState S) : Prop where
  bundles_canon    : ∀ kj b, (kj, b) ∈ hst.base.spkBundles → P.isCanonical b.spkPk = true
  bundles_nodup    : (hst.base.spkBundles.map Prod.fst).Nodup
  principals_nodup : (hst.base.principals.map Prod.fst).Nodup
  sessions_inv     : ∀ s ∈ hst.idealSessions, IdealSessionClean P S hst s
  no_false_win     : hasBadSigAuth hst = false → hasKemPkCollisionAuth hst = false →
                       hst.base.hasWonAuth = false

theorem authCleanSessionInv_empty (P : Primitives) (S : Setup) (secb : Bool) :
    AuthCleanSessionInv P S (AuthHybridState.empty S secb) where
  bundles_canon    := fun _ _ h => False.elim (List.not_mem_nil h)
  bundles_nodup    := List.nodup_nil
  principals_nodup := List.nodup_nil
  sessions_inv     := fun _ h => False.elim (List.not_mem_nil h)
  no_false_win     := fun _ _ => rfl


theorem authCleanSessionInv_finishAuthHybridSend {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry)
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 ck1_0 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg : Bytes)
    (deriveMessageKeys : MessageKeys) (ad aeadCt msgPlain : Bytes)
    (roCache' : List (Bytes × DRKey))
    (rootRoCache' : List ((Bytes × Bytes) × (Bytes × Bytes)))
    (hst : AuthHybridState S)
    (hInv : AuthCleanSessionInv P S hst)
    (hCanonEk : P.isCanonical ekAPk = true) :
    let peerPrincipal? := findHonestPrincipal P hst.base.principals bundle.ikB
    let isFreshPeer : Bool :=
      match peerPrincipal? with
      | some (_, pEntry) => !pEntry.corrupted
      | none             => false
    AuthCleanSessionInv P S
      (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst).2 := by
  intro peerPrincipal? isFreshPeer
  have hSubOPK : hst.base.sentOPKEvents ⊆
      (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
          hst).2.base.sentOPKEvents := by
    unfold finishAuthHybridSend
    dsimp only
    cases peerPrincipal? with
    | none => exact List.Subset.refl _
    | some pp =>
      cases bundle.opkB? with
      | none => exact List.Subset.refl _
      | some op => exact List.subset_cons_self _ _
  have hSubNoOPK : hst.base.sentNoOPKEvents ⊆
      (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
          hst).2.base.sentNoOPKEvents := by
    unfold finishAuthHybridSend
    dsimp only
    cases peerPrincipal? with
    | none => exact List.Subset.refl _
    | some pp =>
      cases bundle.opkB? with
      | none => exact List.subset_cons_self _ _
      | some op => exact List.Subset.refl _
  refine ⟨hInv.bundles_canon, hInv.bundles_nodup, hInv.principals_nodup, ?_, ?_⟩
  · intro s hs
    have hMono : ∀ s0 ∈ hst.idealSessions,
        IdealSessionClean P S
          (finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
            ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
            spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache' hst).2 s0 := by
      intro s0 hs0
      exact IdealSessionClean.mono (hInv.sessions_inv s0 hs0)
        (List.Subset.refl _) (List.subset_cons_self _ _) (List.Subset.refl _)
        hSubOPK hSubNoOPK
    unfold finishAuthHybridSend at hs
    dsimp only at hs
    by_cases hIdeal : (isFreshPeer || (peerPrincipal?.isSome &&
        checkBundleSpkHonIdeal P hst.base.principals hst.base.spkBundles bundle &&
        (checkBundleProvenanceExact P hst.base.principals hst.base.spkBundles hst.base.opkEntries
          bundle).2.2)) = true
    · simp only [hIdeal, ↓reduceIte] at hs
      rcases List.mem_cons.mp hs with rfl | hs_old
      · refine ⟨hCanonEk, ?_, ?_⟩
        · unfold finishAuthHybridSend
          dsimp only
          by_cases hfr : isFreshPeer = true
          · left
            refine ⟨_, List.mem_cons_self, Or.inl hfr, rfl, fun hSpkHon => ?_⟩
            exact exists_spkBundle_of_checkBundleProvenanceExact_fst P
              hst.base.principals hst.base.spkBundles hst.base.opkEntries bundle hSpkHon
          · right
            have hfr_f : isFreshPeer = false := Bool.eq_false_iff.mpr hfr
            simp only [hfr_f, Bool.false_or, Bool.and_eq_true] at hIdeal
            rcases hIdeal with ⟨⟨_, _⟩, hPqHon⟩
            cases hfp : peerPrincipal? with
            | none =>
              have hfp' : findHonestPrincipal P hst.base.principals bundle.ikB = none := hfp
              unfold checkBundleProvenanceExact at hPqHon
              rw [hfp'] at hPqHon
              nomatch hPqHon
            | some pp =>
              rcases pp with ⟨kPeer, pEntry⟩
              have hfp' : findHonestPrincipal P hst.base.principals bundle.ikB =
                some (kPeer, pEntry) := hfp
              have hcorr : pEntry.corrupted = true := by
                have hfr_def : isFreshPeer = !pEntry.corrupted := by simp [isFreshPeer, hfp]
                rw [hfr_def, Bool.not_eq_false'] at hfr_f
                exact hfr_f
              have hp_mem : (kPeer, pEntry) ∈ hst.base.principals :=
                List.mem_of_find?_eq_some hfp'
              rcases exists_spkBundle_of_checkBundleProvenanceExact_pq P
                hst.base.principals hst.base.spkBundles hst.base.opkEntries bundle hfp' hPqHon with
                ⟨jPeer, bPeer, hb_mem, hb_pq⟩
              exact ⟨(kPeer, jPeer), bPeer, pEntry, hb_mem, hb_pq, hp_mem, hcorr⟩
        · right
          unfold finishAuthHybridSend
          dsimp only
          cases hfp : peerPrincipal? with
          | none =>
            have hfr_false : isFreshPeer = false := by simp [isFreshPeer, hfp]
            simp [hfr_false, hfp] at hIdeal
          | some pp =>
            rcases pp with ⟨kPeer, pEntry⟩
            have hfp' : findHonestPrincipal P hst.base.principals bundle.ikB =
              some (kPeer, pEntry) := hfp
            unfold findHonestPrincipal at hfp'
            have hbeq := List.find?_some hfp'
            have hpow : P.pow8 pEntry.ikAPk = P.pow8 bundle.ikB :=
              (beq_iff_eq.mp hbeq).symm
            cases hopk : bundle.opkB? with
            | none =>
              dsimp only [Option.map]
              exact ⟨_, List.mem_cons_self, rfl, rfl, hpow, rfl, rfl, rfl, rfl, rfl⟩
            | some op =>
              rcases op with ⟨opkId, opkPk⟩
              dsimp only [Option.map]
              exact ⟨_, List.mem_cons_self, rfl, rfl, hpow, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact hMono s hs_old
    · simp only [hIdeal, Bool.false_eq_true, ↓reduceIte] at hs
      exact hMono s hs
  · intro hBadSig hKemColl
    have hBadOld : hasBadSigAuth hst = false := by
      unfold finishAuthHybridSend hasBadSigAuth at hBadSig
      unfold hasBadSigAuth
      dsimp only [HasAuthState.toAuthState] at hBadSig ⊢
      simp only [List.any_cons, Bool.or_eq_false_iff] at hBadSig
      exact hBadSig.2
    exact hInv.no_false_win hBadOld hKemColl

theorem ite_mem_support {α : Type} {c : Bool} {t e : ProbComp α} {x : α}
    (h : x ∈ support (if c then t else e)) :
    x ∈ support t ∨ x ∈ support e := by
  cases c <;> [exact Or.inr h; exact Or.inl h]

theorem authCleanSessionInv_evalAuthHybridSendKosk {S : Setup}
    (stage : AuthHybridStage) (useRo : Bool) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridState S) (hInv : AuthCleanSessionInv P S hst)
    (resp : AuthResponse) (hst' : AuthHybridState S)
    (hmem : (resp, hst') ∈
      support (evalAuthHybridSendKosk stage useRo S P sid u bundle m0 m1 hst)) :
    AuthCleanSessionInv P S hst' := by
  unfold evalAuthHybridSendKosk at hmem
  by_cases h1 : (m0.length != m1.length) = true
  · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩; exact hInv
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h2 : (hst.base.usedSendSessions.contains sid) = true
    · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
      cases h3 : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        rw [h3] at hmem
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv
      | some up =>
        rcases up with ⟨_, uEntry⟩
        rw [h3] at hmem
        dsimp only at hmem
        rcases ite_mem_support hmem with hmem | hmem
        · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv
        ·
          by_cases h5 : (!koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
            hst.base.advKeys bundle) = true
          · simp only [h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv
          · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
            rw [MonadAttach.mem_support_bind] at hmem
            rcases hmem with ⟨ekASk, _, hmem⟩
            rw [MonadAttach.mem_support_bind] at hmem
            rcases hmem with ⟨kemCoins, _, hmem⟩
            rw [MonadAttach.mem_support_bind] at hmem
            rcases hmem with ⟨ephASk, _, hmem⟩
            rw [MonadAttach.mem_support_bind] at hmem
            rcases hmem with ⟨spqrCoins, _, hmem⟩
            by_cases h6 : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC
              bundle.spkB) bundle.spkSig &&
                             P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM
                               bundle.pqspkB) bundle.pqspkSig)) = true
            · simp only [h6, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hInv
            · simp only [h6, Bool.false_eq_true, ↓reduceIte] at hmem
              cases h7 : P.kemEncaps bundle.pqspkB kemCoins with
              | none =>
                rw [h7] at hmem
                simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInv
              | some kc =>
                rcases kc with ⟨ss, kemCt⟩
                rw [h7] at hmem
                dsimp only at hmem
                rw [MonadAttach.mem_support_bind] at hmem
                rcases hmem with ⟨⟨drKey, roCache', ⟨rk1, ck1_0⟩, rootRoCache', ⟨mkSeed, ck1_1⟩⟩,
                  _, hmem⟩
                cases h8 : P.spqrInitSend drKey.pqrKey spqrCoins with
                | none =>
                  rw [h8] at hmem
                  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hInv
                | some spqr =>
                  rcases spqr with ⟨_, spqrSalt?, pqRatchetMsg⟩
                  rw [h8] at hmem
                  dsimp only at hmem
                  rw [MonadAttach.mem_support_bind] at hmem
                  rcases hmem with ⟨deriveMessageKeys, _, hmem⟩
                  simp only [support_pure, Set.mem_singleton_iff] at hmem
                  have hst_eq := congrArg Prod.snd hmem
                  dsimp only at hst_eq
                  rw [hst_eq]
                  exact authCleanSessionInv_finishAuthHybridSend P sid uEntry bundle m0 m1
                    ekASk (P.x25519Base ekASk) ss kemCt ephASk (P.x25519Base ephASk)
                    drKey rk1 ck1_0 mkSeed ck1_1 spqrSalt? pqRatchetMsg deriveMessageKeys _ _ _
                    roCache' rootRoCache' hst hInv (hWF.canon_base ekASk)

theorem AuthCleanSessionInv.of_eq_fields {P : Primitives} {S : Setup}
    {hst hst' : AuthHybridState S}
    (hInv : AuthCleanSessionInv P S hst)
    (hBundles : hst'.base.spkBundles = hst.base.spkBundles)
    (hSessions : hst'.base.sessions = hst.base.sessions)
    (hTriples : hst'.base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys)
    (hSentOPK : hst'.base.sentOPKEvents = hst.base.sentOPKEvents)
    (hSentNoOPK : hst'.base.sentNoOPKEvents = hst.base.sentNoOPKEvents)
    (hWon : hst'.base.hasWonAuth = hst.base.hasWonAuth)
    (hIdeal : hst'.idealSessions = hst.idealSessions)
    (hPrincipals : hst'.base.principals = hst.base.principals := by rfl) :
    AuthCleanSessionInv P S hst' where
  bundles_canon := by rw [hBundles]; exact hInv.bundles_canon
  bundles_nodup := by rw [hBundles]; exact hInv.bundles_nodup
  principals_nodup := by rw [hPrincipals]; exact hInv.principals_nodup
  sessions_inv := by
    rw [hIdeal]
    intro s hs
    exact IdealSessionClean.mono (hInv.sessions_inv s hs)
      (by rw [hBundles]) (by rw [hSessions]) (by rw [hTriples])
      (by rw [hSentOPK]) (by rw [hSentNoOPK])
      (by intros k pE hm hc; rw [hPrincipals]; exact ⟨pE, hm, hc⟩)
  no_false_win := by
    intro hBadSig hKemColl
    rw [hWon]
    apply hInv.no_false_win
    · unfold hasBadSigAuth at hBadSig ⊢
      dsimp only [HasAuthState.toAuthState] at hBadSig ⊢
      rw [← hSessions]; exact hBadSig
    · unfold hasKemPkCollisionAuth allHonestKemPksAuth at hKemColl ⊢
      dsimp only [HasAuthState.toAuthState] at hKemColl ⊢
      rw [← hBundles]; exact hKemColl

theorem authCleanSessionInv_finishAuthHybridRecvOPK {S : Setup}
    (checkAuth : Bool) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (oEntry : OpkEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes) ×
      (Bytes × Bytes))))
    (hInv : AuthCleanSessionInv P S hstDec)
    (hPrin : (k.val, kEntry) ∈ hstDec.base.principals)
    (hBundle : ((k.val, j.val), bEntry) ∈ hstDec.base.spkBundles)
    (hCanonEk : P.isCanonical msg.hdr.ekAPk = true)
    (hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
      msg.hdr.ekAPk) ∉ hstDec.base.seenKyberBaseKeys)
    (hTriples' : usedTriples' =
      (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
        msg.hdr.ekAPk) :: hstDec.base.seenKyberBaseKeys)
    (hRes : ∀ drKey rk1 ck1_1 pt roCache' rootRoCache',
      res? = some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') →
      (match findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
       | some (_, sEntry) => !sEntry.corrupted
       | none => false) = true →
      ∃ s ∈ hstDec.idealSessions,
        matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk (some oEntry.opkPk) bEntry.pqspkPk
          msg.hdr s = true ∧
        pt = s.msgPlain) :
    AuthCleanSessionInv P S
      (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry usedTriples' msg hstDec
        res?).2 := by
  unfold finishAuthHybridRecvOPK
  cases hres : res? with
  | none => exact hInv
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases hfp : findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none =>
      dsimp only
      refine ⟨hInv.bundles_canon, hInv.bundles_nodup, hInv.principals_nodup, ?_, hInv.no_false_win⟩
      intro s hs
      exact IdealSessionClean.mono (hInv.sessions_inv s hs)
        (List.Subset.refl _) (List.Subset.refl _)
        (by rw [hTriples']; exact List.subset_cons_self _ _)
        (List.Subset.refl _) (List.Subset.refl _)
    | some sp =>
      rcases sp with ⟨sIdx, senderEntry⟩
      dsimp only
      by_cases hcorr : (!senderEntry.corrupted) = true
      · simp only [hcorr, ↓reduceIte]
        set recvEv : RecvdOPKEvent := {
          bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
          sb := bEntry.spkPk, ob := oEntry.opkPk, a1 := msg.hdr.ekAPk,
          pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt
        }
        refine ⟨hInv.bundles_canon, hInv.bundles_nodup, hInv.principals_nodup, ?_, ?_⟩
        · intro s' hs'
          have hsClean := hInv.sessions_inv s' hs'
          refine ⟨hsClean.canon_ek, hsClean.has_sess_entry, ?_⟩
          rcases hsClean.event_or_replayed with ⟨kj, b, hmem, hpk, htr⟩ | hev
          · exact Or.inl ⟨kj, b, hmem, hpk, by rw [hTriples']; exact List.mem_cons_of_mem _ htr⟩
          · cases hopk' : s'.peerOpkPk? with
            | none =>
              rw [hopk'] at hev
              exact Or.inr hev
            | some sOpk' =>
              rw [hopk'] at hev
              rcases hev with ⟨ev', hev'_mem, hEvMatched, hEvA0, hEvB0, hEvSb, hEvOb, hEvA1,
                hEvPk1, hEvCt, hEvM⟩
              rcases mem_consumeMatchingSentOPK_or_match P recvEv hstDec.base.sentOPKEvents ev'
                hev'_mem with hmatch' | hmem'
              · left
                unfold matchSentOPK at hmatch'
                simp only [Bool.and_eq_true, beq_iff_eq] at hmatch'
                rcases hmatch' with ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hPowA1⟩, _⟩, _⟩, hPk1⟩, _⟩, _⟩
                have hek_eq : msg.hdr.ekAPk = s'.ekAPk := by
                  apply hWF.canon_pow8_inj _ _ hCanonEk hsClean.canon_ek
                  calc P.pow8 msg.hdr.ekAPk = P.pow8 ev'.a1 := hPowA1
                    _ = P.pow8 s'.ekAPk := by rw [hEvA1]
                have hpq_eq : bEntry.pqspkPk = s'.peerPqspkPk := hPk1.trans hEvPk1
                refine ⟨(k.val, j.val), bEntry, hBundle, hpq_eq, ?_⟩
                rw [hTriples', ← hek_eq]
                exact List.mem_cons_self
              · exact Or.inr ⟨ev', hmem', hEvMatched, hEvA0, hEvB0, hEvSb, hEvOb, hEvA1, hEvPk1,
                  hEvCt, hEvM⟩
        · intro hBadSig hKemColl
          have hWonOld : hstDec.base.hasWonAuth = false := hInv.no_false_win hBadSig hKemColl
          have hHon : (match findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
                       | some (_, sEntry) => !sEntry.corrupted
                       | none => false) = true := by
            rw [hfp]; exact hcorr
          rcases hRes drKey rk1 ck1_1 pt roCache' rootRoCache' hres hHon with ⟨s, hs_mem, hMatch,
            hPt⟩
          have hsClean := hInv.sessions_inv s hs_mem
          unfold matchIdealAuthHandshake at hMatch
          simp only [Bool.and_eq_true, beq_iff_eq] at hMatch
          rcases hMatch with ⟨⟨⟨⟨⟨⟨hIkA, hIkB⟩, hSpk⟩, hOpkMatch⟩, hEk⟩, hPq⟩, hCt⟩
          have hek_eq : msg.hdr.ekAPk = s.ekAPk :=
            hWF.canon_pow8_inj _ _ hCanonEk hsClean.canon_ek hEk
          have hspk_or_corr : (kEntry.corrupted || bEntry.spkPk == s.peerSpkPk) = true := by
            rcases hsClean.has_sess_entry with ⟨e, he, hfresh, _, hhon⟩ | ⟨kjP, bP, pE, hbP_mem,
              hbP_pq, hpE_mem, hpE_corr⟩
            · have hSpkHon : e.spkHonest = true :=
                hfresh.elim (spkHonest_of_hasBadSigAuth_eq_false hstDec hBadSig e he) id
              rcases hhon hSpkHon with ⟨kjS, bS, hbS_mem, hbS_spk⟩
              have hCanonSpkS : P.isCanonical s.peerSpkPk = true := by
                rw [← hbS_spk]; exact hInv.bundles_canon kjS bS hbS_mem
              have hCanonSpkB : P.isCanonical bEntry.spkPk = true :=
                hInv.bundles_canon (k.val, j.val) bEntry hBundle
              have hspk_eq : bEntry.spkPk = s.peerSpkPk :=
                hWF.canon_pow8_inj _ _ hCanonSpkB hCanonSpkS hSpk
              simp [hspk_eq]
            · have hkj : kjP = (k.val, j.val) :=
                spkBundles_fst_eq_of_pqspkPk_eq hstDec.base.spkBundles hInv.bundles_nodup hKemColl
                  kjP bP (k.val, j.val) bEntry hbP_mem hBundle (hbP_pq.trans hPq.symm)
              have hk_eq : kjP.1 = k.val := congrArg Prod.fst hkj
              rw [hk_eq] at hpE_mem
              have hpE_eq : pE = kEntry :=
                principals_eq_of_nodup hInv.principals_nodup hpE_mem hPrin
              rw [← hpE_eq, hpE_corr, Bool.true_or]
          rcases hsClean.event_or_replayed with ⟨kj0, b0, hb0_mem, hb0_pq, htr0⟩ | hev
          · exfalso
            have hkj : kj0 = (k.val, j.val) :=
              spkBundles_fst_eq_of_pqspkPk_eq hstDec.base.spkBundles hInv.bundles_nodup hKemColl
                kj0 b0 (k.val, j.val) bEntry hb0_mem hBundle (hb0_pq.trans hPq.symm)
            rw [hkj, ← hek_eq] at htr0
            exact hNotUsed htr0
          · cases hopk : s.peerOpkPk? with
            | none =>
              rw [hopk] at hOpkMatch
              cases hOpkMatch
            | some sOpk =>
              rw [hopk] at hOpkMatch hev
              simp only [beq_iff_eq] at hOpkMatch
              rcases hev with ⟨ev, hev_mem, hEvMatched, hEvA0, hEvB0, hEvSb, hEvOb, hEvA1, hEvPk1,
                hEvCt, hEvM⟩
              have hMatchEv : matchSentOPK P recvEv ev = true := by
                unfold matchSentOPK
                simp only [recvEv, hEvMatched, Bool.not_false, hEvA0, hEvSb, hEvOb, hEvA1,
                  hEvPk1, hEvCt, hEvM, hIkA, hIkB, hEvB0, hOpkMatch, hEk, hSpk, hspk_or_corr,
                  hPq, hCt, hPt, beq_self_eq_true, Bool.and_self]
              have hMatchedOk : (consumeMatchingSentOPK P recvEv hstDec.base.sentOPKEvents).1 =
                true :=
                consumeMatchingSentOPK_fst_eq_true_of_mem P recvEv hstDec.base.sentOPKEvents ev
                  hev_mem hMatchEv
              simp [hWonOld, hMatchedOk]
      · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hInv.bundles_canon, hInv.bundles_nodup, hInv.principals_nodup, ?_,
          hInv.no_false_win⟩
        intro s hs
        exact IdealSessionClean.mono (hInv.sessions_inv s hs)
          (List.Subset.refl _) (List.Subset.refl _)
          (by rw [hTriples']; exact List.subset_cons_self _ _)
          (List.Subset.refl _) (List.Subset.refl _)

theorem authCleanSessionInv_finishAuthHybridRecvNoOPK {S : Setup}
    (checkAuth : Bool) (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry)
    (usedTriples' : List (Nat × KeyId × KeyId × Bytes)) (msg : PreKeyMsg)
    (hstDec : AuthHybridState S)
    (res? : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) × List ((Bytes × Bytes) ×
      (Bytes × Bytes))))
    (hInv : AuthCleanSessionInv P S hstDec)
    (hPrin : (k.val, kEntry) ∈ hstDec.base.principals)
    (hBundle : ((k.val, j.val), bEntry) ∈ hstDec.base.spkBundles)
    (hCanonEk : P.isCanonical msg.hdr.ekAPk = true)
    (hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
      msg.hdr.ekAPk) ∉ hstDec.base.seenKyberBaseKeys)
    (hTriples' : usedTriples' =
      (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
        msg.hdr.ekAPk) :: hstDec.base.seenKyberBaseKeys)
    (hRes : ∀ drKey rk1 ck1_1 pt roCache' rootRoCache',
      res? = some (drKey, rk1, ck1_1, pt, roCache', rootRoCache') →
      (match findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
       | some (_, sEntry) => !sEntry.corrupted
       | none => false) = true →
      ∃ s ∈ hstDec.idealSessions,
        matchIdealAuthHandshake P kEntry.ikAPk bEntry.spkPk none bEntry.pqspkPk msg.hdr s = true ∧
        pt = s.msgPlain) :
    AuthCleanSessionInv P S
      (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry usedTriples' msg hstDec res?).2 :=
        by
  unfold finishAuthHybridRecvNoOPK
  cases hres : res? with
  | none => exact hInv
  | some r =>
    rcases r with ⟨drKey, rk1, ck1_1, pt, roCache', rootRoCache'⟩
    dsimp only
    cases hfp : findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
    | none =>
      dsimp only
      refine ⟨hInv.bundles_canon, hInv.bundles_nodup, hInv.principals_nodup, ?_, hInv.no_false_win⟩
      intro s hs
      exact IdealSessionClean.mono (hInv.sessions_inv s hs)
        (List.Subset.refl _) (List.Subset.refl _)
        (by rw [hTriples']; exact List.subset_cons_self _ _)
        (List.Subset.refl _) (List.Subset.refl _)
    | some sp =>
      rcases sp with ⟨sIdx, senderEntry⟩
      dsimp only
      by_cases hcorr : (!senderEntry.corrupted) = true
      · simp only [hcorr, ↓reduceIte]
        set recvEv : RecvdNoOPKEvent := {
          bCorr := kEntry.corrupted, a0 := msg.hdr.ikAPk, b0 := kEntry.ikAPk,
          sb := bEntry.spkPk, a1 := msg.hdr.ekAPk,
          pk1 := bEntry.pqspkPk, ct := msg.hdr.kemCt, m := pt
        }
        refine ⟨hInv.bundles_canon, hInv.bundles_nodup, hInv.principals_nodup, ?_, ?_⟩
        · intro s' hs'
          have hsClean := hInv.sessions_inv s' hs'
          refine ⟨hsClean.canon_ek, hsClean.has_sess_entry, ?_⟩
          rcases hsClean.event_or_replayed with ⟨kj, b, hmem, hpk, htr⟩ | hev
          · exact Or.inl ⟨kj, b, hmem, hpk, by rw [hTriples']; exact List.mem_cons_of_mem _ htr⟩
          · cases hopk' : s'.peerOpkPk? with
            | some sOpk' =>
              rw [hopk'] at hev
              exact Or.inr hev
            | none =>
              rw [hopk'] at hev
              rcases hev with ⟨ev', hev'_mem, hEvMatched, hEvA0, hEvB0, hEvSb, hEvA1, hEvPk1,
                hEvCt, hEvM⟩
              rcases mem_consumeMatchingSentNoOPK_or_match P recvEv hstDec.base.sentNoOPKEvents ev'
                hev'_mem with hmatch' | hmem'
              · left
                unfold matchSentNoOPK at hmatch'
                simp only [Bool.and_eq_true, beq_iff_eq] at hmatch'
                rcases hmatch' with ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hPowA1⟩, _⟩, _⟩, hPk1⟩, _⟩, _⟩
                have hek_eq : msg.hdr.ekAPk = s'.ekAPk := by
                  apply hWF.canon_pow8_inj _ _ hCanonEk hsClean.canon_ek
                  calc P.pow8 msg.hdr.ekAPk = P.pow8 ev'.a1 := hPowA1
                    _ = P.pow8 s'.ekAPk := by rw [hEvA1]
                have hpq_eq : bEntry.pqspkPk = s'.peerPqspkPk := hPk1.trans hEvPk1
                refine ⟨(k.val, j.val), bEntry, hBundle, hpq_eq, ?_⟩
                rw [hTriples', ← hek_eq]
                exact List.mem_cons_self
              · exact Or.inr ⟨ev', hmem', hEvMatched, hEvA0, hEvB0, hEvSb, hEvA1, hEvPk1, hEvCt,
                  hEvM⟩
        · intro hBadSig hKemColl
          have hWonOld : hstDec.base.hasWonAuth = false := hInv.no_false_win hBadSig hKemColl
          have hHon : (match findHonestPrincipal P hstDec.base.principals msg.hdr.ikAPk with
                       | some (_, sEntry) => !sEntry.corrupted
                       | none => false) = true := by
            rw [hfp]; exact hcorr
          rcases hRes drKey rk1 ck1_1 pt roCache' rootRoCache' hres hHon with ⟨s, hs_mem, hMatch,
            hPt⟩
          have hsClean := hInv.sessions_inv s hs_mem
          unfold matchIdealAuthHandshake at hMatch
          simp only [Bool.and_eq_true, beq_iff_eq] at hMatch
          rcases hMatch with ⟨⟨⟨⟨⟨⟨hIkA, hIkB⟩, hSpk⟩, hOpkMatch⟩, hEk⟩, hPq⟩, hCt⟩
          have hek_eq : msg.hdr.ekAPk = s.ekAPk :=
            hWF.canon_pow8_inj _ _ hCanonEk hsClean.canon_ek hEk
          have hspk_or_corr : (kEntry.corrupted || bEntry.spkPk == s.peerSpkPk) = true := by
            rcases hsClean.has_sess_entry with ⟨e, he, hfresh, _, hhon⟩ | ⟨kjP, bP, pE, hbP_mem,
              hbP_pq, hpE_mem, hpE_corr⟩
            · have hSpkHon : e.spkHonest = true :=
                hfresh.elim (spkHonest_of_hasBadSigAuth_eq_false hstDec hBadSig e he) id
              rcases hhon hSpkHon with ⟨kjS, bS, hbS_mem, hbS_spk⟩
              have hCanonSpkS : P.isCanonical s.peerSpkPk = true := by
                rw [← hbS_spk]; exact hInv.bundles_canon kjS bS hbS_mem
              have hCanonSpkB : P.isCanonical bEntry.spkPk = true :=
                hInv.bundles_canon (k.val, j.val) bEntry hBundle
              have hspk_eq : bEntry.spkPk = s.peerSpkPk :=
                hWF.canon_pow8_inj _ _ hCanonSpkB hCanonSpkS hSpk
              simp [hspk_eq]
            · have hkj : kjP = (k.val, j.val) :=
                spkBundles_fst_eq_of_pqspkPk_eq hstDec.base.spkBundles hInv.bundles_nodup hKemColl
                  kjP bP (k.val, j.val) bEntry hbP_mem hBundle (hbP_pq.trans hPq.symm)
              have hk_eq : kjP.1 = k.val := congrArg Prod.fst hkj
              rw [hk_eq] at hpE_mem
              have hpE_eq : pE = kEntry :=
                principals_eq_of_nodup hInv.principals_nodup hpE_mem hPrin
              rw [← hpE_eq, hpE_corr, Bool.true_or]
          rcases hsClean.event_or_replayed with ⟨kj0, b0, hb0_mem, hb0_pq, htr0⟩ | hev
          · exfalso
            have hkj : kj0 = (k.val, j.val) :=
              spkBundles_fst_eq_of_pqspkPk_eq hstDec.base.spkBundles hInv.bundles_nodup hKemColl
                kj0 b0 (k.val, j.val) bEntry hb0_mem hBundle (hb0_pq.trans hPq.symm)
            rw [hkj, ← hek_eq] at htr0
            exact hNotUsed htr0
          · cases hopk : s.peerOpkPk? with
            | some sOpk =>
              rw [hopk] at hOpkMatch
              cases hOpkMatch
            | none =>
              rw [hopk] at hev
              rcases hev with ⟨ev, hev_mem, hEvMatched, hEvA0, hEvB0, hEvSb, hEvA1, hEvPk1, hEvCt,
                hEvM⟩
              have hMatchEv : matchSentNoOPK P recvEv ev = true := by
                unfold matchSentNoOPK
                simp only [recvEv, hEvMatched, Bool.not_false, hEvA0, hEvSb, hEvA1,
                  hEvPk1, hEvCt, hEvM, hIkA, hIkB, hEvB0, hEk, hSpk, hspk_or_corr,
                  hPq, hCt, hPt, beq_self_eq_true, Bool.and_self]
              have hMatchedOk : (consumeMatchingSentNoOPK P recvEv hstDec.base.sentNoOPKEvents).1 =
                true :=
                consumeMatchingSentNoOPK_fst_eq_true_of_mem P recvEv hstDec.base.sentNoOPKEvents ev
                  hev_mem hMatchEv
              simp [hWonOld, hMatchedOk]
      · simp only [hcorr, Bool.false_eq_true, ↓reduceIte]
        refine ⟨hInv.bundles_canon, hInv.bundles_nodup, hInv.principals_nodup, ?_,
          hInv.no_false_win⟩
        intro s hs
        exact IdealSessionClean.mono (hInv.sessions_inv s hs)
          (List.Subset.refl _) (List.Subset.refl _)
          (by rw [hTriples']; exact List.subset_cons_self _ _)
          (List.Subset.refl _) (List.Subset.refl _)

theorem bind_congr_of_mem_support {α β : Type}
    (oa : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ x ∈ support oa, f x = g x) :
    oa >>= f = oa >>= g := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simpa using h x (by simp)
  | query_bind i t ih =>
    rw [bind_assoc, bind_assoc]
    apply bind_congr; intro u
    exact ih u (fun x hx => h x (MonadAttach.mem_support_bind.mpr ⟨u, by simp, hx⟩))

theorem authCleanSessionInv_pqxdhAuthHybridSplitKoskImpl_g5 {S : Setup}
    (sendStage : AuthHybridStage) (useRo checkAuth : Bool)
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (q : AuthQuery S) (hst : AuthHybridState S)
    (hInv : AuthCleanSessionInv P S hst)
    (resp : AuthResponse) (hst' : AuthHybridState S)
    (hmem : (resp, hst') ∈
      support ((pqxdhAuthHybridSplitKoskImpl sendStage .g5 useRo checkAuth S P q).run hst)) :
    AuthCleanSessionInv P S hst' := by
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h : bundle.opkB?.isNone = true
    · simp only [ h, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [runAuthHybridSendKosk_eq] at hmem
      exact authCleanSessionInv_evalAuthHybridSendKosk sendStage useRo P hWF
        (.sendOPK u i) u bundle m0 m1 hst hInv resp hst' hmem
  | sendNoOPK u i bundle m0 m1 =>
    unfold pqxdhAuthHybridSplitKoskImpl at hmem
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h : bundle.opkB?.isSome = true
    · simp only [ h, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hmem
      rw [runAuthHybridSendKosk_eq] at hmem
      exact authCleanSessionInv_evalAuthHybridSendKosk sendStage useRo P hWF
        (.sendNoOPK u i) u bundle m0 m1 hst hInv resp hst' hmem
  | recvOPK k j o msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvOPK_eq] at hmem
    unfold prepareAuthHybridRecvOPK at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                     msg.hdr.pqspkId == UInt32.ofNat j.val &&
                     msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                     msg.hdr.ikAPk.length == 32 &&
                     msg.hdr.ekAPk.length == 32 &&
                     msg.ephAPk.length == 32)) = true
    · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h2 : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
      · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
        · simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv
        · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
          cases hp : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none =>
            simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv
          | some kp =>
            rcases kp with ⟨_, kEntry⟩
            cases hb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
            | none =>
              simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hInv
            | some bp =>
              rcases bp with ⟨idxB, bEntry⟩
              cases ho : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val,
                o.val)) with
              | none =>
                simp only [hp, hb, ho, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInv
              | some op =>
                rcases op with ⟨_, oEntry⟩
                simp only [hp, hb, ho] at hmem
                by_cases h4 : oEntry.consumed = true
                · simp only [ h4, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                    ] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hInv
                · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hmem
                  by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                    msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                                 !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                  · simp only [ h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                      ] at hmem
                    rcases hmem with ⟨_, rfl⟩; exact hInv
                  · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
                    cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                    | none =>
                      simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                      rcases hmem with ⟨_, rfl⟩; exact hInv
                    | some ss =>
                      simp only [hdec, mem_support_fmap_iff] at hmem
                      rcases hmem with ⟨res?, hres_mem, hfin⟩
                      have hst_eq : hst' =
                        (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry
                          (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                            msg.hdr.spkId msg.hdr.ekAPk).2
                          msg { hst with recvKemRecs := _ :: hst.recvKemRecs } res?).2 :=
                        (congrArg Prod.snd hfin).symm
                      rw [hst_eq]
                      simp only [ Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true,
                          beq_iff_eq] at h1
                      rcases h1 with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, _⟩, _⟩, _⟩, _⟩
                      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at h5
                      rcases h5 with ⟨⟨hReplay, hCanonEk⟩, _⟩
                      have hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                        msg.hdr.ekAPk) ∉ hst.base.seenKyberBaseKeys := by
                        unfold checkAndMarkKyberBaseKeySeen at hReplay
                        dsimp only at hReplay
                        rw [hPqspkId, hSpkId] at hReplay
                        intro hm
                        have hc := List.contains_iff_mem.mpr hm
                        rw [hc] at hReplay
                        cases hReplay
                      have hTriples' : (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                        msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2 =
                          (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                            msg.hdr.ekAPk) :: hst.base.seenKyberBaseKeys := by
                        unfold checkAndMarkKyberBaseKeySeen
                        simp [hPqspkId, hSpkId, hNotUsed]
                      exact authCleanSessionInv_finishAuthHybridRecvOPK checkAuth P hWF k j o
                        kEntry bEntry oEntry _ msg
                        { hst with recvKemRecs := _ :: hst.recvKemRecs }
                        res? (hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl)
                        (by dsimp only; exact mem_of_find?_fst_beq hp)
                        (by dsimp only; exact mem_of_find?_fst_beq hb)
                        hCanonEk hNotUsed hTriples' (fun dk rk ck pt ro rro hres_eq hHon => by
                          subst hres_eq
                          exact mem_support_evalAuthHybridRecvSchedule_g5_honest useRo P _
                            kEntry bEntry (some oEntry.opkPk) _ msg dk rk ck pt ro rro hHon
                              hres_mem)
  | recvNoOPK k j l msg =>
    rw [pqxdhAuthHybridSplitKoskImpl_recvNoOPK_eq] at hmem
    unfold prepareAuthHybridRecvNoOPK at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
    by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                     msg.hdr.pqspkId == UInt32.ofNat j.val &&
                     msg.hdr.opkId? == none &&
                     msg.hdr.ikAPk.length == 32 &&
                     msg.hdr.ekAPk.length == 32 &&
                     msg.ephAPk.length == 32)) = true
    · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hInv
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h2 : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
      · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases h3 : (!koskSenderOk P hst.base.principals hst.base.advKeys msg.hdr.ikAPk) = true
        · simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv
        · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
          cases hp : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
          | none =>
            simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv
          | some kp =>
            rcases kp with ⟨_, kEntry⟩
            cases hb : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
            | none =>
              simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hInv
            | some bp =>
              rcases bp with ⟨idxB, bEntry⟩
              simp only [hp, hb] at hmem
              by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                msg.hdr.spkId msg.hdr.ekAPk).1 ||
                             !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
              · simp only [ h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                  ] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInv
              · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
                cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                | none =>
                  simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hInv
                | some ss =>
                  simp only [hdec, mem_support_fmap_iff] at hmem
                  rcases hmem with ⟨res?, hres_mem, hfin⟩
                  have hst_eq : hst' = (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry
                      (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                        msg.hdr.spkId msg.hdr.ekAPk).2
                      msg { hst with recvKemRecs := _ :: hst.recvKemRecs } res?).2 :=
                    (congrArg Prod.snd hfin).symm
                  rw [hst_eq]
                  simp only [ Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq
                    ] at h1
                  rcases h1 with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, _⟩, _⟩, _⟩, _⟩
                  simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at h5
                  rcases h5 with ⟨⟨hReplay, hCanonEk⟩, _⟩
                  have hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                    msg.hdr.ekAPk) ∉ hst.base.seenKyberBaseKeys := by
                    unfold checkAndMarkKyberBaseKeySeen at hReplay
                    dsimp only at hReplay
                    rw [hPqspkId, hSpkId] at hReplay
                    intro hm
                    have hc := List.contains_iff_mem.mpr hm
                    rw [hc] at hReplay
                    cases hReplay
                  have hTriples' : (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val
                    msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2 =
                      (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                        msg.hdr.ekAPk) :: hst.base.seenKyberBaseKeys := by
                    unfold checkAndMarkKyberBaseKeySeen
                    simp [hPqspkId, hSpkId, hNotUsed]
                  exact authCleanSessionInv_finishAuthHybridRecvNoOPK checkAuth P hWF k j l
                    kEntry bEntry _ msg
                    { hst with recvKemRecs := _ :: hst.recvKemRecs }
                    res? (hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl)
                    (by dsimp only; exact mem_of_find?_fst_beq hp)
                    (by dsimp only; exact mem_of_find?_fst_beq hb)
                    hCanonEk hNotUsed hTriples' (fun dk rk ck pt ro rro hres_eq hHon => by
                      subst hres_eq
                      exact mem_support_evalAuthHybridRecvSchedule_g5_honest useRo P _
                        kEntry bEntry none _ msg dk rk ck pt ro rro hHon hres_mem)
  | initPrin u =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (hst.base.principals.any (fun (idx, _) => idx == u.val)) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨_, _, _, _, _, rfl⟩
      refine ⟨hInv.bundles_canon, hInv.bundles_nodup, ?_, ?_, hInv.no_false_win⟩
      · dsimp only
        rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, hInv.principals_nodup⟩
        intro hmem_fst
        rw [List.mem_map] at hmem_fst
        rcases hmem_fst with ⟨⟨idx0, e0⟩, hmem0, hfst0⟩
        dsimp only at hfst0
        subst hfst0
        exact h (List.any_eq_true.mpr ⟨(u.val, e0), hmem0, by simp⟩)
      · intro s hs
        exact IdealSessionClean.mono (hInv.sessions_inv s hs)
          (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
          (List.Subset.refl _) (List.Subset.refl _)
          (fun k pE hm hc => ⟨pE, List.mem_cons_of_mem _ hm, hc⟩)
  | corruptIK u =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    cases h : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    | some p =>
      rcases p with ⟨_, entry⟩
      simp [h, StateT.run_set] at hbase
      rcases hbase with ⟨_, rfl⟩
      refine ⟨hInv.bundles_canon, hInv.bundles_nodup, ?_, ?_, hInv.no_false_win⟩
      · dsimp only
        rw [List.map_map]
        have hEq :
            List.map (Prod.fst ∘ fun (x : Nat × PrincipalEntry) =>
              if x.1 = u.val then (x.1, { x.2 with corrupted :=
                true }) else x) hst.base.principals =
            List.map Prod.fst hst.base.principals := by
          apply List.map_congr_left
          rintro ⟨idx, e⟩ _
          dsimp only [Function.comp_apply]
          split <;> rfl
        rw [hEq]
        exact hInv.principals_nodup
      · intro s hs
        exact IdealSessionClean.mono (hInv.sessions_inv s hs)
          (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
          (List.Subset.refl _) (List.Subset.refl _)
          (fun k pE hm hc => by
            dsimp only
            by_cases hku : k = u.val
            · refine ⟨{ pE with corrupted := true }, ?_, rfl⟩
              have hmem_map := List.mem_map_of_mem (f := fun (x : Nat × PrincipalEntry) =>
                if x.1 = u.val then (x.1, { x.2 with corrupted := true }) else x) hm
              simpa [hku] using hmem_map
            · refine ⟨pE, ?_, hc⟩
              have hmem_map := List.mem_map_of_mem (f := fun (x : Nat × PrincipalEntry) =>
                if x.1 = u.val then (x.1, { x.2 with corrupted := true }) else x) hm
              simpa [hku] using hmem_map)
  | genSPK u j =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at hbase
      cases hp : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [hp] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
      | some p =>
        rcases p with ⟨_, uEntry⟩
        simp only [hp, StateT.run_bind, StateT.run_monadLift, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hbase
        rcases hbase with ⟨spkSk, _, r1, _, ⟨pqspkPk, pqspkSk⟩, _, r2, _, _, rfl⟩
        refine ⟨?_, ?_, hInv.principals_nodup, ?_, ?_⟩
        · intro kj b hmem_b
          rcases List.mem_cons.mp hmem_b with hhead | htail
          · cases hhead
            exact hWF.canon_base spkSk
          · exact hInv.bundles_canon kj b htail
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, hInv.bundles_nodup⟩
          intro hmem_fst
          rw [List.mem_map] at hmem_fst
          rcases hmem_fst with ⟨⟨kj0, b0⟩, hmem0, hfst0⟩
          dsimp only at hfst0
          subst hfst0
          have hany : (hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true := by
            rw [List.any_eq_true]
            exact ⟨((u.val, j.val), b0), hmem0, by simp⟩
          exact h hany
        · intro s hs
          exact IdealSessionClean.mono (hInv.sessions_inv s hs)
            (List.subset_cons_self _ _) (List.Subset.refl _) (List.Subset.refl _)
            (List.Subset.refl _) (List.Subset.refl _)
        · intro hBadSig hKemColl
          have hKemOld : hasKemPkCollisionAuth hst = false := by
            change hasDuplicateBytes (pqspkPk :: allHonestKemPksAuth hst) = false at hKemColl
            simp only [hasDuplicateBytes, Bool.or_eq_false_iff] at hKemColl
            exact hKemColl.2
          exact hInv.no_false_win hBadSig hKemOld
  | genOPK u j o =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨_, _, _, rfl⟩
      exact hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl
  | registerKey sk =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    cases h : registerAdvKey P hst.base.advKeys sk with
    | none => simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    | some kp =>
      rcases kp with ⟨_, _⟩
      simp [h, StateT.run_set] at hbase
      rcases hbase with ⟨_, rfl⟩
      exact hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl
  | roQuery secrets =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (!useRo) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨⟨_, _⟩, _, _, rfl⟩
      exact hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl
  | roRootQuery rk dh =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : (!useRo) = true
    · simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv
    · simp only [h, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hbase
      rcases hbase with ⟨⟨_, _⟩, _, _, rfl⟩
      exact hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl
  | revealDhSecrets =>
    unfold pqxdhAuthHybridSplitKoskImpl pqxdhAuthImpl at hmem
    rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases h0 : (checkAuth && hst.base.hasWonAuth) = true
    { simp [h0] at hmem; rcases hmem with ⟨_, rfl⟩; exact hInv }
    simp only [h0, Bool.false_eq_true, ↓reduceIte, run_liftAuthBase, mem_support_fmap_iff] at hmem
    rcases hmem with ⟨⟨r, base'⟩, hbase, hprod⟩
    have hst_eq : hst' = { hst with base := base' } := (congrArg Prod.snd hprod).symm
    rw [hst_eq]
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hbase
    by_cases h : useRo = true <;> (simp [h] at hbase; rcases hbase with ⟨_, rfl⟩; exact hInv)

theorem authCleanSessionInv_fullSplitFixedImpl_g5 {S : Setup}
    (sendStage : AuthHybridStage) (useRo checkAuth : Bool)
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (q : (unifSpec + authSpec S).Domain) (hst : AuthHybridStateFixed S)
    (hInv : AuthCleanSessionInv P S hst.toAuthHybridState)
    (resp : (unifSpec + authSpec S).Range q) (hst' : AuthHybridStateFixed S)
    (hmem : (resp, hst') ∈
      support ((((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (AuthHybridStateFixed S)
        ProbComp) +
        pqxdhAuthHybridSplitFixedImpl sendStage .g5 useRo checkAuth S P) q).run hst)) :
    AuthCleanSessionInv P S hst'.toAuthHybridState := by
  cases q with
  | inl uq =>
    change (resp, hst') ∈
      support ((monadLift (QueryImpl.ofLift unifSpec ProbComp uq) : StateT (AuthHybridStateFixed S)
        ProbComp _).run hst) at hmem
    rw [StateT.run_monadLift, MonadAttach.mem_support_bind] at hmem
    rcases hmem with ⟨_, _, h2⟩
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h2
    rcases h2 with ⟨_, rfl⟩
    exact hInv
  | inr kq =>
    change (resp, hst') ∈
      support ((pqxdhAuthHybridSplitFixedImpl sendStage .g5 useRo checkAuth S P kq).run hst) at hmem
    have hIdeal : (AuthHybridStage.g5).idealMsgKeys = true := rfl
    have hApply :=
      authCleanSessionInv_pqxdhAuthHybridSplitKoskImpl_g5 sendStage useRo checkAuth P hWF kq
        hst.toAuthHybridState hInv
    cases kq with
    | recvOPK k j o msg =>
      clear hApply
      unfold pqxdhAuthHybridSplitFixedImpl at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind,
        pqxdhAuthHybridFixedImpl_recvOPK_eq .g5 hIdeal] at hmem
      unfold prepareAuthHybridRecvOPK at hmem
      by_cases h0 : (checkAuth && hst.toAuthHybridState.base.hasWonAuth) = true
      { simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv }
      simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                       msg.hdr.pqspkId == UInt32.ofNat j.val &&
                       msg.hdr.opkId? == some (UInt32.ofNat o.val) &&
                       msg.hdr.ikAPk.length == 32 &&
                       msg.hdr.ekAPk.length == 32 &&
                       msg.ephAPk.length == 32)) = true
      · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases h2 : (hst.toAuthHybridState.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
        · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
            hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
          · simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv
          · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
            cases hp : hst.toAuthHybridState.base.principals.find? (fun (idx,
              _) => idx == k.val) with
            | none =>
              simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hInv
            | some kp =>
              rcases kp with ⟨_, kEntry⟩
              cases hb : hst.toAuthHybridState.base.spkBundles.find? (fun (idx,
                _) => idx == (k.val, j.val)) with
              | none =>
                simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInv
              | some bp =>
                rcases bp with ⟨idxB, bEntry⟩
                cases ho : hst.toAuthHybridState.base.opkEntries.find? (fun (idx,
                  _) => idx == (k.val, j.val, o.val)) with
                | none =>
                  simp only [hp, hb, ho, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hInv
                | some op =>
                  rcases op with ⟨_, oEntry⟩
                  simp only [hp, hb, ho] at hmem
                  by_cases h4 : oEntry.consumed = true
                  · simp only [ h4, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                      ] at hmem
                    rcases hmem with ⟨_, rfl⟩; exact hInv
                  · simp only [h4, Bool.false_eq_true, ↓reduceIte] at hmem
                    by_cases h5 : (!(checkAndMarkKyberBaseKeySeen
                      hst.toAuthHybridState.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                        msg.hdr.spkId msg.hdr.ekAPk).1 ||
                                   !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                    · simp only [ h5, ↓reduceIte, support_pure, Set.mem_singleton_iff,
                          Prod.mk.injEq] at hmem
                      rcases hmem with ⟨_, rfl⟩; exact hInv
                    · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
                      cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                      | none =>
                        simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                        rcases hmem with ⟨_, rfl⟩; exact hInv
                      | some ss =>
                        simp only [hdec, mem_support_fmap_iff] at hmem
                        rcases hmem with ⟨⟨res?, mkSaltCache'⟩, hres_mem, hfin⟩
                        have hst_eq : hst'.toAuthHybridState =
                          (finishAuthHybridRecvOPK checkAuth P k j o kEntry bEntry oEntry
                            (checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys k.val
                              msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2
                            msg { hst.toAuthHybridState with recvKemRecs :=
                              _ :: hst.toAuthHybridState.recvKemRecs } res?).2 :=
                          congrArg AuthHybridStateFixed.toAuthHybridState (congrArg Prod.snd
                            hfin).symm
                        rw [hst_eq]
                        simp only [ Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true,
                            beq_iff_eq] at h1
                        rcases h1 with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, _⟩, _⟩, _⟩, _⟩
                        simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at h5
                        rcases h5 with ⟨⟨hReplay, hCanonEk⟩, _⟩
                        have hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                          msg.hdr.ekAPk) ∉ hst.toAuthHybridState.base.seenKyberBaseKeys := by
                          unfold checkAndMarkKyberBaseKeySeen at hReplay
                          dsimp only at hReplay
                          rw [hPqspkId, hSpkId] at hReplay
                          intro hm
                          have hc := List.contains_iff_mem.mpr hm
                          rw [hc] at hReplay
                          cases hReplay
                        have hTriples' : (checkAndMarkKyberBaseKeySeen
                          hst.toAuthHybridState.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                            msg.hdr.spkId msg.hdr.ekAPk).2 =
                            (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                              msg.hdr.ekAPk) :: hst.toAuthHybridState.base.seenKyberBaseKeys := by
                          unfold checkAndMarkKyberBaseKeySeen
                          simp [hPqspkId, hSpkId, hNotUsed]
                        exact authCleanSessionInv_finishAuthHybridRecvOPK checkAuth P hWF k j o
                          kEntry bEntry oEntry _ msg
                          { hst.toAuthHybridState with recvKemRecs :=
                            _ :: hst.toAuthHybridState.recvKemRecs }
                          res? (hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl)
                          (by dsimp only; exact mem_of_find?_fst_beq hp)
                          (by dsimp only; exact mem_of_find?_fst_beq hb)
                          hCanonEk hNotUsed hTriples' (fun dk rk ck pt ro rro hres_eq hHon => by
                            subst hres_eq
                            exact mem_support_evalAuthFixedRecvScheduleCached_g5_honest useRo P _
                              hst.recvCount hst.mkSaltCache kEntry bEntry (some oEntry.opkPk) _ msg
                                dk rk ck pt ro rro mkSaltCache' hHon hres_mem)
    | recvNoOPK k j l msg =>
      clear hApply
      unfold pqxdhAuthHybridSplitFixedImpl at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get, pure_bind,
        pqxdhAuthHybridFixedImpl_recvNoOPK_eq .g5 hIdeal] at hmem
      unfold prepareAuthHybridRecvNoOPK at hmem
      by_cases h0 : (checkAuth && hst.toAuthHybridState.base.hasWonAuth) = true
      { simp only [h0, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv }
      simp only [h0, Bool.false_eq_true, ↓reduceIte] at hmem
      by_cases h1 : (!(msg.hdr.spkId == UInt32.ofNat j.val &&
                       msg.hdr.pqspkId == UInt32.ofNat j.val &&
                       msg.hdr.opkId? == none &&
                       msg.hdr.ikAPk.length == 32 &&
                       msg.hdr.ekAPk.length == 32 &&
                       msg.ephAPk.length == 32)) = true
      · simp only [h1, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hInv
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hmem
        by_cases h2 : (hst.toAuthHybridState.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) =
          true
        · simp only [h2, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hInv
        · simp only [h2, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases h3 : (!koskSenderOk P hst.toAuthHybridState.base.principals
            hst.toAuthHybridState.base.advKeys msg.hdr.ikAPk) = true
          · simp only [h3, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hInv
          · simp only [h3, Bool.false_eq_true, ↓reduceIte] at hmem
            cases hp : hst.toAuthHybridState.base.principals.find? (fun (idx,
              _) => idx == k.val) with
            | none =>
              simp only [hp, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hInv
            | some kp =>
              rcases kp with ⟨_, kEntry⟩
              cases hb : hst.toAuthHybridState.base.spkBundles.find? (fun (idx,
                _) => idx == (k.val, j.val)) with
              | none =>
                simp only [hp, hb, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                rcases hmem with ⟨_, rfl⟩; exact hInv
              | some bp =>
                rcases bp with ⟨idxB, bEntry⟩
                simp only [hp, hb] at hmem
                by_cases h5 : (!(checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys
                  k.val msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).1 ||
                               !P.isCanonical msg.hdr.ekAPk || !P.isCanonical msg.ephAPk) = true
                · simp only [ h5, ↓reduceIte, support_pure, Set.mem_singleton_iff, Prod.mk.injEq
                    ] at hmem
                  rcases hmem with ⟨_, rfl⟩; exact hInv
                · simp only [h5, Bool.false_eq_true, ↓reduceIte] at hmem
                  cases hdec : P.kemDecaps bEntry.pqspkSk msg.hdr.kemCt with
                  | none =>
                    simp only [hdec, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
                    rcases hmem with ⟨_, rfl⟩; exact hInv
                  | some ss =>
                    simp only [hdec, mem_support_fmap_iff] at hmem
                    rcases hmem with ⟨⟨res?, mkSaltCache'⟩, hres_mem, hfin⟩
                    have hst_eq : hst'.toAuthHybridState =
                      (finishAuthHybridRecvNoOPK checkAuth P k j l kEntry bEntry
                        (checkAndMarkKyberBaseKeySeen hst.toAuthHybridState.base.seenKyberBaseKeys k.val
                          msg.hdr.pqspkId msg.hdr.spkId msg.hdr.ekAPk).2
                        msg { hst.toAuthHybridState with recvKemRecs :=
                          _ :: hst.toAuthHybridState.recvKemRecs } res?).2 :=
                      congrArg AuthHybridStateFixed.toAuthHybridState (congrArg Prod.snd hfin).symm
                    rw [hst_eq]
                    simp only [ Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, beq_iff_eq
                      ] at h1
                    rcases h1 with ⟨⟨⟨⟨⟨hSpkId, hPqspkId⟩, _⟩, _⟩, _⟩, _⟩
                    simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at h5
                    rcases h5 with ⟨⟨hReplay, hCanonEk⟩, _⟩
                    have hNotUsed : (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                      msg.hdr.ekAPk) ∉ hst.toAuthHybridState.base.seenKyberBaseKeys := by
                      unfold checkAndMarkKyberBaseKeySeen at hReplay
                      dsimp only at hReplay
                      rw [hPqspkId, hSpkId] at hReplay
                      intro hm
                      have hc := List.contains_iff_mem.mpr hm
                      rw [hc] at hReplay
                      cases hReplay
                    have hTriples' : (checkAndMarkKyberBaseKeySeen
                      hst.toAuthHybridState.base.seenKyberBaseKeys k.val msg.hdr.pqspkId
                        msg.hdr.spkId msg.hdr.ekAPk).2 =
                        (k.val, UInt32.ofNat j.val, UInt32.ofNat j.val,
                          msg.hdr.ekAPk) :: hst.toAuthHybridState.base.seenKyberBaseKeys := by
                      unfold checkAndMarkKyberBaseKeySeen
                      simp [hPqspkId, hSpkId, hNotUsed]
                    exact authCleanSessionInv_finishAuthHybridRecvNoOPK checkAuth P hWF k j l
                      kEntry bEntry _ msg
                      { hst.toAuthHybridState with recvKemRecs :=
                        _ :: hst.toAuthHybridState.recvKemRecs }
                      res? (hInv.of_eq_fields rfl rfl rfl rfl rfl rfl rfl)
                      (by dsimp only; exact mem_of_find?_fst_beq hp)
                      (by dsimp only; exact mem_of_find?_fst_beq hb)
                      hCanonEk hNotUsed hTriples' (fun dk rk ck pt ro rro hres_eq hHon => by
                        subst hres_eq
                        exact mem_support_evalAuthFixedRecvScheduleCached_g5_honest useRo P _
                          hst.recvCount hst.mkSaltCache kEntry bEntry none _ msg dk rk ck pt ro rro
                            mkSaltCache' hHon hres_mem)
    | sendOPK u i bundle m0 m1 | sendNoOPK u i bundle m0 m1 | initPrin u | corruptIK u
    | genSPK u j | genOPK u j o | registerKey sk | roQuery secrets | roRootQuery rk dh
    | revealDhSecrets =>
      unfold pqxdhAuthHybridSplitFixedImpl at hmem
      simp only [hIdeal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
        StateT.run_get,
        StateT.run_monadLift, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨⟨r0, hst0⟩, hmem0, _, rfl⟩
      exact hApply r0 hst0 hmem0

end SignalPqxdh.Security
