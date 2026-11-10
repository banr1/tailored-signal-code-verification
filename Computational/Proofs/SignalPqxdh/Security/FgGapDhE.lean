/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhD
import Computational.Proofs.SignalPqxdh.Security.WellFormedDelta
import VCVio.EvalDist.Monad.Basic

@[expose] public section

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh

open _root_.SignalPqxdh.Security.FgGapDh

theorem pqxdhKeyIndFgPreImpl_preserves_spkTargetRevealed {S : Setup} (useDh1 : Bool)
    (targetIdx bIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hRev : spkTargetRevealed bIdx hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl useDh1 targetIdx bIdx optUsk optVsk S P q).run hst),
      spkTargetRevealed bIdx x.2 = true := by
  intro x hx
  have hFiredPres :=
    (pqxdhKeyIndFgPreImpl_preserves_hasFired useDh1 targetIdx bIdx optUsk optVsk P q hst x hx).1
      bIdx
  unfold spkTargetRevealed at hRev ⊢
  rcases Bool.and_eq_true_iff.mp hRev with ⟨hDec, hAll⟩
  have hFired : hasFiredSpk S bIdx hst := @of_decide_eq_true _ (Classical.propDecidable _) hDec
  have hFired' : @decide (hasFiredSpk S bIdx x.2) (Classical.propDecidable _) = true :=
    @decide_eq_true _ (Classical.propDecidable _) (hFiredPres hFired)
  rw [hFired', Bool.true_and]
  have hUnchanged : x.2.base.spkBundles = hst.base.spkBundles →
      x.2.base.spkBundles.all (fun (k, b) => !(spkBundleFlatIdxVal S k == bIdx) || b.revealed) =
        true := by
    intro hSpk; rw [hSpk]; exact hAll
  refine mem_support_pqxdhKeyIndFgPreImpl_elim useDh1 targetIdx bIdx optUsk optVsk P q hst x hx
    (fun _ hS _ _ => hUnchanged hS)
    (fun _ _ _ _ hB => hUnchanged (by rw [hB]))
    (fun _ _ _ _ _ hB => hUnchanged (by rw [hB]))
    (fun u j bEntry _ hAny _ _ hB => ?_)
    (fun _ _ _ _ _ _ _ hB => hUnchanged (by rw [hB]))
    (fun _ _ _ hB => hUnchanged (by rw [hB]))
    (fun _ _ _ _ hS _ _ => hUnchanged hS)
    (fun _ _ _ _ _ _ hS _ _ => hUnchanged hS)
    (fun u j hB => ?_)
  · rw [hB]; dsimp only
    rw [List.all_cons, hAll, Bool.and_true]
    by_cases hSlot : (spkBundleFlatIdx S u j == bIdx) = true
    · exfalso
      have hAnyTrue := spkBundles_any_of_hasFiredSpk S bIdx hst hFired u j hSlot
      rw [hAny] at hAnyTrue; cases hAnyTrue
    · have hSlotV : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = false := by
        simpa [spkBundleFlatIdxVal, spkBundleFlatIdx] using hSlot
      simp [hSlotV]
  · rw [hB]; dsimp only
    rw [List.all_map, List.all_eq_true]
    rintro ⟨k, b⟩ hMem
    dsimp only [Function.comp_apply]
    split_ifs
    · simp
    · exact List.all_eq_true.mp hAll (k, b) hMem

theorem spkTargetRevealed_map_revealed_of_eq {S : Setup} (bIdx : ℕ)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hTgt : (spkBundleFlatIdx S u j == bIdx) = true)
    (hst : KeyIndFgCutoffState S) (hValidSpk : ValidSpkBundles S hst.base.spkBundles)
    (k0 : Nat × Nat) (bEntry : SpkBundleEntry)
    (hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) = some (k0, bEntry)) :
    spkTargetRevealed bIdx
      { hst with base := { hst.base with spkBundles := hst.base.spkBundles.map (fun (idx, b) =>
          if idx == (u.val, j.val) then (idx, { b with revealed :=
            true }) else (idx, b)) } } = true := by
  unfold spkTargetRevealed
  dsimp only
  have hMem0 : (k0, bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hFB
  have hEq0 : (k0 == (u.val, j.val)) = true :=
    List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) => x.1 == (u.val, j.val)) hFB
  have hFired' : hasFiredSpk S bIdx
      { hst with base := { hst.base with spkBundles := hst.base.spkBundles.map (fun (idx, b) =>
          if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b)) } } := by
    refine ⟨u, j, beq_iff_eq.mp hTgt, ?_⟩
    dsimp only
    rw [List.any_map, List.any_eq_true]
    refine ⟨(k0, bEntry), hMem0, ?_⟩
    dsimp only [Function.comp_apply]
    split_ifs; exact hEq0
  rw [@decide_eq_true _ (Classical.propDecidable _) hFired', Bool.true_and, List.all_map,
    List.all_eq_true]
  rintro ⟨k, b⟩ hMem
  dsimp only [Function.comp_apply]
  by_cases hk : (k == (u.val, j.val)) = true
  · simp [hk]
  · simp only [hk, Bool.false_eq_true, ↓reduceIte]
    have hNotFlat : (spkBundleFlatIdxVal S k == bIdx) = false := by
      cases hFlat : spkBundleFlatIdxVal S k == bIdx
      · rfl
      · have hBounds := hValidSpk.1 (k, b) hMem
        have hInj : k = (u.val, j.val) :=
          spkSlotFlatIdx_inj S hBounds.2 j.isLt ((beq_iff_eq.mp hFlat).trans (beq_iff_eq.mp
            hTgt).symm)
        exact absurd (beq_iff_eq.mpr hInj) hk
    simp [hNotFlat]

theorem eraseSpkBundlesFg_map_revealed (S : Setup) (bIdx : ℕ) (u : Fin S.N_id) (j : Fin S.N_recv)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    (eraseSpkBundlesFg S bIdx spkBundles).map (fun (idx, b) =>
      if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b)) =
    eraseSpkBundlesFg S bIdx (spkBundles.map (fun (idx, b) =>
      if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))) := by
  unfold eraseSpkBundlesFg eraseSpkBundleEntryFg
  rw [List.map_map, List.map_map]
  congr 1; funext ⟨idx, b⟩; dsimp only [Function.comp_apply]
  split_ifs <;> rfl

theorem eraseSpkBundleEntryFg_eq_self_of_ne (S : Setup) (bIdx : ℕ)
    (u : Fin S.N_id) (j : Fin S.N_recv) (hTgtF : (spkBundleFlatIdx S u j == bIdx) = false)
    (k0 : Nat × Nat) (bEntry : SpkBundleEntry) (hk0 : (k0 == (u.val, j.val)) = true) :
    eraseSpkBundleEntryFg S bIdx k0 bEntry = bEntry := by
  unfold eraseSpkBundleEntryFg
  have hkEq : k0 = (u.val, j.val) := beq_iff_eq.mp hk0
  have hFlat : spkBundleFlatIdxVal S k0 = spkBundleFlatIdx S u j := by
    rw [hkEq]; rfl
  rw [hFlat, hTgtF]
  rfl

noncomputable def deadDh3Full {S : Setup} (P : Primitives) (sIdx bIdx : ℕ) (V : Bytes)
    (hst : KeyIndFgCutoffState S) : Bool :=
  deadDh3 P sIdx bIdx V hst || spkTargetRevealed bIdx hst

theorem badKeyIndFgDh3At_eq_false_of_deadDh3Full {S : Setup} (P : Primitives)
    (maxLen sIdx bIdx : ℕ) (V : Bytes) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh3Full P sIdx bIdx V hst = true) :
    badKeyIndFgDh3At P maxLen sIdx bIdx hst.base hst.advRoLog = false := by
  rcases Bool.or_eq_true_iff.mp hDead with hD | hR
  · exact badKeyIndFgDh3At_eq_false_of_deadDh3 P maxLen sIdx bIdx V hst hD
  · exact badKeyIndFgDh3At_eq_false_of_spkTargetRevealed P maxLen sIdx bIdx hst hR

theorem pqxdhKeyIndFgPreImpl_preserves_deadDh3Full {S : Setup} (P : Primitives)
    (sIdx bIdx : ℕ) (hsIdx : sIdx < S.N_send_tot) (uSk vSk : Bytes)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hDead : deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst = true) :
    ∀ x ∈ support ((pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P q).run hst),
      deadDh3Full P sIdx bIdx (P.x25519Base vSk) x.2 = true := by
  intro x hx
  unfold deadDh3Full at hDead ⊢
  rcases Bool.or_eq_true_iff.mp hDead with hD | hR
  · exact Bool.or_eq_true_iff.mpr (Or.inl
      (pqxdhKeyIndFgPreImpl_preserves_deadDh3 P sIdx bIdx hsIdx uSk vSk q hst hD x hx))
  · exact Bool.or_eq_true_iff.mpr (Or.inr
      (pqxdhKeyIndFgPreImpl_preserves_spkTargetRevealed false sIdx bIdx (some uSk) (some vSk) P q
        hst hR x hx))

theorem evalDist_sampleScalar32_const (m : ProbComp Bool) :
    𝒟[do let _ ← sampleScalar32; m] {true} = 𝒟[m] {true} := by
  simp

theorem recordKeyIndResp_run_eq_choosePartnerDrKeyRandPure {S : Setup} (P : Primitives)
    (r : KeyIndRespEntry S) (st : KeyIndState S) (hLen : st.sessions.length ≤ S.N_dh) :
    (recordKeyIndResp S P r).run st =
      (do
        let drKeyRand ← choosePartnerDrKeyRandPure P st.sessions r
        return ((), { st with respSessions :=
          { r with drKeyRand := drKeyRand } :: st.respSessions })) := by
  unfold recordKeyIndResp choosePartnerDrKeyRandPure
  rw [List.take_of_length_le hLen]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases st.sessions.find? (fun s => keyIndPartner P s r) <;> simp

theorem bne_x25519_zero_eq (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (sk pk : Bytes) (hpk : pk.length = 32) :
    (P.x25519 sk pk != List.replicate 32 0) =
      (P.x25519 (List.replicate 32 0) pk != List.replicate 32 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, not_iff_not]
  exact WellFormedPrimitivesδ.x25519_zero_iff_any P hWF sk (List.replicate 32 0) pk hpk

theorem acceptKeys_opk_eq_none_or_some (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (ikBSk ikBPk spkBSk spkBPk opkSk pqspkBSk pqspkBPk : Bytes)
    (replayOk : Bool) (hdr : HandshakeHdr) (opkId : UInt32)
    (hOpk : hdr.opkId? = some opkId)
    (hIkLen : hdr.ikAPk.length = 32) (hEkLen : hdr.ekAPk.length = 32) :
    (Model.acceptKeys P {
      ikBSk := ikBSk, ikBPk := ikBPk, spkBSk := spkBSk, spkBPk := spkBPk,
      opkBSk? := some opkSk, pqspkBSk := pqspkBSk, pqspkBPk := pqspkBPk,
      trustedPeer := true, replayOk := replayOk, hdr := hdr }).isSome =
    ((replayOk && P.isCanonical hdr.ekAPk &&
      P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
      P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0 &&
      P.x25519 opkSk hdr.ekAPk != List.replicate 32 0) &&
     (P.kemDecaps pqspkBSk hdr.kemCt).isSome) := by
  have hWF := hP.toWellFormedPrimitivesδ
  unfold Model.acceptKeys
  have hIkLenB : (hdr.ikAPk.length == 32) = true := beq_iff_eq.mpr hIkLen
  have hEkLenB : (hdr.ekAPk.length == 32) = true := beq_iff_eq.mpr hEkLen
  have hZ1 := bne_x25519_zero_eq P hWF spkBSk hdr.ikAPk hIkLen
  have hZ2 := bne_x25519_zero_eq P hWF ikBSk hdr.ekAPk hEkLen
  have hZ3 := bne_x25519_zero_eq P hWF spkBSk hdr.ekAPk hEkLen
  have hDh4 : dhOptNonZero (some (P.x25519 opkSk hdr.ekAPk)) =
      (P.x25519 opkSk hdr.ekAPk != List.replicate 32 0) := rfl
  by_cases hCt : hdr.kemCt.length = kyberCtLen
  · have hCtB : (hdr.kemCt.length == kyberCtLen) = true := beq_iff_eq.mpr hCt
    dsimp only
    rw [hOpk, hIkLenB, hEkLenB, hCtB, hZ1, hZ2, hZ3]
    dsimp only [bind, Option.bind]
    rw [hDh4]
    generalize P.isCanonical hdr.ekAPk = b1
    generalize (P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0) = b2
    generalize (P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0) = b3
    generalize (P.x25519 opkSk hdr.ekAPk != List.replicate 32 0) = b4
    generalize P.kemDecaps pqspkBSk hdr.kemCt = dec
    cases replayOk <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases dec <;> rfl
  · have hCtB : (hdr.kemCt.length == kyberCtLen) = false := beq_eq_false_iff_ne.mpr hCt
    have hDecNone := hP.kemDecaps_len_reject pqspkBSk hdr.kemCt hCt
    dsimp only
    rw [hOpk, hIkLenB, hEkLenB, hCtB, hDecNone]
    dsimp only [bind, Option.bind]
    rw [hDh4]
    generalize P.isCanonical hdr.ekAPk = b1
    generalize (P.x25519 spkBSk hdr.ikAPk != List.replicate 32 0) = b2'
    generalize (P.x25519 ikBSk hdr.ekAPk != List.replicate 32 0) = b3'
    generalize (P.x25519 spkBSk hdr.ekAPk != List.replicate 32 0) = b4'
    generalize (P.x25519 opkSk hdr.ekAPk != List.replicate 32 0) = b5'
    cases replayOk <;> cases b1 <;> cases b2' <;> cases b3' <;> cases b4' <;> cases b5' <;> simp

theorem acceptKeys_noOpk_eq_none_or_some (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (ikBSk ikBPk spkBSk spkBPk pqspkBSk pqspkBPk : Bytes)
    (replayOk : Bool) (hdr : HandshakeHdr)
    (hOpk : hdr.opkId? = none)
    (hIkLen : hdr.ikAPk.length = 32) (hEkLen : hdr.ekAPk.length = 32) :
    (Model.acceptKeys P {
      ikBSk := ikBSk, ikBPk := ikBPk, spkBSk := spkBSk, spkBPk := spkBPk,
      opkBSk? := none, pqspkBSk := pqspkBSk, pqspkBPk := pqspkBPk,
      trustedPeer := true, replayOk := replayOk, hdr := hdr }).isSome =
    ((replayOk && P.isCanonical hdr.ekAPk &&
      P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
      P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0) &&
     (P.kemDecaps pqspkBSk hdr.kemCt).isSome) := by
  have hWF := hP.toWellFormedPrimitivesδ
  unfold Model.acceptKeys
  have hIkLenB : (hdr.ikAPk.length == 32) = true := beq_iff_eq.mpr hIkLen
  have hEkLenB : (hdr.ekAPk.length == 32) = true := beq_iff_eq.mpr hEkLen
  have hZ1 := bne_x25519_zero_eq P hWF spkBSk hdr.ikAPk hIkLen
  have hZ2 := bne_x25519_zero_eq P hWF ikBSk hdr.ekAPk hEkLen
  have hZ3 := bne_x25519_zero_eq P hWF spkBSk hdr.ekAPk hEkLen
  by_cases hCt : hdr.kemCt.length = kyberCtLen
  · have hCtB : (hdr.kemCt.length == kyberCtLen) = true := beq_iff_eq.mpr hCt
    simp only [hOpk, hIkLenB, hEkLenB, hCtB, hZ1, hZ2, hZ3, dhOptNonZero]
    cases replayOk <;> cases P.isCanonical hdr.ekAPk <;>
      cases (P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0) <;>
      cases (P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0) <;>
      cases P.kemDecaps pqspkBSk hdr.kemCt <;> simp
  · have hCtB : (hdr.kemCt.length == kyberCtLen) = false := beq_eq_false_iff_ne.mpr hCt
    have hDecNone := hP.kemDecaps_len_reject pqspkBSk hdr.kemCt hCt
    simp only [hOpk, hIkLenB, hEkLenB, hCtB, hDecNone, dhOptNonZero]
    cases replayOk <;> cases P.isCanonical hdr.ekAPk <;>
      cases (P.x25519 spkBSk hdr.ikAPk != List.replicate 32 0) <;>
      cases (P.x25519 ikBSk hdr.ekAPk != List.replicate 32 0) <;>
      cases (P.x25519 spkBSk hdr.ekAPk != List.replicate 32 0) <;> simp

def FgAdvEq (P : Primitives) (stLog hstLog : List Bytes)
    (advKeyPows advKeys : List (Bytes × Bytes)) : Prop :=
  stLog = hstLog ∧
  advKeyPows = advKeys.map (fun (sk, pk) => (sk, P.pow8 pk)) ∧
  (∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)

def FgSimInvDh3 (S : Setup) (b : QueryBudget) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (sIdx bIdx : ℕ) (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S) : Prop :=
  st.base = eraseStateFg false sIdx bIdx hst.base ∧
  FgAdvEq P st.advRoLog hst.advRoLog st.advKeyPows hst.base.advKeys ∧
  FgCacheRel (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk) b.q_total st.fgL st.rawRoCache
    hst.base.roCache ∧
  st.fgL.length + rem ≤ b.q_total ∧
  hst.advRoLog.length + rem ≤ b.q_total ∧
  ValidKeyIndEcFg S hst.base ∧
  spkTargetIsV bIdx (P.x25519Base vSk) hst = true ∧
  (∀ kv ∈ hst.base.principals, kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0) ∧
  (∀ kv ∈ hst.base.spkBundles,
    kv.2.spkSk.length = 32 ∧ kv.2.spkPk = P.x25519Base kv.2.spkSk ∧
    ((spkBundleFlatIdxVal S kv.1 == bIdx) = true → kv.2.spkSk = vSk)) ∧
  (∀ kv ∈ hst.base.opkEntries, kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk) ∧
  (∀ s ∈ hst.base.sessions,
    s.ekASk.length = 32 ∧ s.hdr.ekAPk = P.x25519Base s.ekASk ∧
    ((initSessionSlotIdx s.sid == sIdx) = true → s.ekASk = uSk))

theorem fgSimInvDh3_empty (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32) (secb : Bool) :
    FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk b.q_total
      (KeyIndFgCutoffState.empty S secb) (FgKeyIndSimState.empty S secb) := by
  refine ⟨rfl, ⟨rfl, rfl, fun _ h => False.elim (List.not_mem_nil h)⟩,
    ⟨Nat.zero_le _, rfl, List.Forall₂.nil⟩,
    by change 0 + b.q_total ≤ b.q_total; omega, by simp [KeyIndFgCutoffState.empty],
    validKeyIndEcFg_empty S secb, rfl, ?_, ?_, ?_, ?_⟩
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · intro _ h; exact False.elim (List.not_mem_nil h)

theorem fgSimInvDh3_terminal_le (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (maxLen sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (_a : Bool) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (_hDead : deadDh3Full P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st) :
    𝒟[(pure (badKeyIndFgDh3At P maxLen sIdx bIdx hst.base hst.advRoLog) : ProbComp Bool)] {true} ≤
      𝒟[(pure (P.pow8 (pureExtractCdhFromAdvRoLog P.isValidDhTriple false b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) st.advRoLog) ==
        P.pow8 (P.x25519 uSk (P.x25519Base vSk))) : ProbComp Bool)] {true} := by
  by_cases hBad : badKeyIndFgDh3At P maxLen sIdx bIdx hst.base hst.advRoLog = true
  · rcases hInv with ⟨_, hAdvEq, _, _, hAdvLen, _, _, _, hSpks, _, hSess⟩
    have hBad' := hBad
    unfold badKeyIndFgDh3At at hBad'
    cases hFS : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
    | none => rw [hFS] at hBad'; cases hBad'
    | some s =>
      rw [hFS] at hBad'
      cases hFB : hst.base.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
      | none => rw [hFB] at hBad'; cases hBad'
      | some kb =>
        rcases kb with ⟨k, bEntry⟩
        rw [hFB] at hBad'
        dsimp only at hBad'
        rcases Bool.and_eq_true_iff.mp hBad' with ⟨_, hAny⟩
        have hsMem : s ∈ hst.base.sessions := List.mem_of_find?_eq_some hFS
        have hsIdx : (initSessionSlotIdx s.sid == sIdx) = true :=
          List.find?_some (p := fun s : KeyIndInitiatorEntry S =>
            initSessionSlotIdx s.sid == sIdx) hFS
        have hbMem : (k, bEntry) ∈ hst.base.spkBundles := List.mem_of_find?_eq_some hFB
        have hbIdx : (spkBundleFlatIdxVal S k == bIdx) = true :=
          List.find?_some (p := fun (x : (Nat × Nat) × SpkBundleEntry) =>
            spkBundleFlatIdxVal S x.1 == bIdx) hFB
        have hsEq : s.ekASk = uSk := (hSess s hsMem).2.2 hsIdx
        have hbSkEq : bEntry.spkSk = vSk := (hSpks (k, bEntry) hbMem).2.2 hbIdx
        have hbPkEq : bEntry.spkPk = P.x25519Base vSk := by
          rw [(hSpks (k, bEntry) hbMem).2.1, hbSkEq]
        rw [hsEq, hbPkEq] at hAny
        rcases List.any_eq_true.mp hAny with ⟨sec, hSecTake, hSecEq⟩
        have hSecMem : sec ∈ hst.advRoLog := List.mem_of_mem_take hSecTake
        have hSecMemTake : sec ∈ st.advRoLog.take b.q_total := by
          rw [hAdvEq.1, List.take_of_length_le (by omega)]
          exact hSecMem
        have hWin := pureExtractCdhFromAdvRoLog_wins_of_mem P hP.toWellFormedPrimitivesδ
          false b.q_total uSk vSk st.advRoLog ⟨sec, hSecMemTake, beq_iff_eq.mp hSecEq⟩
        rw [hBad, hWin]
  · have hBadF : badKeyIndFgDh3At P maxLen sIdx bIdx hst.base hst.advRoLog = false :=
      Bool.eq_false_iff.mpr hBad
    rw [hBadF]
    simp

theorem length_of_mem_support_sampleScalar32 {x : Bytes} (hx : x ∈ support sampleScalar32) :
    x.length = 32 := by
  unfold sampleScalar32 sampleBytes32 at hx
  simp only [support_map, Set.mem_image] at hx
  rcases hx with ⟨w, _, rfl⟩
  simp [word256ToBytes]

theorem validKeyIndEc_of_fields_eq {S : Setup} {st1 st2 : KeyIndState S}
    (hV : ValidKeyIndEcFg S st1)
    (hP : st2.principals = st1.principals)
    (hS : st2.spkBundles = st1.spkBundles)
    (hO : st2.opkEntries = st1.opkEntries)
    (hSess : st2.sessions.map KeyIndInitiatorEntry.sid = st1.sessions.map KeyIndInitiatorEntry.sid)
    (hUsedOpk : st2.usedRecvOPK = st1.usedRecvOPK := by rfl)
    (hUsedNoOpk : st2.usedRecvNoOPK = st1.usedRecvNoOPK := by rfl)
    (hRespLen : st2.respSessions.length = st1.respSessions.length := by simp) :
    ValidKeyIndEcFg S st2 := by
  unfold ValidKeyIndEcFg ValidKeyIndRespFg sessPksKeyInd at hV ⊢
  simp only [List.map_map] at hV ⊢
  change ValidPrincipals S st2.principals ∧ ValidSpkBundles S st2.spkBundles ∧
    ValidOpkEntries S st2.opkEntries ∧ ValidSessionIds S (st2.sessions.map KeyIndInitiatorEntry.sid) ∧
    (ValidUsedRecvOpk S st2.usedRecvOPK ∧ ValidUsedRecvNoOpk S st2.usedRecvNoOPK ∧
     st2.respSessions.length ≤ st2.usedRecvOPK.length + st2.usedRecvNoOPK.length)
  rw [hP, hS, hO, hSess, hUsedOpk, hUsedNoOpk, hRespLen]
  exact hV

theorem validKeyIndEcFg_acceptNoOPK {S : Setup} {st1 st2 : KeyIndState S}
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hV : ValidKeyIndEcFg S st1)
    (hFresh : ¬(st1.usedRecvNoOPK.contains (k.val, j.val, l.val) = true))
    (hP : st2.principals = st1.principals := by rfl)
    (hS : st2.spkBundles = st1.spkBundles := by rfl)
    (hO : st2.opkEntries = st1.opkEntries := by rfl)
    (hSess : st2.sessions = st1.sessions := by rfl)
    (hUsedOpk : st2.usedRecvOPK = st1.usedRecvOPK := by rfl)
    (hUsedNoOpk : st2.usedRecvNoOPK = (k.val, j.val, l.val) :: st1.usedRecvNoOPK := by rfl)
    (hRespLen : st2.respSessions.length = st1.respSessions.length + 1 := by rfl) :
    ValidKeyIndEcFg S st2 := by
  refine ⟨by rw [hP]; exact hV.1, by rw [hS]; exact hV.2.1, by rw [hO]; exact hV.2.2.1,
    by unfold sessPksKeyInd; rw [hSess]; exact hV.2.2.2.1, ?_, ?_, ?_⟩
  · rw [hUsedOpk]; exact hV.2.2.2.2.1
  · rw [hUsedNoOpk]
    exact validUsedRecvNoOpk_cons S k j l st1.usedRecvNoOPK hV.2.2.2.2.2.1 (Bool.eq_false_iff.mpr
      hFresh)
  · rw [hRespLen, hUsedOpk, hUsedNoOpk, List.length_cons]
    have := hV.2.2.2.2.2.2; omega

theorem validKeyIndEcFg_acceptOPK {S : Setup} {st1 st2 : KeyIndState S}
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hV : ValidKeyIndEcFg S st1)
    (hValidOpk' : ValidOpkEntries S st2.opkEntries)
    (hFresh : ¬(st1.usedRecvOPK.contains (k.val, j.val, o.val) = true))
    (hP : st2.principals = st1.principals := by rfl)
    (hS : st2.spkBundles = st1.spkBundles := by rfl)
    (hSess : st2.sessions = st1.sessions := by rfl)
    (hUsedOpk : st2.usedRecvOPK = (k.val, j.val, o.val) :: st1.usedRecvOPK := by rfl)
    (hUsedNoOpk : st2.usedRecvNoOPK = st1.usedRecvNoOPK := by rfl)
    (hRespLen : st2.respSessions.length = st1.respSessions.length + 1 := by rfl) :
    ValidKeyIndEcFg S st2 := by
  refine ⟨by rw [hP]; exact hV.1, by rw [hS]; exact hV.2.1, hValidOpk',
    by unfold sessPksKeyInd; rw [hSess]; exact hV.2.2.2.1, ?_, ?_, ?_⟩
  · rw [hUsedOpk]
    exact validUsedRecvOpk_cons S k j o st1.usedRecvOPK hV.2.2.2.2.1 (Bool.eq_false_iff.mpr hFresh)
  · rw [hUsedNoOpk]; exact hV.2.2.2.2.2.1
  · rw [hRespLen, hUsedOpk, hUsedNoOpk, List.length_cons]
    have := hV.2.2.2.2.2.2; omega

theorem isEmpty_false_of_length_eq_32 {xs : Bytes} (h : xs.length = 32) :
    xs.isEmpty = false := by
  cases xs with
  | nil => cases h
  | cons _ _ => rfl

@[simp]
theorem computeTwoSideOrPairPosPure_left_len32 (P : Primitives) (sk1 sk2 pk1 pk2 : Bytes)
    (h1 : sk1.length = 32) :
    computeTwoSideOrPairPosPure P sk1 sk2 pk1 pk2 = mkSecretPosPure P (P.x25519 sk1 pk2) := by
  unfold computeTwoSideOrPairPosPure
  simp [isEmpty_false_of_length_eq_32 h1]

@[simp]
theorem computeTwoSideOrPairPosPure_nil_right_len32 (P : Primitives) (sk2 pk1 pk2 : Bytes)
    (h2 : sk2.length = 32) :
    computeTwoSideOrPairPosPure P [] sk2 pk1 pk2 = mkSecretPosPure P (P.x25519 sk2 pk1) := by
  unfold computeTwoSideOrPairPosPure
  simp [isEmpty_false_of_length_eq_32 h2]

@[simp]
theorem computeTwoSideOrPairPosPure_nil_nil (P : Primitives) (pk1 pk2 : Bytes) :
    computeTwoSideOrPairPosPure P [] [] pk1 pk2 = mkPairPosPure P pk1 pk2 := rfl

theorem onCurveKeyLocal_of_isAdvRegistered (P : Primitives)
    (advKeys : List (Bytes × Bytes)) (pk : Bytes)
    (hAdv : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hReg : isAdvRegistered P advKeys pk = true) :
    onCurveKeyLocal P pk := by
  unfold isAdvRegistered at hReg
  rcases List.any_eq_true.mp hReg with ⟨⟨sk, pk0⟩, hMem, hBeq⟩
  rcases hAdv (sk, pk0) hMem with ⟨hLen, hPk0⟩
  dsimp only at hLen hPk0
  have hPow : P.pow8 pk = P.pow8 (P.x25519Base sk) := by
    rw [← hPk0, (beq_iff_eq.mp hBeq).symm]
  exact Or.inr ⟨sk, hLen, hPow⟩

theorem onCurveKeyLocal_of_koskSenderOk (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (advKeys : List (Bytes × Bytes)) (ikAPk : Bytes)
    (hPrins : ∀ kv ∈ principals, kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0)
    (hAdv : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hNotKosk : (!koskSenderOk P principals advKeys ikAPk) = true → False) :
    onCurveKeyLocal P ikAPk := by
  have hKosk : koskSenderOk P principals advKeys ikAPk = true := by
    cases h : koskSenderOk P principals advKeys ikAPk
    · exfalso; exact hNotKosk (by simp [h])
    · rfl
  unfold koskSenderOk at hKosk
  rcases (Bool.or_eq_true _ _).mp hKosk with hGame | hReg
  · unfold isGameIdKey findHonestPrincipal at hGame
    rw [List.find?_isSome] at hGame
    rcases hGame with ⟨⟨u0, e⟩, hMem, hBeq⟩
    rcases hPrins (u0, e) hMem with ⟨hLen, hPk0⟩
    have hPow : P.pow8 ikAPk = P.pow8 (P.x25519Base e.secIKA0) := by
      rw [← hPk0, beq_iff_eq.mp hBeq]
    exact Or.inr ⟨e.secIKA0, hLen, hPow⟩
  · exact onCurveKeyLocal_of_isAdvRegistered P advKeys ikAPk hAdv hReg

theorem onCurveKeyLocal_of_koskBundleOk (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeys : List (Bytes × Bytes)) (bundle : PreKeyBundleInput)
    (hPrins : ∀ kv ∈ principals, kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0)
    (hOpks : ∀ kv ∈ opkEntries, kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk)
    (hAdv : ∀ kv ∈ advKeys, kv.1.length = 32 ∧ kv.2 = P.x25519Base kv.1)
    (hNotKosk : (!koskBundleOk P principals spkBundles opkEntries advKeys bundle) = true → False) :
    onCurveKeyLocal P bundle.ikB ∧
    (match bundle.opkB? with
     | none => True
     | some (_, opkPk) => onCurveKeyLocal P opkPk) := by
  have hKosk : koskBundleOk P principals spkBundles opkEntries advKeys bundle = true := by
    cases h : koskBundleOk P principals spkBundles opkEntries advKeys bundle
    · exfalso; exact hNotKosk (by simp [h])
    · rfl
  unfold koskBundleOk at hKosk
  rcases (Bool.and_eq_true _ _).mp hKosk with ⟨h12, h3⟩
  rcases (Bool.and_eq_true _ _).mp h12 with ⟨h1, _⟩
  refine ⟨?_, ?_⟩
  · exact onCurveKeyLocal_of_koskSenderOk P principals advKeys bundle.ikB hPrins hAdv
      (by simp [koskSenderOk, h1])
  · cases hopk : bundle.opkB? with
    | none => trivial
    | some p =>
      rcases p with ⟨opkId, opkPk⟩
      rw [hopk] at h3
      rcases (Bool.or_eq_true _ _).mp h3 with hGame | hReg
      · unfold isGameOpk at hGame
        rcases List.any_eq_true.mp hGame with ⟨⟨idx0, e⟩, hMem, hBeq⟩
        rcases hOpks (idx0, e) hMem with ⟨hLen, hPk0⟩
        have hPow : P.pow8 opkPk = P.pow8 (P.x25519Base e.opkSk) := by
          rw [← hPk0, (beq_iff_eq.mp hBeq).symm]
        exact Or.inr ⟨e.opkSk, hLen, hPow⟩
      · exact onCurveKeyLocal_of_isAdvRegistered P advKeys opkPk hAdv hReg

theorem computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep
    (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P) (S : Setup) (bIdx : ℕ)
    (vSk : Bytes) (k : Nat × Nat) (bEntry : SpkBundleEntry) (pk : Bytes)
    (hb : bEntry.spkSk.length = 32 ∧ bEntry.spkPk = P.x25519Base bEntry.spkSk ∧
      ((spkBundleFlatIdxVal S k == bIdx) = true → bEntry.spkSk = vSk))
    (hpk : onCurveKeyLocal P pk) :
    FgPosRightRep P vSk
      (computeTwoSideOrPairPosPure P [] (eraseSpkBundleEntryFg S bIdx k bEntry).spkSk pk
        bEntry.spkPk)
      (P.x25519 bEntry.spkSk pk) := by
  dsimp only [eraseSpkBundleEntryFg]
  by_cases hIdx : (spkBundleFlatIdxVal S k == bIdx) = true
  · have hSk : bEntry.spkSk = vSk := hb.2.2 hIdx
    have hPk : bEntry.spkPk = P.x25519Base vSk := by rw [hb.2.1, hSk]
    simp only [hIdx, ↓reduceIte, computeTwoSideOrPairPosPure_nil_nil, hPk, hSk]
    exact fgPosRightRep_mkPair_right P hP.toWellFormedPrimitivesδ vSk pk hpk
  · have hIdxF : (spkBundleFlatIdxVal S k == bIdx) = false := Bool.eq_false_iff.mpr hIdx
    simp only [hIdxF, Bool.false_eq_true, ↓reduceIte,
      computeTwoSideOrPairPosPure_nil_right_len32 P bEntry.spkSk pk bEntry.spkPk hb.1]
    exact fgPosRightRep_mkSecret P vSk _ (hP.x25519_len _ _)

theorem fgRoQueryPure_eq_or_sample {S : Setup} {P : Primitives} (R : FgSlotReps P)
    {maxLen : ℕ} {secrets : Bytes} {hst : KeyIndFgCutoffState S} {st : FgKeyIndSimState S}
    (hCache : FgCacheRel R maxLen st.fgL st.rawRoCache hst.base.roCache) :
    (∃ dk,
      evalHkdfOrRo true P hst.base.roCache secrets = pure (dk, hst.base.roCache) ∧
      fgRoQueryPure P P.isValidDhTriple maxLen secrets st =
        pure (.drKeyResp dk, { st with advRoLog := secrets :: st.advRoLog })) ∨
    (∃ (newRaw : DRKey → List (Bytes × DRKey)) (newFgL : DRKey → List FgPatchEntry),
      evalHkdfOrRo true P hst.base.roCache secrets =
        (sampleDRKey96 >>= fun dk => pure (dk, (secrets, dk) :: hst.base.roCache)) ∧
      fgRoQueryPure P P.isValidDhTriple maxLen secrets st =
        (sampleDRKey96 >>= fun dk =>
          pure (.drKeyResp dk, { st with
            rawRoCache := newRaw dk
            fgL        := newFgL dk
            advRoLog   := secrets :: st.advRoLog })) ∧
      (∀ dk, st.fgL.length < maxLen →
        (newFgL dk).length ≤ st.fgL.length + 1 ∧
        FgCacheRel R maxLen (newFgL dk) (newRaw dk) ((secrets, dk) :: hst.base.roCache))) := by
  unfold fgRoQueryPure
  cases hParse : parseRoSecrets secrets with
  | none =>
    rcases hCache with ⟨hLen, hRaw, hForall⟩
    have hFiltFind :
        st.rawRoCache.find? (fun (s, _) => s == secrets) =
        hst.base.roCache.find? (fun (s, _) => s == secrets) := by
      rw [hRaw]
      apply find?_filter_eq_find?_of_imp
      rintro ⟨s, dk⟩ hs
      simp only [beq_iff_eq] at hs
      subst hs
      simp [hParse]
    unfold evalHkdfOrRo
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hFiltFind]
    cases hst.base.roCache.find? (fun (s, _) => s == secrets) with
    | some p =>
      rcases p with ⟨_, dk⟩
      left
      exact ⟨dk, rfl, by simp⟩
    | none =>
      right
      refine ⟨fun dk => (secrets, dk) :: st.rawRoCache, fun _ => st.fgL, rfl, by simp, ?_⟩
      intro dk _
      refine ⟨by dsimp; omega, hLen, ?_, ?_⟩
      · rw [hRaw, List.filter_cons_of_pos (by simp [hParse])]
      · rw [List.filter_cons_of_neg (by simp [hParse])]
        exact hForall
  | some tup =>
    rcases tup with ⟨dh1, dh2, dh3, dh4?, ss⟩
    rcases buildSecrets_of_parseRoSecrets hParse with ⟨hSecEq, h1, h2, h3, h4, hss⟩
    have hT : FgTupleRel R (mkSecretPosPure P dh1) (mkSecretPosPure P dh2)
        (mkSecretPosPure P dh3) (dh4?.map (mkSecretPosPure P)) dh1 dh2 dh3 dh4? ss :=
      ⟨R.sec1 dh1 h1, R.sec2 dh2 h2, R.sec3 dh3 h3, R.sec4 dh4? h4, hss⟩
    have hPatch := fgPatchPure_eq_or_sample R hCache hT
    dsimp only at hPatch
    rw [← hSecEq] at hPatch
    rcases hPatch with ⟨dk, hEval, hFg⟩ | ⟨hEval, hFg, hCache'⟩
    · left
      refine ⟨dk, hEval, ?_⟩
      dsimp only
      rw [hFg, pure_bind]
    · right
      refine ⟨fun _ => st.rawRoCache,
        fun dk => { pos1 := mkSecretPosPure P dh1, pos2 := mkSecretPosPure P dh2,
                    pos3 := mkSecretPosPure P dh3, pos4? := dh4?.map (mkSecretPosPure P),
                    ss := ss, dk := dk } :: st.fgL,
        hEval, ?_, ?_⟩
      · dsimp only
        rw [hFg, bind_assoc]
        simp only [pure_bind]
      · intro dk hLt
        exact ⟨by simp, hCache' dk hLt⟩

theorem deadDh3_eq_of_spk_sess {S : Setup} (P : Primitives) (sIdx bIdx : ℕ) (V : Bytes)
    {hst1 hst2 : KeyIndFgCutoffState S}
    (hSpk : hst2.base.spkBundles = hst1.base.spkBundles)
    (hSess : (hst2.base.sessions.find? (fun s =>
      initSessionSlotIdx s.sid == sIdx)).map KeyIndInitiatorEntry.peerSpkPk =
      (hst1.base.sessions.find? (fun s =>
        initSessionSlotIdx s.sid == sIdx)).map KeyIndInitiatorEntry.peerSpkPk) :
    deadDh3 P sIdx bIdx V hst2 = deadDh3 P sIdx bIdx V hst1 := by
  unfold deadDh3 spkTargetIsV
  rw [hSpk]
  congr 1
  cases h1 : hst1.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) <;>
    cases h2 : hst2.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)
  · rfl
  · rw [h1, h2] at hSess; cases hSess
  · rw [h1, h2] at hSess; cases hSess
  · rw [h1, h2] at hSess
    simp only [Option.map_some, Option.some.injEq] at hSess
    dsimp only
    rw [hSess]

theorem fgStepCoupling_dh3_unchanged (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (r : KeyIndResponse)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[k1 (r, hst)] {true} ≤ 𝒟[k2 (r, st)] {true} := by
  rcases hInv with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact hCont r hst st hDead ⟨h1, h2, h3, by omega, by omega, h6, h7, h8, h9, h10, h11⟩

theorem fgStepCoupling_dh3_initPrin (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.initPrin u)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.initPrin u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hPrinEq : st.base.principals = hst.base.principals := by
    rw [hBaseEq]; rfl
  unfold pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, hPrinEq, bind_assoc, pure_bind]
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKA0 hSec0 => ?_)
    have hLen0 : secIKA0.length = 32 := length_of_mem_support_sampleScalar32 hSec0
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun secIKAsign _ => ?_)
    let entry : PrincipalEntry := {
      secIKA0 := secIKA0, ikAPk := P.x25519Base secIKA0,
      secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false }
    apply hCont (.initPrinResp entry.ikAPk entry.ikSignPk)
    · rw [deadDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl]
      exact hDead
    · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache,
      by dsimp; omega, by dsimp; omega, ?_, hSpkV, ?_, hSpks, hOpks, hSess⟩
      · exact ⟨(validPrincipals_cons S u entry hst.base.principals hValidEc.1 hAny).1,
          hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
      · intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLen0, rfl⟩
        · exact hPrins kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh3_corruptIK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.corruptIK u)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.corruptIK u) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hPrinEq : st.base.principals = hst.base.principals := by rw [hBaseEq]; rfl
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hPrinEq, bind_assoc, pure_bind]
  cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none =>
    simp only [StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont
  | some p =>
    rcases p with ⟨_, entry⟩
    simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
    apply hCont (.corrResp entry.secIKA0 entry.secIKAsign)
    · rw [deadDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl]
      exact hDead
    · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache,
      by dsimp; omega, by dsimp; omega, ?_, hSpkV, ?_, hSpks, hOpks, hSess⟩
      · exact ⟨(validPrincipals_map_corrupted S P u.val hst.base.principals hValidEc.1).1,
          hValidEc.2.1, hValidEc.2.2.1, hValidEc.2.2.2⟩
      · intro kv hkv
        rw [List.mem_map] at hkv
        rcases hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
        have hPr := hPrins (idx, e) heMem
        by_cases hIdx : idx == u.val <;> simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hEq <;>
          (subst hEq; exact hPr)

theorem fgStepCoupling_dh3_genOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.genOPK u j o)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genOPK u j o) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hOpkEq : st.base.opkEntries = hst.base.opkEntries := by rw [hBaseEq]; rfl
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hOpkEq, bind_assoc, pure_bind]
  cases hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun opkSk hOpk => ?_)
    have hLen : opkSk.length = 32 := length_of_mem_support_sampleScalar32 hOpk
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := P.x25519Base opkSk, consumed := false }
    apply hCont (.pkResp (P.x25519Base opkSk))
    · rw [deadDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl]
      exact hDead
    · refine ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache,
      by dsimp; omega, by dsimp; omega, ?_, hSpkV, hPrins, hSpks, ?_, hSess⟩
      · exact ⟨hValidEc.1, hValidEc.2.1,
          (validOpkEntries_cons S u j o oEntry hst.base.opkEntries hValidEc.2.2.1 hAny).1,
          hValidEc.2.2.2⟩
      · intro kv hkv
        rcases List.mem_cons.mp hkv with rfl | hMem
        · exact ⟨hLen, rfl⟩
        · exact hOpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgStepCoupling_dh3_genSPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.genSPK u j)).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.genSPK u j) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hPrinEq : st.base.principals = hst.base.principals := by rw [hBaseEq]; rfl
  have hSpkAnyEq : st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) =
      hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) := by
    rw [hBaseEq]; exact any_idx_eraseSpkBundlesFg S bIdx (u.val, j.val) hst.base.spkBundles
  unfold pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSpkAnyEq, hPrinEq, bind_assoc,
    pure_bind]
  cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
        .noneResp k1 k2 hCont
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      have hFlatEq : spkBundleFlatIdx S u j = spkBundleFlatIdxVal S (u.val, j.val) := rfl
      by_cases hTgt : (spkBundleFlatIdx S u j == bIdx) = true
      · simp only [hTgt, ↓reduceIte, StateT.run_bind, StateT.run_monadLift, monadLift_self,
          StateT.run_set, StateT.run_pure, sampleKemKeyGen, bind_assoc, pure_bind,
          evalDist_sampleScalar32_const]
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun seedKem _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
        let spkPk := P.x25519Base vSk
        let pqspkPk := (P.kemKeyGen seedKem).1
        let pqspkSk := (P.kemKeyGen seedKem).2
        let bEntry1 : SpkBundleEntry := {
          spkSk := vSk, spkPk := spkPk,
          spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq }
        let bundleOut : PreKeyBundleInput := {
          ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
          spkSig := bEntry1.spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
          pqspkB := pqspkPk, pqspkSig := bEntry1.pqspkSig }
        have hTgtVal : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = true := hTgt
        have hSpkV' : spkTargetIsV bIdx (P.x25519Base vSk)
            { hst with base :=
              { hst.base with spkBundles :=
              ((u.val, j.val), bEntry1) :: hst.base.spkBundles } } = true := by
          unfold spkTargetIsV at hSpkV ⊢
          simp [List.all_cons, bEntry1, spkPk, hSpkV]
        apply hCont (.bundleResp bundleOut)
        · unfold deadDh3 at hDead ⊢
          rw [hSpkV'] at *
          rw [hSpkV] at hDead
          exact hDead
        · refine ⟨?_, hAdvEq, hCache,
          by dsimp; omega, by dsimp; omega, ?_, hSpkV', hPrins, ?_, hOpks, hSess⟩
          · rw [hBaseEq]
            simp [eraseStateFg, eraseSpkBundlesFg, eraseSpkBundleEntryFg, beq_iff_eq.mp hTgtVal]
          · exact ⟨hValidEc.1,
              (validSpkBundles_cons S u j bEntry1 hst.base.spkBundles hValidEc.2.1 hAny).1,
              hValidEc.2.2.1, hValidEc.2.2.2⟩
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hvSk, rfl, fun _ => rfl⟩
            · exact hSpks kv hMem
      · have hTgtF : (spkBundleFlatIdx S u j == bIdx) = false := Bool.eq_false_iff.mpr hTgt
        have hTgtValF : (spkBundleFlatIdxVal S (u.val, j.val) == bIdx) = false := hTgtF
        simp only [hTgtF, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, sampleKemKeyGen, bind_assoc, pure_bind]
        refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun spkSk hSpkSk => ?_)
        have hSpkLen : spkSk.length = 32 := length_of_mem_support_sampleScalar32 hSpkSk
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rSpk _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun seedKem _ => ?_)
        refine evalDist_bind_true_mono_of_support sampleRandom64 _ _ (fun rPq _ => ?_)
        let spkPk := P.x25519Base spkSk
        let pqspkPk := (P.kemKeyGen seedKem).1
        let pqspkSk := (P.kemKeyGen seedKem).2
        let bEntry1 : SpkBundleEntry := {
          spkSk := spkSk, spkPk := spkPk,
          spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk,
          pqspkSk := pqspkSk, pqspkPk := pqspkPk,
          pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq }
        let bundleOut : PreKeyBundleInput := {
          ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk,
          spkSig := bEntry1.spkSig, opkB? := none, pqspkId := UInt32.ofNat j.val,
          pqspkB := pqspkPk, pqspkSig := bEntry1.pqspkSig }
        have hSpkV' : spkTargetIsV bIdx (P.x25519Base vSk)
            { hst with base :=
              { hst.base with spkBundles :=
              ((u.val, j.val), bEntry1) :: hst.base.spkBundles } } = true := by
          unfold spkTargetIsV at hSpkV ⊢
          simp [List.all_cons, hTgtValF, hSpkV]
        apply hCont (.bundleResp bundleOut)
        · unfold deadDh3 at hDead ⊢
          rw [hSpkV'] at *
          rw [hSpkV] at hDead
          exact hDead
        · refine ⟨?_, hAdvEq, hCache,
          by dsimp; omega, by dsimp; omega, ?_, hSpkV', hPrins, ?_, hOpks, hSess⟩
          · rw [hBaseEq]
            simp [eraseStateFg, eraseSpkBundlesFg, eraseSpkBundleEntryFg,
              beq_eq_false_iff_ne.mp hTgtValF]
          · exact ⟨hValidEc.1,
              (validSpkBundles_cons S u j bEntry1 hst.base.spkBundles hValidEc.2.1 hAny).1,
              hValidEc.2.2.1, hValidEc.2.2.2⟩
          · intro kv hkv
            rcases List.mem_cons.mp hkv with rfl | hMem
            · exact ⟨hSpkLen, rfl, fun h => by rw [hTgtValF] at h; cases h⟩
            · exact hSpks kv hMem
  · simp only [↓reduceIte, StateT.run_pure, pure_bind]
    exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont

theorem fgPatchPure_bind_le {P : Primitives} (R : FgSlotReps P)
    {maxLen rem : ℕ} {fgL : List FgPatchEntry} {rawRoCache roCache : List (Bytes × DRKey)}
    {pos1 pos2 pos3 : FgPoS} {pos4? : Option FgPoS}
    {dh1 dh2 dh3 : Bytes} {dh4? : Option Bytes} {ss : Bytes}
    {k1 : DRKey × List (Bytes × DRKey) → ProbComp Bool}
    {k2 : DRKey × List FgPatchEntry → ProbComp Bool}
    (hCache : FgCacheRel R maxLen fgL rawRoCache roCache)
    (hFgLen : fgL.length + (rem + 1) ≤ maxLen)
    (hT : FgTupleRel R pos1 pos2 pos3 pos4? dh1 dh2 dh3 dh4? ss)
    (hStep : ∀ dk roCache' fgL',
      FgCacheRel R maxLen fgL' rawRoCache roCache' →
      fgL'.length + rem ≤ maxLen →
      𝒟[k1 (dk, roCache')] {true} ≤ 𝒟[k2 (dk, fgL')] {true}) :
    𝒟[evalHkdfOrRo true P roCache (buildSecrets dh1 dh2 dh3 dh4? ss) >>= k1] {true} ≤
      𝒟[fgPatchPure P.isValidDhTriple maxLen pos1 pos2 pos3 pos4? ss fgL >>= k2] {true} := by
  rcases fgPatchPure_eq_or_sample R hCache hT with
    ⟨dk, hEval, hFg⟩ | ⟨hEval, hFg, hStepCache⟩
  · rw [hEval, hFg, pure_bind, pure_bind]
    exact hStep dk roCache fgL hCache (by omega)
  · rw [hEval, hFg, bind_assoc, bind_assoc]
    refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun dk _ => ?_)
    rw [pure_bind, pure_bind]
    exact hStep dk _ _ (hStepCache dk (by omega)) (by simp [List.length_cons]; omega)

theorem fgRoQuery_coupling {S : Setup} {P : Primitives} (R : FgSlotReps P)
    {useDh1 : Bool} {targetIdx bIdx maxLen rem : ℕ} {uSk? vSk? : Option Bytes} {U V secrets : Bytes}
    {hst : KeyIndFgCutoffState S} {st : FgKeyIndSimState S}
    {k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool}
    {k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool}
    (hCache : FgCacheRel R maxLen st.fgL st.rawRoCache hst.base.roCache)
    (hFgLen : st.fgL.length + (rem + 1) ≤ maxLen)
    (hStep : ∀ dk roCache' rawRoCache' fgL',
      FgCacheRel R maxLen fgL' rawRoCache' roCache' →
      fgL'.length + rem ≤ maxLen →
      𝒟[k1 (.drKeyResp dk,
          { base := { hst.base with roCache := roCache' },
            advRoLog := secrets :: hst.advRoLog })] {true} ≤
        𝒟[k2 (.drKeyResp dk,
          { st with rawRoCache := rawRoCache', fgL := fgL',
                    advRoLog := secrets :: st.advRoLog })] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl useDh1 targetIdx bIdx uSk? vSk? S P (.roQuery secrets)).run hst >>= k1]
      {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple useDh1 targetIdx bIdx S maxLen
          U V (.roQuery secrets) st >>= k2] {true} := by
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
    StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
  rcases fgRoQueryPure_eq_or_sample R hCache with
    ⟨dk, hEval, hFg⟩ | ⟨newRaw, newFgL, hEval, hFg, hStepCache⟩
  · rw [hEval, hFg]
    simp only [pure_bind]
    exact hStep dk hst.base.roCache st.rawRoCache st.fgL hCache (by omega)
  · rw [hEval, hFg]
    simp only [bind_assoc, pure_bind]
    refine evalDist_bind_true_mono_of_support sampleDRKey96 _ _ (fun dk _ => ?_)
    rcases hStepCache dk (by omega) with ⟨hLenNew, hCacheNew⟩
    exact hStep dk _ _ _ hCacheNew (by omega)

theorem fgAdvEq_registerKey {P : Primitives} {advRoLogSim advRoLog : List Bytes}
    {advKeyPows advKeys : List (Bytes × Bytes)}
    {sk : Bytes} (hSkLen32 : sk.length = 32)
    (hAdvEq : FgAdvEq P advRoLogSim advRoLog advKeyPows advKeys) :
    FgAdvEq P advRoLogSim advRoLog
      ((sk, P.pow8 (P.x25519Base sk)) :: advKeyPows)
      ((sk, P.x25519Base sk) :: advKeys) := by
  refine ⟨hAdvEq.1, by rw [List.map_cons, hAdvEq.2.1], ?_⟩
  intro kv hkv
  rcases List.mem_cons.mp hkv with rfl | hMem
  · exact ⟨hSkLen32, rfl⟩
  · exact hAdvEq.2.2 kv hMem

theorem fgRegisterKey_coupling {S : Setup} {P : Primitives}
    {useDh1 : Bool} {targetIdx bIdx maxLen : ℕ} {uSk? vSk? : Option Bytes} {U V sk : Bytes}
    {hst : KeyIndFgCutoffState S} {st : FgKeyIndSimState S}
    {k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool}
    {k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool}
    (hUnchanged : 𝒟[k1 (.noneResp, hst)] {true} ≤ 𝒟[k2 (.noneResp, st)] {true})
    (hStep : sk.length = 32 →
      𝒟[k1 (.pkResp (P.x25519Base sk),
          { hst with base := { hst.base with advKeys := (sk, P.x25519Base sk) :: hst.base.advKeys } })]
        {true} ≤
        𝒟[k2 (.pkResp (P.x25519Base sk),
          { st with
            base := { st.base with advKeys := (sk, P.x25519Base sk) :: st.base.advKeys },
            advKeyPows := (sk, P.pow8 (P.x25519Base sk)) :: st.advKeyPows })] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl useDh1 targetIdx bIdx uSk? vSk? S P (.registerKey sk)).run hst >>= k1]
      {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple useDh1 targetIdx bIdx S maxLen
          U V (.registerKey sk) st >>= k2] {true} := by
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl registerAdvKey liftFgBase
    fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, bind_assoc, pure_bind]
  by_cases hLen : (sk.length != 32) = true
  · simp only [hLen, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hUnchanged
  · have hSkLen32 : sk.length = 32 := by
      cases hEq : (sk.length == 32)
      · simp [bne, hEq] at hLen
      · exact beq_iff_eq.mp hEq
    simp only [hLen, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
      StateT.run_pure, pure_bind]
    exact hStep hSkLen32

theorem validKeyIndEc_map_tested {S : Setup} {st : KeyIndState S}
    (sid : SessionId S) (h : ValidKeyIndEcFg S st) :
    ValidKeyIndEcFg S { st with sessions := st.sessions.map (fun s =>
      if s.sid == sid then { s with tested := true } else s) } := by
  refine validKeyIndEc_of_fields_eq h rfl rfl rfl ?_
  rw [List.map_map]; refine List.map_congr_left (fun s _ => ?_)
  dsimp; cases s.sid == sid <;> rfl

theorem validKeyIndEc_map_revealed {S : Setup} {st : KeyIndState S}
    (sid : SessionId S) (h : ValidKeyIndEcFg S st) :
    ValidKeyIndEcFg S { st with sessions := st.sessions.map (fun s =>
      if s.sid == sid then { s with revealed := true } else s) } := by
  refine validKeyIndEc_of_fields_eq h rfl rfl rfl ?_
  rw [List.map_map]; refine List.map_congr_left (fun s _ => ?_)
  dsimp; cases s.sid == sid <;> rfl

theorem fgTestSession_coupling {S : Setup} {P : Primitives}
    (eraseSess : KeyIndInitiatorEntry S → KeyIndInitiatorEntry S)
    {useDh1 : Bool} {targetIdx bIdx maxLen : ℕ} {uSk? vSk? : Option Bytes} {U V : Bytes}
    {sid : SessionId S} {hst : KeyIndFgCutoffState S} {st : FgKeyIndSimState S}
    {k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool}
    {k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool}
    (hFreshEq : isKeyIndSessionTestable st.base sid = isKeyIndSessionTestable hst.base sid)
    (hSecbEq : st.base.secb = hst.base.secb)
    (hRespEq : st.base.respSessions = hst.base.respSessions)
    (hSessFind : st.base.sessions.find? (fun e => e.sid == sid) =
      (hst.base.sessions.find? (fun e => e.sid == sid)).map eraseSess)
    (hDrReal : ∀ e, (eraseSess e).drKeyReal = e.drKeyReal)
    (hDrRand : ∀ e, (eraseSess e).drKeyRand = e.drKeyRand)
    (hUnchanged : 𝒟[k1 (.noneResp, hst)] {true} ≤ 𝒟[k2 (.noneResp, st)] {true})
    (hInit : ∀ r,
      𝒟[k1 (r, { hst with base := { hst.base with sessions := hst.base.sessions.map (fun s =>
          if s.sid == sid then { s with tested := true } else s) } })] {true} ≤
        𝒟[k2 (r, { st with base := { st.base with sessions := st.base.sessions.map (fun s =>
          if s.sid == sid then { s with tested := true } else s) } })] {true})
    (hResp : ∀ r,
      𝒟[k1 (r, { hst with base := { hst.base with respSessions := hst.base.respSessions.map (fun s =>
          if s.sid == sid then { s with tested := true } else s) } })] {true} ≤
        𝒟[k2 (r, { st with base := { st.base with respSessions := hst.base.respSessions.map (fun s =>
          if s.sid == sid then { s with tested := true } else s) } })] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl useDh1 targetIdx bIdx uSk? vSk? S P (.testSession sid)).run hst >>= k1]
      {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple useDh1 targetIdx bIdx S maxLen
          U V (.testSession sid) st >>= k2] {true} := by
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hFreshEq, hSessFind, hRespEq, hSecbEq,
    bind_assoc, pure_bind]
  cases hFr : isKeyIndSessionTestable hst.base sid
  · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, pure_bind]
    exact hUnchanged
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hFS : hst.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only [Option.map]
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, hDrReal, hDrRand]
      simpa [hSecbEq, hRespEq] using hInit _
    | none =>
      dsimp only [Option.map]
      cases hFR : hst.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        simp only [StateT.run_pure, pure_bind]
        exact hUnchanged
      | some r =>
        dsimp only
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        simpa [hSecbEq, hRespEq] using hResp _

theorem fgRevealSessionKey_coupling {S : Setup} {P : Primitives}
    (eraseSess : KeyIndInitiatorEntry S → KeyIndInitiatorEntry S)
    {useDh1 : Bool} {targetIdx bIdx maxLen : ℕ} {uSk? vSk? : Option Bytes} {U V : Bytes}
    {sid : SessionId S} {hst : KeyIndFgCutoffState S} {st : FgKeyIndSimState S}
    {k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool}
    {k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool}
    (hRespEq : st.base.respSessions = hst.base.respSessions)
    (hSessFind : st.base.sessions.find? (fun e => e.sid == sid) =
      (hst.base.sessions.find? (fun e => e.sid == sid)).map eraseSess)
    (hTested : ∀ e, (eraseSess e).tested = e.tested)
    (hDrReal : ∀ e, (eraseSess e).drKeyReal = e.drKeyReal)
    (hUnchanged : 𝒟[k1 (.noneResp, hst)] {true} ≤ 𝒟[k2 (.noneResp, st)] {true})
    (hInit : ∀ r,
      𝒟[k1 (r, { hst with base := { hst.base with sessions := hst.base.sessions.map (fun s =>
          if s.sid == sid then { s with revealed := true } else s) } })] {true} ≤
        𝒟[k2 (r, { st with base := { st.base with sessions := st.base.sessions.map (fun s =>
          if s.sid == sid then { s with revealed := true } else s) } })] {true})
    (hResp : ∀ r,
      𝒟[k1 (r, { hst with base := { hst.base with respSessions := hst.base.respSessions.map (fun s =>
          if s.sid == sid then { s with revealed := true } else s) } })] {true} ≤
        𝒟[k2 (r, { st with base := { st.base with respSessions := hst.base.respSessions.map (fun s =>
          if s.sid == sid then { s with revealed := true } else s) } })] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl useDh1 targetIdx bIdx uSk? vSk? S P (.revealSessionKey sid)).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple useDh1 targetIdx bIdx S maxLen
          U V (.revealSessionKey sid) st >>= k2] {true} := by
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hSessFind, hRespEq, bind_assoc,
    pure_bind]
  cases hFS : hst.base.sessions.find? (fun e => e.sid == sid) with
  | some e =>
    dsimp only [Option.map]
    simp only [hTested, hDrReal]
    cases hT : e.tested
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
        pure_bind]
      simpa [hRespEq] using hInit _
    · simp only [↓reduceIte, StateT.run_pure, pure_bind]
      exact hUnchanged
  | none =>
    dsimp only [Option.map]
    cases hFR : hst.base.respSessions.find? (fun r => r.sid == sid) with
    | none =>
      simp only [StateT.run_pure, pure_bind]
      exact hUnchanged
    | some r =>
      dsimp only
      cases hT : r.tested
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure,
          pure_bind]
        simpa [hRespEq] using hResp _
      · simp only [↓reduceIte, StateT.run_pure, pure_bind]
        exact hUnchanged

theorem fgStepCoupling_dh3_roQuery (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (secrets : Bytes) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.roQuery secrets)).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.roQuery secrets) st >>= k2] {true} := by
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  refine fgRoQuery_coupling (FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk) hCache hFgLen
    (fun dk roCache' rawRoCache' fgL' hCache' hFgLen' => ?_)
  apply hCont (.drKeyResp dk)
  · rw [deadDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl]; exact hDead
  · exact ⟨hBaseEq, ⟨by dsimp; rw [hAdvEq.1], hAdvEq.2⟩, hCache', hFgLen',
      by dsimp [List.length_cons]; omega, hValidEc, hSpkV, hPrins, hSpks, hOpks, hSess⟩

theorem fgStepCoupling_dh3_revealDhSecrets (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P .revealDhSecrets).run hst >>=
      k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) .revealDhSecrets st >>= k2] {true} := by
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, ↓reduceIte,
    StateT.run_pure, pure_bind]
  exact fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv
    .noneResp k1 k2 hCont

theorem deadDh3_map_tested {S : Setup} (P : Primitives) (sIdx bIdx : ℕ) (V : Bytes)
    (sid : SessionId S) (hst : KeyIndFgCutoffState S) :
    deadDh3 P sIdx bIdx V
      { hst with base := { hst.base with sessions := hst.base.sessions.map (fun s =>
          if s.sid == sid then { s with tested := true } else s) } } =
      deadDh3 P sIdx bIdx V hst := by
  unfold deadDh3 spkTargetIsV
  have hF : (hst.base.sessions.map (fun s =>
      if s.sid == sid then { s with tested := true } else s)).find?
        (fun s => initSessionSlotIdx s.sid == sIdx) =
      (hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        (fun s => if s.sid == sid then { s with tested := true } else s) := by
    rw [List.find?_map]
    congr 1; congr 1; funext s; dsimp only [Function.comp_def]; cases s.sid == sid <;> rfl
  rw [hF]
  cases hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s => dsimp only [Option.map]; cases s.sid == sid <;> rfl

theorem deadDh3_map_revealed {S : Setup} (P : Primitives) (sIdx bIdx : ℕ) (V : Bytes)
    (sid : SessionId S) (hst : KeyIndFgCutoffState S) :
    deadDh3 P sIdx bIdx V
      { hst with base := { hst.base with sessions := hst.base.sessions.map (fun s =>
          if s.sid == sid then { s with revealed := true } else s) } } =
      deadDh3 P sIdx bIdx V hst := by
  unfold deadDh3 spkTargetIsV
  have hF : (hst.base.sessions.map (fun s =>
      if s.sid == sid then { s with revealed := true } else s)).find?
        (fun s => initSessionSlotIdx s.sid == sIdx) =
      (hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx)).map
        (fun s => if s.sid == sid then { s with revealed := true } else s) := by
    rw [List.find?_map]
    congr 1; congr 1; funext s; dsimp only [Function.comp_def]; cases s.sid == sid <;> rfl
  rw [hF]
  cases hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx) with
  | none => rfl
  | some s => dsimp only [Option.map]; cases s.sid == sid <;> rfl

theorem fgStepCoupling_dh3_testSession (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.testSession sid)).run hst
      >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.testSession sid) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  refine fgTestSession_coupling (eraseSessionEntryFg sIdx)
    (by rw [hBaseEq]; exact isFreshKeyIndSession_eraseStateFg false sIdx bIdx hst.base sid)
    (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl)
    (by rw [hBaseEq]; exact find?_sid_eraseSessionsFg sIdx sid hst.base.sessions)
    (eraseSessionEntryFg_drKeyReal sIdx) (eraseSessionEntryFg_drKeyRand sIdx)
    (fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont)
    (fun r => hCont r _ _ (by rw [deadDh3_map_tested]; exact hDead)
      ⟨by rw [hBaseEq]; dsimp [eraseStateFg]; rw [test_map_eraseSessionsFg], hAdvEq, hCache,
       by dsimp; omega, by dsimp; omega, validKeyIndEc_map_tested sid hValidEc, hSpkV, hPrins,
       hSpks, hOpks, fun s hs => by
         rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
         cases s0.sid == sid <;> exact hSess s0 hs0⟩)
    (fun r => hCont r _ _ (by rw [deadDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl]; exact hDead)
      ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
       validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hSpkV, hPrins, hSpks, hOpks, hSess⟩)

theorem fgStepCoupling_dh3_revealSessionKey (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (sid : SessionId S) (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.revealSessionKey sid)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.revealSessionKey sid) st >>= k2] {true} := by
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  refine fgRevealSessionKey_coupling (eraseSessionEntryFg sIdx)
    (by rw [hBaseEq]; rfl)
    (by rw [hBaseEq]; exact find?_sid_eraseSessionsFg sIdx sid hst.base.sessions)
    (eraseSessionEntryFg_tested sIdx) (eraseSessionEntryFg_drKeyReal sIdx)
    (fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont)
    (fun r => hCont r _ _ (by rw [deadDh3_map_revealed]; exact hDead)
      ⟨by rw [hBaseEq]; dsimp [eraseStateFg]; rw [reveal_map_eraseSessionsFg], hAdvEq, hCache,
       by dsimp; omega, by dsimp; omega, validKeyIndEc_map_revealed sid hValidEc, hSpkV, hPrins,
       hSpks, hOpks, fun s hs => by
         rcases List.mem_map.mp hs with ⟨s0, hs0, rfl⟩
         cases s0.sid == sid <;> exact hSess s0 hs0⟩)
    (fun r => hCont r _ _ (by rw [deadDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl]; exact hDead)
      ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache, by dsimp; omega, by dsimp; omega,
       validKeyIndEc_of_fields_eq hValidEc rfl rfl rfl rfl, hSpkV, hPrins, hSpks, hOpks, hSess⟩)

theorem not_beq_true_eq_false {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> simp_all

theorem of_not_not_eq_true {b : Bool} (h : ¬((!b) = true)) : b = true := by
  cases b <;> simp_all

theorem hdr_noOpk_extract {S : Setup} {j : Fin S.N_recv} {hdr : HandshakeHdr}
    (h : ¬(!(hdr.spkId == UInt32.ofNat j.val &&
             hdr.pqspkId == UInt32.ofNat j.val &&
             hdr.opkId? == none &&
             hdr.ikAPk.length == 32 &&
             hdr.ekAPk.length == 32)) = true) :
    hdr.opkId? = none ∧ hdr.ikAPk.length = 32 ∧ hdr.ekAPk.length = 32 := by
  have h1 := of_not_not_eq_true h
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨h1.1.1.2, h1.1.2, h1.2⟩

theorem hdr_opk_extract {S : Setup} {j : Fin S.N_recv} {o : Fin S.N_opk} {hdr : HandshakeHdr}
    (h : ¬(!(hdr.spkId == UInt32.ofNat j.val &&
             hdr.pqspkId == UInt32.ofNat j.val &&
             hdr.opkId? == some (UInt32.ofNat o.val) &&
             hdr.ikAPk.length == 32 &&
             hdr.ekAPk.length == 32)) = true) :
    hdr.opkId? = some (UInt32.ofNat o.val) ∧ hdr.ikAPk.length = 32 ∧ hdr.ekAPk.length = 32 := by
  have h1 := of_not_not_eq_true h
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact ⟨h1.1.1.2, h1.1.2, h1.2⟩

theorem isAdvRegisteredPows_map_eq (P : Primitives) (advKeys : List (Bytes × Bytes)) (pk : Bytes) :
    isAdvRegisteredPows (advKeys.map (fun (sk, pk') => (sk, P.pow8 pk'))) (P.pow8 pk) =
      isAdvRegistered P advKeys pk := by
  unfold isAdvRegisteredPows isAdvRegistered
  simp only [List.any_map, Function.comp_def]
  congr 1; funext ⟨sk, pk'⟩
  exact BEq.comm

@[simp]
theorem isGameIdKey_erasePrincipalsFg (P : Primitives) (uIdx : ℕ)
    (principals : List (Nat × PrincipalEntry)) (pk : Bytes) :
    isGameIdKey P (erasePrincipalsFg uIdx principals) pk =
      isGameIdKey P principals pk :=
  findHonestPrincipal_erasePrincipalsFg_isSome P uIdx principals pk

@[simp]
theorem isGameSpk_eraseSpkBundlesFg (P : Primitives) (S : Setup) (bIdx : ℕ)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (pk : Bytes) :
    isGameSpk P (eraseSpkBundlesFg S bIdx spkBundles) pk =
      isGameSpk P spkBundles pk := by
  simp [isGameSpk, eraseSpkBundlesFg, List.any_map, Function.comp_def]

@[simp]
theorem match_findHonestPrincipal_erasePrincipalsFg {α : Type} (P : Primitives) (uIdx : ℕ)
    (principals : List (ℕ × PrincipalEntry)) (pk : Bytes) (a b : α) :
    (match findHonestPrincipal P (erasePrincipalsFg uIdx principals) pk with
     | some _ => a
     | none => b) =
    (match findHonestPrincipal P principals pk with
     | some _ => a
     | none => b) := by
  rw [findHonestPrincipal_erasePrincipalsFg]
  cases findHonestPrincipal P principals pk <;> rfl

@[simp]
theorem option_map_prod_id {α β : Type} (o : Option (α × β)) :
    o.map (fun (a, b) => (a, b)) = o := by
  cases o <;> rfl

theorem koskSenderOkTake_eq_koskSenderOk (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (advKeyPows advKeys : List (Bytes × Bytes)) (ikAPk : Bytes)
    (hP : principals.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) :
    koskSenderOkTake S P principals advKeyPows ikAPk =
      koskSenderOk P principals advKeys ikAPk := by
  unfold koskSenderOkTake koskSenderOk isGameIdKey
  rw [List.take_of_length_le hP, hAdvPows, isAdvRegisteredPows_map_eq]

theorem koskSenderOkTake_erasePrincipalsFg_eq (S : Setup) (P : Primitives) (uIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (advKeyPows advKeys : List (Bytes × Bytes)) (ikAPk : Bytes)
    (hP : principals.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) :
    koskSenderOkTake S P (erasePrincipalsFg uIdx principals) advKeyPows ikAPk =
      koskSenderOk P principals advKeys ikAPk := by
  rw [koskSenderOkTake_eq_koskSenderOk S P (erasePrincipalsFg uIdx principals)
    advKeyPows advKeys ikAPk (by rw [erasePrincipalsFg_length]; exact hP) hAdvPows]
  unfold koskSenderOk
  rw [isGameIdKey_erasePrincipalsFg]

theorem koskBundleOkTake_eq_of_le (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows advKeys : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput)
    (hP : principals.length ≤ S.N_dh)
    (hS : spkBundles.length ≤ S.N_dh)
    (hO : opkEntries.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) :
    koskBundleOkTake S P principals spkBundles opkEntries advKeyPows bundle =
      koskBundleOk P principals spkBundles opkEntries advKeys bundle := by
  unfold koskBundleOkTake koskBundleOk isGameIdKey isGameSpk isGameOpk
  rw [List.take_of_length_le hP, List.take_of_length_le hS, List.take_of_length_le hO, hAdvPows]
  simp only [isAdvRegisteredPows_map_eq]
  cases bundle.opkB? with
  | none => rfl
  | some p => rcases p with ⟨_, opkPk⟩; rfl

theorem koskBundleOkTake_eraseSpk_eq (S : Setup) (P : Primitives) (bIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows advKeys : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput)
    (hP : principals.length ≤ S.N_dh)
    (hS : spkBundles.length ≤ S.N_dh)
    (hO : opkEntries.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) :
    koskBundleOkTake S P principals (eraseSpkBundlesFg S bIdx spkBundles)
      opkEntries advKeyPows bundle =
    koskBundleOk P principals spkBundles opkEntries advKeys bundle := by
  rw [koskBundleOkTake_eq_of_le S P principals (eraseSpkBundlesFg S bIdx spkBundles)
    opkEntries advKeyPows advKeys bundle hP (by rw [eraseSpkBundlesFg_length]; exact hS) hO hAdvPows]
  unfold koskBundleOk
  rw [isGameSpk_eraseSpkBundlesFg]

theorem koskBundleOkTake_erasePrin_eraseSpk_eq (S : Setup) (P : Primitives) (uIdx bIdx : ℕ)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows advKeys : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput)
    (hP : principals.length ≤ S.N_dh)
    (hS : spkBundles.length ≤ S.N_dh)
    (hO : opkEntries.length ≤ S.N_dh)
    (hAdvPows : advKeyPows = advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))) :
    koskBundleOkTake S P (erasePrincipalsFg uIdx principals)
      (eraseSpkBundlesFg S bIdx spkBundles) opkEntries advKeyPows bundle =
    koskBundleOk P principals spkBundles opkEntries advKeys bundle := by
  rw [koskBundleOkTake_eraseSpk_eq S P bIdx (erasePrincipalsFg uIdx principals)
    spkBundles opkEntries advKeyPows advKeys bundle
    (by rw [erasePrincipalsFg_length]; exact hP) hS hO hAdvPows]
  unfold koskBundleOk
  rw [isGameIdKey_erasePrincipalsFg]

theorem computeOptPosPure_left_len32_rep4 {P : Primitives} (R : FgSlotReps P)
    (hP : WellFormedPrimitivesδ P) (ekASk ekAPk : Bytes) (hLen : ekASk.length = 32)
    (opkB? : Option (UInt32 × Bytes)) :
    R.Rep4
      (computeOptPosPure P ekASk ekAPk (opkB?.map (fun (_, opkPk) => ([], opkPk))))
      (opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
  have hEq :
      computeOptPosPure P ekASk ekAPk (opkB?.map (fun (_, opkPk) => ([], opkPk))) =
        (opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)).map (mkSecretPosPure P) := by
    cases opkB? with
    | none => rfl
    | some p =>
      dsimp only [Option.map, computeOptPosPure]
      rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk p.2 hLen]
  rw [hEq]
  apply R.sec4
  intro d hd
  cases opkB? with
  | none => cases hd
  | some p =>
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    exact hP.x25519_len ekASk p.2

theorem computeOptPosPure_left_len32_fgOptRightRep (P : Primitives)
    (hP : WellFormedPrimitivesδ P) (vSk ekASk ekAPk : Bytes)
    (hLen : ekASk.length = 32) (opkB? : Option (UInt32 × Bytes)) :
    FgOptRightRep P vSk
      (computeOptPosPure P ekASk ekAPk (opkB?.map (fun (_, opkPk) => ([], opkPk))))
      (opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
  cases opkB? with
  | none => trivial
  | some p =>
    rcases p with ⟨_, opkPk⟩
    dsimp only [Option.map, computeOptPosPure]
    rw [computeTwoSideOrPairPosPure_left_len32 P ekASk [] ekAPk opkPk hLen]
    exact ⟨hP.x25519_len _ _, Or.inl rfl⟩

theorem fgAcceptNoOPK_coupling {S : Setup} {P : Primitives} (R : FgSlotReps P)
    (hP : CryptoWellFormedPrimitivesδ P)
    (erasePrin : ℕ → PrincipalEntry → PrincipalEntry)
    (eraseSpk : ℕ × ℕ → SpkBundleEntry → SpkBundleEntry)
    {useDh1 : Bool} {targetIdx bIdx maxLen rem : ℕ} {uSk? vSk? : Option Bytes} {U V : Bytes}
    {k : Fin S.N_id} {j : Fin S.N_recv} {l : Fin S.N_no_opk} {hdr : HandshakeHdr}
    {hst : KeyIndFgCutoffState S} {st : FgKeyIndSimState S}
    {k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool}
    {k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool}
    (hCache : FgCacheRel R maxLen st.fgL st.rawRoCache hst.base.roCache)
    (hFgLen : st.fgL.length + (rem + 1) ≤ maxLen)
    (hValidEc : ValidKeyIndEcFg S hst.base)
    (hAdvEq : FgAdvEq P st.advRoLog hst.advRoLog st.advKeyPows hst.base.advKeys)
    (hPrins : ∀ kv ∈ hst.base.principals,
      kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0)
    (hUsedEq : st.base.usedRecvNoOPK = hst.base.usedRecvNoOPK)
    (hKyberEq : st.base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys)
    (hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk)
    (hPrinFind : st.base.principals.find? (fun (idx, _) => idx == k.val) =
      (hst.base.principals.find? (fun (idx, _) => idx == k.val)).map
        (fun (idx, e) => (idx, erasePrin idx e)))
    (hSpkFind : st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) =
      (hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))).map
        (fun (idx, b) => (idx, eraseSpk idx b)))
    (hErasePrinIk : ∀ idx e, (erasePrin idx e).ikAPk = e.ikAPk)
    (hEraseSpkPqSk : ∀ idx b, (eraseSpk idx b).pqspkSk = b.pqspkSk)
    (hEraseSpkPk : ∀ idx b, (eraseSpk idx b).spkPk = b.spkPk)
    (hEraseSpkPqPk : ∀ idx b, (eraseSpk idx b).pqspkPk = b.pqspkPk)
    (hSenderIsSome : (findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk).isSome =
      (findHonestPrincipal P hst.base.principals hdr.ikAPk).isSome)
    (hChooseEq : ∀ rInit,
      choosePartnerDrKeyRandPure P st.base.sessions rInit =
        choosePartnerDrKeyRandPure P hst.base.sessions rInit)
    (hUnchanged : 𝒟[k1 (.noneResp, hst)] {true} ≤ 𝒟[k2 (.noneResp, st)] {true})
    (hSlots : ∀ k0 kEntry kb0 bEntry,
      (k0, kEntry) ∈ hst.base.principals →
      (kb0, bEntry) ∈ hst.base.spkBundles →
      onCurveKeyLocal P hdr.ikAPk →
      onCurveKeyLocal P hdr.ekAPk →
      R.Rep1 (computeTwoSideOrPairPosPure P [] (eraseSpk kb0 bEntry).spkSk hdr.ikAPk bEntry.spkPk)
        (P.x25519 bEntry.spkSk hdr.ikAPk) ∧
      R.Rep2 (computeTwoSideOrPairPosPure P [] (erasePrin k0 kEntry).secIKA0 hdr.ekAPk kEntry.ikAPk)
        (P.x25519 kEntry.secIKA0 hdr.ekAPk) ∧
      R.Rep3 (computeTwoSideOrPairPosPure P [] (eraseSpk kb0 bEntry).spkSk hdr.ekAPk bEntry.spkPk)
        (P.x25519 bEntry.spkSk hdr.ekAPk))
    (hStep : ∀ (r : KeyIndResponse) (rEntry : KeyIndRespEntry S)
      (roCache' : List (Bytes × DRKey)) (fgL' : List FgPatchEntry),
      let hst' : KeyIndFgCutoffState S := { hst with
        base := { hst.base with
          respSessions := rEntry :: hst.base.respSessions,
          usedRecvNoOPK := (k.val, j.val, l.val) :: hst.base.usedRecvNoOPK,
          seenKyberBaseKeys :=
            (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
              hdr.ekAPk).2,
          roCache := roCache' } }
      let st' : FgKeyIndSimState S := { st with
        base := { st.base with
          respSessions := rEntry :: st.base.respSessions,
          usedRecvNoOPK := (k.val, j.val, l.val) :: hst.base.usedRecvNoOPK,
          seenKyberBaseKeys :=
            (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
              hdr.ekAPk).2 },
        fgL := fgL' }
      ValidKeyIndEcFg S hst'.base →
      FgCacheRel R maxLen fgL' st.rawRoCache roCache' →
      fgL'.length + rem ≤ maxLen →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl useDh1 targetIdx bIdx uSk? vSk? S P (.acceptNoOPK k j l hdr)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple useDh1 targetIdx bIdx S maxLen
          U V (.acceptNoOPK k j l hdr) st >>= k2] {true} := by
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
    fgRunAcceptNoOPKPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hUsedEq, hPrinFind, hKyberEq, hKoskEq,
    hSpkFind, bind_assoc, pure_bind]
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind]; exact hUnchanged
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    rcases hdr_noOpk_extract hHdr with ⟨hOpkNone, hIkLen, hEkLen⟩
    by_cases hUsed : (hst.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind]; exact hUnchanged
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : (!koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]; exact hUnchanged
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hFK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          dsimp only [Option.map]
          simp only [StateT.run_pure, pure_bind]; exact hUnchanged
        | some pk =>
          rcases pk with ⟨k0, kEntry⟩
          dsimp only [Option.map]
          have hkMem := List.mem_of_find?_eq_some hFK
          cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            dsimp only [Option.map]
            simp only [StateT.run_pure, pure_bind]; exact hUnchanged
          | some pb =>
            rcases pb with ⟨kb0, bEntry⟩
            dsimp only [Option.map]
            have hbMem := List.mem_of_find?_eq_some hFB
            simp only [hErasePrinIk, hEraseSpkPqSk, hEraseSpkPk, hEraseSpkPqPk]
            have hAccSome := acceptKeys_noOpk_eq_none_or_some P hP
              kEntry.secIKA0 kEntry.ikAPk bEntry.spkSk bEntry.spkPk bEntry.pqspkSk bEntry.pqspkPk
              (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                hdr.ekAPk).1
              hdr hOpkNone hIkLen hEkLen
            by_cases hChk : (!((checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId
                 hdr.spkId hdr.ekAPk).1 &&
                 P.isCanonical hdr.ekAPk &&
                 P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
                 P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0)) = true
            · have hChkF := not_beq_true_eq_false hChk
              have hAccNone : Model.acceptKeys P {
                  ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                  spkBPk := bEntry.spkPk, opkBSk? := none, pqspkBSk := bEntry.pqspkSk,
                  pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
                  replayOk :=
                    (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                    hdr.ekAPk).1,
                  hdr := hdr } = none := by
                rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, hAccSome, hChkF,
                  Bool.false_and]
              simp only [hAccNone, hChk, ↓reduceIte, StateT.run_pure, pure_bind]; exact hUnchanged
            · have hChkT := of_not_not_eq_true hChk
              simp only [hChk, Bool.false_eq_true, ↓reduceIte]
              cases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
              | none =>
                have hAccNone : Model.acceptKeys P {
                    ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                    spkBPk := bEntry.spkPk, opkBSk? := none, pqspkBSk := bEntry.pqspkSk,
                    pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
                    replayOk :=
                      (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                      hdr.ekAPk).1,
                    hdr := hdr } = none := by
                  rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, hAccSome, hChkT, hDec]; rfl
                simp only [hAccNone, StateT.run_pure, pure_bind]; exact hUnchanged
              | some ss =>
                have hAccIsSome : (Model.acceptKeys P {
                    ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                    spkBPk := bEntry.spkPk, opkBSk? := none, pqspkBSk := bEntry.pqspkSk,
                    pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
                    replayOk :=
                      (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                      hdr.ekAPk).1,
                    hdr := hdr }).isSome = true := by
                  rw [hAccSome, hChkT, hDec]; rfl
                obtain ⟨accOut, hAccOut⟩ := Option.isSome_iff_exists.mp hAccIsSome
                simp only [hAccOut]
                have hIkOnCurve : onCurveKeyLocal P hdr.ikAPk :=
                  onCurveKeyLocal_of_koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk
                    hPrins hAdvEq.2.2 hKosk
                have hEkOnCurve : onCurveKeyLocal P hdr.ekAPk :=
                  Or.inl (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _
                    |>.mp hChkT).1).1).2
                rcases hSlots k0 kEntry kb0 bEntry hkMem hbMem hIkOnCurve hEkOnCurve with
                  ⟨hPos1, hPos2, hPos3⟩
                have hTup : FgTupleRel R _ _ _ none _ _ _ none ss :=
                  ⟨hPos1, hPos2, hPos3, R.sec4 none (fun _ h => by cases h),
                    hP.toWellFormedPrimitivesδ.kemDecaps_len _ _ _ hDec⟩
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  bind_assoc, pure_bind]
                refine fgPatchPure_bind_le R hCache hFgLen hTup
                  (fun drKey roCache' fgL' hCache' hFgLen' => ?_)
                dsimp only
                rw [hChooseEq, hSenderIsSome, recordKeyIndResp_run_eq_choosePartnerDrKeyRandPure P _ _
                  (by dsimp; exact hLengths.2.2.2)]
                simp only [bind_assoc, pure_bind]
                refine evalDist_bind_true_mono_of_support
                  (choosePartnerDrKeyRandPure P hst.base.sessions _) _ _
                  (fun drKeyRand _ => ?_)
                cases h1 : findHonestPrincipal P hst.base.principals hdr.ikAPk <;>
                  cases h2 : findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk <;>
                  simp only [h1, h2, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
                    Bool.true_eq_false] at hSenderIsSome <;>
                  simp only [StateT.run_pure, pure_bind] <;>
                  simpa [hUsedEq, hKyberEq] using hStep _ _ roCache' fgL'
                    (validKeyIndEcFg_acceptNoOPK k j l hValidEc hUsed) hCache' hFgLen'

theorem fgAcceptOPK_coupling {S : Setup} {P : Primitives} (R : FgSlotReps P)
    (hP : CryptoWellFormedPrimitivesδ P)
    (erasePrin : ℕ → PrincipalEntry → PrincipalEntry)
    (eraseSpk : ℕ × ℕ → SpkBundleEntry → SpkBundleEntry)
    {useDh1 : Bool} {targetIdx bIdx maxLen rem : ℕ} {uSk? vSk? : Option Bytes} {U V : Bytes}
    {k : Fin S.N_id} {j : Fin S.N_recv} {o : Fin S.N_opk} {hdr : HandshakeHdr}
    {hst : KeyIndFgCutoffState S} {st : FgKeyIndSimState S}
    {k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool}
    {k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool}
    (hCache : FgCacheRel R maxLen st.fgL st.rawRoCache hst.base.roCache)
    (hFgLen : st.fgL.length + (rem + 1) ≤ maxLen)
    (hValidEc : ValidKeyIndEcFg S hst.base)
    (hAdvEq : FgAdvEq P st.advRoLog hst.advRoLog st.advKeyPows hst.base.advKeys)
    (hPrins : ∀ kv ∈ hst.base.principals,
      kv.2.secIKA0.length = 32 ∧ kv.2.ikAPk = P.x25519Base kv.2.secIKA0)
    (hOpks : ∀ kv ∈ hst.base.opkEntries,
      kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk)
    (hUsedEq : st.base.usedRecvOPK = hst.base.usedRecvOPK)
    (hOpkEq : st.base.opkEntries = hst.base.opkEntries)
    (hKyberEq : st.base.seenKyberBaseKeys = hst.base.seenKyberBaseKeys)
    (hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk)
    (hPrinFind : st.base.principals.find? (fun (idx, _) => idx == k.val) =
      (hst.base.principals.find? (fun (idx, _) => idx == k.val)).map
        (fun (idx, e) => (idx, erasePrin idx e)))
    (hSpkFind : st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) =
      (hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))).map
        (fun (idx, b) => (idx, eraseSpk idx b)))
    (hErasePrinIk : ∀ idx e, (erasePrin idx e).ikAPk = e.ikAPk)
    (hEraseSpkPqSk : ∀ idx b, (eraseSpk idx b).pqspkSk = b.pqspkSk)
    (hEraseSpkPk : ∀ idx b, (eraseSpk idx b).spkPk = b.spkPk)
    (hEraseSpkPqPk : ∀ idx b, (eraseSpk idx b).pqspkPk = b.pqspkPk)
    (hSenderIsSome : (findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk).isSome =
      (findHonestPrincipal P hst.base.principals hdr.ikAPk).isSome)
    (hChooseEq : ∀ rInit,
      choosePartnerDrKeyRandPure P st.base.sessions rInit =
        choosePartnerDrKeyRandPure P hst.base.sessions rInit)
    (hUnchanged : 𝒟[k1 (.noneResp, hst)] {true} ≤ 𝒟[k2 (.noneResp, st)] {true})
    (hSlots : ∀ k0 kEntry kb0 bEntry,
      (k0, kEntry) ∈ hst.base.principals →
      (kb0, bEntry) ∈ hst.base.spkBundles →
      onCurveKeyLocal P hdr.ikAPk →
      onCurveKeyLocal P hdr.ekAPk →
      R.Rep1 (computeTwoSideOrPairPosPure P [] (eraseSpk kb0 bEntry).spkSk hdr.ikAPk bEntry.spkPk)
        (P.x25519 bEntry.spkSk hdr.ikAPk) ∧
      R.Rep2 (computeTwoSideOrPairPosPure P [] (erasePrin k0 kEntry).secIKA0 hdr.ekAPk kEntry.ikAPk)
        (P.x25519 kEntry.secIKA0 hdr.ekAPk) ∧
      R.Rep3 (computeTwoSideOrPairPosPure P [] (eraseSpk kb0 bEntry).spkSk hdr.ekAPk bEntry.spkPk)
        (P.x25519 bEntry.spkSk hdr.ekAPk))
    (hStep : ∀ (r : KeyIndResponse) (rEntry : KeyIndRespEntry S)
      (roCache' : List (Bytes × DRKey)) (fgL' : List FgPatchEntry),
      let opkEntries' := hst.base.opkEntries.map (fun (idx, e) =>
        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
      let hst' : KeyIndFgCutoffState S := { hst with
        base := { hst.base with
          opkEntries := opkEntries',
          respSessions := rEntry :: hst.base.respSessions,
          usedRecvOPK := (k.val, j.val, o.val) :: hst.base.usedRecvOPK,
          seenKyberBaseKeys :=
            (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
              hdr.ekAPk).2,
          roCache := roCache' } }
      let st' : FgKeyIndSimState S := { st with
        base := { st.base with
          opkEntries := opkEntries',
          respSessions := rEntry :: st.base.respSessions,
          usedRecvOPK := (k.val, j.val, o.val) :: hst.base.usedRecvOPK,
          seenKyberBaseKeys :=
            (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
              hdr.ekAPk).2 },
        fgL := fgL' }
      ValidKeyIndEcFg S hst'.base →
      (∀ kv ∈ opkEntries', kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk) →
      FgCacheRel R maxLen fgL' st.rawRoCache roCache' →
      fgL'.length + rem ≤ maxLen →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl useDh1 targetIdx bIdx uSk? vSk? S P (.acceptOPK k j o hdr)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple useDh1 targetIdx bIdx S maxLen
          U V (.acceptOPK k j o hdr) st >>= k2] {true} := by
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgKeyIndStepPure
    fgRunAcceptOPKPure
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, hUsedEq, hPrinFind, hOpkEq, hKyberEq,
    hKoskEq, hSpkFind, bind_assoc, pure_bind]
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, StateT.run_pure, pure_bind]; exact hUnchanged
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    rcases hdr_opk_extract hHdr with ⟨hOpkSome, hIkLen, hEkLen⟩
    by_cases hUsed : (hst.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [hUsed, ↓reduceIte, StateT.run_pure, pure_bind]; exact hUnchanged
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      by_cases hKosk : (!koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk) = true
      · simp only [hKosk, ↓reduceIte, StateT.run_pure, pure_bind]; exact hUnchanged
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
        cases hFK : hst.base.principals.find? (fun (idx, _) => idx == k.val) with
        | none =>
          dsimp only [Option.map]
          simp only [StateT.run_pure, pure_bind]; exact hUnchanged
        | some pk =>
          rcases pk with ⟨k0, kEntry⟩
          dsimp only [Option.map]
          have hkMem := List.mem_of_find?_eq_some hFK
          cases hFB : hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
          | none =>
            dsimp only [Option.map]
            simp only [StateT.run_pure, pure_bind]; exact hUnchanged
          | some pb =>
            rcases pb with ⟨kb0, bEntry⟩
            dsimp only [Option.map]
            have hbMem := List.mem_of_find?_eq_some hFB
            cases hFO : hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
            | none =>
              simp only [StateT.run_pure, pure_bind]; exact hUnchanged
            | some po =>
              rcases po with ⟨ko0, oEntry⟩
              dsimp only
              by_cases hCons : oEntry.consumed = true
              · simp only [hCons, ↓reduceIte, StateT.run_pure, pure_bind]; exact hUnchanged
              · simp only [hCons, Bool.false_eq_true, ↓reduceIte,
                  hErasePrinIk, hEraseSpkPqSk, hEraseSpkPk, hEraseSpkPqPk]
                have hAccSome := acceptKeys_opk_eq_none_or_some P hP
                  kEntry.secIKA0 kEntry.ikAPk bEntry.spkSk bEntry.spkPk oEntry.opkSk bEntry.pqspkSk
                    bEntry.pqspkPk
                  (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                    hdr.ekAPk).1
                  hdr (UInt32.ofNat o.val) hOpkSome hIkLen hEkLen
                by_cases hChk : (!((checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId
                     hdr.spkId hdr.ekAPk).1 &&
                     P.isCanonical hdr.ekAPk &&
                     P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
                     P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0 &&
                     P.x25519 oEntry.opkSk hdr.ekAPk != List.replicate 32 0)) = true
                · have hChkF := not_beq_true_eq_false hChk
                  have hAccNone : Model.acceptKeys P {
                      ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                      spkBPk := bEntry.spkPk, opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk,
                      pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
                      replayOk :=
                        (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                        hdr.ekAPk).1,
                      hdr := hdr } = none := by
                    rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, hAccSome, hChkF,
                      Bool.false_and]
                  simp only [hAccNone, hChk, ↓reduceIte, StateT.run_pure, pure_bind]; exact hUnchanged
                · have hChkT := of_not_not_eq_true hChk
                  simp only [hChk, Bool.false_eq_true, ↓reduceIte]
                  cases hDec : P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                  | none =>
                    have hAccNone : Model.acceptKeys P {
                        ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                        spkBPk := bEntry.spkPk, opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk,
                        pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
                        replayOk :=
                          (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                          hdr.ekAPk).1,
                        hdr := hdr } = none := by
                      rw [← Option.not_isSome_iff_eq_none, Bool.not_eq_true, hAccSome, hChkT, hDec]; rfl
                    simp only [hAccNone, StateT.run_pure, pure_bind]; exact hUnchanged
                  | some ss =>
                    have hAccIsSome : (Model.acceptKeys P {
                        ikBSk := kEntry.secIKA0, ikBPk := kEntry.ikAPk, spkBSk := bEntry.spkSk,
                        spkBPk := bEntry.spkPk, opkBSk? := some oEntry.opkSk, pqspkBSk := bEntry.pqspkSk,
                        pqspkBPk := bEntry.pqspkPk, trustedPeer := true,
                        replayOk :=
                          (checkAndMarkKyberBaseKeySeen hst.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                          hdr.ekAPk).1,
                        hdr := hdr }).isSome = true := by
                      rw [hAccSome, hChkT, hDec]; rfl
                    obtain ⟨accOut, hAccOut⟩ := Option.isSome_iff_exists.mp hAccIsSome
                    simp only [hAccOut]
                    have hIkOnCurve : onCurveKeyLocal P hdr.ikAPk :=
                      onCurveKeyLocal_of_koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk
                        hPrins hAdvEq.2.2 hKosk
                    have hEkOnCurve : onCurveKeyLocal P hdr.ekAPk :=
                      Or.inl (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true
                        _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hChkT).1).1).1).2
                    rcases hSlots k0 kEntry kb0 bEntry hkMem hbMem hIkOnCurve hEkOnCurve with
                      ⟨hPos1, hPos2, hPos3⟩
                    have hPos4 : R.Rep4 (some (mkSecretPosPure P (P.x25519 oEntry.opkSk hdr.ekAPk)))
                        (some (P.x25519 oEntry.opkSk hdr.ekAPk)) :=
                      R.sec4 (some _) (fun d hd => by
                        simp only [Option.some.injEq] at hd
                        subst hd; exact hP.toWellFormedPrimitivesδ.x25519_len _ _)
                    have hTup : FgTupleRel R _ _ _ (some _) _ _ _ (some _) ss :=
                      ⟨hPos1, hPos2, hPos3, hPos4, hP.toWellFormedPrimitivesδ.kemDecaps_len _ _ _ hDec⟩
                    have hValidOpk' : ValidOpkEntries S (hst.base.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed :=
                          true }) else (idx, e))) :=
                      (validOpkEntries_map_consumed S P (k.val, j.val,
                        o.val) hst.base.opkEntries hValidEc.2.2.1).1
                    have hOpks' : ∀ kv ∈ hst.base.opkEntries.map (fun (idx, e) =>
                        if idx == (k.val, j.val, o.val) then (idx, { e with consumed :=
                          true }) else (idx, e)),
                        kv.2.opkSk.length = 32 ∧ kv.2.opkPk = P.x25519Base kv.2.opkSk := by
                      intro kv hkv
                      rcases List.mem_map.mp hkv with ⟨⟨idx, e⟩, heMem, hEq⟩
                      have hO := hOpks (idx, e) heMem
                      by_cases hIdx : idx == (k.val, j.val, o.val) <;>
                        simp only [hIdx, ↓reduceIte, Bool.false_eq_true] at hEq <;>
                        (subst hEq; exact hO)
                    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                      bind_assoc, pure_bind]
                    refine fgPatchPure_bind_le R hCache hFgLen hTup
                      (fun drKey roCache' fgL' hCache' hFgLen' => ?_)
                    dsimp only
                    rw [hChooseEq, hSenderIsSome, recordKeyIndResp_run_eq_choosePartnerDrKeyRandPure P _ _
                      (by dsimp; exact hLengths.2.2.2)]
                    simp only [bind_assoc, pure_bind]
                    refine evalDist_bind_true_mono_of_support
                      (choosePartnerDrKeyRandPure P hst.base.sessions _) _ _
                      (fun drKeyRand _ => ?_)
                    cases h1 : findHonestPrincipal P hst.base.principals hdr.ikAPk <;>
                      cases h2 : findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk <;>
                      simp only [h1, h2, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
                        Bool.true_eq_false] at hSenderIsSome <;>
                      simp only [StateT.run_pure, pure_bind] <;>
                      simpa [hUsedEq, hOpkEq, hKyberEq] using hStep _ _ roCache' fgL'
                        (validKeyIndEcFg_acceptOPK k j o hValidEc hValidOpk' hUsed)
                        hOpks' hCache' hFgLen'

theorem fgStepCoupling_dh3_acceptNoOPK (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sIdx bIdx : ℕ)
    (uSk vSk : Bytes) (huSk : uSk.length = 32) (hvSk : vSk.length = 32)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (st : FgKeyIndSimState S)
    (hDead : deadDh3 P sIdx bIdx (P.x25519Base vSk) hst = false)
    (hInv : FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk (rem + 1) hst st)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyIndSimState S → ProbComp Bool)
    (hCont : ∀ r hst' st', deadDh3 P sIdx bIdx (P.x25519Base vSk) hst' = false →
      FgSimInvDh3 S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst' st' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, st')] {true}) :
    𝒟[(pqxdhKeyIndFgPreImpl false sIdx bIdx (some uSk) (some vSk) S P (.acceptNoOPK k j l hdr)).run
      hst >>= k1] {true} ≤
      𝒟[fgKeyIndStepPure P P.isValidDhTriple false sIdx bIdx S b.q_total
          (P.x25519Base uSk) (P.x25519Base vSk) (.acceptNoOPK k j l hdr) st >>= k2] {true} := by
  let R := FgSlotReps.ofDh3 P hP uSk vSk huSk hvSk
  have hInv0 := hInv
  rcases hInv with ⟨hBaseEq, hAdvEq, hCache, hFgLen, hAdvLen, hValidEc, hSpkV, hPrins, hSpks, hOpks,
    hSess⟩
  have hLengths := validKeyIndEc_lengths_le_fg S P hst.base hValidEc
  have hTakePrin : st.base.principals.take S.N_dh = hst.base.principals := by
    rw [hBaseEq]; exact List.take_of_length_le hLengths.1
  have hKoskEq : koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk =
      koskSenderOk P hst.base.principals hst.base.advKeys hdr.ikAPk := by
    rw [hBaseEq]
    exact koskSenderOkTake_eq_koskSenderOk S P hst.base.principals st.advKeyPows
      hst.base.advKeys hdr.ikAPk hLengths.1 hAdvEq.2.1
  refine fgAcceptNoOPK_coupling R hP (fun _ e => e) (eraseSpkBundleEntryFg S bIdx)
    hCache hFgLen hValidEc hAdvEq hPrins
    (by rw [hBaseEq]; rfl) (by rw [hBaseEq]; rfl) hKoskEq
    (by rw [hBaseEq, option_map_prod_id]; rfl)
    (by rw [hBaseEq]; exact find?_idx_eraseSpkBundlesFg S bIdx (k.val, j.val) hst.base.spkBundles)
    (fun _ _ => rfl) (eraseSpkBundleEntryFg_pqspkSk S bIdx)
    (eraseSpkBundleEntryFg_spkPk S bIdx) (eraseSpkBundleEntryFg_pqspkPk S bIdx)
    (by rw [hTakePrin])
    (fun rInit => by
      rw [hBaseEq]; exact choosePartnerDrKeyRandPure_eraseSessionsFg P sIdx hst.base.sessions rInit)
    (fgStepCoupling_dh3_unchanged S b P hP sIdx bIdx uSk vSk huSk hvSk rem hst st hDead hInv0
      .noneResp k1 k2 hCont)
    (fun k0 kEntry kb0 bEntry hkMem hbMem hIkOnCurve hEkOnCurve => ?_)
    (fun r rEntry roCache' fgL' hValidEc' hCache' hFgLen' => ?_)
  · refine ⟨computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
        hdr.ikAPk (hSpks (kb0, bEntry) hbMem) hIkOnCurve, ?_,
      computeTwoSideOrPairPosPure_eraseSpk_fgPosRightRep P hP S bIdx vSk kb0 bEntry
        hdr.ekAPk (hSpks (kb0, bEntry) hbMem) hEkOnCurve⟩
    rw [computeTwoSideOrPairPosPure_nil_right_len32 P kEntry.secIKA0 hdr.ekAPk
      kEntry.ikAPk (hPrins (k0, kEntry) hkMem).1]
    exact R.sec2 _ (hP.toWellFormedPrimitivesδ.x25519_len _ _)
  · apply hCont r
    · rw [deadDh3_eq_of_spk_sess P sIdx bIdx _ rfl rfl]; exact hDead
    · exact ⟨by rw [hBaseEq]; rfl, hAdvEq, hCache', hFgLen', by dsimp; omega,
        hValidEc', hSpkV, hPrins, hSpks, hOpks, hSess⟩

end Proofs.SignalPqxdh.Security.FgGapDh
