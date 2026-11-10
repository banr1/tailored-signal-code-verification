/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.WireRatchet
import Computational.Proofs.CryptoGames.SM.Theorem7Proof
import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec

/-!
# Synchronization invariants `EpochSync` and `KeptInv`

Preservation and consequence lemmas for the primitive invariants `EpochSync` and `KeptInv` of
`SimInvCX`, covering `predictReceive` agreement on salt-replaced ciphertexts (`KeptInv.evalC_spec`),
state carry-over, receiving-epoch updates, and sending steps.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-! ## Carry-over -/

theorem SnapSync.congr {C : Crypto} {Dh : DHFun (BitVec 256) Pt} {encT : Pt → PublicKey}
    {K K' rk rk' epExp epExp' : ℕ → BitVec 256} {tFront tFront' : ℕ}
    {snap : Party × ℕ × GhostState PQ}
    (h : SnapSync C Dh encT K rk epExp tFront snap)
    (ht : tFront ≤ tFront')
    (hK : ∀ t ≤ tFront, K' t = K t)
    (hrk : ∀ t ≤ tFront, rk' t = rk t)
    (hep : ∀ t ≤ tFront, epExp' t = epExp t) :
    SnapSync C Dh encT K' rk' epExp' tFront' snap := by
  rcases h with ⟨h1, h2, h3, ⟨j, hj, h4⟩, h5, h6⟩
  refine ⟨h1, le_trans h2 ht, ?_, ⟨j, hj, ?_⟩, ?_, ?_⟩
  · rw [hrk snap.2.1 h2, h3]
  · rw [hep snap.2.1 h2, hK snap.2.1 h2, h4]
  · intro rc hrc
    rcases h5 rc hrc with ⟨ep, hep_le, hsrk, hck, hmk⟩
    have hep_tf : ep ≤ tFront := le_trans hep_le h2
    refine ⟨ep, hep_le, ?_, ?_, ?_⟩
    · rw [hep ep hep_tf, hsrk]
    · rwa [hK ep hep_tf]
    · intro mk hmk_mem
      rw [hK ep hep_tf]
      exact hmk mk hmk_mem
  · intro h2le
    rcases h6 h2le with ⟨rc_last, hlast, hsrk⟩
    refine ⟨rc_last, hlast, ?_⟩
    rw [hep (snap.2.1 - 1) (by omega), hsrk]

/-! ## Receive prediction -/

private theorem sec_mem_of_lookup {α : Type} {l : List (ℕ × α)} {i : ℕ} {v : α}
    (h : l.lookup i = some v) : (i, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p ps ih =>
    simp only [List.lookup] at h
    cases hbeq : (i == p.1)
    · rw [hbeq] at h
      exact List.mem_cons_of_mem p (ih h)
    · rw [hbeq] at h
      injection h with hv
      subst hv
      rcases p with ⟨p1, p2⟩
      have hi : i = p1 := beq_iff_eq.1 hbeq
      subst hi
      exact List.mem_cons_self ..

private theorem sec_mem_of_find {α : Type} {l : List α} {p : α → Bool} {x : α}
    (h : l.find? p = some x) : x ∈ l ∧ p x = true := by
  induction l with
  | nil => simp [List.find?] at h
  | cons a as ih =>
    simp only [List.find?] at h
    cases hp : p a
    · rw [hp] at h
      rcases ih h with ⟨hm, hpx⟩
      exact ⟨List.mem_cons_of_mem a hm, hpx⟩
    · rw [hp] at h
      injection h with hx
      subst hx
      exact ⟨List.mem_cons_self .., hp⟩

private theorem sec_skipKeys_fst (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256) :
    ∀ (n p : ℕ) (acc : List (ℕ × BitVec 256)),
      (skipKeys (lChainPRG F) n (lChainAt F k p) p acc).1 = lChainAt F k (p + n)
  | 0, p, acc => by simp [skipKeys]
  | n + 1, p, acc => by
    simp only [skipKeys]
    have hstep : ((lChainPRG F p).gen (lChainAt F k p)).1 = lChainAt F k (p + 1) := rfl
    rw [hstep, sec_skipKeys_fst F k n (p + 1)]
    congr 1
    omega

private theorem sec_lFS_receive_of_recvAgrees (P : Params PQ PQC) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (k : BitVec 256)
    (v : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
    (hv : RecvAgrees P.C.F k v) (i : ℕ) :
    (∀ a e, (lFS P.C P.codec ℓ encT idOf 25000).receive v a (i, e) = none) ∨
    (∃ v', ∀ a e, (lFS P.C P.codec ℓ encT idOf 25000).receive v a (i, e) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (lSeedAt P.C.F k i) (i, a) e).map fun m => (v', i, m)) := by
  unfold lFS fromAEADPRG
  dsimp only
  cases hlk : v.skippedKeys.lookup i with
  | some key =>
    have hkey : key = lSeedAt P.C.F k i := hv.2 (i, key) (sec_mem_of_lookup hlk)
    subst hkey
    exact Or.inr ⟨{ v with skippedKeys := v.skippedKeys.filter (·.1 != i) },
      fun a e => by simp [hlk]⟩
  | none =>
    by_cases hcond : i ≤ v.lastIndex ∨ 25000 < i - v.lastIndex - 1
    · exact Or.inl (fun a e => by simp [hlk, hcond])
    · have hw₁ : (skipKeys (lChainPRG P.C.F) (i - v.lastIndex - 1) v.chainKey v.lastIndex
          v.skippedKeys).1 = lChainAt P.C.F k (i - 1) := by
        rw [hv.1, sec_skipKeys_fst]
        congr 1
        omega
      rcases hsk : skipKeys (lChainPRG P.C.F) (i - v.lastIndex - 1) v.chainKey v.lastIndex
        v.skippedKeys with ⟨w₁, skipped'⟩
      have hw₁_eq : w₁ = lChainAt P.C.F k (i - 1) := by
        rw [← hw₁, hsk]
      subst hw₁_eq
      have hseed : ((lChainPRG P.C.F (i - 1)).gen (lChainAt P.C.F k (i - 1))).2 =
          lSeedAt P.C.F k i := rfl
      exact Or.inr ⟨⟨((lChainPRG P.C.F (i - 1)).gen (lChainAt P.C.F k (i - 1))).1, i, skipped'⟩,
        fun a e => by simp [hlk, hcond, hsk, hseed]⟩

private theorem sec_lFS_receive_fresh (P : Params PQ PQC) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (k : BitVec 256) (i : ℕ) (hi : 1 ≤ i) (a : Header Pt) (e : LibsignalCiphertextWithSalt32) :
    (lFS P.C P.codec ℓ encT idOf 25000).receive
        ⟨lChainAt P.C.F k (i - 1), i - 1, []⟩ a (i, e) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (lSeedAt P.C.F k i) (i, a) e).map fun m =>
          (⟨((lChainPRG P.C.F (i - 1)).gen (lChainAt P.C.F k (i - 1))).1, i, []⟩, i, m) := by
  unfold lFS fromAEADPRG
  have hcond : ¬ (i ≤ i - 1 ∨ 25000 < i - (i - 1) - 1) := by omega
  have hsub : i - (i - 1) - 1 = 0 := by omega
  dsimp only [List.lookup]
  rw [ite_eq_right hcond, hsub]
  rfl

private theorem sec_kept_eval_eq (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hkept : KeptInv P Dh encPt encT idOf lam sC s_fig8)
    (Q : Party) (hid : (s_fig8.st Q).id = Q) (c' : Fig8C Pt)
    (r : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (heval : Kept.eval (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
      (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q) = some r) :
    r = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c').map (·.2) := by
  unfold Kept.eval at heval
  cases hfull : (sC.kept Q).full with
  | some st =>
    rw [hfull] at heval
    injection heval with hr
    rw [← hr, hkept.hfull Q st hfull]
  | none =>
    rw [hfull] at heval
    cases hrs : (sC.kept Q).rs c'.1.1 with
    | none =>
      rw [hrs] at heval
      cases heval
    | some v =>
      rw [hrs] at heval
      dsimp only [Option.map] at heval
      injection heval with hr
      have hvR : (s_fig8.st Q).vR c'.1.1 = some v := hkept.hrs Q c'.1.1 v hfull hrs
      have ht : c'.1.1 ≤ (s_fig8.st Q).tcur ∧ Q.sendsIn c'.1.1 = false :=
        (hkept.hvR Q c'.1.1).1 (by simp [hvR])
      have hnot_gt : ¬ ((s_fig8.st Q).tcur + 1 < c'.1.1) := by omega
      have hne_succ : c'.1.1 ≠ (s_fig8.st Q).tcur + 1 := by omega
      unfold lFig8 SM.Construction.scheme SM.Construction.receive
      dsimp only
      simp only [hid, ht.2, decide_eq_true_eq, hnot_gt, Bool.or_self, Bool.false_eq_true,
        ↓reduceIte, hne_succ, hvR]
      cases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v c'.1 c'.2 with
      | none => simp [← hr, hfs]
      | some vim =>
        rcases vim with ⟨v', i', m'⟩
        simp [← hr, hfs]

private theorem sec_lFig8_receive_dichotomy (P : Params PQ PQC) (Inv : ℕ → PQ → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (K rk : ℕ → BitVec 256)
    (hK : EpochSyncK P ℓ encT idOf Dh encPt sC.base.honest sC.sent sC.snaps s_fig8.st K rk epExp)
    (Q : Party) (w : List (BitVec 8)) (c : Fig8C Pt)
    (hmem : (w, c) ∈ sC.base.honest) (hsnd : Party.senderOf c.1.1 = Q.other) :
    (∀ e, (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
        (c.1, (c.2.1, e)) = none) ∨
    (∃ st', ∀ e, (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q)
        (c.1, (c.2.1, e)) =
      (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) e).map fun m => (st', c.1.1, c.2.1, m)) := by
  by_cases hbad : ((s_fig8.st Q).id.sendsIn c.1.1 || decide ((s_fig8.st Q).tcur + 1 < c.1.1)) = true
  · exact Or.inl (fun e => by
      unfold lFig8 SM.Construction.scheme SM.Construction.receive
      dsimp only
      rw [ite_eq_left hbad])
  · by_cases hnew : c.1.1 = (s_fig8.st Q).tcur + 1
    · have ht_le_snd : c.1.1 ≤ (s_fig8.st Q.other).tcur := by
        have h1 := (hinv.hsim.hhon (w, c) hmem).2.2.2
        rw [hsnd, ← hinv.hsim.htcur Q.other] at h1
        exact h1
      have hother : Q.other.other = Q := by cases Q <;> rfl
      have hgap := hK.hgap Q.other
      rw [hother] at hgap
      have ht_other : (s_fig8.st Q.other).tcur = (s_fig8.st Q).tcur + 1 := by omega
      have hahead_eq : (s_fig8.st Q.other).tcur = (s_fig8.st Q.other.other).tcur + 1 := by
        rw [hother, ht_other]
      rcases hK.hahead Q.other hahead_eq with ⟨_, x, _, hTcur, hup⟩
      rw [hother, ht_other, ← hnew] at hup
      have hhdr : c.1.2 = some (Dh.dh x Dh.base) := by
        have hh := hK.hhdr (w, c) hmem (by rw [hsnd, ht_other, ← hnew])
        rw [hsnd, hTcur] at hh
        exact hh.symm
      set v₀ : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256) :=
        (lFS P.C P.codec ℓ encT idOf 25000).initReceiver (K c.1.1)
      have hv₀ : RecvAgrees P.C.F (K c.1.1) v₀ := by
        refine ⟨rfl, ?_⟩
        intro p hp
        cases hp
      set s₁ : Fig8St Pt :=
        { s_fig8.st Q with
          tcur := c.1.1
          γ := ((dhScheme Dh).receive (s_fig8.st Q).γ (Dh.dh x Dh.base)).1
          root := (s_fig8.st Q.other).root
          vR := Function.update (s_fig8.st Q).vR c.1.1 (some v₀) }
      rcases sec_lFS_receive_of_recvAgrees P ℓ encT idOf (K c.1.1) v₀ hv₀ c.2.1 with
        hnone | ⟨v', hv'⟩
      · refine Or.inl (fun e => ?_)
        unfold lFig8 SM.Construction.scheme SM.Construction.receive
        dsimp only
        rw [ite_eq_right hbad, ite_eq_left hnew, hhdr]
        dsimp only
        rw [hup, Function.update_self]
        dsimp only
        rw [hnone c.1 e]
      · refine Or.inr ⟨{ s₁ with vR := Function.update s₁.vR c.1.1 (some v') }, fun e => ?_⟩
        unfold lFig8 SM.Construction.scheme SM.Construction.receive
        dsimp only
        rw [ite_eq_right hbad, ite_eq_left hnew, hhdr]
        dsimp only
        rw [hup, Function.update_self]
        dsimp only
        rw [hv' c.1 e]
        cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
          (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) e <;> rfl
    · cases hv : (s_fig8.st Q).vR c.1.1 with
      | none =>
        refine Or.inl (fun e => ?_)
        unfold lFig8 SM.Construction.scheme SM.Construction.receive
        dsimp only
        rw [ite_eq_right hbad, ite_eq_right hnew]
        dsimp only
        rw [hv]
      | some v =>
        have hv_agrees : RecvAgrees P.C.F (K c.1.1) v := hK.hrecv Q c.1.1 v hv
        rcases sec_lFS_receive_of_recvAgrees P ℓ encT idOf (K c.1.1) v hv_agrees c.2.1 with
          hnone | ⟨v', hv'⟩
        · refine Or.inl (fun e => ?_)
          unfold lFig8 SM.Construction.scheme SM.Construction.receive
          dsimp only
          rw [ite_eq_right hbad, ite_eq_right hnew]
          dsimp only
          rw [hv]
          dsimp only
          rw [hnone c.1 e]
        · refine Or.inr ⟨{ s_fig8.st Q with vR := Function.update (s_fig8.st Q).vR c.1.1 (some v') },
            fun e => ?_⟩
          unfold lFig8 SM.Construction.scheme SM.Construction.receive
          dsimp only
          rw [ite_eq_right hbad, ite_eq_right hnew]
          dsimp only
          rw [hv]
          dsimp only
          rw [hv' c.1 e]
          cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
            (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) e <;> rfl

/-- Relates `predictReceive` on an in-transit honest record `c` to Fig. 8's `receive` on `c` and a
salt-replaced copy `c'`. -/
theorem KeptInv.evalC_spec (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (hwin : s_fig8.win = false)
    (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    (hmem : (w, c) ∈ sC.base.honest) (hsnd : Party.senderOf c.1.1 = Q.other)
    (htr : (sC.base.mir.inTransit Q.other w).isSome)
    (h1 : c'.1 = c.1) (h2 : c'.2.1 = c.2.1) (h3 : c'.2.2.1 = c.2.2.1) :
    (predictReceive (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) sC Q c c' = some none →
      (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' = none) ∧
    (∀ x, predictReceive (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) sC Q c c' = some (some x) →
      (∃ st', (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
          some (st', x) ∧
        ∃ pm, (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
          some (st', (x.1, x.2.1, pm))) ∨
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' = none ∧
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c = none)) := by
  obtain ⟨K, rk, hK⟩ := hinv.hsync hwin
  have hi_ge : 1 ≤ c.2.1 := (hinv.hsim.hhon (w, c) hmem).1.2.2.2.2.1
  have hc_eta : (c.1, (c.2.1, c.2.2)) = c := by
    rcases c with ⟨hdr, i, e⟩; rfl
  have hc'_eta : (c.1, (c.2.1, c'.2.2)) = c' := by
    rcases c' with ⟨hdr', i', e'⟩
    dsimp only at h1 h2
    subst h1 h2
    rfl
  obtain ⟨pm, hdec_c⟩ : ∃ pm,
      ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c.2.2 = some pm := by
    obtain ⟨res, hres⟩ := hK.hhon (w, c) hmem
    have hres' : (lFS P.C P.codec ℓ encT idOf 25000).receive
        ⟨lChainAt P.C.F (K c.1.1) (c.2.1 - 1), c.2.1 - 1, []⟩ c.1 (c.2.1, c.2.2) = some res :=
      hres
    rw [sec_lFS_receive_fresh P encT idOf (K c.1.1) c.2.1 hi_ge c.1 c.2.2,
      Option.map_eq_some_iff] at hres'
    rcases hres' with ⟨pm, hdec, _⟩
    exact ⟨pm, hdec⟩
  have hdich := sec_lFig8_receive_dichotomy P Inv Dh encPt encT idOf lam qep q r x₀
    s_R sC s_fig8 ec winBefore epExp hinv K rk hK Q w c hmem hsnd
  have hsent_eq : ∀ r_s,
      sentEval (fs := lFS P.C P.codec ℓ encT idOf 25000) sC.sent c c' = some r_s →
      r_s = (((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
        (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2).map fun m => (c.1.1, c.2.1, m) := by
    intro r_s hs
    unfold sentEval at hs
    rw [Option.map_eq_some_iff] at hs
    rcases hs with ⟨e, hfind, hr_s⟩
    rcases sec_mem_of_find hfind with ⟨he_mem, he_eq⟩
    have he_c : e.1 = c := of_decide_eq_true he_eq
    rcases hK.hsent e he_mem with ⟨hlast, hck⟩
    rw [he_c] at hlast hck
    have hlast_eq : e.2.lastIndex = c.2.1 - 1 := by omega
    have hck_eq : e.2.chainKey = lChainAt P.C.F (K c.1.1) (c.2.1 - 1) := by
      rw [← hlast_eq]; exact hck
    have hst_eq : (⟨e.2.chainKey, e.2.lastIndex, []⟩ :
        FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) =
        ⟨lChainAt P.C.F (K c.1.1) (c.2.1 - 1), c.2.1 - 1, []⟩ := by
      rw [hck_eq, hlast_eq]
    have hc'_2 : c'.2 = (c.2.1, c'.2.2) := by
      rcases c' with ⟨_, i', e'⟩
      dsimp only at h2
      subst h2
      rfl
    rw [← hr_s, hst_eq, h1, hc'_2,
      sec_lFS_receive_fresh P encT idOf (K c.1.1) c.2.1 hi_ge c.1 c'.2.2]
    cases ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
      (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2 <;> rfl
  constructor
  · intro heval
    unfold predictReceive at heval
    cases hke : Kept.eval (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q) with
    | some r_k =>
      rw [hke] at heval
      injection heval with hr_k
      subst hr_k
      have hmap := sec_kept_eval_eq P Dh encPt encT idOf lam sC s_fig8 hinv.hkept
        Q (hinv.hsim.hst_id Q) c' none hke
      cases hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' with
      | none => rfl
      | some val => rw [hfig] at hmap; cases hmap
    | none =>
      rw [hke] at heval
      have hr_s := hsent_eq none heval
      have hdec_none : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
          (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2 = none := by
        cases hdec : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
          (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2 with
        | none => rfl
        | some m => rw [hdec] at hr_s; cases hr_s
      rcases hdich with hnone | ⟨st', hst'⟩
      · rw [← hc'_eta]; exact hnone c'.2.2
      · rw [← hc'_eta, hst' c'.2.2, hdec_none]; rfl
  · intro x heval
    unfold predictReceive at heval
    cases hke : Kept.eval (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) c' (sC.kept Q) with
    | some r_k =>
      rw [hke] at heval
      injection heval with hr_k
      subst hr_k
      have hmap := sec_kept_eval_eq P Dh encPt encT idOf lam sC s_fig8 hinv.hkept
        Q (hinv.hsim.hst_id Q) c' (some x) hke
      rcases hdich with hnone | ⟨st', hst'⟩
      · have hnone' := hnone c'.2.2
        rw [hc'_eta] at hnone'
        rw [hnone'] at hmap
        cases hmap
      · left
        have hfig_c' := hst' c'.2.2
        rw [hc'_eta] at hfig_c'
        have hfig_c := hst' c.2.2
        rw [hc_eta, hdec_c] at hfig_c
        rw [hfig_c'] at hmap
        cases hdec' : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
            (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2 with
        | none => rw [hdec'] at hmap; cases hmap
        | some m' =>
          rw [hdec'] at hmap hfig_c'
          dsimp only [Option.map] at hmap hfig_c' hfig_c
          injection hmap with hx_eq
          subst hx_eq
          exact ⟨st', hfig_c', pm, hfig_c⟩
    | none =>
      rw [hke] at heval
      have hr_s := hsent_eq (some x) heval
      rcases hdich with hnone | ⟨st', hst'⟩
      · right
        have h1' := hnone c'.2.2
        have h2' := hnone c.2.2
        rw [hc'_eta] at h1'
        rw [hc_eta] at h2'
        exact ⟨h1', h2'⟩
      · left
        have hfig_c' := hst' c'.2.2
        rw [hc'_eta] at hfig_c'
        have hfig_c := hst' c.2.2
        rw [hc_eta, hdec_c] at hfig_c
        cases hdec' : ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)).dec
            (lSeedAt P.C.F (K c.1.1) c.2.1) (c.2.1, c.1) c'.2.2 with
        | none => rw [hdec'] at hr_s; cases hr_s
        | some m' =>
          rw [hdec'] at hr_s hfig_c'
          dsimp only [Option.map] at hr_s hfig_c' hfig_c
          injection hr_s with hx_eq
          subst hx_eq
          exact ⟨st', hfig_c', pm, hfig_c⟩

/-! ## Preservation after a receive -/

private theorem ssm_skipKeys_agrees (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256)
    (n : ℕ) : ∀ (p : ℕ) (acc : List (ℕ × BitVec 256)),
    (∀ q ∈ acc, q.2 = lSeedAt F k q.1) →
    (skipKeys (lChainPRG F) n (lChainAt F k p) p acc).1 = lChainAt F k (p + n) ∧
    ∀ q ∈ (skipKeys (lChainPRG F) n (lChainAt F k p) p acc).2, q.2 = lSeedAt F k q.1 := by
  induction n with
  | zero =>
    intro p acc hacc
    exact ⟨rfl, hacc⟩
  | succ n ih =>
    intro p acc hacc
    have hacc' : ∀ q ∈ (p + 1, ((lChainPRG F p).gen (lChainAt F k p)).2) :: acc,
        q.2 = lSeedAt F k q.1 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · exact hacc q hq
    have hstep := ih (p + 1) _ hacc'
    have hchain : ((lChainPRG F p).gen (lChainAt F k p)).1 = lChainAt F k (p + 1) := rfl
    have hadd : p + 1 + n = p + (n + 1) := by omega
    simpa only [skipKeys, hchain, hadd] using hstep

theorem recvAgrees_receive (P : Params PQ PQC) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (k : BitVec 256) (v v' : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
    (a : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32) (res : ℕ × (LibsignalMsgPublicPart × Plain ℓ))
    (hv : RecvAgrees P.C.F k v)
    (hrecv : (lFS P.C P.codec ℓ encT idOf 25000).receive v a e = some (v', res)) :
    RecvAgrees P.C.F k v' := by
  rcases e with ⟨i, ct⟩
  unfold lFS FSAEAD.fromAEADPRG at hrecv
  dsimp only at hrecv
  rcases hlk : v.skippedKeys.lookup i with _ | key
  · rw [hlk] at hrecv
    dsimp only at hrecv
    split_ifs at hrecv with hcond
    rw [Option.map_eq_some_iff] at hrecv
    rcases hrecv with ⟨m, _, hpair⟩
    rcases Prod.mk.inj hpair with ⟨rfl, _⟩
    have hlt : v.lastIndex < i := by omega
    have hskip := ssm_skipKeys_agrees P.C.F k (i - v.lastIndex - 1) v.lastIndex v.skippedKeys hv.2
    rw [← hv.1] at hskip
    have hadd1 : v.lastIndex + (i - v.lastIndex - 1) = i - 1 := by omega
    have hadd2 : i - 1 + 1 = i := by omega
    refine ⟨?_, hskip.2⟩
    dsimp only
    rw [hskip.1, hadd1]
    change lChainAt P.C.F k (i - 1 + 1) = lChainAt P.C.F k i
    rw [hadd2]
  · rw [hlk, Option.map_eq_some_iff] at hrecv
    rcases hrecv with ⟨m, _, hpair⟩
    rcases Prod.mk.inj hpair with ⟨rfl, _⟩
    exact ⟨hv.1, fun p hp => hv.2 p (List.mem_of_mem_filter hp)⟩

/-- `EpochSync` is preserved when Fig. 8 accepts at an existing receiving epoch `t ≤ t_cur`. -/
theorem epochSync_recv_old (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (honest honest' : List (List (BitVec 8) × Fig8C Pt))
    (sent : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    {snaps : List (Party × ℕ × GhostState PQ)}
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {epExp : ℕ → BitVec 256}
    (h : EpochSync P Dh encPt encT idOf honest sent snaps s_fig8 epExp)
    (Q : Party) (c : Fig8C Pt) (st' : Fig8St Pt) (res : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c =
      some (st', res))
    (hold : c.1.1 ≤ (s_fig8.st Q).tcur)
    (hst : s_fig8'.st = Function.update s_fig8.st Q st')
    (hwin : s_fig8'.win = false → s_fig8.win = false)
    (hhon : ∀ wc ∈ honest', wc ∈ honest) :
    EpochSync P Dh encPt encT idOf honest' sent snaps s_fig8' epExp := by
  intro hw
  obtain ⟨K, rk, hK⟩ := h (hwin hw)
  unfold lFig8 SM.Construction.scheme SM.Construction.receive at hfig
  dsimp only at hfig
  split_ifs at hfig with hcond hnew
  · omega
  · dsimp only at hfig
    cases hvR : (s_fig8.st Q).vR c.1.1 with
  | none => simp [hvR] at hfig
  | some v =>
    rw [hvR] at hfig
    dsimp only at hfig
    cases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive v c.1 c.2 with
    | none => simp [hfs] at hfig
    | some vir =>
      rcases vir with ⟨v', i, m⟩
      rw [hfs] at hfig
      injection hfig with hpair
      rcases Prod.mk.inj hpair with ⟨hst', _⟩
      subst hst'
      have htcur : ∀ R, (s_fig8'.st R).tcur = (s_fig8.st R).tcur := by
        intro R; rw [hst]; by_cases hR : R = Q <;> simp [hR]
      have hTcur : ∀ R, (s_fig8'.st R).curCkaMsg = (s_fig8.st R).curCkaMsg := by
        intro R; rw [hst]; by_cases hR : R = Q <;> simp [hR]
      have hroot : ∀ R, (s_fig8'.st R).root = (s_fig8.st R).root := by
        intro R; rw [hst]; by_cases hR : R = Q <;> simp [hR]
      have hγ : ∀ R, (s_fig8'.st R).γ = (s_fig8.st R).γ := by
        intro R; rw [hst]; by_cases hR : R = Q <;> simp [hR]
      have hvS : ∀ R, (s_fig8'.st R).vS = (s_fig8.st R).vS := by
        intro R; rw [hst]; by_cases hR : R = Q <;> simp [hR]
      refine ⟨K, rk, ?_⟩
      refine
        { hhon := fun wc hwc => hK.hhon wc (hhon wc hwc)
          hhdr := fun wc hwc => by
            simp only [htcur, hTcur]
            exact hK.hhdr wc (hhon wc hwc)
          hsent := hK.hsent
          hrecv := ?_
          hsend := fun R w => by
            simp only [hvS, htcur]
            exact hK.hsend R w
          hahead := fun R => by
            simp only [htcur, hγ, hTcur, hroot]
            exact hK.hahead R
          hequal := fun R => by
            simp only [htcur, hroot, hγ]
            exact hK.hequal R
          hgap := fun R => by
            simp only [htcur]
            exact hK.hgap R
          hvS := fun R => by
            simp only [htcur, hvS]
            exact hK.hvS R
          hsent_ep := fun e he => by
            simp only [htcur]
            exact hK.hsent_ep e he
          hroot := fun R => by
            simp only [hroot, htcur]
            exact hK.hroot R
          hγ_exp := fun R hRsnd => by
            simp only [htcur, hγ] at hRsnd ⊢
            exact hK.hγ_exp R hRsnd
          hStep := fun t ht1 => by
            rw [htcur .A, htcur .B] at ht1
            exact hK.hStep t ht1
          hsnaps := fun snap hsnap => by
            rw [htcur .A, htcur .B]
            exact hK.hsnaps snap hsnap }
      intro R t w hw_vR
      rw [hst] at hw_vR
      by_cases hR : R = Q
      · subst R
        simp only [Function.update_self] at hw_vR
        by_cases ht : t = c.1.1
        · subst ht
          simp only [Function.update_self, Option.some.injEq] at hw_vR
          subst hw_vR
          exact recvAgrees_receive P encT idOf (K c.1.1) v v' c.1 c.2 (i, m)
            (hK.hrecv Q c.1.1 v hvR) hfs
        · simp only [Function.update_of_ne ht] at hw_vR
          exact hK.hrecv Q t w hw_vR
      · simp only [Function.update_of_ne hR] at hw_vR
        exact hK.hrecv R t w hw_vR

private theorem srn_skipKeys_agrees (F : ShaState → List (BitVec 8) → ShaState) (k : BitVec 256) :
    ∀ (n p : ℕ) (acc : List (ℕ × BitVec 256)),
      (∀ q ∈ acc, q.2 = lSeedAt F k q.1) →
      (skipKeys (lChainPRG F) n (lChainAt F k p) p acc).1 = lChainAt F k (p + n) ∧
      ∀ q ∈ (skipKeys (lChainPRG F) n (lChainAt F k p) p acc).2, q.2 = lSeedAt F k q.1
  | 0, _, _, hacc => ⟨rfl, hacc⟩
  | n + 1, p, acc, hacc => by
    simp only [skipKeys]
    have hstep1 : ((lChainPRG F p).gen (lChainAt F k p)).1 = lChainAt F k (p + 1) := rfl
    have hstep2 : ((lChainPRG F p).gen (lChainAt F k p)).2 = lSeedAt F k (p + 1) := rfl
    rw [hstep1, hstep2]
    have ih := srn_skipKeys_agrees F k n (p + 1) ((p + 1, lSeedAt F k (p + 1)) :: acc) ?_
    · rwa [Nat.add_right_comm p 1 n] at ih
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · exact hacc q hq

private theorem srn_recvAgrees_init (P : Params PQ PQC) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (k : BitVec 256)
    (v' : FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256))
    (a : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32) (res : ℕ × (LibsignalMsgPublicPart × Plain ℓ))
    (hrecv : (lFS P.C P.codec ℓ encT idOf 25000).receive ⟨k, 0, []⟩ a e = some (v', res)) :
    RecvAgrees P.C.F k v' := by
  rcases e with ⟨i, ct⟩
  dsimp only [lFS, fromAEADPRG, List.lookup] at hrecv
  split_ifs at hrecv with hi
  have hi_pos : 1 ≤ i := by omega
  rw [Option.map_eq_some_iff] at hrecv
  rcases hrecv with ⟨m, _, hveq⟩
  cases Prod.mk.inj hveq with
  | intro hv' _ =>
    subst hv'
    have hsk := srn_skipKeys_agrees P.C.F k (i - 1) 0 [] (by simp)
    simp only [Nat.zero_add, lChainAt] at hsk
    refine ⟨?_, by simpa only [Nat.sub_zero] using hsk.2⟩
    dsimp only
    simp only [Nat.sub_zero, hsk.1]
    have h1 : ((lChainPRG P.C.F (i - 1)).gen (lChainAt P.C.F k (i - 1))).1 =
        lChainAt P.C.F k ((i - 1) + 1) := rfl
    rw [h1, Nat.sub_add_cancel hi_pos]

private theorem srn_dhReceive_fst (Dh : DHFun (BitVec 256) Pt)
    (γ : CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T : Pt) :
    ((dhScheme Dh).receive γ T).1 = .pub T := by
  cases γ <;> rfl

private theorem srn_party_dichotomy (Q R : Party) : Q = R ∨ Q.other = R := by
  cases Q <;> cases R <;> simp

/-- `EpochSync` is preserved when Fig. 8 accepts at a new epoch `t_cur + 1` matching an honest
header. -/
theorem epochSync_recv_new (P : Params PQ PQC) (Inv : ℕ → PQ → Prop) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q r : ℕ) (x₀ : BitVec 256)
    (s_R : SM.GameState (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (s_fig8 : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ec : Party → BitVec 256) (winBefore : ℕ → Bool) (epExp : ℕ → BitVec 256)
    (hinv : SimInvCX P Inv ℓ Dh encPt encT idOf lam qep q r x₀ s_R sC s_fig8 ec winBefore epExp)
    (Q : Party) (w : List (BitVec 8)) (c c' : Fig8C Pt)
    (hmem : (w, c) ∈ sC.base.honest) (hsnd : Party.senderOf c.1.1 = Q.other)
    (hhdr : c'.1 = c.1)
    (hnew : c.1.1 = (s_fig8.st Q).tcur + 1)
    (st' : Fig8St Pt) (res : ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ))
    (hfig : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s_fig8.st Q) c' =
      some (st', res))
    (honest' : List (List (BitVec 8) × Fig8C Pt))
    (s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hst : s_fig8'.st = Function.update s_fig8.st Q st')
    (hwin : s_fig8'.win = false → s_fig8.win = false)
    (hhon : ∀ wc ∈ honest', wc ∈ sC.base.honest)
    {rc : BitVec 256} :
    EpochSync P Dh encPt encT idOf honest' sC.sent sC.snaps s_fig8'
      (Function.update epExp (sC.base.mir.epoch Q + 2) rc) := by
  intro hw'
  obtain ⟨K, rk, hK⟩ := hinv.hsync (hwin hw')
  have hle_other : c.1.1 ≤ (s_fig8.st Q.other).tcur := by
    have h1 := (hinv.hsim.hhon (w, c) hmem).2.2.2
    rw [hsnd, ← hinv.hsim.htcur Q.other] at h1
    exact h1
  have hgap_other : (s_fig8.st Q.other).tcur ≤ (s_fig8.st Q).tcur + 1 := by
    simpa [Party.other_other] using hK.hgap Q.other
  have ht_other : (s_fig8.st Q.other).tcur = (s_fig8.st Q.other.other).tcur + 1 := by
    rw [Party.other_other]; omega
  have ht_eq : (s_fig8.st Q.other).tcur = c.1.1 := by omega
  obtain ⟨_, x, hγ_other, hT_other, hup⟩ := hK.hahead Q.other ht_other
  rw [Party.other_other, ht_eq] at hup
  have hT_c : c.1.2 = some (Dh.dh x Dh.base) := by
    have h1 := hK.hhdr (w, c) hmem (by rw [hsnd, ht_eq])
    rw [hsnd, hT_other] at h1
    exact h1.symm
  have hc'_11 : c'.1.1 = c.1.1 := congrArg Prod.fst hhdr
  have hc'_12 : c'.1.2 = some (Dh.dh x Dh.base) := (congrArg Prod.snd hhdr).trans hT_c
  dsimp only [lFig8, SM.Construction.scheme, SM.Construction.receive] at hfig
  rw [hc'_11, hc'_12] at hfig
  split_ifs at hfig with hcond
  have hsends_Q : Q.sendsIn c.1.1 = false := by
    rw [hinv.hsim.hst_id Q] at hcond
    cases hq : Q.sendsIn c.1.1
    · rfl
    · simp [hq] at hcond
  simp only [hnew, ↓reduceIte, Function.update_self] at hfig
  rw [← hnew] at hfig
  cases hfs : (lFS P.C P.codec ℓ encT idOf 25000).receive
      ((lFS P.C P.codec ℓ encT idOf 25000).initReceiver
        ((rootPRNG P.C.F encPt).up (s_fig8.st Q).root
          ((dhScheme Dh).receive (s_fig8.st Q).γ (Dh.dh x Dh.base)).2).2)
      c'.1 c'.2 with
  | none => simp [hfs] at hfig
  | some vim =>
    rcases vim with ⟨v', i, m⟩
    simp only [hfs, Option.some.injEq, Prod.mk.injEq] at hfig
    rcases hfig with ⟨hst', _⟩
    rw [hup] at hfs hst'
    have hrecv_v' : RecvAgrees P.C.F (K c.1.1) v' :=
      srn_recvAgrees_init P encT idOf (K c.1.1) v' c'.1 c'.2 (i, m) hfs
    have hst_Q : s_fig8'.st Q = st' := by rw [hst, Function.update_self]
    have hst_other : s_fig8'.st Q.other = s_fig8.st Q.other := by
      rw [hst, Function.update_of_ne (Party.other_ne Q)]
    have htcur_all : ∀ R, (s_fig8'.st R).tcur = c.1.1 := by
      intro R
      rcases srn_party_dichotomy Q R with rfl | rfl
      · rw [hst_Q, ← hst']
      · rw [hst_other, ht_eq]
    have hmax_old : max (s_fig8.st .A).tcur (s_fig8.st .B).tcur = c.1.1 := by
      cases Q with
      | A =>
        have hB : (s_fig8.st .B).tcur = c.1.1 := ht_eq
        omega
      | B =>
        have hA : (s_fig8.st .A).tcur = c.1.1 := ht_eq
        omega
    have hmax_new : max (s_fig8'.st .A).tcur (s_fig8'.st .B).tcur = c.1.1 := by
      simp [htcur_all]
    have hepExp_le : ∀ t₀ ≤ c.1.1,
        Function.update epExp (sC.base.mir.epoch Q + 2) rc t₀ = epExp t₀ := by
      intro t₀ ht₀
      have htcur_mir := hinv.hsim.htcur Q
      have hne : t₀ ≠ sC.base.mir.epoch Q + 2 := by omega
      exact Function.update_of_ne hne rc epExp
    refine ⟨K, rk, ?_⟩
    refine
      { hhon := fun wc hwc => hK.hhon wc (hhon wc hwc)
        hhdr := ?_
        hsent := hK.hsent
        hrecv := ?_
        hsend := ?_
        hahead := ?_
        hequal := ?_
        hgap := ?_
        hvS := ?_
        hsent_ep := ?_
        hroot := ?_
        hγ_exp := ?_
        hStep := ?_
        hsnaps := ?_ }
    · intro wc hwc ht_wc
      by_cases hS : Party.senderOf wc.2.1.1 = Q
      · rw [hS, htcur_all Q] at ht_wc
        rw [← ht_wc, hsnd] at hS
        exact absurd hS (Party.other_ne Q)
      · have hne : s_fig8'.st (Party.senderOf wc.2.1.1) = s_fig8.st (Party.senderOf wc.2.1.1) := by
          rw [hst, Function.update_of_ne hS]
        rw [hne] at ht_wc ⊢
        exact hK.hhdr wc (hhon wc hwc) ht_wc
    · intro R t₀ v₀ hvR
      rcases srn_party_dichotomy Q R with rfl | rfl
      · rw [hst_Q, ← hst'] at hvR
        dsimp only at hvR
        rw [Function.update_idem] at hvR
        by_cases ht₀ : t₀ = c.1.1
        · subst ht₀
          rw [Function.update_self, Option.some.injEq] at hvR
          subst hvR
          exact hrecv_v'
        · rw [Function.update_of_ne ht₀] at hvR
          exact hK.hrecv Q t₀ v₀ hvR
      · rw [hst_other] at hvR
        exact hK.hrecv Q.other t₀ v₀ hvR
    · intro R v₀ hvS hsends
      rcases srn_party_dichotomy Q R with rfl | rfl
      · rw [htcur_all Q, hsends_Q] at hsends
        cases hsends
      · rw [hst_other] at hvS hsends ⊢
        exact hK.hsend Q.other v₀ hvS hsends
    · intro R h_ah
      rw [htcur_all R, htcur_all R.other] at h_ah
      omega
    · intro R _ hsends
      rcases srn_party_dichotomy Q R with rfl | rfl
      · rw [htcur_all Q, hsends_Q] at hsends
        cases hsends
      · rw [Party.other_other, hst_other, hst_Q, ← hst']
        dsimp only
        rw [srn_dhReceive_fst]
        exact ⟨rfl, x, hγ_other, rfl⟩
    · intro R
      rw [htcur_all R, htcur_all R.other]
      omega
    · intro R hsends
      rcases srn_party_dichotomy Q R with rfl | rfl
      · rw [htcur_all Q, hsends_Q] at hsends
        cases hsends
      · rw [hst_other] at hsends ⊢
        exact hK.hvS Q.other hsends
    · intro e he
      have h1 := hK.hsent_ep e he
      rcases srn_party_dichotomy Q (Party.senderOf e.1.1.1) with hS | hS
      · rw [← hS, htcur_all Q]
        rw [← hS] at h1
        omega
      · rw [← hS, hst_other]
        rw [← hS] at h1
        exact h1
    · intro R
      rcases srn_party_dichotomy Q R with rfl | rfl
      · rw [hst_Q, ← hst']
        dsimp only
        rw [← ht_eq]
        exact hK.hroot Q.other
      · rw [hst_other]
        exact hK.hroot Q.other
    · intro R hsends
      rcases srn_party_dichotomy Q R with rfl | rfl
      · rw [htcur_all Q, hsends_Q] at hsends
        cases hsends
      · rw [hst_other] at hsends ⊢
        rw [hepExp_le _ (by rw [ht_eq])]
        exact hK.hγ_exp Q.other hsends
    · intro t₀ ht1
      rw [hmax_new] at ht1
      rw [hepExp_le (t₀ + 1) (by omega), hepExp_le t₀ (by omega)]
      exact hK.hStep t₀ (by rw [hmax_old]; exact ht1)
    · intro snap hsnap
      rw [hmax_new]
      exact SnapSync.congr (hK.hsnaps snap hsnap) (by rw [hmax_old])
        (fun _ _ => rfl) (fun _ _ => rfl)
        (fun t₀ ht₀ => hepExp_le t₀ (by rw [← hmax_old]; exact ht₀))

/-! ## Preservation after a send -/

private theorem ssm_send_fst {KC Γ CCoins T I KR Sig K MK M C : Type} [Inhabited (ℕ × C)]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (ae : AEADScheme MK (ℕ × Header T) M C) (G : ℕ → PRGScheme K (K × MK)) (maxSkip : ℕ)
    (s : PartyState Γ T Sig (RatchetSenderState K) (RatchetReceiverState K MK))
    (m : M) (r : CCoins) :
    let fs := FSAEAD.fromAEADPRG ae G maxSkip
    ((SM.Construction.send cka prng fs s m r).1).vR = s.vR ∧
    ((SM.Construction.send cka prng fs s m r).1).tcur =
      (if s.id.sendsIn (s.tcur + 1) then s.tcur + 1 else s.tcur) ∧
    (s.id.sendsIn (s.tcur + 1) = false →
      ∀ m' r', (SM.Construction.send cka prng fs s m' r').1 =
        (SM.Construction.send cka prng fs s m r).1) := by
  dsimp only
  unfold SM.Construction.send FSAEAD.fromAEADPRG
  dsimp only
  cases hs : s.id.sendsIn (s.tcur + 1)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases s.vS <;> simp
  · simp

/-- `KeptInv` is preserved when Fig. 8 steps by `send` and `kept` steps by `Kept.send`. -/
theorem keptInv_send {P : Params PQ PQC} {Dh : DHFun (BitVec 256) Pt}
    {encPt : Pt → List (BitVec 8)} {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {lam : Pt}
    {sC sC' : LibsignalToModularSchemeSimState PQ Pt ℓ}
    {s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (h : KeptInv P Dh encPt encT idOf lam sC s_fig8)
    (Q : Party) (hid : (s_fig8.st Q).id = Q) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : BitVec 256)
    (hst : s_fig8'.st = Function.update s_fig8.st Q
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).1)
    (hkept : sC'.kept = Function.update sC.kept Q
      (Kept.send (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (sC.kept Q))) :
    KeptInv P Dh encPt encT idOf lam sC' s_fig8' := by
  obtain ⟨hvR_eq, htcur_eq, hsend_same⟩ :=
    ssm_send_fst (dhScheme Dh) (rootPRNG P.C.F encPt)
      ((lAead P.C P.codec ℓ encT idOf).movePubPartToAD (lPubOf P.codec)) (lChainPRG P.C.F) 25000
      (s_fig8.st Q) m rc
  change (((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).1).vR =
    (s_fig8.st Q).vR at hvR_eq
  change (((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).1).tcur =
    (if (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) then (s_fig8.st Q).tcur + 1
     else (s_fig8.st Q).tcur) at htcur_eq
  refine ⟨?_, ?_, ?_⟩
  · intro R st hfull
    rw [hkept] at hfull
    rw [hst]
    by_cases hR : R = Q
    · subst R
      simp only [Function.update_self] at hfull ⊢
      unfold Kept.send at hfull
      cases hk : (sC.kept Q).full with
      | none => simp [hk] at hfull
      | some st₀ =>
        rw [hk] at hfull
        dsimp only at hfull
        have hst₀ : st₀ = s_fig8.st Q := h.hfull Q st₀ hk
        subst hst₀
        split_ifs at hfull with hs
        simp only [Option.some.injEq] at hfull
        subst hfull
        exact hsend_same (Bool.eq_false_iff.mpr hs) _ _
    · simp only [Function.update_of_ne hR] at hfull ⊢
      exact h.hfull R st hfull
  · intro R t v hfull hrs
    rw [hkept] at hfull hrs
    rw [hst]
    by_cases hR : R = Q
    · subst R
      simp only [Function.update_self] at hfull hrs ⊢
      rw [hvR_eq]
      unfold Kept.send at hfull hrs
      cases hk : (sC.kept Q).full with
      | none =>
        rw [hk] at hrs
        exact h.hrs Q t v hk hrs
      | some st₀ =>
        rw [hk] at hfull hrs
        dsimp only at hfull hrs
        have hst₀ : st₀ = s_fig8.st Q := h.hfull Q st₀ hk
        subst hst₀
        split_ifs at hfull hrs with hs
        exact hrs
    · simp only [Function.update_of_ne hR] at hfull hrs ⊢
      exact h.hrs R t v hfull hrs
  · intro R t
    rw [hst]
    by_cases hR : R = Q
    · subst R
      simp only [Function.update_self, hvR_eq, h.hvR Q t, htcur_eq, hid]
      split_ifs with hs
      · constructor
        · rintro ⟨hle, hrf⟩
          exact ⟨by omega, hrf⟩
        · rintro ⟨hle, hrf⟩
          refine ⟨?_, hrf⟩
          have hne : t ≠ (s_fig8.st Q).tcur + 1 := by
            intro heq; subst heq; rw [hs] at hrf; cases hrf
          omega
      · rfl
    · simp only [Function.update_of_ne hR]
      exact h.hvR R t

private theorem ses_short_lHeader {P : Params PQ PQC} (hrt : RoundTrip.RtHyp P ℓ)
    (encT : Pt → PublicKey) (i : ℕ) (h : Header Pt) (p : LibsignalMsgPublicPart)
    (hpq : p.pqmsg.length < rustLenBound)
    (haddr : ∀ a, p.addrs = some a → a.length < rustLenBound)
    (body : List (BitVec 8)) (hb : body.length = 16 * nBlocks ℓ) :
    SignalWireShort (lHeader encT i h p) body :=
  ⟨rfl, hpq, haddr, by rw [hb]; exact RoundTrip.LengthsOk.body_lt hrt.len⟩

private theorem ses_lPubOf_enc {P : Params PQ PQC} (hrt : RoundTrip.RtHyp P ℓ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (k : BitVec 256) (a : ℕ × Header Pt) (p : LibsignalMsgPublicPart) (plain : Plain ℓ)
    (hpq : p.pqmsg.length < rustLenBound)
    (haddr : ∀ a, p.addrs = some a → a.length < rustLenBound) :
    lPubOf P.codec ((lAead P.C P.codec ℓ encT idOf).enc k (a, p) plain) = some p := by
  simp only [lPubOf, lAead, lAeadK, lWire, libsignalWireAead, wireEncode]
  rw [hrt.rt (lHeader encT a.1 a.2 p) _
    (ses_short_lHeader hrt encT a.1 a.2 p hpq haddr _ (RoundTrip.length_cbcBody _))]
  cases p
  rfl

private theorem ses_lAead_dec_enc {P : Params PQ PQC}
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (k : BitVec 256) (a : ℕ × Header Pt) (p : LibsignalMsgPublicPart) (plain : Plain ℓ)
    (hpq : p.pqmsg.length < rustLenBound)
    (haddr : ∀ a, p.addrs = some a → a.length < rustLenBound) :
    (lAead P.C P.codec ℓ encT idOf).dec k (a, p)
      ((lAead P.C P.codec ℓ encT idOf).enc k (a, p) plain) = some plain := by
  have h : (lWire P.C P.codec ℓ).dec (deriveMessageKeys P.C.F p.salt (keyToBytes32 k)) (lIds idOf a.2.1)
      ((lWire P.C P.codec ℓ).enc (deriveMessageKeys P.C.F p.salt (keyToBytes32 k)) (lIds idOf a.2.1)
        (lHeader encT a.1 a.2 p) plain) = some (lHeader encT a.1 a.2 p, plain.toList) := by
    simp only [lWire, libsignalWireAead, libsignalReceiveWire, wireEncode, beq_self_eq_true, ↓reduceIte]
    rw [hrt.rt (lHeader encT a.1 a.2 p) _
      (ses_short_lHeader hrt encT a.1 a.2 p hpq haddr _ (RoundTrip.length_cbcBody _))]
    simp only [cbcPkcs7EncryptOnly, cbcScheme]
    rw [cbcDecRaw_correct hD]
    have hok' : addressCheckPasses (none : Option (List (BitVec 8))) none = true := rfl
    simp [hok']
  simp only [lAead, lAeadK, lWire, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [h]
  simp [fitPlain_toList]

private theorem ses_lFS_receive_send {P : Params PQ PQC}
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (k : BitVec 256) (v : FSAEAD.RatchetSenderState (BitVec 256))
    (hdr : Header Pt) (m : LibsignalMsgPublicPart × Plain ℓ)
    (hv : SendAgrees P.C.F k v)
    (hpq : m.1.pqmsg.length < rustLenBound)
    (haddr : ∀ a, m.1.addrs = some a → a.length < rustLenBound) :
    let out := (lFS P.C P.codec ℓ encT idOf 25000).send v hdr m
    out.1.lastIndex = v.lastIndex + 1 ∧
      SendAgrees P.C.F k out.1 ∧
      out.2.1 = v.lastIndex + 1 ∧
      ∃ res, (lFS P.C P.codec ℓ encT idOf 25000).receive
        ⟨lChainAt P.C.F k (out.2.1 - 1), out.2.1 - 1, []⟩ hdr out.2 = some res := by
  rcases v with ⟨ck, idx⟩
  rcases m with ⟨p, plain⟩
  unfold SendAgrees at hv
  dsimp only at hv ⊢
  subst hv
  refine ⟨rfl, rfl, rfl, ?_⟩
  have hsub1 : idx + 1 - 1 = idx := by omega
  have hsub2 : idx + 1 - idx - 1 = 0 := by omega
  have hcond : ¬ (idx + 1 ≤ idx ∨ 25000 < 0) := by omega
  dsimp only [lFS, FSAEAD.fromAEADPRG]
  simp only [List.lookup, hsub1, hsub2, hcond, ↓reduceIte, FSAEAD.skipKeys]
  dsimp only [AEADScheme.movePubPartToAD]
  rw [ses_lPubOf_enc hrt encT idOf _ _ p plain hpq haddr]
  dsimp only
  rw [ses_lAead_dec_enc hD hrt encT idOf _ _ p plain hpq haddr]
  exact ⟨_, rfl⟩

private theorem ses_senderOf_of_sendsIn {Q : Party} {t : ℕ} (h : Q.sendsIn t = true) :
    Party.senderOf t = Q := by
  cases Q with
  | A =>
    dsimp only [Party.sendsIn] at h
    simp [Party.senderOf, h]
  | B =>
    dsimp only [Party.sendsIn] at h
    rw [beq_iff_eq] at h
    have h1 : (t % 2 == 1) = false := beq_false_of_ne (by omega)
    simp [Party.senderOf, h1]

private theorem ses_epochSync_send_same (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (honest honest' : List (List (BitVec 8) × Fig8C Pt))
    (sent sent' : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    {snaps : List (Party × ℕ × GhostState PQ)}
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (K rk epExp : ℕ → BitVec 256)
    (hk : EpochSyncK P ℓ encT idOf Dh encPt honest sent snaps s_fig8.st K rk epExp)
    (hid : ∀ R, (s_fig8.st R).id = R)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : BitVec 256)
    (hsame : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = false)
    (hst : s_fig8'.st = Function.update s_fig8.st Q
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).1)
    (hhon : ∀ wc ∈ honest', wc ∈ honest ∨
      wc.2 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2)
    (hsent : ∀ e ∈ sent', e ∈ sent ∨
      ((s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = false ∧
        e.1 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2 ∧
        (s_fig8.st Q).vS = some e.2))
    (hpq : m.1.pqmsg.length < rustLenBound)
    (haddr : ∀ a, m.1.addrs = some a → a.length < rustLenBound) :
    EpochSyncK P ℓ encT idOf Dh encPt honest' sent' snaps s_fig8'.st K rk epExp := by
  set stQ := s_fig8.st Q
  set t := stQ.tcur
  have hQ_succ : Q.sendsIn (t + 1) = false := by rw [← hid Q]; exact hsame
  have hQ_t : Q.sendsIn t = true := Party.sendsIn_of_succ_eq_false Q t hQ_succ
  have hsnd_t : Party.senderOf t = Q := ses_senderOf_of_sendsIn hQ_t
  obtain ⟨v, hvS⟩ := Option.isSome_iff_exists.mp (hk.hvS Q hQ_t)
  have hv_agree : SendAgrees P.C.F (K t) v := hk.hsend Q v hvS hQ_t
  set out := (lFS P.C P.codec ℓ encT idOf 25000).send v (t, stQ.curCkaMsg) m
  have hsend_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send stQ m rc =
      ({ stQ with vS := some out.1 }, ((t, stQ.curCkaMsg), out.2)) := by
    dsimp only [lFig8, scheme, SM.Construction.send]
    simp only [stQ, t, hsame, Bool.false_eq_true, ↓reduceIte, hvS, out]
  rcases ses_lFS_receive_send hD hrt encT idOf (K t) v (t, stQ.curCkaMsg) m hv_agree hpq haddr with
    ⟨hlast, hout_agree, hout_idx, hres⟩
  have htcur_eq : ∀ R, (s_fig8'.st R).tcur = (s_fig8.st R).tcur := fun R => by
    rw [hst, hsend_eq]; by_cases hR : R = Q <;> simp [Function.update, hR, stQ]
  have hTcur_eq : ∀ R, (s_fig8'.st R).curCkaMsg = (s_fig8.st R).curCkaMsg := fun R => by
    rw [hst, hsend_eq]; by_cases hR : R = Q <;> simp [Function.update, hR, stQ]
  have hroot_eq : ∀ R, (s_fig8'.st R).root = (s_fig8.st R).root := fun R => by
    rw [hst, hsend_eq]; by_cases hR : R = Q <;> simp [Function.update, hR, stQ]
  have hγ_eq : ∀ R, (s_fig8'.st R).γ = (s_fig8.st R).γ := fun R => by
    rw [hst, hsend_eq]; by_cases hR : R = Q <;> simp [Function.update, hR, stQ]
  have hvR_eq : ∀ R, (s_fig8'.st R).vR = (s_fig8.st R).vR := fun R => by
    rw [hst, hsend_eq]; by_cases hR : R = Q <;> simp [Function.update, hR, stQ]
  refine
    { hhon := fun wc hwc => by
        rcases hhon wc hwc with hmem | hnew_c
        · exact hk.hhon wc hmem
        · rw [hnew_c, hsend_eq]
          exact hres
      hhdr := fun wc hwc hep => by
        rw [htcur_eq] at hep
        rw [hTcur_eq]
        rcases hhon wc hwc with hmem | hnew_c
        · exact hk.hhdr wc hmem hep
        · rw [hnew_c, hsend_eq]
          dsimp only
          rw [hsnd_t]
      hsent := fun e he => by
        rcases hsent e he with hmem | ⟨_, he1, he2⟩
        · exact hk.hsent e hmem
        · rw [hvS] at he2
          injection he2 with hv_eq
          subst hv_eq
          rw [he1, hsend_eq]
          exact ⟨hout_idx.symm, hv_agree⟩
      hrecv := fun R t₀ v₀ hv₀ => by
        rw [hvR_eq] at hv₀
        exact hk.hrecv R t₀ v₀ hv₀
      hsend := fun R v₀ hv₀ hRsnd => by
        rw [htcur_eq] at hRsnd ⊢
        by_cases hR : R = Q
        · subst hR
          rw [hst, hsend_eq, Function.update_self] at hv₀
          injection hv₀ with hv₀_eq
          subst hv₀_eq
          exact hout_agree
        · rw [hst, Function.update_of_ne hR] at hv₀
          exact hk.hsend R v₀ hv₀ hRsnd
      hahead := fun R hR => by
        simp only [htcur_eq, hγ_eq, hTcur_eq, hroot_eq] at hR ⊢
        exact hk.hahead R hR
      hequal := fun R hR hRsnd => by
        simp only [htcur_eq, hroot_eq, hγ_eq] at hR hRsnd ⊢
        exact hk.hequal R hR hRsnd
      hgap := fun R => by
        simp only [htcur_eq]
        exact hk.hgap R
      hvS := fun R hRsnd => by
        rw [htcur_eq] at hRsnd
        by_cases hR : R = Q
        · subst hR
          rw [hst, hsend_eq, Function.update_self]
          rfl
        · rw [hst, Function.update_of_ne hR]
          exact hk.hvS R hRsnd
      hsent_ep := fun e he => by
        rw [htcur_eq]
        rcases hsent e he with hmem | ⟨_, he1, _⟩
        · exact hk.hsent_ep e hmem
        · rw [he1, hsend_eq]
          dsimp only
          rw [hsnd_t]
      hroot := fun R => by
        simp only [hroot_eq, htcur_eq]
        exact hk.hroot R
      hγ_exp := fun R hRsnd => by
        simp only [htcur_eq, hγ_eq] at hRsnd ⊢
        exact hk.hγ_exp R hRsnd
      hStep := fun t₀ ht1 => by
        rw [htcur_eq .A, htcur_eq .B] at ht1
        exact hk.hStep t₀ ht1
      hsnaps := fun snap hsnap => by
        rw [htcur_eq .A, htcur_eq .B]
        exact hk.hsnaps snap hsnap }

private theorem ses_epochSync_send_new (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (hDh : Dh.Commutes) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (honest honest' : List (List (BitVec 8) × Fig8C Pt))
    (sent sent' : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    {snaps : List (Party × ℕ × GhostState PQ)}
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (K rk epExp : ℕ → BitVec 256)
    (hk : EpochSyncK P ℓ encT idOf Dh encPt honest sent snaps s_fig8.st K rk epExp)
    (hvR' : ∀ R t, ((s_fig8.st R).vR t).isSome ↔ (t ≤ (s_fig8.st R).tcur ∧ R.sendsIn t = false))
    (hid : ∀ R, (s_fig8.st R).id = R)
    (hhonEp : ∀ wc ∈ honest, wc.2.1.1 ≤ (s_fig8.st (Party.senderOf wc.2.1.1)).tcur)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : BitVec 256)
    (hnew : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = true)
    (hrc : epExp ((s_fig8.st Q).tcur + 1) = rc)
    (hst : s_fig8'.st = Function.update s_fig8.st Q
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).1)
    (hhon : ∀ wc ∈ honest', wc ∈ honest ∨
      wc.2 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2)
    (hsent : ∀ e ∈ sent', e ∈ sent ∨
      ((s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = false ∧
        e.1 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2 ∧
        (s_fig8.st Q).vS = some e.2))
    (hpq : m.1.pqmsg.length < rustLenBound)
    (haddr : ∀ a, m.1.addrs = some a → a.length < rustLenBound) :
    ∃ K' rk', EpochSyncK P ℓ encT idOf Dh encPt honest' sent' snaps s_fig8'.st K' rk' epExp := by
  set stQ := s_fig8.st Q
  set stO := s_fig8.st Q.other
  set t := stQ.tcur
  have hQ_succ : Q.sendsIn (t + 1) = true := by rw [← hid Q]; exact hnew
  have hQ_t : Q.sendsIn t = false := Party.sendsIn_eq_false_of_succ Q t hQ_succ
  have hO_t : Q.other.sendsIn t = true := Party.other_sendsIn_of_eq_false Q t hQ_t
  have hO_succ : Q.other.sendsIn (t + 1) = false :=
    Party.sendsIn_eq_false_of_other Q.other (t + 1) (by simpa [Party.other_other] using hQ_succ)
  have hsnd_succ : Party.senderOf (t + 1) = Q := ses_senderOf_of_sendsIn hQ_succ
  have hle1 : t ≤ stO.tcur + 1 := hk.hgap Q
  have hle2 : stO.tcur ≤ t + 1 := by simpa [stO, stQ, t, Party.other_other] using hk.hgap Q.other
  have hne1 : t ≠ stO.tcur + 1 := fun heq => by
    have := (hk.hahead Q heq).1
    rw [show (s_fig8.st Q).tcur = t from rfl, hQ_t] at this
    cases this
  have hne2 : stO.tcur ≠ t + 1 := fun heq => by
    have := (hk.hahead Q.other (by simpa [stO, stQ, t, Party.other_other] using heq)).1
    rw [show (s_fig8.st Q.other).tcur = stO.tcur from rfl, heq, hO_succ] at this
    cases this
  have htO : stO.tcur = t := by omega
  have htcur_all : ∀ R, (s_fig8.st R).tcur = t := fun R => by
    rcases Party.eq_or_eq_other Q R with rfl | rfl
    · rfl
    · exact htO
  rcases hk.hequal Q.other (by simp [htcur_all]) (by rw [htcur_all]; exact hO_t) with
    ⟨hroot_eq, x, hγO, hγQ⟩
  have hγQ' : stQ.γ = .pub (Dh.dh x Dh.base) := by simpa [stQ, Party.other_other] using hγQ
  have hx_eq : x = epExp t := by
    have hγO_exp := hk.hγ_exp Q.other (by rw [htcur_all]; exact hO_t)
    rw [htcur_all Q.other, hγO] at hγO_exp
    exact CryptoGames.CKA.DDH.State.exp.inj hγO_exp
  set c_cka := (dhScheme Dh).send stQ.γ rc
  set p_up := (rootPRNG P.C.F encPt).up stQ.root c_cka.2.2
  set v₀ := (lFS P.C P.codec ℓ encT idOf 25000).initSender p_up.2
  set out := (lFS P.C P.codec ℓ encT idOf 25000).send v₀ (t + 1, some c_cka.2.1) m
  set K' := Function.update K (t + 1) p_up.2
  set rk' := Function.update rk (t + 1) p_up.1
  have hK'_le : ∀ t₀ ≤ t, K' t₀ = K t₀ := fun t₀ ht₀ => by
    have hne : t₀ ≠ t + 1 := by omega
    exact Function.update_of_ne hne p_up.2 K
  have hK'_succ : K' (t + 1) = p_up.2 := Function.update_self (t + 1) p_up.2 K
  have hrk'_le : ∀ t₀ ≤ t, rk' t₀ = rk t₀ := fun t₀ ht₀ => by
    have hne : t₀ ≠ t + 1 := by omega
    exact Function.update_of_ne hne p_up.1 rk
  have hrk'_succ : rk' (t + 1) = p_up.1 := Function.update_self (t + 1) p_up.1 rk
  have hv₀_agree : SendAgrees P.C.F (K' (t + 1)) v₀ := by
    rw [hK'_succ]; rfl
  rcases ses_lFS_receive_send hD hrt encT idOf (K' (t + 1)) v₀ (t + 1, some c_cka.2.1) m
      hv₀_agree hpq haddr with
    ⟨hlast, hout_agree, hout_idx, hres⟩
  have hsend_eq : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send stQ m rc =
      ({ stQ with tcur := t + 1, γ := c_cka.1, curCkaMsg := some c_cka.2.1, root := p_up.1,
                  vS := some out.1 },
        ((t + 1, some c_cka.2.1), out.2)) := by
    dsimp only [lFig8, scheme, SM.Construction.send]
    simp only [stQ, t, hnew, ↓reduceIte, c_cka, p_up, v₀, out]
  have hvR_eq : ∀ R, (s_fig8'.st R).vR = (s_fig8.st R).vR := fun R => by
    rw [hst, hsend_eq]; by_cases hR : R = Q <;> simp [Function.update, hR, stQ]
  have hmax_old : max (s_fig8.st .A).tcur (s_fig8.st .B).tcur = t := by
    simp [htcur_all]
  have hmax_new : max (s_fig8'.st .A).tcur (s_fig8'.st .B).tcur = t + 1 := by
    cases Q with
    | A =>
      have hA : (s_fig8'.st .A).tcur = t + 1 := by rw [hst, hsend_eq, Function.update_self]
      have hB : (s_fig8'.st .B).tcur = t := by
        rw [hst, Function.update_of_ne (by decide), htcur_all .B]
      omega
    | B =>
      have hA : (s_fig8'.st .A).tcur = t := by
        rw [hst, Function.update_of_ne (by decide), htcur_all .A]
      have hB : (s_fig8'.st .B).tcur = t + 1 := by rw [hst, hsend_eq, Function.update_self]
      omega
  refine ⟨K', rk', ?_⟩
  refine
    { hhon := fun wc hwc => by
        rcases hhon wc hwc with hmem | hnew_c
        · have hep : wc.2.1.1 ≤ t := by
            have := hhonEp wc hmem
            rwa [htcur_all] at this
          rw [hK'_le wc.2.1.1 hep]
          exact hk.hhon wc hmem
        · rw [hnew_c, hsend_eq]
          exact hres
      hhdr := fun wc hwc hep => by
        rcases hhon wc hwc with hmem | hnew_c
        · have hep_le : wc.2.1.1 ≤ t := by
            have := hhonEp wc hmem
            rwa [htcur_all] at this
          by_cases hS : Party.senderOf wc.2.1.1 = Q
          · rw [hS, hst, hsend_eq, Function.update_self] at hep
            dsimp only at hep
            omega
          · rw [hst, Function.update_of_ne hS] at hep ⊢
            exact hk.hhdr wc hmem hep
        · rw [hnew_c, hsend_eq] at hep ⊢
          dsimp only at hep ⊢
          rw [hsnd_succ, hst, hsend_eq, Function.update_self]
      hsent := fun e he => by
        rcases hsent e he with hmem | ⟨hfalse, _⟩
        · have hep : e.1.1.1 ≤ t := by
            have := hk.hsent_ep e hmem
            rwa [htcur_all] at this
          rw [hK'_le e.1.1.1 hep]
          exact hk.hsent e hmem
        · rw [hnew] at hfalse
          cases hfalse
      hrecv := fun R t₀ v₁ hv₁ => by
        rw [hvR_eq] at hv₁
        have ht₀ : t₀ ≤ t := by
          have := ((hvR' R t₀).mp (by rw [hv₁]; rfl)).1
          rwa [htcur_all] at this
        rw [hK'_le t₀ ht₀]
        exact hk.hrecv R t₀ v₁ hv₁
      hsend := fun R v₁ hv₁ hRsnd => by
        by_cases hR : R = Q
        · subst hR
          rw [hst, hsend_eq, Function.update_self] at hv₁ ⊢
          injection hv₁ with hv₁_eq
          subst hv₁_eq
          exact hout_agree
        · rw [hst, Function.update_of_ne hR] at hv₁ hRsnd ⊢
          rw [htcur_all R, hK'_le t (le_refl t), ← htcur_all R]
          exact hk.hsend R v₁ hv₁ hRsnd
      hahead := fun R hR => by
        rcases Party.eq_or_eq_other Q R with hRQ | hRQ
        · subst hRQ
          rw [hst, hsend_eq, Function.update_self, Function.update_of_ne (Party.other_ne R)]
          dsimp only
          refine ⟨hQ_succ, rc, ?_, ?_, ?_⟩
          · dsimp only [c_cka, dhScheme]; rw [hγQ']
          · dsimp only [c_cka, dhScheme]; rw [hγQ']
          · rw [hK'_succ]
            change (rootPRNG P.C.F encPt).up stO.root
              ((dhScheme Dh).receive stO.γ (Dh.dh rc Dh.base)).2 =
              (p_up.1, p_up.2)
            rw [hroot_eq, Party.other_other, hγO]
            dsimp only [p_up, c_cka, dhScheme, stQ]
            rw [hγQ']
            dsimp only
            rw [hDh rc x]
        · subst hRQ
          rw [hst, hsend_eq, Party.other_other, Function.update_of_ne (Party.other_ne Q),
            Function.update_self] at hR
          dsimp only at hR
          rw [htO] at hR
          omega
      hequal := fun R hR _ => by
        rcases Party.eq_or_eq_other Q R with hRQ | hRQ
        · subst hRQ
          rw [hst, hsend_eq, Function.update_self, Function.update_of_ne (Party.other_ne R)] at hR
          dsimp only at hR
          rw [htO] at hR
          omega
        · subst hRQ
          rw [hst, hsend_eq, Party.other_other, Function.update_of_ne (Party.other_ne Q),
            Function.update_self] at hR
          dsimp only at hR
          rw [htO] at hR
          omega
      hgap := fun R => by
        rcases Party.eq_or_eq_other Q R with hRQ | hRQ
        · subst hRQ
          rw [hst, hsend_eq, Function.update_self, Function.update_of_ne (Party.other_ne R)]
          dsimp only
          rw [htO]
        · subst hRQ
          rw [hst, hsend_eq, Party.other_other, Function.update_of_ne (Party.other_ne Q),
            Function.update_self]
          dsimp only
          rw [htO]
          omega
      hvS := fun R hRsnd => by
        by_cases hR : R = Q
        · subst hR
          rw [hst, hsend_eq, Function.update_self]
          rfl
        · rw [hst, Function.update_of_ne hR] at hRsnd ⊢
          exact hk.hvS R hRsnd
      hsent_ep := fun e he => by
        rcases hsent e he with hmem | ⟨hfalse, _⟩
        · have hep : e.1.1.1 ≤ t := by
            have := hk.hsent_ep e hmem
            rwa [htcur_all] at this
          by_cases hS : Party.senderOf e.1.1.1 = Q
          · rw [hS, hst, hsend_eq, Function.update_self]
            dsimp only
            omega
          · rw [hst, Function.update_of_ne hS, htcur_all]
            exact hep
        · rw [hnew] at hfalse
          cases hfalse
      hroot := fun R => by
        by_cases hR : R = Q
        · subst hR
          rw [hst, hsend_eq, Function.update_self]
          dsimp only
          exact hrk'_succ.symm
        · rw [hst, Function.update_of_ne hR, htcur_all R, hrk'_le t (le_refl t), ← htcur_all R]
          exact hk.hroot R
      hγ_exp := fun R hRsnd => by
        by_cases hR : R = Q
        · subst hR
          rw [hst, hsend_eq, Function.update_self]
          dsimp only [c_cka, dhScheme, stQ, t]
          rw [hγQ', hrc]
        · rw [hst, Function.update_of_ne hR] at hRsnd ⊢
          exact hk.hγ_exp R hRsnd
      hStep := fun t₀ ht1 => by
        rw [hmax_new] at ht1
        by_cases ht₀_eq : t₀ = t
        · subst ht₀_eq
          rw [hrk'_succ, hK'_succ, hrk'_le t (le_refl t)]
          have hroot_Q : stQ.root = rk t := hk.hroot Q
          dsimp only [p_up, Ratchet.rootPRNG, c_cka, dhScheme]
          rw [hγQ', hroot_Q, hx_eq, ← hrc]
        · have ht₀_lt : t₀ < t := by omega
          rw [hrk'_le t₀ (by omega), hK'_le (t₀ + 1) (by omega), hrk'_le (t₀ + 1) (by omega)]
          exact hk.hStep t₀ (by rw [hmax_old]; exact ht₀_lt)
      hsnaps := fun snap hsnap => by
        rw [hmax_new]
        exact SnapSync.congr (hk.hsnaps snap hsnap) (by rw [hmax_old]; omega)
          (fun t₀ ht₀ => hK'_le t₀ (by rw [← hmax_old]; exact ht₀))
          (fun t₀ ht₀ => hrk'_le t₀ (by rw [← hmax_old]; exact ht₀))
          (fun _ _ => rfl) }

theorem epochSync_send_of_short (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (honest honest' : List (List (BitVec 8) × Fig8C Pt))
    (sent sent' : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    {snaps : List (Party × ℕ × GhostState PQ)}
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {epExp : ℕ → BitVec 256}
    (h : EpochSync P Dh encPt encT idOf honest sent snaps s_fig8 epExp)
    (hvR' : ∀ R t, ((s_fig8.st R).vR t).isSome ↔ (t ≤ (s_fig8.st R).tcur ∧ R.sendsIn t = false))
    (hid : ∀ R, (s_fig8.st R).id = R)
    (hhonEp : ∀ wc ∈ honest, wc.2.1.1 ≤ (s_fig8.st (Party.senderOf wc.2.1.1)).tcur)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : BitVec 256)
    (hrc : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = true →
      epExp ((s_fig8.st Q).tcur + 1) = rc)
    (hst : s_fig8'.st = Function.update s_fig8.st Q
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).1)
    (hwin : s_fig8'.win = false → s_fig8.win = false)
    (hhon : ∀ wc ∈ honest', wc ∈ honest ∨
      wc.2 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2)
    (hsent : ∀ e ∈ sent', e ∈ sent ∨
      ((s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = false ∧
        e.1 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2 ∧
        (s_fig8.st Q).vS = some e.2))
    (hm : (decide (m.1.pqmsg.length < rustLenBound) &&
      m.1.addrs.all fun a => decide (a.length < rustLenBound)) = true) :
    EpochSync P Dh encPt encT idOf honest' sent' snaps s_fig8' epExp := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
  obtain ⟨hpq, haddr_all⟩ := hm
  have haddr : ∀ a, m.1.addrs = some a → a.length < rustLenBound := fun a ha => by
    rw [ha] at haddr_all
    simpa using haddr_all
  intro hw'
  obtain ⟨K, rk, hk⟩ := h (hwin hw')
  cases hcond : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) with
  | false =>
    exact ⟨K, rk, ses_epochSync_send_same P Dh encPt encT idOf lam hD hrt honest honest' sent sent'
      s_fig8 s_fig8' K rk epExp hk hid Q m rc hcond hst hhon hsent hpq haddr⟩
  | true =>
    exact ses_epochSync_send_new P Dh hDh encPt encT idOf lam hD hrt honest honest' sent sent'
      s_fig8 s_fig8' K rk epExp hk hvR' hid hhonEp Q m rc hcond (hrc hcond) hst hhon hsent hpq haddr

theorem epochSync_send_of_sent (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (honest honest' : List (List (BitVec 8) × Fig8C Pt))
    (sent sent' : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    {snaps : List (Party × ℕ × GhostState PQ)}
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {epExp : ℕ → BitVec 256}
    (h : EpochSync P Dh encPt encT idOf honest sent snaps s_fig8 epExp)
    (hvR' : ∀ R t, ((s_fig8.st R).vR t).isSome ↔ (t ≤ (s_fig8.st R).tcur ∧ R.sendsIn t = false))
    (hid : ∀ R, (s_fig8.st R).id = R)
    (hhonEp : ∀ wc ∈ honest, wc.2.1.1 ≤ (s_fig8.st (Party.senderOf wc.2.1.1)).tcur)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : BitVec 256)
    (hrc : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = true →
      epExp ((s_fig8.st Q).tcur + 1) = rc)
    (hst : s_fig8'.st = Function.update s_fig8.st Q
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).1)
    (hwin : s_fig8'.win = false → s_fig8.win = false)
    (hhon : ∀ wc ∈ honest', wc ∈ honest ∨
      wc.2 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2)
    (hsent : ∀ e ∈ sent', e ∈ sent ∨
      ((s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = false ∧
        e.1 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2 ∧
        (s_fig8.st Q).vS = some e.2))
    (hpq : RoundTrip.SentPq P m.1.pqmsg) (haddr : RoundTrip.SentAddrs P m.1.addrs) :
    EpochSync P Dh encPt encT idOf honest' sent' snaps s_fig8' epExp := by
  have hshort := RoundTrip.LengthsOk.short hrt.len (h := lHeader encT 1 (0, none) m.1)
    (body := List.replicate (16 * nBlocks ℓ) 0) rfl hpq haddr (by simp)
  refine epochSync_send_of_short P Dh hDh encPt encT idOf lam hD hrt honest honest' sent sent'
    s_fig8 s_fig8' h hvR' hid hhonEp Q m rc hrc hst hwin hhon hsent ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hshort.2.1, ?_⟩
  cases h : m.1.addrs with
  | none => rfl
  | some a =>
    simp only [Option.all_some, decide_eq_true_eq]
    exact hshort.2.2.1 a h

/-- `EpochSync` is preserved across a session `send` step. -/
theorem epochSync_send (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (hD : ∀ k x, P.C.D k (P.C.E k x) = x) (hrt : RoundTrip.RtHyp P ℓ)
    (honest honest' : List (List (BitVec 8) × Fig8C Pt))
    (sent sent' : List (Fig8C Pt × FSAEAD.RatchetSenderState (BitVec 256)))
    {snaps : List (Party × ℕ × GhostState PQ)}
    (s_fig8 s_fig8' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    {epExp : ℕ → BitVec 256}
    (h : EpochSync P Dh encPt encT idOf honest sent snaps s_fig8 epExp)
    (hvR' : ∀ R t, ((s_fig8.st R).vR t).isSome ↔ (t ≤ (s_fig8.st R).tcur ∧ R.sendsIn t = false))
    (hid : ∀ R, (s_fig8.st R).id = R)
    (hhonEp : ∀ wc ∈ honest, wc.2.1.1 ≤ (s_fig8.st (Party.senderOf wc.2.1.1)).tcur)
    (Q : Party) (m : LibsignalMsgPublicPart × Plain ℓ) (rc : BitVec 256)
    (hrc : (s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = true →
      epExp ((s_fig8.st Q).tcur + 1) = rc)
    (hst : s_fig8'.st = Function.update s_fig8.st Q
      ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).1)
    (hwin : s_fig8'.win = false → s_fig8.win = false)
    (hhon : ∀ wc ∈ honest', wc ∈ honest ∨
      wc.2 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2)
    (hsent : ∀ e ∈ sent', e ∈ sent ∨
      ((s_fig8.st Q).id.sendsIn ((s_fig8.st Q).tcur + 1) = false ∧
        e.1 = ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).send (s_fig8.st Q) m rc).2 ∧
        (s_fig8.st Q).vS = some e.2))
    (hpq : RoundTrip.SentPq P m.1.pqmsg) (haddr : RoundTrip.SentAddrs P m.1.addrs) :
    EpochSync P Dh encPt encT idOf honest' sent' snaps s_fig8' epExp :=
  epochSync_send_of_sent P Dh hDh encPt encT idOf lam hD hrt honest honest' sent sent' s_fig8 s_fig8' h
    hvR' hid hhonEp Q m rc hrc hst hwin hhon hsent hpq haddr

end CryptoGames.LibsignalSM.Proofs.Refinement
