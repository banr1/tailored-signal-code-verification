/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.WireHop
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RoundTrip
import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Wire-hop synchronization invariant for short public parts

**Checked by Lean.**

Defines `RealSync` and proves observational equivalence between `wireBranch ... false 0` and
`saltRunNF ... false` when encryption ADs have short public parts.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.LibsignalSM.Proofs.ProstWireHop.Helpers

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD CryptoGames.LibsignalSM.Proofs.WireHop

variable {Pt : Type}

/-- Synchronization invariant between `wRealStep` and `saltImplNF ... false` recording `shortB` on
the challenge AD. -/
structure RealSync [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (epoch : ℕ)
    (st : WRedSt) (wc : Option (SerializedIdentityKeys × (List (BitVec 8) × BitVec 64)))
    (o : Option DerivedMessageKeys) (sst : SaltSt Pt) : Prop where
  hab : st.2.2.1 = false
  hchal :
    if st.2.2.2 then
      ∃ (a₀ : ADType Pt) (m₀ : Plain ℓ) (k₀ : DerivedMessageKeys),
        st.1.idxOf? a₀.2.2.salt = some 0 ∧
        o = some k₀ ∧
        sst.table.lookup a₀.2.2.salt = some k₀ ∧
        lCls a₀ = epoch ∧
        ¬(a₀.1 = 0 ∨ 2 ^ 32 < a₀.1) ∧
        a₀.2.2.shortB = true ∧
        wc = some (lIds idOf a₀.2.1.1,
          (lWire C codec ℓ).enc k₀ (lIds idOf a₀.2.1.1) (lHeader encT a₀.1 a₀.2.1 a₀.2.2) m₀) ∧
        sst.chal = some (a₀,
          ((lWire C codec ℓ).enc k₀ (lIds idOf a₀.2.1.1) (lHeader encT a₀.1 a₀.2.1 a₀.2.2) m₀,
            a₀.2.2.salt))
    else
      st.1 = [] ∧ wc = none ∧ o = none ∧ sst.chal = none ∧ sst.table = []

theorem RealSync.chal_preserve [DecidableEq Pt] {C : Crypto} {codec : SignalMessageProtoCodec} {ℓ : ℕ}
    {encT : Pt → PublicKey} {idOf : Party → IdentityKey} {epoch : ℕ}
    {st : WRedSt} {wc : Option (SerializedIdentityKeys × (List (BitVec 8) × BitVec 64))}
    {o : Option DerivedMessageKeys} {sst : SaltSt Pt}
    (hsync : RealSync C codec ℓ encT idOf epoch st wc o sst)
    (salt : Salt32) (heq : st.2.2.2 = true) :
    RealSync C codec ℓ encT idOf epoch
      ((stepSlot st.1 salt).2, st.2.1, st.2.2.1, true) wc o sst := by
  have hch := hsync.hchal
  simp only [heq, ↓reduceIte] at hch
  rcases hch with ⟨a₀, m₀, k₀, hidx, ho, hlk, hcls₀, hbad₀, hshort₀, hwc, hsas⟩
  refine ⟨hsync.hab, ?_⟩
  simp only [↓reduceIte]
  exact ⟨a₀, m₀, k₀, stepSlot_idxOf?_pres st.1 salt a₀.2.2.salt hidx,
    ho, hlk, hcls₀, hbad₀, hshort₀, hwc, hsas⟩

theorem evalDist_wRealLazy_eq_saltRunNF_false_aux [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (epoch : ℕ)
    (hinj : Function.Injective encT) (hdum : ∀ r, encT r ≠ dummyKey)
    (hrt : SignalRoundTripShort codec)
    (oa : OracleComp (QSpecS Pt ℓ) Bool) :
    ∀ (st : WRedSt) (wc : Option (SerializedIdentityKeys × (List (BitVec 8) × BitVec 64)))
      (o : Option DerivedMessageKeys) (sst : SaltSt Pt),
      oa.IsQueryBoundP (fun t => otQueryADOutsideClass lCls epoch t = true) 0 →
      oa.IsQueryBoundP (fun t => otBadIdx (Pt := Pt) (ℓ := ℓ) t = true) 0 →
      oa.IsQueryBoundP (fun t => otEncBad (M := Plain ℓ) (C := CtType)
        (fun a : ADType Pt => a.2.2.shortB) t = true) 0 →
      RealSync C codec ℓ encT idOf epoch st wc o sst →
      𝒟[(simulateQ (wRealStep C codec ℓ encT idOf 0 getSlotKey) oa).run ((st, wc), o) >>= fun z =>
        if z.2.1.1.2.2.1 || (!z.2.1.1.2.2.2 && (0 : ℕ) ≠ 0) then $ᵗ Bool else pure z.1] =
      𝒟[(simulateQ (saltImplNF C codec ℓ encT idOf false) oa).run sst >>= fun z => pure z.1] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st wc o sst _ _ _ hsync
    simp [hsync.hab]
  | query_bind q k ih =>
    intro st wc o sst hcls hidx hshort hsync
    have ⟨hcls_q, hcls_k⟩ := isQueryBoundP_zero_query_bind q k hcls
    have ⟨hidx_q, hidx_k⟩ := isQueryBoundP_zero_query_bind q k hidx
    have ⟨hshort_q, hshort_k⟩ := isQueryBoundP_zero_query_bind q k hshort
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc]
    rcases q with n | ⟨a, m⟩ | ⟨a, e⟩
    · simp only [wRealStep, saltImplNF, onH, EtMProof.coin, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, StateT.run_monadLift, StateT.run_mk, map_eq_bind_pure_comp,
        Function.comp_apply, bind_assoc, pure_bind]
      exact evalDist_bind_congr _ _ _ fun u =>
        ih u st wc o sst (hcls_k u) (hidx_k u) (hshort_k u) hsync
    · have ha_cls : lCls a = epoch := by
        simpa [otQueryADOutsideClass] using hcls_q
      have ha_idx : ¬(a.1 = 0 ∨ 2 ^ 32 < a.1) := by
        simpa [otBadIdx] using hidx_q
      have ha_short : a.2.2.shortB = true := by
        simpa [otEncBad] using hshort_q
      by_cases heq : st.2.2.2 = true
      · have hchal := hsync.hchal
        simp only [heq, ↓reduceIte] at hchal
        rcases hchal with ⟨a₀, m₀, k₀, _, _, _, _, _, _, _, hsas⟩
        have hcs : sst.chal.isSome = true := by simp [hsas]
        simp only [wRealStep, saltImplNF, onH, StateT.run_bind, StateT.run_get, StateT.run_mk,
          map_pure, pure_bind, heq, hcs, ↓reduceIte, StateT.run_pure]
        exact ih none st wc o sst (hcls_k none) (hidx_k none) (hshort_k none) hsync
      · have heqf : st.2.2.2 = false := Bool.eq_false_iff.mpr heq
        have hchal := hsync.hchal
        simp only [heqf, Bool.false_eq_true, ↓reduceIte] at hchal
        rcases hchal with ⟨hst1, hwc, ho, hsas, htab⟩
        have hcs : sst.chal.isSome = false := by simp [hsas]
        have hn0 : (stepSlot st.1 a.2.2.salt).1 = 0 := by simp [hst1, stepSlot]
        have hs0 : (stepSlot st.1 a.2.2.salt).2 = [a.2.2.salt] := by simp [hst1, stepSlot]
        simp only [wRealStep, saltImplNF, onH, getSlotKey, sKeyOf, StateT.run_bind,
          StateT.run_get, StateT.run_mk, map_pure, pure_bind, heqf, hcs, Bool.false_eq_true,
          ↓reduceIte, ne_eq, hn0, not_true_eq_false, StateT.run_set, StateT.run_modify,
          StateT.run_pure, bind_assoc, ho, htab, List.lookup_nil, bind_map_left, lAeadK]
        refine evalDist_bind_congr ($ᵗ DerivedMessageKeys) _ _ fun k₀ => ?_
        refine ih _ _ _ (some k₀) _ (hcls_k _) (hidx_k _) (hshort_k _) ⟨hsync.hab, ?_⟩
        dsimp only [↓reduceIte]
        exact ⟨a, m, k₀, by simp [hs0], rfl, by simp, ha_cls, ha_idx, ha_short, rfl, rfl⟩
    · have ha_cls : lCls a = epoch := by
        simpa [otQueryADOutsideClass] using hcls_q
      have ha_idx : ¬(a.1 = 0 ∨ 2 ^ 32 < a.1) := by
        simpa [otBadIdx] using hidx_q
      by_cases hs : e.2 ≠ a.2.2.salt
      · simp only [wRealStep, saltImplNF, onH, StateT.run_bind, StateT.run_get, StateT.run_mk,
          map_pure, pure_bind, hs, ne_eq, not_false_eq_true, decide_true, Bool.or_true, ↓reduceIte,
          StateT.run_pure]
        exact ih none st wc o sst (hcls_k none) (hidx_k none) (hshort_k none) hsync
      · simp only [ne_eq, Decidable.not_not] at hs
        by_cases heq : st.2.2.2 = true
        · have hchal := hsync.hchal
          simp only [heq, ↓reduceIte] at hchal
          rcases hchal with ⟨a₀, m₀, k₀, hidx₀, ho, hlk₀, hcls₀, hbad₀, hshort₀, hwc, hsas⟩
          have hsync_step := hsync.chal_preserve a.2.2.salt heq
          by_cases hn0 : (stepSlot st.1 a.2.2.salt).1 = 0
          · have hsalt_eq : a.2.2.salt = a₀.2.2.salt :=
              (stepSlot_fst_eq_iff_idxOf? st.1 a.2.2.salt a₀.2.2.salt hidx₀).mp hn0
            have hcs_true : isChalSalt sst.chal a.2.2.salt = true := by
              simp [isChalSalt, hsas, hsalt_eq]
            have hlk_salt : sst.table.lookup a.2.2.salt = some k₀ := by
              rw [hsalt_eq, hlk₀]
            have hids_eq : lIds idOf a.2.1.1 = lIds idOf a₀.2.1.1 := by
              have : a.2.1.1 = a₀.2.1.1 := ha_cls.trans hcls₀.symm
              rw [this]
            by_cases he1 : e.1 =
                (lWire C codec ℓ).enc k₀ (lIds idOf a₀.2.1.1) (lHeader encT a₀.1 a₀.2.1 a₀.2.2) m₀
            · have hwc_true : (wc == some (lIds idOf a.2.1.1, e.1)) = true := by
                simp [hwc, hids_eq, he1]
              by_cases ha : a = a₀
              · have he_eq : e =
                    ((lWire C codec ℓ).enc k₀ (lIds idOf a₀.2.1.1)
                      (lHeader encT a₀.1 a₀.2.1 a₀.2.2) m₀, a₀.2.2.salt) :=
                  Prod.ext he1 (hs.trans hsalt_eq)
                have hchal_true : (sst.chal == some (a, e)) = true := by
                  simp [hsas, ha, he_eq]
                simp only [wRealStep, saltImplNF, onH, StateT.run_bind, StateT.run_get,
                  StateT.run_mk, map_pure, pure_bind, heq, Bool.not_true, hs, ne_eq,
                  not_true_eq_false, decide_false, Bool.false_or, ↓reduceIte, StateT.run_set, hn0,
                  hwc_true, hcs_true, hchal_true, StateT.run_pure]
                exact ih none _ wc o sst (hcls_k none) (hidx_k none) (hshort_k none) hsync_step
              · have hchal_false : (sst.chal == some (a, e)) = false := by
                  rw [hsas]
                  simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
                  intro ha_eq _
                  exact ha ha_eq.symm
                have hdec_none : (lAeadK C codec ℓ encT idOf).dec k₀ ((a.1, a.2.1), a.2.2) e =
                    none := by
                  have hparse_ex : ∃ body, (signalWireCodec codec).parse e.1.1 =
                      some (lHeader encT a₀.1 a₀.2.1 a₀.2.2, body) := by
                    rw [he1]
                    exact ⟨_, hrt (lHeader encT a₀.1 a₀.2.1 a₀.2.2) _
                      (ProstMsgAeadCorrect.short_lHeader hℓ encT a₀.1 a₀.2.1 hshort₀ _
                        (RoundTrip.length_cbcBody _))⟩
                  rcases hparse_ex with ⟨body, hparse⟩
                  have hne_hdr : lHeader encT a₀.1 a₀.2.1 a₀.2.2 ≠
                      lHeader encT a.1 a.2.1 a.2.2 := by
                    intro hhdr
                    have hepoch : a₀.2.1.1 = a.2.1.1 := hcls₀.trans ha_cls.symm
                    exact ha (lHeader_inj hinj hdum hepoch.symm hsalt_eq
                      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hhdr.symm)
                  exact lAeadK_dec_eq_none_of_parse C codec ℓ encT idOf k₀ a e _ body hparse hne_hdr
                simp only [wRealStep, saltImplNF, onH, StateT.run_bind, StateT.run_get,
                  StateT.run_mk, map_pure, pure_bind, heq, Bool.not_true, hs, ne_eq,
                  not_true_eq_false, decide_false, Bool.false_or, ↓reduceIte, StateT.run_set, hn0,
                  hwc_true, hcs_true, hchal_false, Bool.false_eq_true, sKeyOf, hlk_salt, hdec_none,
                  StateT.run_pure]
                exact ih none _ wc o sst (hcls_k none) (hidx_k none) (hshort_k none) hsync_step
            · have hwc_false : (wc == some (lIds idOf a.2.1.1, e.1)) = false := by
                rw [hwc, hids_eq]
                simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
                intro _ he_eq
                exact he1 he_eq.symm
              have hchal_false : (sst.chal == some (a, e)) = false := by
                rw [hsas]
                simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
                intro _ he_eq
                exact he1 (congrArg Prod.fst he_eq).symm
              simp only [wRealStep, saltImplNF, onH, getSlotKey, sKeyOf, StateT.run_bind,
                StateT.run_get, StateT.run_mk, map_pure, pure_bind, heq, Bool.not_true, hs,
                ne_eq, not_true_eq_false, decide_false, Bool.false_or, ↓reduceIte, StateT.run_set,
                hn0, hwc_false, Bool.false_eq_true, ho, hcs_true, hchal_false, hlk_salt,
                StateT.run_pure]
              exact ih _ _ wc (some k₀) sst (hcls_k _) (hidx_k _) (hshort_k _) (ho ▸ hsync_step)
          · have hne_salt : a.2.2.salt ≠ a₀.2.2.salt := fun he =>
              hn0 ((stepSlot_fst_eq_iff_idxOf? st.1 a.2.2.salt a₀.2.2.salt hidx₀).mpr he)
            have hcs_false : isChalSalt sst.chal a.2.2.salt = false := by
              simp [isChalSalt, hsas, beq_eq_false_iff_ne.mpr hne_salt]
            simp only [wRealStep, saltImplNF, onH, StateT.run_bind, StateT.run_get,
              StateT.run_mk, map_pure, pure_bind, heq, Bool.not_true, hs, ne_eq,
              not_true_eq_false, decide_false, Bool.false_or, ↓reduceIte, StateT.run_set, hn0,
              hcs_false, Bool.not_false, Bool.true_or, StateT.run_pure]
            exact ih none _ wc o sst (hcls_k none) (hidx_k none) (hshort_k none) hsync_step
        · have heqf : st.2.2.2 = false := Bool.eq_false_iff.mpr heq
          have hchal := hsync.hchal
          simp only [heqf, Bool.false_eq_true, ↓reduceIte] at hchal
          have hcs_false : isChalSalt sst.chal a.2.2.salt = false := by
            simp [isChalSalt, hchal.2.2.2.1]
          simp only [wRealStep, saltImplNF, onH, StateT.run_bind, StateT.run_get,
            StateT.run_mk, map_pure, pure_bind, heqf, Bool.not_false, hs, ne_eq,
            not_true_eq_false, decide_false, Bool.false_or, Bool.true_or, ↓reduceIte, hcs_false,
            StateT.run_pure]
          exact ih none st wc o sst (hcls_k none) (hidx_k none) (hshort_k none) hsync

theorem evalDist_wireBranch_false [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (ADType Pt) (Plain ℓ) CtType)
    (hinj : Function.Injective encT) (hdum : ∀ r, encT r ≠ dummyKey)
    (hrt : SignalRoundTripShort codec)
    (hcls : AEADScheme.OTAllQueriesInOneADClass lCls B)
    (hidx : B.IsQueryBoundP (fun t => otBadIdx (Pt := Pt) (ℓ := ℓ) t = true) 0)
    (hshort : AEADScheme.OTEncADsOk (fun a : ADType Pt => a.2.2.shortB) B) :
    𝒟[wireBranch C codec ℓ encT idOf false 0 B] =
      𝒟[saltRunNF C codec ℓ encT idOf false B] := by
  rcases hcls with ⟨epoch, hcls_epoch⟩
  rw [evalDist_wireBranch_false_eq_lazy]
  unfold saltRunNF saltFullNF
  rw [map_eq_bind_pure_comp]
  exact evalDist_wRealLazy_eq_saltRunNF_false_aux C codec ℓ hℓ encT idOf epoch hinj hdum hrt B
    ([], [], false, false) none none {} hcls_epoch hidx hshort
    ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

end CryptoGames.LibsignalSM.Proofs.ProstWireHop.Helpers
